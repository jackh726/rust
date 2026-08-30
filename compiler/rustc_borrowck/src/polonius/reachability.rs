//! Set-based computation of loan liveness within the localized constraint graph.
//!
//! The graph has two kinds of edge, and the difference between them is what this module is built
//! around:
//!
//! - **Subset edges**, `'a@p -> 'b@p`, one per outlives constraint: a loan in `'a` at `p` is also in
//!   `'b` at `p`. A constraint tied to a single location applies at that one point and is indexed by
//!   it -- the "physical" edges; a constraint that holds at every point applies wherever the
//!   traversal happens to be, and is stored once per region rather than materialized per point --
//!   the "logical" edges. Those two names describe how the edge is *stored*, not what it means: both
//!   are the same edge, and the split exists so that an all-points constraint does not cost one
//!   edge per point in the CFG.
//! - **Liveness edges**, `'a@p -> 'a@q` for CFG-adjacent `p` and `q`: how a loan moves through the
//!   CFG within one region. These are not outlives constraints at all. They exist where the region
//!   is live, and point forwards, backwards, or both according to its variance.
//!
//! A subset edge hands a set of points to another region *unchanged*. A liveness edge transforms
//! one -- and the transformation is a closure within a single basic block, which is what makes the
//! set representation pay off.
//!
//! The direct way to compute this is a DFS per loan over the `(region, point)` nodes of the graph:
//! that is what [`LocalizedConstraintGraph::traverse`] does, and what the polonius MIR dumps use to
//! show the individual edges. Its cost is proportional to the number of reachable nodes, and a
//! region that is live over a large part of the CFG -- a universal region in particular, which is
//! semantically live everywhere -- is walked point by point, once per loan. That is quadratic in
//! the number of loans.
//!
//! Here, we instead propagate *sets of points* per region. The worklist holds `(region, block)`
//! pairs rather than nodes, and the two kinds of edge become two kinds of set operation:
//!
//! - a subset edge unions points into the successor region: for a logical edge, the whole set
//!   reached for `r` in this block; for a physical edge at `(r, p)`, only `p`, and only when `p` is
//!   in that set,
//! - a liveness edge closes the set over the CFG: forwards, "step to the next point in the same
//!   block, if the region is live there", plus terminator to successor-block entry; backwards, the
//!   same in reverse, gated on liveness at the *source* point.
//!
//! The intra-block closures are the interesting part, see [`LoanReachability::close_within_block`].
//! Per loan, the cost is then proportional to the number of reachable regions times the number of
//! rounds, rather than to the number of reachable points.
//!
//! The reachable set is the same as the DFS's by construction: both are the least fixpoint of the
//! same edge relation, starting from the same node.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};

use rustc_data_structures::fx::FxHashMap;
use rustc_index::bit_set::{DenseBitSet, GrowableBitSet};
use rustc_index::{IndexSlice, IndexVec};
use rustc_middle::mir::{BasicBlock, Body};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use self::loan_set::{BATCH_SIZE, LoanSet};
use crate::BorrowSet;
use crate::dataflow::BorrowIndex;
use crate::polonius::ConstraintDirection::{self, Backward, Bidirectional, Forward};
use crate::polonius::constraints::liveness_edge_direction;
use crate::polonius::live_loans::LiveLoans;
use crate::polonius::{DeferredLiveness, LocalizedConstraintGraph};
#[cfg(debug_assertions)]
use crate::polonius::{
    LocalizedConstraintGraphTraversal, LocalizedConstraintGraphVisitor, LocalizedNode,
};
use crate::region_infer::values::LivenessValues;
use crate::universal_regions::UniversalRegions;

mod loan_set;
#[cfg(test)]
mod tests;

rustc_index::newtype_index! {
    #[orderable]
    struct RegionInBlockIndex {}
}

rustc_index::newtype_index! {
    #[orderable]
    struct BlockIndex {}
}

impl BlockIndex {
    /// The index of `point` within `block`.
    fn from_point(point: PointIndex, block: BasicBlock, location_map: &DenseLocationMap) -> Self {
        let entry = location_map.entry_point(block);
        BlockIndex::from_usize(point.as_usize() - entry.as_usize())
    }
}

/// A worklist of pairs: a priority queue that holds a pair at most once.
struct Queue {
    heap: BinaryHeap<Reverse<(u32, RegionInBlockIndex)>>,
    queued: GrowableBitSet<RegionInBlockIndex>,
}

impl Queue {
    fn new() -> Queue {
        Queue { heap: BinaryHeap::new(), queued: GrowableBitSet::new_empty() }
    }

    fn push(&mut self, region_block: RegionInBlockIndex, priority: u32) {
        if self.queued.insert(region_block) {
            self.heap.push(Reverse((priority, region_block)));
        }
    }

    fn pop(&mut self) -> Option<RegionInBlockIndex> {
        let Reverse((_, region_block)) = self.heap.pop()?;
        self.queued.remove(region_block);
        Some(region_block)
    }

    fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    fn clear(&mut self) {
        self.heap.clear();
        self.queued.clear();
    }
}

/// The loans of the batch that have reached one region within one basic block: per point of the
/// block, the loans reached so far, and among those, the ones not yet propagated onwards.
struct RegionInBlock {
    region: RegionVid,
    block: BasicBlock,
    /// Whether the region is universal: semantically live at all points, propagating loans
    /// forwards only.
    universal: bool,
    /// The direction the region's liveness edges flow in.
    direction: ConstraintDirection,
    loans: IndexVec<BlockIndex, LoanSet>,
    pending: IndexVec<BlockIndex, LoanSet>,
}

/// Computes the points at which each loan is live, as the reachability of each loan within the
/// localized constraint graph. See the module documentation for the general shape of the
/// computation.
///
/// Nothing in the graph depends on the loan being traversed -- liveness, variances and edges are
/// all per body, only the start node is per loan -- so the loans are traversed [`BATCH_SIZE`] at a
/// time: the state a batch keeps per reached `(region, block)` is one loan set per point, holding
/// the set of the batch's loans that reach the region there, and every step of the traversal is a
/// word-wise operation on those. A node reached by many loans of a batch is then processed once
/// rather than once per loan, which is what makes the shapes where loans pile up -- a builder
/// chain, or loans held in a universal region across a big CFG -- cost the same as a single loan.
pub(super) struct LoanReachability<'a, 'tcx> {
    body: &'a Body<'tcx>,
    location_map: &'a DenseLocationMap,
    liveness: &'a mut LivenessValues,
    graph: &'a LocalizedConstraintGraph,
    live_region_variances: &'a mut BTreeMap<RegionVid, ConstraintDirection>,
    universal_regions: &'a UniversalRegions<'tcx>,

    /// The liveness `liveness::generate` deferred, computed the first time a loan reaches one of
    /// its regions -- before any of that region's liveness or variance is read.
    deferred: DeferredLiveness<'a, 'tcx>,

    /// The direction of each reached region's liveness edges, computed on the first touch.
    directions: IndexVec<RegionVid, Option<ConstraintDirection>>,

    /// What the current batch has reached, per `(region, block)` pair.
    ///
    /// FIXME: this allocates two vectors per pair per batch; a single arena reused across batches
    /// would avoid that.
    region_blocks: IndexVec<RegionInBlockIndex, RegionInBlock>,
    region_block_indices: FxHashMap<(RegionVid, BasicBlock), RegionInBlockIndex>,

    /// The position of each block in a reverse postorder of the CFG.
    rpo_index: IndexVec<BasicBlock, u32>,

    /// The pairs that have loans pending propagation.
    ///
    /// The order they are processed in matters a lot: the loans of a batch enter the graph at
    /// different points, and if pairs were processed in the order they are reached, a pair
    /// downstream of several of them would be processed once per loan arriving -- which is the
    /// per-loan cost this batching is meant to avoid. So the pairs reached through edges flowing
    /// forwards in the CFG are processed in reverse postorder, which lets every loan that reaches
    /// a pair from upstream arrive before the pair is processed, and the pairs reached through
    /// edges flowing backwards in postorder, for the same reason in the other direction. The two
    /// queues are drained alternately until both are empty; only back edges, and a loan crossing
    /// from one direction to the other, cost another sweep.
    ///
    /// FIXME: a bucket queue over the reverse postorder index would make this O(1) per operation.
    forward_queue: Queue,
    backward_queue: Queue,
}

impl<'a, 'tcx> LoanReachability<'a, 'tcx> {
    pub(super) fn new(
        body: &'a Body<'tcx>,
        location_map: &'a DenseLocationMap,
        liveness: &'a mut LivenessValues,
        graph: &'a LocalizedConstraintGraph,
        live_region_variances: &'a mut BTreeMap<RegionVid, ConstraintDirection>,
        universal_regions: &'a UniversalRegions<'tcx>,
        deferred: DeferredLiveness<'a, 'tcx>,
    ) -> Self {
        let mut rpo_index = IndexVec::from_elem_n(u32::MAX, body.basic_blocks.len());
        for (i, &block) in body.basic_blocks.reverse_postorder().iter().enumerate() {
            rpo_index[block] = i as u32;
        }
        // Blocks unreachable from the start are not in the reverse postorder; order them last.
        let mut next = body.basic_blocks.reverse_postorder().len() as u32;
        for index in rpo_index.iter_mut() {
            if *index == u32::MAX {
                *index = next;
                next += 1;
            }
        }

        LoanReachability {
            body,
            location_map,
            liveness,
            graph,
            live_region_variances,
            universal_regions,
            deferred,
            directions: IndexVec::new(),
            region_blocks: IndexVec::new(),
            region_block_indices: FxHashMap::default(),
            rpo_index,
            forward_queue: Queue::new(),
            backward_queue: Queue::new(),
        }
    }

    /// Traverses the graph once per batch of loans, and returns the points at which each loan is
    /// live: the points it reaches a live region at.
    pub(super) fn compute_live_loans(&mut self, borrow_set: &BorrowSet<'tcx>) -> LiveLoans {
        let num_loans = borrow_set.len();
        let mut live_loans = LiveLoans::new(num_loans, self.location_map.num_points());

        for batch_start in (0..num_loans).step_by(BATCH_SIZE) {
            // Each loan of the batch enters the graph at the region and point it is introduced
            // at, with its own bit.
            for bit in 0..BATCH_SIZE.min(num_loans - batch_start) {
                let loan = &borrow_set[BorrowIndex::from_usize(batch_start + bit)];
                let start = loan.reserve_location;
                let point = self.location_map.point_from_location(start);
                self.add_at_point(loan.region, start.block, point, LoanSet::single(bit));
            }

            loop {
                while let Some(region_block) = self.forward_queue.pop() {
                    self.process(region_block, &mut live_loans, batch_start);
                }
                if self.backward_queue.is_empty() {
                    break;
                }
                while let Some(region_block) = self.backward_queue.pop() {
                    self.process(region_block, &mut live_loans, batch_start);
                }
                if self.forward_queue.is_empty() {
                    break;
                }
            }

            self.region_blocks.raw.clear();
            self.region_block_indices.clear();
            self.forward_queue.clear();
            self.backward_queue.clear();
        }

        #[cfg(debug_assertions)]
        debug_check_against_dfs(
            self.body,
            self.liveness,
            self.graph,
            self.live_region_variances,
            self.universal_regions,
            borrow_set,
            &live_loans,
        );

        live_loans
    }

    /// Propagates the loans pending for `region_block` to their successors in the graph, and records them
    /// in `live_loans` where the region is live.
    ///
    /// Propagation is per basic block rather than per point: the work is proportional to the
    /// `(region, block)` pairs a batch reaches, times the points of the block.
    fn process(
        &mut self,
        region_block: RegionInBlockIndex,
        live_loans: &mut LiveLoans,
        batch_start: usize,
    ) {
        let state = &mut self.region_blocks[region_block];
        let (region, block) = (state.region, state.block);
        let (universal, direction) = (state.universal, state.direction);
        let entry = self.location_map.entry_point(block);
        let len = state.loans.len();

        if state.pending.iter().all(|loans| loans.is_empty()) {
            return;
        }
        // Take the pending loans, leaving the pair with none.
        let pending =
            std::mem::replace(&mut state.pending, IndexVec::from_elem_n(LoanSet::EMPTY, len));

        let mut live: DenseBitSet<BlockIndex> = DenseBitSet::new_empty(len);
        let terminator = PointIndex::from_usize(entry.as_usize() + len - 1);
        if universal {
            live.insert_range(BlockIndex::ZERO..BlockIndex::from_usize(len));
        } else if let Some(live_points) = self.liveness.points().row(region) {
            for interval in live_points.iter_intervals() {
                if interval.end <= entry {
                    continue;
                }
                if interval.start > terminator {
                    break;
                }
                let start = interval.start.as_usize().max(entry.as_usize());
                let end = interval.end.as_usize().min(terminator.as_usize() + 1);
                live.insert_range(
                    BlockIndex::from_usize(start - entry.as_usize())
                        ..BlockIndex::from_usize(end - entry.as_usize()),
                );
            }
        }

        let mut closure = pending.clone();
        if matches!(direction, Forward | Bidirectional) {
            let mut previous = LoanSet::EMPTY;
            for (i, loans) in closure.iter_enumerated_mut() {
                if live.contains(i) {
                    loans.insert(previous);
                }
                previous = *loans;
            }
        }
        if matches!(direction, Backward | Bidirectional) {
            // Backward edges are only taken from a point where the region is live.
            let mut carry = LoanSet::EMPTY;
            for (i, loans) in closure.iter_enumerated_mut().rev() {
                let here = pending[i].union(carry);
                loans.insert(here);
                carry = if live.contains(i) { here } else { LoanSet::EMPTY };
            }
        }

        let state = &mut self.region_blocks[region_block];
        for (i, &loans) in closure.iter_enumerated() {
            state.loans[i].insert(loans);
            if live.contains(i) {
                for bit in loans.iter() {
                    live_loans
                        .insert(entry + i.index(), BorrowIndex::from_usize(batch_start + bit));
                }
            }
        }

        self.propagate_liveness_edges(region_block, &closure, &live);
        self.propagate_subset_edges(region_block, entry, terminator, &closure);
    }

    /// The liveness edges leaving the block: to the entry point of the successor blocks, and to
    /// the terminator of the predecessor blocks.
    fn propagate_liveness_edges(
        &mut self,
        region_block: RegionInBlockIndex,
        closure: &IndexSlice<BlockIndex, LoanSet>,
        live: &DenseBitSet<BlockIndex>,
    ) {
        let state = &self.region_blocks[region_block];
        let (region, block) = (state.region, state.block);
        let (universal, direction) = (state.universal, state.direction);
        let body = self.body;
        let last = BlockIndex::from_usize(closure.len() - 1);
        if matches!(direction, Forward | Bidirectional) && !closure[last].is_empty() {
            for successor in body[block].terminator().successors() {
                let point = self.location_map.entry_point(successor);
                if universal || self.liveness.is_live_at_point(region, point) {
                    self.add_at_point(region, successor, point, closure[last]);
                }
            }
        }
        if matches!(direction, Backward | Bidirectional)
            && !closure[BlockIndex::ZERO].is_empty()
            && live.contains(BlockIndex::ZERO)
        {
            for &predecessor in &body.basic_blocks.predecessors()[block] {
                let point = self.location_map.point_from_location(body.terminator_loc(predecessor));
                let region_block = self.region_block(region, predecessor);
                let i = BlockIndex::from_point(point, predecessor, self.location_map);
                if Self::add_at_point_inner(
                    &mut self.region_blocks[region_block],
                    i,
                    closure[BlockIndex::ZERO],
                ) {
                    let block = self.region_blocks[region_block].block;
                    let last = self.rpo_index.len() as u32 - 1;
                    self.backward_queue.push(region_block, last - self.rpo_index[block]);
                }
            }
        }
    }

    /// The subset edges: a logical one hands every point reached to the target region unchanged,
    /// a physical one applies at its own point only, and only if that point has been reached.
    fn propagate_subset_edges(
        &mut self,
        region_block: RegionInBlockIndex,
        entry: PointIndex,
        terminator: PointIndex,
        closure: &IndexSlice<BlockIndex, LoanSet>,
    ) {
        let (region, block) = {
            let state = &self.region_blocks[region_block];
            (state.region, state.block)
        };
        let graph = self.graph;
        for successor in graph.logical_successors(region) {
            let region_block = self.region_block(successor, block);
            self.add_at_points(region_block, closure);
        }
        // The points with physical edges are sorted, so we can jump to this block's range.
        let physical_points = graph.physical_points(region);
        let start = physical_points.partition_point(|&point| point < entry);
        for &point in &physical_points[start..] {
            if point > terminator {
                break;
            }
            let loans = closure[BlockIndex::from_usize(point.as_usize() - entry.as_usize())];
            if !loans.is_empty() {
                for successor in graph.physical_successors(region, point) {
                    self.add_at_point(successor, block, point, loans);
                }
            }
        }
    }

    /// The index of the `(region, block)` pair, creating its state if this is the first time the
    /// batch reaches the region in this block.
    fn region_block(&mut self, region: RegionVid, block: BasicBlock) -> RegionInBlockIndex {
        if let Some(&region_block) = self.region_block_indices.get(&(region, block)) {
            return region_block;
        }

        let universal = self.universal_regions.is_universal_region(region);

        // The first time any loan reaches `region`: computes the liveness that was deferred for it,
        // since everything below reads this region's liveness and variance, and the direction of its
        // liveness edges.
        let direction = *self.directions.get_or_insert_with(region, || {
            self.deferred.materialize(region, self.liveness, self.live_region_variances);
            if universal {
                Forward
            } else {
                liveness_edge_direction(self.live_region_variances, region)
            }
        });

        let len = self.body[block].statements.len() + 1;
        let region_block = self.region_blocks.push(RegionInBlock {
            region,
            block,
            universal,
            direction,
            loans: IndexVec::from_elem_n(LoanSet::EMPTY, len),
            pending: IndexVec::from_elem_n(LoanSet::EMPTY, len),
        });
        self.region_block_indices.insert((region, block), region_block);
        region_block
    }

    /// Records that the loans in `loans`, indexed by point offset within the pair's block, reach
    /// the pair's region.
    fn add_at_points(
        &mut self,
        region_block: RegionInBlockIndex,
        loans: &IndexSlice<BlockIndex, LoanSet>,
    ) {
        let state = &mut self.region_blocks[region_block];
        let mut any_new = false;
        for (i, &loans) in loans.iter_enumerated() {
            any_new |= Self::add_at_point_inner(state, i, loans);
        }
        if any_new {
            let block = self.region_blocks[region_block].block;
            self.forward_queue.push(region_block, self.rpo_index[block]);
        }
    }

    /// Records that the loans in `loans` reach `region` at `point`, which belongs to `block`.
    fn add_at_point(
        &mut self,
        region: RegionVid,
        block: BasicBlock,
        point: PointIndex,
        loans: LoanSet,
    ) {
        let region_block = self.region_block(region, block);
        let block_index = BlockIndex::from_point(point, block, self.location_map);
        if Self::add_at_point_inner(&mut self.region_blocks[region_block], block_index, loans) {
            let block = self.region_blocks[region_block].block;
            self.forward_queue.push(region_block, self.rpo_index[block]);
        }
    }

    /// Records that the loans in `loans` reach the pair at `block_index`, and returns whether any
    /// of them is new there.
    fn add_at_point_inner(
        state: &mut RegionInBlock,
        block_index: BlockIndex,
        loans: LoanSet,
    ) -> bool {
        let new = loans.difference(state.loans[block_index]);
        if new.is_empty() {
            return false;
        }
        state.loans[block_index].insert(new);
        state.pending[block_index].insert(new);
        true
    }
}

/// Recomputes loan liveness with the node-by-node DFS and checks that it agrees with the batched
/// traversal.
///
/// The two are meant to be the same least fixpoint of the same edge relation, and the DFS is still
/// around for the polonius MIR dumps, so a debug-assertions build can afford to check that claim on
/// every body it compiles rather than leaving the two implementations to drift. It is not cheap --
/// it is the per-loan traversal this module exists to replace -- so it is `debug_assertions` only.
#[cfg(debug_assertions)]
fn debug_check_against_dfs<'tcx>(
    body: &Body<'tcx>,
    liveness: &LivenessValues,
    graph: &LocalizedConstraintGraph,
    live_region_variances: &BTreeMap<RegionVid, ConstraintDirection>,
    universal_regions: &UniversalRegions<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    live_loans: &LiveLoans,
) {
    struct DfsTraversal<'a> {
        liveness: &'a LivenessValues,
        live_region_variances: &'a BTreeMap<RegionVid, ConstraintDirection>,
        live_loans: LiveLoans,
    }

    struct DfsVisitor<'a> {
        liveness: &'a LivenessValues,
        live_loans: &'a mut LiveLoans,
    }

    impl LocalizedConstraintGraphTraversal for DfsTraversal<'_> {
        type Visitor<'a>
            = DfsVisitor<'a>
        where
            Self: 'a;

        // The batched traversal has already materialized the liveness of every region a loan
        // reaches, so there is nothing left to compute here.
        fn mk_visitor(
            &mut self,
            _region: RegionVid,
        ) -> (&LivenessValues, &BTreeMap<RegionVid, ConstraintDirection>, Self::Visitor<'_>)
        {
            (
                self.liveness,
                self.live_region_variances,
                DfsVisitor { liveness: self.liveness, live_loans: &mut self.live_loans },
            )
        }
    }

    impl LocalizedConstraintGraphVisitor for DfsVisitor<'_> {
        fn on_node_traversed(&mut self, loan: BorrowIndex, node: LocalizedNode) {
            if self.liveness.is_live_at_point(node.region, node.point) {
                self.live_loans.insert(node.point, loan);
            }
        }
    }

    let mut traversal = DfsTraversal {
        liveness,
        live_region_variances,
        live_loans: LiveLoans::new(borrow_set.len(), live_loans.num_points()),
    };
    graph.traverse(body, universal_regions, borrow_set, liveness.location_map(), &mut traversal);

    for (loan, _) in borrow_set.iter_enumerated() {
        if let Some(point) = live_loans.first_difference(&traversal.live_loans, loan) {
            panic!(
                "batched and DFS loan liveness disagree for {loan:?} at {:?}: {} vs {}",
                liveness.location_map().to_location(point),
                live_loans.contains(point, loan),
                traversal.live_loans.contains(point, loan),
            );
        }
    }
}
