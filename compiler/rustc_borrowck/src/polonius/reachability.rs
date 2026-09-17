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
use std::collections::BinaryHeap;

use rustc_data_structures::fx::FxHashMap;
use rustc_index::IndexVec;
use rustc_index::bit_set::GrowableBitSet;
use rustc_middle::mir::{BasicBlock, Body};
use rustc_middle::ty::{RegionVid, TypeVisitable};
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};
use rustc_trait_selection::traits::outlives_for_liveness::FreeRegionsVisitor;

use self::loan_set::{BATCH_SIZE, LoanSet};
use crate::BorrowSet;
use crate::dataflow::BorrowIndex;
use crate::polonius::ConstraintDirection::{self, Backward, Bidirectional, Forward};
use crate::polonius::{
    DeferredLocals, LiveLoans, LiveRegionVariances, LocalizedConstraintGraph,
    record_live_region_variance,
};
#[cfg(debug_assertions)]
use crate::polonius::{
    LivenessSource, LocalizedConstraintGraphVisitor, LocalizedNode, RegionLiveness,
};
use crate::region_infer::values::LivenessValues;
use crate::type_check::liveness::LivenessComputation;
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
    universal: bool,
    /// The direction the region's liveness edges flow in.
    direction: ConstraintDirection,
    /// The loans added for a block that have not yet been propagated.
    pending: IndexVec<BlockIndex, LoanSet>,
    /// This serves to avoid requeuing a `RegionInBlock` when a given loan
    /// has already been propagated *or will be*. This second part is important,
    /// because there are *two queues* that a `RegionInBlock` can be pulled
    /// from, and queuing in both is just slower.
    loans: IndexVec<BlockIndex, LoanSet>,
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
    graph: &'a LocalizedConstraintGraph,
    universal_regions: &'a UniversalRegions<'tcx>,

    region_blocks: LoanReachabilityRegionBlocks<'a, 'tcx>,

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

    /// Buffers reused across `process` calls.
    //
    // It might seem tempting to remove these. However, the allocations avoided
    // by keeping these around can be up to 20% on some benchmarks.
    pending_buf: IndexVec<BlockIndex, LoanSet>,
    block_loans_buf: IndexVec<BlockIndex, LoanSet>,
    liveness_buf: GrowableBitSet<BlockIndex>,
}

impl<'a, 'tcx> LoanReachability<'a, 'tcx> {
    pub(super) fn new(
        body: &'a Body<'tcx>,
        location_map: &'a DenseLocationMap,
        liveness: &'a mut LivenessValues,
        graph: &'a LocalizedConstraintGraph,
        live_region_variances: &'a mut LiveRegionVariances,
        universal_regions: &'a UniversalRegions<'tcx>,
        deferred_locals_for_liveness: DeferredLocals<'tcx>,
        comp: LivenessComputation<'a, 'tcx>,
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
            location_map,
            body,
            graph,
            universal_regions,
            region_blocks: LoanReachabilityRegionBlocks {
                body,
                liveness,
                live_region_variances,
                universal_regions,
                deferred_locals_for_liveness,
                comp,
                directions: IndexVec::new(),
                region_blocks: IndexVec::new(),
                region_block_indices: FxHashMap::default(),
            },
            rpo_index,
            forward_queue: Queue::new(),
            backward_queue: Queue::new(),
            pending_buf: IndexVec::new(),
            block_loans_buf: IndexVec::new(),
            liveness_buf: GrowableBitSet::new_empty(),
        }
    }

    /// Traverses the graph once per batch of loans, and returns the points at which each loan is
    /// live: the points it reaches a live region at.
    pub(super) fn compute_live_loans(&mut self, borrow_set: &BorrowSet<'tcx>) -> LiveLoans {
        let num_loans = borrow_set.len();
        let mut live_loans = LiveLoans::new(self.location_map.num_points(), num_loans);

        for batch_start in (0..num_loans).step_by(BATCH_SIZE) {
            // Each loan of the batch enters the graph at the region and point it is introduced
            // at, with its own bit.
            for bit in 0..BATCH_SIZE.min(num_loans - batch_start) {
                let loan = &borrow_set[BorrowIndex::from_usize(batch_start + bit)];
                let start = loan.reserve_location;
                let point = self.location_map.point_from_location(start);
                let region = loan.region;
                let block = start.block;

                let block_index = BlockIndex::from_point(point, block, self.location_map);
                let (region_block, state) = self.region_blocks.region_block(region, block);
                state.loans[block_index].insert(LoanSet::single(bit));
                state.pending[block_index].insert(LoanSet::single(bit));
                self.forward_queue.push(region_block, self.rpo_index[block]);
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

            self.region_blocks.region_blocks.raw.clear();
            self.region_blocks.region_block_indices.clear();
            self.forward_queue.clear();
            self.backward_queue.clear();
        }

        #[cfg(debug_assertions)]
        debug_check_against_dfs(
            self.body,
            self.region_blocks.liveness,
            self.graph,
            self.region_blocks.live_region_variances,
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
        let state = &mut self.region_blocks.region_blocks[region_block];
        let region = state.region;
        let block = state.block;
        let universal = state.universal;
        let direction = state.direction;
        let block_len = state.loans.len();

        let entry = self.location_map.entry_point(block);
        let terminator = PointIndex::from_usize(entry.as_usize() + block_len - 1);

        // Take the pending loans, leaving the pair with none.
        let mut pending = std::mem::take(&mut self.pending_buf);
        pending.raw.clear();
        pending.resize(block_len, LoanSet::EMPTY);
        std::mem::swap(&mut state.pending, &mut pending);
        if pending.iter().all(|loans| loans.is_empty()) {
            self.pending_buf = pending;
            return;
        }

        // It may seem weird to recompute this liveness every time process is
        // called for this `RegionInBlock`, but turns out this is the most
        // efficient both in instructions and memory compared to both eagerly
        // computing at creation *or* lazily computing and caching for later.
        let liveness = &mut self.liveness_buf;
        liveness.clear();
        liveness.ensure(block_len);
        if universal {
            liveness.insert_range(BlockIndex::ZERO..BlockIndex::from_usize(block_len));
        } else if let Some(live_points) = self.region_blocks.liveness.points().row(region) {
            for interval in live_points.iter_intervals() {
                if interval.end <= entry {
                    continue;
                }
                if interval.start > terminator {
                    break;
                }
                let start = interval.start.as_usize().max(entry.as_usize());
                let end = interval.end.as_usize().min(terminator.as_usize() + 1);
                liveness.insert_range(
                    BlockIndex::from_usize(start - entry.as_usize())
                        ..BlockIndex::from_usize(end - entry.as_usize()),
                );
            }
        }

        // We first need to propagate the loans within the block.

        let block_loans = &mut self.block_loans_buf;
        block_loans.raw.clear();
        block_loans.raw.extend_from_slice(&pending.raw);
        if matches!(direction, Forward | Bidirectional) {
            let mut previous = LoanSet::EMPTY;
            for (block_index, loans) in block_loans.iter_enumerated_mut() {
                if liveness.contains(block_index) {
                    loans.insert(previous);
                }
                previous = *loans;
            }
        }
        if matches!(direction, Backward | Bidirectional) {
            // Backward edges are only taken from a point where the region is live.
            let mut carry = LoanSet::EMPTY;
            for (block_index, loans) in block_loans.iter_enumerated_mut().rev() {
                let here = pending[block_index].union(carry);
                loans.insert(here);
                carry = if liveness.contains(block_index) { here } else { LoanSet::EMPTY };
            }
        }

        // At this point, we have propagated the loans *within* this block
        // It would be nice to use `state.loans` directly, but
        // `self.region_block` makes that tricky
        let block_loans = block_loans;

        for (block_index, &loans) in block_loans.iter_enumerated() {
            state.loans[block_index].insert(loans);
            if liveness.contains(block_index) {
                for bit in loans.iter() {
                    live_loans.insert(
                        entry + block_index.index(),
                        BorrowIndex::from_usize(batch_start + bit),
                    );
                }
            }
        }

        // The liveness edges leaving the block: to the entry point of the successor blocks, and to
        // the terminator of the predecessor blocks.

        let body = self.body;
        let last = BlockIndex::from_usize(block_len - 1);
        if matches!(direction, Forward | Bidirectional) && !block_loans[last].is_empty() {
            for successor in body[block].terminator().successors() {
                let successor_entry = self.location_map.entry_point(successor);
                if !self.region_blocks.liveness.is_live_at_point(region, successor_entry) {
                    continue;
                }

                let block_index = BlockIndex::from_usize(0);
                let (region_block, state) = self.region_blocks.region_block(region, successor);
                let loans = block_loans[last];
                let new = loans.difference(state.loans[block_index]);
                if !new.is_empty() {
                    state.loans[block_index].insert(new);
                    state.pending[block_index].insert(new);
                    self.forward_queue.push(region_block, self.rpo_index[block]);
                }
            }
        }
        if matches!(direction, Backward | Bidirectional)
            && !block_loans[BlockIndex::ZERO].is_empty()
            && liveness.contains(BlockIndex::ZERO)
        {
            for &predecessor in &body.basic_blocks.predecessors()[block] {
                let point = self.location_map.point_from_location(body.terminator_loc(predecessor));
                let block_index = BlockIndex::from_point(point, predecessor, self.location_map);
                let (region_block, state) = self.region_blocks.region_block(region, predecessor);
                let loans = block_loans[BlockIndex::ZERO];
                let new = loans.difference(state.loans[block_index]);
                if !new.is_empty() {
                    state.loans[block_index].insert(new);
                    state.pending[block_index].insert(new);
                    let last = self.rpo_index.len() as u32 - 1;
                    self.backward_queue.push(region_block, last - self.rpo_index[block]);
                }
            }
        }

        // The subset edges: a logical one hands every point reached to the target region unchanged,
        // a physical one applies at its own point only, and only if that point has been reached.

        for successor in self.graph.logical_successors(region) {
            let (region_block, state) = self.region_blocks.region_block(successor, block);
            for (block_index, &loans) in block_loans.iter_enumerated() {
                let new = loans.difference(state.loans[block_index]);
                if !new.is_empty() {
                    state.loans[block_index].insert(new);
                    state.pending[block_index].insert(new);
                    self.forward_queue.push(region_block, self.rpo_index[block]);
                }
            }
        }
        // The points with physical edges are sorted, so we can jump to this block's range.
        let physical_points = self.graph.physical_points(region);
        let start = physical_points.partition_point(|&point| point < entry);
        for &point in &physical_points[start..] {
            if point > terminator {
                break;
            }
            let loans = block_loans[BlockIndex::from_point(point, block, self.location_map)];
            if loans.is_empty() {
                continue;
            }
            for successor in self.graph.physical_successors(region, point) {
                let block_index = BlockIndex::from_point(point, block, self.location_map);
                let (region_block, state) = self.region_blocks.region_block(successor, block);
                let new = loans.difference(state.loans[block_index]);
                if !new.is_empty() {
                    state.loans[block_index].insert(new);
                    state.pending[block_index].insert(new);
                    self.forward_queue.push(region_block, self.rpo_index[block]);
                }
            }
        }

        self.pending_buf = pending;
    }
}

struct LoanReachabilityRegionBlocks<'a, 'tcx> {
    body: &'a Body<'tcx>,
    liveness: &'a mut LivenessValues,
    live_region_variances: &'a mut LiveRegionVariances,
    universal_regions: &'a UniversalRegions<'tcx>,

    deferred_locals_for_liveness: DeferredLocals<'tcx>,
    comp: LivenessComputation<'a, 'tcx>,

    /// The direction of each reached region's liveness edges, computed on the first touch.
    directions: IndexVec<RegionVid, Option<ConstraintDirection>>,

    /// What the current batch has reached, per `(region, block)` pair.
    ///
    /// FIXME: this allocates two vectors per pair per batch; a single arena reused across batches
    /// would avoid that.
    region_blocks: IndexVec<RegionInBlockIndex, RegionInBlock>,
    region_block_indices: FxHashMap<(RegionVid, BasicBlock), RegionInBlockIndex>,
}

impl<'a, 'tcx> LoanReachabilityRegionBlocks<'a, 'tcx> {
    fn materialize_liveness(
        deferred_locals_for_liveness: &mut DeferredLocals<'tcx>,
        liveness: &mut LivenessValues,
        live_region_variances: &mut LiveRegionVariances,
        universal_regions: &'a UniversalRegions<'tcx>,
        comp: &mut LivenessComputation<'a, 'tcx>,
        region: RegionVid,
    ) {
        if let Some((local, drop_args)) = deferred_locals_for_liveness.use_deferred_local(region) {
            comp.compute(local);

            if !comp.use_live_at.is_empty() || !comp.drop_live_at.is_empty() {
                record_live_region_variance(
                    comp.infcx.tcx,
                    live_region_variances,
                    universal_regions,
                    comp.body.local_decls[local].ty,
                );
            }
            if !comp.use_live_at.is_empty() {
                let local_ty = comp.body.local_decls[local].ty;

                local_ty.visit_with(&mut FreeRegionsVisitor {
                    tcx: comp.infcx.tcx,
                    param_env: comp.infcx.param_env,
                    op: |live_region| {
                        let region = universal_regions.to_region_vid(live_region);
                        liveness.add_points(region, &comp.use_live_at);
                    },
                });
            }
            if !comp.drop_live_at.is_empty() {
                for drop_arg in drop_args {
                    drop_arg.visit_with(&mut FreeRegionsVisitor {
                        tcx: comp.infcx.tcx,
                        param_env: comp.infcx.param_env,
                        op: |live_region| {
                            let region = universal_regions.to_region_vid(live_region);
                            liveness.add_points(region, &comp.drop_live_at());
                        },
                    });
                }
            }
        }
    }

    /// The index of the `(region, block)` pair, creating its state if this is the first time the
    /// batch reaches the region in this block.
    fn region_block(
        &mut self,
        region: RegionVid,
        block: BasicBlock,
    ) -> (RegionInBlockIndex, &mut RegionInBlock) {
        if let Some(&region_block) = self.region_block_indices.get(&(region, block)) {
            return (region_block, &mut self.region_blocks[region_block]);
        }

        let universal = self.universal_regions.is_universal_region(region);

        // The first time any loan reaches `region`: computes the liveness that was deferred for it,
        // since everything below reads this region's liveness and variance, and the direction of its
        // liveness edges.
        let direction = *self.directions.get_or_insert_with(region, || {
            Self::materialize_liveness(
                &mut self.deferred_locals_for_liveness,
                self.liveness,
                self.live_region_variances,
                self.universal_regions,
                &mut self.comp,
                region,
            );
            if universal {
                Forward
            } else {
                self.live_region_variances
                    .get(region)
                    .copied()
                    .flatten()
                    .unwrap_or(ConstraintDirection::Bidirectional)
            }
        });

        let block_len = self.body[block].statements.len() + 1;
        let region_block = self.region_blocks.push(RegionInBlock {
            region,
            block,
            universal,
            direction,
            loans: IndexVec::from_elem_n(LoanSet::EMPTY, block_len),
            pending: IndexVec::from_elem_n(LoanSet::EMPTY, block_len),
        });
        self.region_block_indices.insert((region, block), region_block);
        (region_block, &mut self.region_blocks[region_block])
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
    live_region_variances: &LiveRegionVariances,
    universal_regions: &UniversalRegions<'tcx>,
    borrow_set: &BorrowSet<'tcx>,
    live_loans: &LiveLoans,
) {
    /// A `LivenessSource` for already-existing liveness and variance data.
    struct CachedLivenessSource<'a> {
        live_region_variances: &'a LiveRegionVariances,
        liveness: &'a LivenessValues,
    }

    impl<'a> LivenessSource for CachedLivenessSource<'a> {
        fn liveness_for_region(&mut self, region: RegionVid) -> RegionLiveness<'_> {
            RegionLiveness::new(region, self.live_region_variances, self.liveness)
        }
        fn location_map(&self) -> &DenseLocationMap {
            self.liveness.location_map()
        }
    }
    struct DfsVisitor {
        live_loans: LiveLoans,
    }

    impl LocalizedConstraintGraphVisitor for DfsVisitor {
        fn on_node_traversed(&mut self, loan: BorrowIndex, node: LocalizedNode, is_live: bool) {
            if is_live {
                self.live_loans.insert(node.point, loan)
            }
        }
    }

    let mut liveness_source = CachedLivenessSource { live_region_variances, liveness };
    let mut visitor =
        DfsVisitor { live_loans: LiveLoans::new(live_loans.num_points(), borrow_set.len()) };
    graph.traverse(body, universal_regions, borrow_set, &mut liveness_source, &mut visitor);

    for (loan, _) in borrow_set.iter_enumerated() {
        if let Some(point) = live_loans.first_difference(&visitor.live_loans, loan) {
            panic!(
                "batched and DFS loan liveness disagree for {loan:?} at {:?}: {} vs {}",
                liveness.location_map().to_location(point),
                live_loans.contains(point, loan),
                visitor.live_loans.contains(point, loan),
            );
        }
    }
}
