//! Set-based computation of loan liveness within the localized constraint graph.
//!
//! The direct way to compute this is a DFS per loan over the `(region, point)` nodes of the graph:
//! that is what [`LocalizedConstraintGraph::traverse`] does, and what the polonius MIR dumps use to
//! show the individual edges. Its cost is proportional to the number of reachable nodes, and a
//! region that is live over a large part of the CFG -- a universal region in particular, which is
//! semantically live everywhere -- is walked point by point, once per loan. That is quadratic in
//! the number of loans.
//!
//! Here, we instead propagate *sets of points* per region: the worklist holds regions rather than
//! nodes, and each edge of the graph becomes a set operation on a point bitset:
//!
//! - a logical edge `r -> s` carries the whole set of points reached for `r` over to `s`,
//! - a physical edge at `(r, p)` applies only when `p` is in the set reached for `r`,
//! - the forward liveness edges are the closure of the set under "step to the next point in the
//!   same block, if the region is live there", plus the block terminator to successor block entry
//!   edges,
//! - the backward liveness edges are the same in reverse, gated on liveness at the *source* point.
//!
//! The intra-block closures are the interesting part: they are computed a word at a time with a
//! carry chain, see [`forward_fill`]. Per loan, the cost is then proportional to the number of
//! reachable regions times the number of rounds, rather than to the number of reachable points.
//!
//! The reachable set is the same as the DFS's by construction: both are the least fixpoint of the
//! same edge relation, starting from the same node.

use std::collections::VecDeque;

use rustc_data_structures::fx::FxIndexMap;
use rustc_index::IndexVec;
use rustc_index::bit_set::DenseBitSet;
use rustc_middle::mir::{BasicBlock, Body, Location};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::points::PointIndex;

use crate::BorrowSet;
use crate::constraints::OutlivesConstraintSet;
use crate::constraints::graph::NormalConstraintGraph;
use crate::dataflow::BorrowIndex;
use crate::polonius::{ConstraintDirection, LazyLiveness, LocalizedConstraintGraph};
use crate::region_infer::values::LivenessValues;
use crate::universal_regions::UniversalRegions;

/// The unit the point sets in this module are manipulated in.
type Word = u64;
const WORD_BITS: usize = Word::BITS as usize;

#[inline]
fn num_words(num_points: usize) -> usize {
    num_points.div_ceil(WORD_BITS)
}

#[inline]
fn word_and_mask(point: PointIndex) -> (usize, Word) {
    let point = point.as_usize();
    (point / WORD_BITS, 1 << (point % WORD_BITS))
}

#[inline]
fn test_bit(words: &[Word], point: PointIndex) -> bool {
    let (word, mask) = word_and_mask(point);
    words[word] & mask != 0
}

fn empty_points(num_points: usize) -> Box<[Word]> {
    vec![0; num_words(num_points)].into_boxed_slice()
}

/// Sets the bits in the half-open range `start..end`.
fn insert_range(words: &mut [Word], start: usize, end: usize) {
    if start >= end {
        return;
    }
    let (start_word, start_bit) = (start / WORD_BITS, start % WORD_BITS);
    let (end_word, end_bit) = ((end - 1) / WORD_BITS, (end - 1) % WORD_BITS);

    let start_mask = !0 << start_bit;
    let end_mask = if end_bit == WORD_BITS - 1 { !0 } else { (1 << (end_bit + 1)) - 1 };

    if start_word == end_word {
        words[start_word] |= start_mask & end_mask;
    } else {
        words[start_word] |= start_mask;
        words[start_word + 1..end_word].fill(!0);
        words[end_word] |= end_mask;
    }
}

/// Computes one word of the closure `f[i] = seed[i] | (propagate[i] & f[i - 1])`, and the value of
/// `f` at the word's last bit, which is the `carry` for the next word.
///
/// This is the carry chain of an adder, with `seed` as the generate signal and `propagate` as the
/// propagate signal, so we can let the hardware adder compute all 64 steps at once: for `x = seed +
/// propagate` (an `or`, as the two are disjoint), the sum bit `i` of `x + seed` is `propagate[i] ^
/// f[i - 1]`, and the carry out of the addition is `f[63]`.
#[inline]
fn carry_chain(seed: Word, propagate: Word, carry: bool) -> (Word, bool) {
    let propagate = propagate & !seed;
    let x = propagate | seed;
    let (sum, overflow) = x.overflowing_add(seed);
    let (sum, carried) = sum.overflowing_add(carry as Word);
    let carry_out = overflow | carried;
    (((sum ^ propagate) >> 1) | ((carry_out as Word) << (WORD_BITS - 1)), carry_out)
}

/// Writes into `out[lo..=hi]` the closure of `seeds` under "step from a point to the next point
/// within the same basic block, if that next point is in `mask`". `entries` marks the first point
/// of each basic block: those are the points whose predecessor in point order is in another block,
/// and which therefore stop the propagation.
///
/// The result contains `seeds`, and only the words in `lo..=hi` are written.
fn forward_fill(
    out: &mut [Word],
    seeds: &[Word],
    mask: &[Word],
    entries: &[Word],
    lo: usize,
    hi: usize,
) {
    let mut carry = false;
    for word in lo..=hi {
        let propagate = mask[word] & !entries[word];
        let (filled, carry_out) = carry_chain(seeds[word], propagate, carry);
        out[word] = filled;
        carry = carry_out;
    }
}

/// The backwards counterpart of [`forward_fill`]: writes into `out[lo..=hi]` the closure of `seeds`
/// under "step from a point to the previous point within the same basic block, if the point we step
/// *from* is in `mask`".
///
/// The result contains `seeds`, and only the words in `lo..=hi` are written.
fn backward_fill(
    out: &mut [Word],
    seeds: &[Word],
    mask: &[Word],
    entries: &[Word],
    lo: usize,
    hi: usize,
) {
    // The propagation runs from high points to low points, so we work on bit-reversed words: that
    // turns it back into the carry chain of an adder, which runs from low bits to high bits.
    let mut carry = false;
    for word in (lo..=hi).rev() {
        // We can step from point `i + 1` down to point `i` when `i + 1` is live and is not a block
        // entry, i.e. the propagate signal at `i` is the mask at `i + 1`.
        let current = mask[word] & !entries[word];
        let next = mask.get(word + 1).map_or(0, |&next| next & !entries[word + 1]);
        let propagate = (current >> 1) | (next << (WORD_BITS - 1));

        let (filled, carry_out) =
            carry_chain(seeds[word].reverse_bits(), propagate.reverse_bits(), carry);
        out[word] = filled.reverse_bits();
        carry = carry_out;
    }
}

/// The per-region state of the traversal. The edge-direction data is computed once per body; the
/// reachability buffers are only held while a loan is actually reaching the region, and are
/// recycled between loans.
struct RegionState {
    /// The points the loan currently being traversed has reached this region at, and the points
    /// added to it since the region's block was last processed. Empty when the loan currently being
    /// traversed has not reached this region: the buffers come from, and go back to,
    /// [`LoanReachability::free_buffers`].
    reached: Box<[Word]>,
    delta: Box<[Word]>,

    /// The inclusive word span of `reached`, to reset it between loans.
    reached_lo: usize,
    reached_hi: usize,

    /// Whether this is a universal region: it is semantically live at all points, and propagates
    /// loans forwards only.
    universal: bool,

    /// Whether the liveness edges of this region flow forwards, or backwards, according to its
    /// variance.
    forward: bool,
    backward: bool,

    /// Whether this region has been reached by the loan currently being traversed.
    in_loan: bool,
}

/// Computes the points at which each loan is live, as the reachability of each loan within the
/// localized constraint graph. See the module documentation for the general shape of the
/// computation.
pub(super) struct LoanReachability<'a, 'tcx> {
    body: &'a Body<'tcx>,
    liveness: &'a LivenessValues,

    /// The liveness only polonius asks for, computed as we ask for it; see
    /// `polonius::deferred_liveness`. A region is live if either store says so, so every read of
    /// `liveness` in this module has to consult this one too -- after `ensure`ing it, which is
    /// what actually computes it.
    lazy: Option<&'a mut LazyLiveness<'a, 'tcx>>,

    graph: &'a mut LocalizedConstraintGraph,

    /// The outlives constraints, and the index from a region to its own, which is what the graph
    /// builds its rows from as the traversal reaches new regions.
    constraints: &'a OutlivesConstraintSet<'tcx>,
    constraint_graph: &'a NormalConstraintGraph,
    live_region_variances: &'a mut IndexVec<RegionVid, Option<ConstraintDirection>>,
    universal_regions: &'a UniversalRegions<'tcx>,

    num_points: usize,

    /// The first point of each basic block.
    entries: Box<[Word]>,

    /// All the points of the body, used as the liveness mask of universal regions.
    all_points: Box<[Word]>,

    /// The first and last point of each basic block, and the words they span.
    block_entry: IndexVec<BasicBlock, PointIndex>,
    block_terminator: IndexVec<BasicBlock, PointIndex>,
    block_words: IndexVec<BasicBlock, (usize, usize)>,

    states: IndexVec<RegionVid, Option<RegionState>>,

    /// The point sets released by the regions the previous loans reached. A loan generally reaches
    /// a small part of the graph, so recycling these keeps the traversal's memory proportional to
    /// the biggest single loan rather than to the whole body.
    free_buffers: Vec<Box<[Word]>>,

    /// The regions and blocks that have points waiting to be propagated. The same pair can be
    /// queued more than once; the second time around its delta is empty and it is skipped, which is
    /// cheaper than keeping a per-pair "already queued" bit.
    worklist: VecDeque<(RegionVid, BasicBlock)>,

    /// The regions the loan currently being traversed has reached.
    touched: Vec<RegionVid>,

    /// A cleared scratch buffer, holding the points being propagated out of a block.
    points_scratch: Box<[Word]>,

    /// A scratch buffer holding the result of the liveness closures.
    fill_scratch: Box<[Word]>,

    /// A scratch buffer holding the liveness of the region being processed, over the words of the
    /// block being processed.
    live_scratch: Box<[Word]>,

    /// The inclusive word span written into the current loan's point set, so that it can be
    /// cleared between loans without touching the whole body.
    row_lo: usize,
    row_hi: usize,

    /// The CFG walk that finds where a loan goes out of scope, reused across loans.
    visited: DenseBitSet<BasicBlock>,
    visit_stack: Vec<BasicBlock>,
}

impl<'a, 'tcx> LoanReachability<'a, 'tcx> {
    pub(super) fn new(
        body: &'a Body<'tcx>,
        liveness: &'a LivenessValues,
        lazy: Option<&'a mut LazyLiveness<'a, 'tcx>>,
        graph: &'a mut LocalizedConstraintGraph,
        constraints: &'a OutlivesConstraintSet<'tcx>,
        constraint_graph: &'a NormalConstraintGraph,
        live_region_variances: &'a mut IndexVec<RegionVid, Option<ConstraintDirection>>,
        universal_regions: &'a UniversalRegions<'tcx>,
    ) -> Self {
        let num_points = liveness.num_points();

        let mut entries = empty_points(num_points);
        let mut block_entry = IndexVec::with_capacity(body.basic_blocks.len());
        let mut block_terminator = IndexVec::with_capacity(body.basic_blocks.len());
        let mut block_words = IndexVec::with_capacity(body.basic_blocks.len());

        for (block, block_data) in body.basic_blocks.iter_enumerated() {
            let entry = liveness.point_from_location(Location { block, statement_index: 0 });
            let terminator = liveness.point_from_location(Location {
                block,
                statement_index: block_data.statements.len(),
            });

            let (word, mask) = word_and_mask(entry);
            entries[word] |= mask;

            block_entry.push(entry);
            block_terminator.push(terminator);
            block_words.push((entry.as_usize() / WORD_BITS, terminator.as_usize() / WORD_BITS));
        }

        let mut all_points = empty_points(num_points);
        insert_range(&mut all_points, 0, num_points);

        LoanReachability {
            body,
            liveness,
            lazy,
            graph,
            constraints,
            constraint_graph,
            live_region_variances,
            universal_regions,
            num_points,
            entries,
            all_points,
            block_entry,
            block_terminator,
            block_words,
            states: IndexVec::new(),
            free_buffers: Vec::new(),
            worklist: VecDeque::new(),
            touched: Vec::new(),
            points_scratch: empty_points(num_points),
            fill_scratch: empty_points(num_points),
            live_scratch: empty_points(num_points),
            row_lo: usize::MAX,
            row_hi: 0,
            visited: DenseBitSet::new_empty(body.basic_blocks.len()),
            visit_stack: Vec::new(),
        }
    }

    /// Traverses the graph once per loan, and returns where each loan goes out of scope.
    ///
    /// The traversal computes the set of points a loan is live at, and that set used to be handed
    /// out whole, as `LiveLoans`, for `Borrows` to walk afterwards. But the walk reads a short
    /// prefix of it -- forwards from where the loan is issued, stopping at the first point it is
    /// not live, and not descending into successors past that -- so a row per loan, sized to the
    /// whole body, was built and then almost entirely ignored. Doing the walk here, while the row
    /// is in hand, means one row exists at a time and it is recycled.
    pub(super) fn compute_loans_out_of_scope(
        &mut self,
        borrow_set: &BorrowSet<'tcx>,
    ) -> FxIndexMap<Location, Vec<BorrowIndex>> {
        let mut out_of_scope: FxIndexMap<Location, Vec<BorrowIndex>> = FxIndexMap::default();
        let mut row = empty_points(self.num_points);

        for (loan_idx, loan) in borrow_set.iter_enumerated() {
            // The loan enters the graph at the region and point it is introduced at.
            let start = loan.reserve_location;
            self.add_point(loan.region, self.liveness.point_from_location(start), start.block);

            (self.row_lo, self.row_hi) = (usize::MAX, 0);
            while let Some((region, block)) = self.worklist.pop_front() {
                self.process(region, block, &mut row);
            }

            self.record_loan_out_of_scope(loan_idx, start, &row, &mut out_of_scope);

            // Release the per-loan state.
            let mut touched = std::mem::take(&mut self.touched);
            for &region in &touched {
                let state = self.states[region].as_mut().unwrap();
                let (lo, hi) = (state.reached_lo, state.reached_hi);
                state.reached_lo = usize::MAX;
                state.reached_hi = 0;
                state.in_loan = false;

                // The delta has been drained by the worklist, and only `reached` needs clearing.
                let mut reached = std::mem::take(&mut state.reached);
                let delta = std::mem::take(&mut state.delta);
                reached[lo..=hi].fill(0);
                self.free_buffers.push(reached);
                self.free_buffers.push(delta);
            }
            touched.clear();
            self.touched = touched;

            // Recycle the row. Only the words this loan actually reached need clearing, which is
            // why the whole point set can be a single reused buffer.
            if self.row_lo <= self.row_hi {
                row[self.row_lo..=self.row_hi].fill(0);
            }
        }

        out_of_scope
    }

    /// Records where `loan_idx` goes out of scope: the first point, walking forwards from where it
    /// is issued, at which it is not live.
    ///
    /// A loan is live while it is contained within some live region, so this is looking for the
    /// first point where no region the loan reached is live -- which `row` already says.
    fn record_loan_out_of_scope(
        &mut self,
        loan_idx: BorrowIndex,
        loan_issued_at: Location,
        row: &[Word],
        out_of_scope: &mut FxIndexMap<Location, Vec<BorrowIndex>>,
    ) {
        let first_block = loan_issued_at.block;
        let first_bb_data = &self.body.basic_blocks[first_block];

        // The first block starts at the statement where the loan is issued, rather than at the
        // block entry.
        if let Some(kill) = self.loan_kill_location(
            loan_issued_at,
            row,
            first_block,
            loan_issued_at.statement_index,
            first_bb_data.statements.len(),
        ) {
            out_of_scope.entry(kill).or_default().push(loan_idx);
            return;
        }

        for succ in first_bb_data.terminator().successors() {
            if self.visited.insert(succ) {
                self.visit_stack.push(succ);
            }
        }

        // We may end up visiting `first_block` again. This is not an issue: we know at this point
        // that the loan is not killed in the range above, so checking the whole block gives the
        // same answer.
        while let Some(block) = self.visit_stack.pop() {
            let bb_data = &self.body[block];
            if let Some(kill) =
                self.loan_kill_location(loan_issued_at, row, block, 0, bb_data.statements.len())
            {
                // The loan dies within this block, so its successors are not reached from here.
                out_of_scope.entry(kill).or_default().push(loan_idx);
                continue;
            }

            for succ in bb_data.terminator().successors() {
                if self.visited.insert(succ) {
                    self.visit_stack.push(succ);
                }
            }
        }

        self.visited.clear();
        debug_assert!(self.visit_stack.is_empty(), "visit stack should be empty");
    }

    /// The lowest statement in `start..=end` at which the loan is not live, if any.
    ///
    /// This is the innermost thing the out-of-scope walk does, and the walk visits more blocks
    /// than the graph traversal processes worklist items, so it looks for the first *clear* bit
    /// a word at a time rather than testing one bit per statement. A block's points span one or
    /// two words, so this is one or two iterations however many statements there are.
    fn loan_kill_location(
        &self,
        loan_issued_at: Location,
        row: &[Word],
        block: BasicBlock,
        start: usize,
        end: usize,
    ) -> Option<Location> {
        // Points are dense and in statement order within a block, so the block's entry point plus
        // the statement index is the point, without going back through the location map.
        let entry = self.block_entry[block].as_usize();
        let (lo, hi) = (entry + start, entry + end);
        debug_assert_eq!(
            PointIndex::from_usize(lo),
            self.liveness.point_from_location(Location { block, statement_index: start })
        );

        // A loan is always live at the point it is issued: it reaches its own region, which is
        // live there. The row does not say so, so add it back for the word it falls in.
        let (issued_word, issued_mask) = word_and_mask(PointIndex::from_usize(
            self.block_entry[loan_issued_at.block].as_usize() + loan_issued_at.statement_index,
        ));

        for word in lo / WORD_BITS..=hi / WORD_BITS {
            let mut live = row[word];
            if word == issued_word {
                live |= issued_mask;
            }

            // Mask down to the points of this block that are in range: the first and last words
            // are shared with the neighbouring blocks.
            let mut dead = !live;
            if word == lo / WORD_BITS {
                dead &= !0 << (lo % WORD_BITS);
            }
            if word == hi / WORD_BITS {
                let last_bit = hi % WORD_BITS;
                dead &= if last_bit == WORD_BITS - 1 { !0 } else { (1 << (last_bit + 1)) - 1 };
            }

            if dead != 0 {
                let point = word * WORD_BITS + dead.trailing_zeros() as usize;
                return Some(Location { block, statement_index: point - entry });
            }
        }

        None
    }

    /// Propagates the points newly reached for `region` within `block` to its successors in the
    /// graph, and records them in `row` where the region is live.
    ///
    /// Propagation is per basic block rather than per region: the points of a block are a couple of
    /// words at most, so the liveness closures and the set operations below all stay O(1), and the
    /// work is proportional to the `(loan, region, block)` triples a loan reaches rather than to
    /// the size of the body.
    fn process(&mut self, region: RegionVid, block: BasicBlock, row: &mut [Word]) {
        // The graph rows for a region are built the first time it is processed, rather than for
        // every region in the body up front.
        self.graph.ensure(region, self.liveness, self.constraints, self.constraint_graph);

        let (w0, w1) = self.block_words[block];
        let entry = self.block_entry[block];
        let terminator = self.block_terminator[block];

        // The first and last words of a block are shared with the neighbouring blocks, so mask the
        // delta down to this block's points: the rest belongs to another worklist item.
        let first_mask = !0 << (entry.as_usize() % WORD_BITS);
        let last_bit = terminator.as_usize() % WORD_BITS;
        let last_mask = if last_bit == WORD_BITS - 1 { !0 } else { (1 << (last_bit + 1)) - 1 };

        // Take this block's part of the region's delta.
        let mut points = std::mem::replace(&mut self.points_scratch, Box::default());
        let (universal, forward, backward) = {
            let state = self.states[region].as_mut().unwrap();
            let mut any = false;
            for word in w0..=w1 {
                let mut mask = !0;
                if word == w0 {
                    mask &= first_mask;
                }
                if word == w1 {
                    mask &= last_mask;
                }
                let bits = state.delta[word] & mask;
                points[word] = bits;
                state.delta[word] &= !bits;
                any |= bits != 0;
            }
            if !any {
                self.points_scratch = points;
                return;
            }
            (state.universal, state.forward, state.backward)
        };

        // The region's liveness over this block, read out of its interval set. Materializing it for
        // the whole body would cost a bitset per region, which is a lot of memory on bodies with
        // many regions, and only a couple of words of it are ever needed at a time.
        let mut live = std::mem::replace(&mut self.live_scratch, Box::default());
        live[w0..=w1].fill(0);
        let lazy_row = self.lazy.as_ref().and_then(|lazy| lazy.row(region));
        for live_points in [self.liveness.points().row(region), lazy_row].into_iter().flatten() {
            for interval in live_points.iter_intervals_from(entry) {
                if interval.start > terminator {
                    break;
                }
                let start = interval.start.as_usize().max(entry.as_usize());
                let end = interval.end.as_usize().min(terminator.as_usize() + 1);
                insert_range(&mut live, start, end);
            }
        }

        // 1. The liveness edges within the block: the loan flows from point to point, in the
        // direction(s) allowed by the region's variance, as long as the region is live there. The
        // two closures cannot feed each other: the edge between `p` and `p + 1` exists in both
        // directions or in neither, so their union is the whole closure.
        let mut filled = std::mem::replace(&mut self.fill_scratch, Box::default());
        if forward {
            // A universal region is live at all points, so its loans flow to the next point
            // unconditionally.
            let mask = if universal { &self.all_points } else { &live };
            forward_fill(&mut filled, &points, mask, &self.entries, w0, w1);
            for word in w0..=w1 {
                points[word] |= filled[word];
            }
        }
        if backward {
            // Backward edges are only taken from a point where the region is live, and universal
            // regions have none.
            backward_fill(&mut filled, &points, &live, &self.entries, w0, w1);
            for word in w0..=w1 {
                points[word] |= filled[word];
            }
        }
        self.fill_scratch = filled;

        // The loan is live wherever it reaches a live region. Everything the closures derived is
        // reached as well; it does not go back into the delta, as its outgoing edges are taken
        // right below, together with the delta's.
        {
            let state = self.states[region].as_mut().unwrap();
            let (mut new_lo, mut new_hi) = (usize::MAX, 0);
            self.row_lo = self.row_lo.min(w0);
            self.row_hi = self.row_hi.max(w1);
            for word in w0..=w1 {
                row[word] |= points[word] & live[word];
                if points[word] & !state.reached[word] != 0 {
                    state.reached[word] |= points[word];
                    new_lo = new_lo.min(word);
                    new_hi = word;
                }
            }
            if new_lo <= new_hi {
                state.reached_lo = state.reached_lo.min(new_lo);
                state.reached_hi = state.reached_hi.max(new_hi);
            }
        }

        // 2. The liveness edges leaving the block, to the entry point of the successor blocks and
        // to the terminator of the predecessor blocks.
        let body = self.body;
        if forward && test_bit(&points, terminator) {
            for successor in body[block].terminator().successors() {
                let point = self.block_entry[successor];
                if universal || self.is_live_at_point(region, point) {
                    self.add_point(region, point, successor);
                }
            }
        }
        if backward && test_bit(&points, entry) && test_bit(&live, entry) {
            for &predecessor in &body.basic_blocks.predecessors()[block] {
                self.add_point(region, self.block_terminator[predecessor], predecessor);
            }
        }
        self.live_scratch = live;

        // The graph rows are moved out for the rest of this: they belong to `region`, and nothing
        // reached from them looks at `region`'s own rows, so they are only missing for a window in
        // which no one asks.
        let (physical_edges, logical_edges) = self.graph.take_rows(region);

        // 3. The logical edges: constraints that hold at all points, so all the points reached here
        // flow to the target regions.
        for &successor in &logical_edges {
            self.add_words(successor, &points, w0, w1, block);
        }

        // 4. The physical edges: constraints that hold at a single point, so they only apply when
        // that point has been reached. They are sorted, so we can jump to this block's range.
        let start = physical_edges.partition_point(|&(point, _)| point < entry);
        let mut idx = start;
        while let Some(&(point, _)) = physical_edges.get(idx) {
            if point > terminator {
                break;
            }
            let successors = LocalizedConstraintGraph::successors_at(&physical_edges, point);
            if test_bit(&points, point) {
                for &(_, successor) in successors {
                    self.add_point(successor, point, block);
                }
            }
            idx += successors.len();
        }

        self.graph.put_rows(region, physical_edges, logical_edges);

        points[w0..=w1].fill(0);
        self.points_scratch = points;
    }

    /// Whether `region` is live at `point`, according to either liveness store.
    fn is_live_at_point(&self, region: RegionVid, point: PointIndex) -> bool {
        self.liveness.is_live_at_point(region, point)
            || self.lazy.as_ref().is_some_and(|lazy| lazy.is_live_at_point(region, point))
    }

    /// Records that the loan currently being traversed reaches `region` at the points in
    /// `points[lo..=hi]`, which all belong to `block`.
    fn add_words(
        &mut self,
        region: RegionVid,
        points: &[Word],
        lo: usize,
        hi: usize,
        block: BasicBlock,
    ) {
        let state = self.ensure_state(region);
        let (mut new_lo, mut new_hi) = (usize::MAX, 0);
        for word in lo..=hi {
            let new = points[word] & !state.reached[word];
            if new == 0 {
                continue;
            }
            state.reached[word] |= new;
            state.delta[word] |= new;
            new_lo = new_lo.min(word);
            new_hi = word;
        }
        if new_lo > new_hi {
            return;
        }

        self.record_new_points(region, block, new_lo, new_hi);
    }

    /// Records that the loan currently being traversed reaches `region` at `point`, which belongs
    /// to `block`.
    fn add_point(&mut self, region: RegionVid, point: PointIndex, block: BasicBlock) {
        let (word, mask) = word_and_mask(point);
        let state = self.ensure_state(region);
        if state.reached[word] & mask != 0 {
            return;
        }
        state.reached[word] |= mask;
        state.delta[word] |= mask;

        self.record_new_points(region, block, word, word);
    }

    /// Widens the span of `region`'s reached set to the newly reached words, and schedules the
    /// region's block for propagation.
    fn record_new_points(
        &mut self,
        region: RegionVid,
        block: BasicBlock,
        new_lo: usize,
        new_hi: usize,
    ) {
        let state = self.states[region].as_mut().unwrap();
        state.reached_lo = state.reached_lo.min(new_lo);
        state.reached_hi = state.reached_hi.max(new_hi);

        let first_touch = !state.in_loan;
        state.in_loan = true;

        self.worklist.push_back((region, block));
        if first_touch {
            self.touched.push(region);
        }
    }

    /// Returns `region`'s state, creating it and acquiring its point sets if needed.
    fn ensure_state(&mut self, region: RegionVid) -> &mut RegionState {
        // A deferred local's liveness -- and its variance, which `make_state` is about to read --
        // is computed the first time a loan reaches one of its regions. This is that first time.
        if let Some(lazy) = self.lazy.as_mut() {
            lazy.ensure(region, self.live_region_variances);
        }

        let num_points = self.num_points;
        if self.states.get(region).is_none_or(Option::is_none) {
            let state = self.make_state(region);
            *self.states.ensure_contains_elem(region, || None) = Some(state);
        }

        let state = self.states[region].as_mut().unwrap();
        if state.reached.is_empty() {
            state.reached = self.free_buffers.pop().unwrap_or_else(|| empty_points(num_points));
            state.delta = self.free_buffers.pop().unwrap_or_else(|| empty_points(num_points));
        }
        state
    }

    fn make_state(&self, region: RegionVid) -> RegionState {
        let universal = self.universal_regions.is_universal_region(region);

        // Note: there currently are cases related to promoted and const generics, where we don't
        // yet have variance information (possibly about temporary regions created when typeck
        // sanitizes the promoteds). Until that is done, we conservatively fallback to maximizing
        // reachability by taking both directions here. This will not limit traversal whatsoever,
        // and thus propagate liveness when needed.
        //
        // FIXME: add the missing variance information and remove this fallback.
        let direction = self
            .live_region_variances
            .get(region)
            .copied()
            .flatten()
            .unwrap_or(ConstraintDirection::Bidirectional);

        RegionState {
            reached: Box::default(),
            delta: Box::default(),
            reached_lo: usize::MAX,
            reached_hi: 0,
            universal,
            // Universal regions propagate loans along the CFG forwards only, whatever their
            // variance.
            forward: universal
                || matches!(
                    direction,
                    ConstraintDirection::Forward | ConstraintDirection::Bidirectional
                ),
            backward: !universal
                && matches!(
                    direction,
                    ConstraintDirection::Backward | ConstraintDirection::Bidirectional
                ),
            in_loan: false,
        }
    }
}
