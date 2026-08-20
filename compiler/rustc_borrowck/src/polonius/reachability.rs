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
//! The intra-block closures are the interesting part: they are computed a word at a time with a
//! carry chain, see [`forward_fill`]. Per loan, the cost is then proportional to the number of
//! reachable regions times the number of rounds, rather than to the number of reachable points.
//!
//! The reachable set is the same as the DFS's by construction: both are the least fixpoint of the
//! same edge relation, starting from the same node.

use std::collections::VecDeque;

use std::collections::BTreeMap;

use rustc_index::IndexVec;
use rustc_middle::mir::{BasicBlock, Body, Location};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::points::PointIndex;

use crate::BorrowSet;
use crate::dataflow::BorrowIndex;
use crate::polonius::{ConstraintDirection, LocalizedConstraintGraph};
#[cfg(debug_assertions)]
use crate::polonius::{LocalizedConstraintGraphVisitor, LocalizedNode};
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

/// The points at which each loan is live, when using `-Zpolonius=next`.
#[derive(Clone)] // FIXME(#146079)
pub(crate) struct LiveLoans {
    num_points: usize,
    /// The set of points at which a given loan is live, materialized on demand.
    rows: IndexVec<BorrowIndex, Option<Box<[Word]>>>,
}

impl LiveLoans {
    fn new(num_loans: usize, num_points: usize) -> Self {
        LiveLoans { num_points, rows: IndexVec::from_fn_n(|_| None, num_loans) }
    }

    fn row_mut(&mut self, loan: BorrowIndex) -> &mut [Word] {
        let num_points = self.num_points;
        self.rows[loan].get_or_insert_with(|| empty_points(num_points))
    }

    /// Records that `loan` is live at `point`.
    #[cfg(debug_assertions)]
    fn insert(&mut self, loan: BorrowIndex, point: PointIndex) {
        let (word, mask) = word_and_mask(point);
        self.row_mut(loan)[word] |= mask;
    }

    /// The raw point set of a loan, for the debug crosscheck below.
    #[cfg(debug_assertions)]
    fn row(&self, loan: BorrowIndex) -> Option<&[Word]> {
        self.rows[loan].as_deref()
    }

    /// Returns whether the `loan` is live at the given `point`.
    pub(crate) fn contains(&self, loan: BorrowIndex, point: PointIndex) -> bool {
        let (word, mask) = word_and_mask(point);
        self.rows[loan].as_ref().is_some_and(|row| row[word] & mask != 0)
    }
}

/// The per-region state of the traversal. The edge-direction data is computed once per body; the
/// reachability buffers are only held while a loan is actually reaching the region.
struct RegionState {
    /// The points the loan currently being traversed has reached this region at, and the points
    /// added to it since the region's block was last processed. Empty when the loan currently being
    /// traversed has not reached this region.
    reached: Box<[Word]>,
    delta: Box<[Word]>,

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
    graph: &'a LocalizedConstraintGraph,
    live_region_variances: &'a BTreeMap<RegionVid, ConstraintDirection>,
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
}

impl<'a, 'tcx> LoanReachability<'a, 'tcx> {
    pub(super) fn new(
        body: &'a Body<'tcx>,
        liveness: &'a LivenessValues,
        graph: &'a LocalizedConstraintGraph,
        live_region_variances: &'a BTreeMap<RegionVid, ConstraintDirection>,
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
            graph,
            live_region_variances,
            universal_regions,
            num_points,
            entries,
            all_points,
            block_entry,
            block_terminator,
            block_words,
            states: IndexVec::new(),
            worklist: VecDeque::new(),
            touched: Vec::new(),
            points_scratch: empty_points(num_points),
            fill_scratch: empty_points(num_points),
            live_scratch: empty_points(num_points),
        }
    }

    /// Traverses the graph once per loan, and returns the points at which each loan is live: the
    /// points it reaches a live region at.
    ///
    /// This is an approximation of liveness (which is the thing we want), in that we're using a
    /// single notion of reachability to represent what used to be _two_ different transitive
    /// closures. It didn't seem impactful when coming up with the single-graph and reachability
    /// through space (regions) + time (CFG) concepts, but in practice the combination of
    /// time-traveling with kills is more impactful than initially anticipated.
    ///
    /// Kills should prevent a loan from reaching its successor points in the CFG, but not while
    /// time-traveling: we're not actually at that CFG point, but looking for predecessor regions
    /// that contain the loan. One of the two TCs we had pushed the transitive subset edges to each
    /// point instead of having backward edges, and the problem didn't exist before. In the
    /// abstract, naive reachability is not enough to model this, we'd need a slightly different
    /// solution. For example, maybe with a two-step traversal:
    /// - at each point we first traverse the subgraph (and possibly time-travel) looking for exit
    ///   nodes while ignoring kills,
    /// - and then when we're back at the current point, we continue normally.
    ///
    /// Another (less annoying) subtlety is that kills and the loan use-map are flow-insensitive.
    /// Kills can actually appear in places before a loan is introduced, or at a location that is
    /// actually unreachable in the CFG from the introduction point, and these can also be
    /// encountered during time-traveling.
    ///
    /// The simplest change that made sense to "fix" the issues above is taking into account kills
    /// that are:
    /// - reachable from the introduction point
    /// - encountered during forward traversal. Note that this is not transitive like the two-step
    ///   traversal described above: only kills encountered on exit via a backward edge are ignored.
    ///
    /// This version of the analysis, however, is enough in practice to pass the tests that we care
    /// about and NLLs reject, without regressions on crater, and is an actionable subset of the
    /// full analysis. It also naturally points to areas of improvement that we wish to explore
    /// later, namely handling kills appropriately during traversal, instead of continuing traversal
    /// to all the reachable nodes.
    ///
    /// FIXME: analyze potential unsoundness, possibly in concert with a borrowck implementation in
    /// a-mir-formality, fuzzing, or manually crafting counter-examples.
    pub(super) fn compute_live_loans(&mut self, borrow_set: &BorrowSet<'tcx>) -> LiveLoans {
        let mut live_loans = LiveLoans::new(borrow_set.len(), self.num_points);

        for (loan_idx, loan) in borrow_set.iter_enumerated() {
            // The loan enters the graph at the region and point it is introduced at.
            let start = loan.reserve_location;
            self.add_point(loan.region, self.liveness.point_from_location(start), start.block);

            let row = live_loans.row_mut(loan_idx);
            while let Some((region, block)) = self.worklist.pop_front() {
                self.process(region, block, row);
            }

            // Release the per-loan state.
            let mut touched = std::mem::take(&mut self.touched);
            for &region in &touched {
                let state = self.states[region].as_mut().unwrap();
                state.in_loan = false;

                // Release the point sets: a loan reaches a small part of the graph, and holding a
                // set per region for the whole body is a lot of memory on a big one.
                state.reached = Box::default();
                state.delta = Box::default();
            }
            touched.clear();
            self.touched = touched;
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

    /// Propagates the points newly reached for `region` within `block` to its successors in the
    /// graph, and records them in `row` where the region is live.
    ///
    /// Propagation is per basic block rather than per region: the points of a block are a couple of
    /// words at most, so the liveness closures and the set operations below all stay O(1), and the
    /// work is proportional to the `(loan, region, block)` triples a loan reaches rather than to
    /// the size of the body.
    fn process(&mut self, region: RegionVid, block: BasicBlock, row: &mut [Word]) {
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
        if let Some(live_points) = self.liveness.points().row(region) {
            for interval in live_points.iter_intervals() {
                if interval.end <= entry {
                    continue;
                }
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
            for word in w0..=w1 {
                row[word] |= points[word] & live[word];
                state.reached[word] |= points[word];
            }
        }

        // 2. The liveness edges leaving the block, to the entry point of the successor blocks and
        // to the terminator of the predecessor blocks.
        let body = self.body;
        if forward && test_bit(&points, terminator) {
            for successor in body[block].terminator().successors() {
                let point = self.block_entry[successor];
                if universal || self.liveness.is_live_at_point(region, point) {
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

        let graph = self.graph;

        // 3. The subset edges that hold at every point -- the logical ones. Every point reached
        // here flows to the target region, unchanged.
        for successor in graph.logical_successors(region) {
            self.add_words(successor, &points, w0, w1, block);
        }

        // 4. The subset edges tied to a single location -- the physical ones. Each applies at its
        // own point only, and only if that point has been reached. They are sorted, so we can jump
        // to this block's range.
        let physical_points = graph.physical_points(region);
        let start = physical_points.partition_point(|&point| point < entry);
        for &point in &physical_points[start..] {
            if point > terminator {
                break;
            }
            if test_bit(&points, point) {
                for successor in graph.physical_successors(region, point) {
                    self.add_point(successor, point, block);
                }
            }
        }

        points[w0..=w1].fill(0);
        self.points_scratch = points;
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
        let mut any_new = false;
        for word in lo..=hi {
            let new = points[word] & !state.reached[word];
            if new == 0 {
                continue;
            }
            state.reached[word] |= new;
            state.delta[word] |= new;
            any_new = true;
        }
        if !any_new {
            return;
        }

        self.record_new_points(region, block);
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

        self.record_new_points(region, block);
    }

    /// Schedules `region`'s block for propagation, now that the loan has reached new points in
    /// it.
    fn record_new_points(&mut self, region: RegionVid, block: BasicBlock) {
        let state = self.states[region].as_mut().unwrap();
        let first_touch = !state.in_loan;
        state.in_loan = true;

        self.worklist.push_back((region, block));
        if first_touch {
            self.touched.push(region);
        }
    }

    /// Returns `region`'s state, creating it and acquiring its point sets if needed.
    fn ensure_state(&mut self, region: RegionVid) -> &mut RegionState {
        let num_points = self.num_points;
        if self.states.get(region).is_none_or(Option::is_none) {
            let state = self.make_state(region);
            *self.states.ensure_contains_elem(region, || None) = Some(state);
        }

        let state = self.states[region].as_mut().unwrap();
        if state.reached.is_empty() {
            state.reached = empty_points(num_points);
            state.delta = empty_points(num_points);
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
        let direction = *self
            .live_region_variances
            .get(&region)
            .unwrap_or(&ConstraintDirection::Bidirectional);

        RegionState {
            reached: Box::default(),
            delta: Box::default(),
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

/// Recomputes loan liveness with the node-by-node DFS and checks that it agrees with the
/// set-based traversal.
///
/// The two are meant to be the same least fixpoint of the same edge relation, and the DFS is still
/// around for the polonius MIR dumps, so a debug-assertions build can afford to check that claim on
/// every body it compiles rather than leaving the two implementations to drift. It is not cheap --
/// it is the quadratic traversal this module exists to replace -- so it is `debug_assertions` only.
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
    struct DfsVisitor<'a> {
        liveness: &'a LivenessValues,
        live_loans: LiveLoans,
    }

    impl LocalizedConstraintGraphVisitor for DfsVisitor<'_> {
        fn on_node_traversed(&mut self, loan: BorrowIndex, node: LocalizedNode) {
            if self.liveness.is_live_at_point(node.region, node.point) {
                self.live_loans.insert(loan, node.point);
            }
        }
    }

    let mut visitor = DfsVisitor {
        liveness,
        live_loans: LiveLoans::new(borrow_set.len(), liveness.num_points()),
    };
    graph.traverse(
        body,
        liveness,
        live_region_variances,
        universal_regions,
        borrow_set,
        &mut visitor,
    );

    for (loan, _) in borrow_set.iter_enumerated() {
        // Compare a word at a time, and only decode a point if the two disagree.
        let ours = live_loans.row(loan);
        let dfs = visitor.live_loans.row(loan);
        let words = num_words(liveness.num_points());
        for word in 0..words {
            let (a, b) = (ours.map_or(0, |row| row[word]), dfs.map_or(0, |row| row[word]));
            if a == b {
                continue;
            }
            let bit = (a ^ b).trailing_zeros() as usize;
            let point = PointIndex::from_usize(word * WORD_BITS + bit);
            panic!(
                "set-based and DFS loan liveness disagree for {loan:?} at {:?}: {} vs {}",
                liveness.location_from_point(point),
                a & (1 << bit) != 0,
                b & (1 << bit) != 0,
            );
        }
    }
}
