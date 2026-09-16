use std::collections::{BTreeMap, VecDeque};

use itertools::Itertools;
use rustc_data_structures::fx::FxHashMap;
use rustc_index::{IndexVec, bit_set::GrowableBitSet};
use rustc_middle::{mir::{BasicBlock, Body}, ty::RegionVid};
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};

use crate::{consumers::BorrowSet, polonius::{ConstraintDirection, LiveLoans, LocalizedConstraintGraph}, region_infer::values::LivenessValues, universal_regions::UniversalRegions};

/// The number of loans traversed together.
pub(super) const BATCH_SIZE: usize = u64::BITS as usize;

/// A set of the loans of a batch, one bit each.
#[derive(Copy, Clone, PartialEq, Eq, Default)]
pub(super) struct LoanSet(u64);

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

struct LoanLiveness<'a, 'tcx> {
    body: &'a Body<'tcx>,
    location_map: &'a DenseLocationMap,
    liveness: &'a mut LivenessValues,
    graph: &'a LocalizedConstraintGraph,
    live_region_variances: &'a mut BTreeMap<RegionVid, ConstraintDirection>,
    universal_regions: &'a UniversalRegions<'tcx>,
    borrow_set: &'a BorrowSet<'tcx>,

    live_loans: LiveLoans,

    region_blocks: IndexVec<RegionInBlockIndex, RegionInBlock>,
    region_block_indices: FxHashMap<(RegionVid, BasicBlock), RegionInBlockIndex>,

    worklist: VecDeque<RegionInBlockIndex>,
    queued: GrowableBitSet<RegionInBlockIndex>,
}

impl<'a, 'tcx> LoanLiveness<'a, 'tcx> {
    pub(super) fn compute(
        body: &'a Body<'tcx>,
        location_map: &'a DenseLocationMap,
        liveness: &'a mut LivenessValues,
        graph: &'a LocalizedConstraintGraph,
        live_region_variances: &'a mut BTreeMap<RegionVid, ConstraintDirection>,
        universal_regions: &'a UniversalRegions<'tcx>,
        borrow_set: &'a BorrowSet<'tcx>,
    ) -> LiveLoans {
        let mut loan_liveness = Self {
            body,
            location_map,
            liveness,
            graph,
            live_region_variances,
            universal_regions,
            borrow_set,

            live_loans: LiveLoans::new(location_map.num_points(), borrow_set.len()),

            region_blocks: IndexVec::new(),
            region_block_indices: FxHashMap::default(),

            worklist: VecDeque::new(),
            queued: GrowableBitSet::new_empty(),
        };
        loan_liveness.compute_live_laons();
        loan_liveness.live_loans
    }

    fn compute_live_laons(&mut self) {
        let num_loans = self.borrow_set.len();

        for batch_start in (0..num_loans).step_by(BATCH_SIZE) {
        }
    }
}