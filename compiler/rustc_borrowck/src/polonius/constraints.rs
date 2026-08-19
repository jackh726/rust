use rustc_data_structures::fx::FxHashSet;
use rustc_index::bit_set::DenseBitSet;
use rustc_index::interval::IntervalSet;
use rustc_index::{IndexSlice, IndexVec};
use rustc_middle::mir::{Body, Location};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::points::PointIndex;

use crate::BorrowSet;
use crate::constraints::OutlivesConstraintSet;
use crate::constraints::graph::NormalConstraintGraph;
use crate::polonius::ConstraintDirection;
use crate::region_infer::values::LivenessValues;
use crate::type_check::Locations;
use crate::universal_regions::UniversalRegions;

/// A localized outlives constraint reifies the CFG location where the outlives constraint holds,
/// within the origins themselves as if they were different from point to point: from `a: b`
/// outlives constraints to `a@p: b@p`, where `p` is the point in the CFG.
///
/// This models two sources of constraints:
/// - constraints that traverse the subsets between regions at a given point, `a@p: b@p`. These
///   depend on typeck constraints generated via assignments, calls, etc.
/// - constraints that traverse the CFG via the same region, `a@p: a@q`, where `p` is a predecessor
///   of `q`. These depend on the liveness of the regions at these points, as well as their
///   variance.
///
/// This dual of NLL's [crate::constraints::OutlivesConstraint] therefore encodes the
/// position-dependent outlives constraints used by Polonius, to model the flow-sensitive loan
/// propagation via reachability within a graph of localized constraints.
///
/// That `LocalizedConstraintGraph` can create these edges on-demand during traversal, and we
/// therefore model them as a pair of `LocalizedNode` vertices.
///
#[derive(Copy, Clone, PartialEq, Eq)]
pub(super) struct LocalizedNode {
    pub region: RegionVid,
    pub point: PointIndex,
}

impl std::hash::Hash for LocalizedNode {
    /// Hashes the pair as a single `u64`. The derived implementation hashes the two indices
    /// separately, which costs two `FxHasher` rounds; the localized graph traversal inserts and
    /// probes one of these per node visited, so it is worth the manual impl.
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        let packed = ((self.region.as_u32() as u64) << 32) | (self.point.as_u32() as u64);
        state.write_u64(packed);
    }
}

/// The localized constraint graph indexes the physical and logical edges to lazily compute a given
/// node's successors during traversal.
///
/// The index is built one region at a time, the first time the traversal asks about that region. A
/// loan enters the graph at its own region and reaches only what that region flows into, which on
/// a body whose loans are confined to a corner of it -- the common shape -- is a small part of the
/// whole. Indexing every constraint up front is work done for regions nothing ever asks about, and
/// on a big body with one loan it is the whole cost of loan liveness.
pub(super) struct LocalizedConstraintGraph {
    /// Per region, its physical edges: the outlives constraints that hold at a single point,
    /// recorded as `(point, sub)` and sorted, so that the successors at a point are a contiguous
    /// range and the points belonging to a block are too. We localize them on-demand when
    /// traversing from the node to the successor region.
    physical_edges: IndexVec<RegionVid, Vec<(PointIndex, RegionVid)>>,

    /// Per region, the logical edges representing the outlives constraints that hold at all points
    /// in the CFG, which we don't localize to avoid creating a lot of unnecessary edges in the
    /// graph. Some CFGs can be big, and we don't need to create such a physical edge for every
    /// point in the CFG.
    logical_edges: IndexVec<RegionVid, Vec<RegionVid>>,

    /// The regions whose rows above have been built. A region with no outgoing constraints at all
    /// is marked too, so that it is looked up once rather than every time it is reached.
    indexed: DenseBitSet<RegionVid>,
}

/// The visitor interface when traversing a `LocalizedConstraintGraph`.
pub(super) trait LocalizedConstraintGraphVisitor {
    /// Callback called when discovering a new `successor` node for the `current_node`.
    fn on_successor_discovered(&mut self, _current_node: LocalizedNode, _successor: LocalizedNode) {
    }
}

impl LocalizedConstraintGraph {
    /// An empty graph, whose rows are built as the traversal asks for them.
    pub(super) fn new(num_region_vars: usize) -> Self {
        LocalizedConstraintGraph {
            physical_edges: IndexVec::new(),
            logical_edges: IndexVec::new(),
            indexed: DenseBitSet::new_empty(num_region_vars),
        }
    }

    /// Indexes `region`'s outlives constraints, unless that has already been done. Every read of
    /// the rows below has to be preceded by this: an unindexed region looks like one with no edges
    /// at all, which would silently cut the traversal short.
    pub(super) fn ensure<'tcx>(
        &mut self,
        region: RegionVid,
        liveness: &LivenessValues,
        constraints: &OutlivesConstraintSet<'tcx>,
        constraint_graph: &NormalConstraintGraph,
    ) {
        if !self.indexed.insert(region) {
            return;
        }

        let mut physical = Vec::new();
        let mut logical = Vec::new();
        for constraint in constraint_graph.outgoing_edges_from_graph(region, constraints) {
            match constraint.locations {
                Locations::All(_) => logical.push(constraint.sub),
                Locations::Single(location) => {
                    physical.push((liveness.point_from_location(location), constraint.sub));
                }
            }
        }

        // A region can have several constraints to the same target, and several at the same point:
        // both traversals only need to visit each successor once. Sorting the physical edges is
        // also what lets them be looked up by point, and by range of points.
        logical.sort_unstable();
        logical.dedup();
        physical.sort_unstable();
        physical.dedup();

        *self.physical_edges.ensure_contains_elem(region, Vec::new) = physical;
        *self.logical_edges.ensure_contains_elem(region, Vec::new) = logical;
    }

    /// `region`'s physical edges, sorted by point. Call [`Self::ensure`] first.
    pub(super) fn physical_edges(&self, region: RegionVid) -> &[(PointIndex, RegionVid)] {
        self.physical_edges.get(region).map_or(&[], |edges| edges)
    }

    /// `region`'s logical edges. Call [`Self::ensure`] first.
    pub(super) fn logical_edges(&self, region: RegionVid) -> &[RegionVid] {
        self.logical_edges.get(region).map_or(&[], |edges| edges)
    }

    /// Takes `region`'s rows out, so that the traversal can walk them while it goes on mutating
    /// the rest of its state. [`Self::put_rows`] puts them back.
    ///
    /// Nothing reached from `region`'s own edges reads `region`'s rows, so they are only missing
    /// for a window in which no one looks.
    pub(super) fn take_rows(
        &mut self,
        region: RegionVid,
    ) -> (Vec<(PointIndex, RegionVid)>, Vec<RegionVid>) {
        (
            std::mem::take(self.physical_edges.ensure_contains_elem(region, Vec::new)),
            std::mem::take(self.logical_edges.ensure_contains_elem(region, Vec::new)),
        )
    }

    /// Puts back what [`Self::take_rows`] took.
    pub(super) fn put_rows(
        &mut self,
        region: RegionVid,
        physical: Vec<(PointIndex, RegionVid)>,
        logical: Vec<RegionVid>,
    ) {
        self.physical_edges[region] = physical;
        self.logical_edges[region] = logical;
    }

    /// The successors of `region`'s physical edges at `point`, as a range of `edges`, which must be
    /// the row [`Self::ensure`] built for `region`.
    pub(super) fn successors_at(
        edges: &[(PointIndex, RegionVid)],
        point: PointIndex,
    ) -> &[(PointIndex, RegionVid)] {
        let lo = edges.partition_point(|&(p, _)| p < point);
        let hi = edges[lo..].partition_point(|&(p, _)| p == point);
        &edges[lo..lo + hi]
    }

    /// Traverses the localized constraint graph per-loan, and notifies the `visitor` of discovered
    /// successors.
    ///
    /// Note: this node-by-node DFS is only used by the polonius MIR dumps, which need the
    /// individual edges. The loan liveness computation itself uses the set-based traversal in
    /// [`super::reachability`], which visits the same nodes but does not materialize the edges.
    pub(super) fn traverse<'tcx>(
        &mut self,
        body: &Body<'tcx>,
        liveness: &LivenessValues,
        constraints: &OutlivesConstraintSet<'tcx>,
        constraint_graph: &NormalConstraintGraph,
        live_region_variances: &IndexSlice<RegionVid, Option<ConstraintDirection>>,
        universal_regions: &UniversalRegions<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        visitor: &mut impl LocalizedConstraintGraphVisitor,
    ) {
        let live_regions = liveness.points();

        let mut visited = FxHashSet::default();
        let mut stack = Vec::new();

        // Compute reachability per loan by traversing each loan's subgraph starting from where it
        // is introduced.
        for (_, loan) in borrow_set.iter_enumerated() {
            visited.clear();
            stack.clear();

            let start_node = LocalizedNode {
                region: loan.region,
                point: liveness.point_from_location(loan.reserve_location),
            };
            stack.push(start_node);

            while let Some(node) = stack.pop() {
                if !visited.insert(node) {
                    continue;
                }

                // We've reached a node we haven't visited before.
                self.ensure(node.region, liveness, constraints, constraint_graph);
                let location = liveness.location_from_point(node.point);

                // The points where this node's region is live are needed twice below, to decide
                // whether the forward and backward liveness edges exist. Look the row up once.
                let live_points = live_regions.row(node.region);
                let is_live_here = live_points.is_some_and(|points| points.contains(node.point));

                // When we find a _new_ successor, we'd like to
                // - visit it eventually,
                // - and let the generic visitor know about it.
                let mut successor_found = |succ| {
                    if !visited.contains(&succ) {
                        stack.push(succ);
                        visitor.on_successor_discovered(node, succ);
                    }
                };

                // Then, we propagate the loan along the localized constraint graph. The outgoing
                // edges are computed lazily, from:
                // - the various physical edges present at this node,
                // - the materialized logical edges that exist virtually at all points for this
                //   node's region, localized at this point.

                // Universal regions propagate loans along the CFG, i.e. forwards only.
                let is_universal_region = universal_regions.is_universal_region(node.region);

                // The physical edges present at this node are:
                //
                // 1. the typeck edges that flow from region to region *at this point*. Most
                // regions have no physical edges at all, so check that before hashing the node.
                let physical_edges = self.physical_edges(node.region);
                for &(_, succ) in Self::successors_at(physical_edges, node.point) {
                    let succ = LocalizedNode { region: succ, point: node.point };
                    successor_found(succ);
                }

                // 2a. the liveness edges that flow *forward*, from this node's point to its
                // successors in the CFG.
                if body[location.block].statements.get(location.statement_index).is_some() {
                    // Intra-block edges, straight line constraints from each point to its successor
                    // within the same block.
                    let next_point = node.point + 1;
                    if let Some(succ) = compute_forward_successor(
                        node.region,
                        next_point,
                        live_points,
                        live_region_variances,
                        is_universal_region,
                    ) {
                        successor_found(succ);
                    }
                } else {
                    // Inter-block edges, from the block's terminator to each successor block's
                    // entry point.
                    for successor_block in body[location.block].terminator().successors() {
                        let next_location = Location { block: successor_block, statement_index: 0 };
                        let next_point = liveness.point_from_location(next_location);
                        if let Some(succ) = compute_forward_successor(
                            node.region,
                            next_point,
                            live_points,
                            live_region_variances,
                            is_universal_region,
                        ) {
                            successor_found(succ);
                        }
                    }
                }

                // 2b. the liveness edges that flow *backward*, from this node's point to its
                // predecessors in the CFG.
                if !is_universal_region {
                    if location.statement_index > 0 {
                        // Backward edges to the predecessor point in the same block.
                        let previous_point = PointIndex::from(node.point.as_usize() - 1);
                        if let Some(succ) = compute_backward_successor(
                            node.region,
                            is_live_here,
                            previous_point,
                            live_region_variances,
                        ) {
                            successor_found(succ);
                        }
                    } else {
                        // Backward edges from the block entry point to the terminator of the
                        // predecessor blocks.
                        let predecessors = body.basic_blocks.predecessors();
                        for &pred_block in &predecessors[location.block] {
                            let previous_location = Location {
                                block: pred_block,
                                statement_index: body[pred_block].statements.len(),
                            };
                            let previous_point = liveness.point_from_location(previous_location);
                            if let Some(succ) = compute_backward_successor(
                                node.region,
                                is_live_here,
                                previous_point,
                                live_region_variances,
                            ) {
                                successor_found(succ);
                            }
                        }
                    }
                }

                // And finally, we have the logical edges, materialized at this point.
                for &logical_succ in self.logical_edges(node.region) {
                    let succ = LocalizedNode { region: logical_succ, point: node.point };
                    successor_found(succ);
                }
            }
        }
    }
}

/// Returns the successor for the current region/point node when propagating a loan through forward
/// edges, if applicable, according to liveness and variance.
fn compute_forward_successor(
    region: RegionVid,
    next_point: PointIndex,
    live_points: Option<&IntervalSet<PointIndex>>,
    live_region_variances: &IndexSlice<RegionVid, Option<ConstraintDirection>>,
    is_universal_region: bool,
) -> Option<LocalizedNode> {
    // 1. Universal regions are semantically live at all points.
    if is_universal_region {
        let succ = LocalizedNode { region, point: next_point };
        return Some(succ);
    }

    // 2. Otherwise, gather the edges due to explicit region liveness, when applicable.
    if !live_points.is_some_and(|points| points.contains(next_point)) {
        return None;
    }

    // Here, `region` could be live at the current point, and is live at the next point: add a
    // constraint between them, according to variance.

    // Note: there currently are cases related to promoted and const generics, where we don't yet
    // have variance information (possibly about temporary regions created when typeck sanitizes the
    // promoteds). Until that is done, we conservatively fallback to maximizing reachability by
    // adding a bidirectional edge here. This will not limit traversal whatsoever, and thus
    // propagate liveness when needed.
    //
    // FIXME: add the missing variance information and remove this fallback bidirectional edge.
    let direction = live_region_variances
        .get(region)
        .copied()
        .flatten()
        .unwrap_or(ConstraintDirection::Bidirectional);

    match direction {
        ConstraintDirection::Backward => {
            // Contravariant cases: loans flow in the inverse direction, but we're only interested
            // in forward successors and there are none here.
            None
        }
        ConstraintDirection::Forward | ConstraintDirection::Bidirectional => {
            // 1. For covariant cases: loans flow in the regular direction, from the current point
            // to the next point.
            // 2. For invariant cases, loans can flow in both directions, but here as well, we only
            // want the forward path of the bidirectional edge.
            Some(LocalizedNode { region, point: next_point })
        }
    }
}

/// Returns the successor for the current region/point node when propagating a loan through backward
/// edges, if applicable, according to liveness and variance.
fn compute_backward_successor(
    region: RegionVid,
    is_live_at_current_point: bool,
    previous_point: PointIndex,
    live_region_variances: &IndexSlice<RegionVid, Option<ConstraintDirection>>,
) -> Option<LocalizedNode> {
    // Liveness flows into the regions live at the next point. So, in a backwards view, we'll link
    // the region from the current point, if it's live there, to the previous point.
    if !is_live_at_current_point {
        return None;
    }

    // FIXME: add the missing variance information and remove this fallback bidirectional edge. See
    // the same comment in `compute_forward_successor`.
    let direction = live_region_variances
        .get(region)
        .copied()
        .flatten()
        .unwrap_or(ConstraintDirection::Bidirectional);

    match direction {
        ConstraintDirection::Forward => {
            // Covariant cases: loans flow in the regular direction, but we're only interested in
            // backward successors and there are none here.
            None
        }
        ConstraintDirection::Backward | ConstraintDirection::Bidirectional => {
            // 1. For contravariant cases: loans flow in the inverse direction, from the current
            // point to the previous point.
            // 2. For invariant cases, loans can flow in both directions, but here as well, we only
            // want the backward path of the bidirectional edge.
            Some(LocalizedNode { region, point: previous_point })
        }
    }
}
