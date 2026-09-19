use rustc_data_structures::fx::{FxHashMap, FxHashSet, FxIndexSet};
use rustc_index::IndexVec;
use rustc_index::interval::IntervalSet;
use rustc_middle::mir::{Body, Location};
use rustc_middle::ty::RegionVid;
use rustc_mir_dataflow::points::{DenseLocationMap, PointIndex};
use tracing::debug;

use crate::BorrowSet;
use crate::constraints::OutlivesConstraint;
use crate::dataflow::BorrowIndex;
use crate::polonius::{ConstraintDirection, LiveRegionVariances};
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
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub(super) struct LocalizedNode {
    pub region: RegionVid,
    pub point: PointIndex,
}

/// The localized constraint graph indexes the physical and logical edges to lazily compute a given
/// node's successors during traversal.
pub(super) struct LocalizedConstraintGraph {
    /// The actual, physical, edges we have recorded for a given node. We localize them on-demand
    /// when traversing from the node to the successor region.
    edges: FxHashMap<LocalizedNode, FxIndexSet<RegionVid>>,

    /// The logical edges representing the outlives constraints that hold at all points in the CFG,
    /// which we don't localize to avoid creating a lot of unnecessary edges in the graph. Some CFGs
    /// can be big, and we don't need to create such a physical edge for every point in the CFG.
    logical_edges: IndexVec<RegionVid, Option<FxIndexSet<RegionVid>>>,
}

/// For a given region, the relevant liveness and variance information.
pub(super) struct RegionLiveness<'a> {
    region: RegionVid,
    direction: ConstraintDirection,
    liveness: &'a LivenessValues,
    /// The region's row in the liveness matrix, looked up once per node rather than once per
    /// `is_live_at` call.
    live_points: Option<&'a IntervalSet<PointIndex>>,
}

impl<'a> RegionLiveness<'a> {
    pub(super) fn new(
        region: RegionVid,
        live_region_variances: &LiveRegionVariances,
        liveness: &'a LivenessValues,
    ) -> Self {
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
        let live_points = liveness.points().row(region);
        Self { region, direction, liveness, live_points }
    }

    fn is_live_at(&self, point: PointIndex) -> bool {
        self.live_points.is_some_and(|points| points.contains(point))
    }
}

/// The source of liveness information for a given region.
pub(super) trait LivenessSource {
    fn liveness_for_region(&mut self, region: RegionVid) -> RegionLiveness<'_>;
    fn location_map(&self) -> &DenseLocationMap;
}

/// The visitor interface when traversing a `LocalizedConstraintGraph`.
pub(super) trait LocalizedConstraintGraphVisitor {
    /// Callback called when traversing a given `loan` encounters a localized `node` it hasn't
    /// visited before.
    fn on_node_traversed(&mut self, _loan: BorrowIndex, _node: LocalizedNode, _is_live: bool) {}

    /// Callback called when discovering a new `successor` node for the `current_node`.
    fn on_successor_discovered(&mut self, _current_node: LocalizedNode, _successor: LocalizedNode) {
    }
}

impl LocalizedConstraintGraph {
    /// Traverses the constraints and returns the indexed graph of edges per node.
    pub(super) fn new<'tcx>(
        location_map: &DenseLocationMap,
        outlives_constraints: impl Iterator<Item = OutlivesConstraint<'tcx>>,
    ) -> Self {
        let mut edges: FxHashMap<_, FxIndexSet<_>> = FxHashMap::default();
        let mut logical_edges: IndexVec<RegionVid, Option<FxIndexSet<_>>> = IndexVec::new();

        for outlives_constraint in outlives_constraints {
            match outlives_constraint.locations {
                Locations::All(_) => {
                    logical_edges
                        .ensure_contains_elem(outlives_constraint.sup, || None)
                        .get_or_insert_with(FxIndexSet::default)
                        .insert(outlives_constraint.sub);
                }

                Locations::Single(location) => {
                    let node = LocalizedNode {
                        region: outlives_constraint.sup,
                        point: location_map.point_from_location(location),
                    };
                    edges.entry(node).or_default().insert(outlives_constraint.sub);
                }
            }
        }

        LocalizedConstraintGraph { edges, logical_edges }
    }

    /// Traverses the localized constraint graph per-loan, and notifies the `visitor` of discovered
    /// nodes and successors.
    pub(super) fn traverse<'tcx>(
        &self,
        body: &Body<'tcx>,
        universal_regions: &UniversalRegions<'tcx>,
        borrow_set: &BorrowSet<'tcx>,
        liveness_source: &mut impl LivenessSource,
        visitor: &mut impl LocalizedConstraintGraphVisitor,
    ) {
        let mut visited = FxHashSet::default();
        let mut stack = Vec::new();

        // Compute reachability per loan by traversing each loan's subgraph starting from where it
        // is introduced.
        for (loan_idx, loan) in borrow_set.iter_enumerated() {
            visited.clear();
            stack.clear();

            let start_node = LocalizedNode {
                region: loan.region,
                point: liveness_source.location_map().point_from_location(loan.reserve_location),
            };
            visited.insert(start_node);
            stack.push(start_node);

            while let Some(node) = stack.pop() {
                let liveness = liveness_source.liveness_for_region(node.region);
                // We've reached a node we haven't visited before.
                let location = liveness.liveness.location_map().to_location(node.point);
                visitor.on_node_traversed(loan_idx, node, liveness.is_live_at(node.point));

                // When we find a _new_ successor, we'd like to
                // - visit it eventually,
                // - and let the generic visitor know about it.
                let mut successor_found = |succ| {
                    // Nodes are marked visited on discovery: a node is pushed at most once, so
                    // this costs a single hash lookup per edge instead of one here and one on pop.
                    if visited.insert(succ) {
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
                // 1. the typeck edges that flow from region to region *at this point*.
                for &succ in self.edges.get(&node).into_flat_iter() {
                    let succ = LocalizedNode { region: succ, point: node.point };
                    successor_found(succ);
                }

                debug!(?liveness.direction);

                // 2a. the liveness edges that flow *forward*, from this node's point to its
                // successors in the CFG.
                let has_forward_edges = is_universal_region
                    || matches!(
                        liveness.direction,
                        ConstraintDirection::Forward | ConstraintDirection::Bidirectional
                    );
                if has_forward_edges {
                    if body[location.block].statements.get(location.statement_index).is_some() {
                        // Intra-block edges, straight line constraints from each point to its successor
                        // within the same block.
                        let next_point = node.point + 1;
                        let succ = LocalizedNode { region: liveness.region, point: next_point };
                        if is_universal_region || liveness.is_live_at(next_point) {
                            successor_found(succ);
                        }
                    } else {
                        // Inter-block edges, from the block's terminator to each successor block's
                        // entry point.
                        for successor_block in body[location.block].terminator().successors() {
                            let next_location =
                                Location { block: successor_block, statement_index: 0 };
                            let next_point = liveness.liveness.point_from_location(next_location);
                            let succ = LocalizedNode { region: liveness.region, point: next_point };
                            if is_universal_region || liveness.is_live_at(next_point) {
                                successor_found(succ);
                            }
                        }
                    }
                }

                // 2b. the liveness edges that flow *backward*, from this node's point to its
                // predecessors in the CFG.
                // Both conditions are invariant across the predecessors, so check them once
                // rather than once per predecessor block:
                // - contravariant/invariant regions have backward edges, covariant ones don't,
                // - and liveness is tested at the *current* point, which doesn't vary either.
                let has_backward_edges = !is_universal_region
                    && !matches!(liveness.direction, ConstraintDirection::Forward)
                    && liveness.is_live_at(node.point);
                if has_backward_edges {
                    if location.statement_index > 0 {
                        // Backward edges to the predecessor point in the same block.
                        let previous_point = PointIndex::from(node.point.as_usize() - 1);
                        successor_found(LocalizedNode {
                            region: node.region,
                            point: previous_point,
                        });
                    } else {
                        // Backward edges from the block entry point to the terminator of the
                        // predecessor blocks.
                        let predecessors = body.basic_blocks.predecessors();
                        for &pred_block in &predecessors[location.block] {
                            let previous_location = Location {
                                block: pred_block,
                                statement_index: body[pred_block].statements.len(),
                            };
                            let previous_point =
                                liveness.liveness.point_from_location(previous_location);
                            successor_found(LocalizedNode {
                                region: node.region,
                                point: previous_point,
                            });
                        }
                    }
                }

                // And finally, we have the logical edges, materialized at this point.
                if let Some(Some(logical_succs)) = self.logical_edges.get(node.region) {
                    for &logical_succ in logical_succs {
                        let succ = LocalizedNode { region: logical_succ, point: node.point };
                        successor_found(succ);
                    }
                }
            }
        }
    }
}
