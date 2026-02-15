/-
# Network Theory via Computational Paths

This module models network theory concepts using computational paths:
network graphs, flow conservation, routing, network capacity,
protocol equivalence, and network composition.

## References

- Ahuja, Magnanti & Orlin, "Network Flows"
- Tanenbaum, "Computer Networks"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace NetworkPaths

universe u v

open ComputationalPaths.Path

/-! ## Network Nodes and Edges -/

/-- A network node with associated data. -/
structure NetNode (S : Type u) where
  nodeId : S

/-- A network edge connecting two nodes, with capacity. -/
structure NetEdge (S : Type u) where
  source : S
  target : S
  capacity : Nat

/-- Edge equivalence: two edges carry the same flow. -/
structure EdgeEquivData (S : Type u) where
  flow1 : S
  flow2 : S
  edgePath : Path flow1 flow2

/-- Edge equivalence path trans refl. -/
theorem edgeEquiv_trans_refl {S : Type u} (d : EdgeEquivData S) :
    Path.trans d.edgePath (Path.refl d.flow2) = d.edgePath := by
  simp

/-- Edge equivalence path refl trans. -/
theorem edgeEquiv_refl_trans {S : Type u} (d : EdgeEquivData S) :
    Path.trans (Path.refl d.flow1) d.edgePath = d.edgePath := by
  simp

/-- RwEq: edge equiv trans refl. -/
theorem edgeEquiv_rweq_trans_refl {S : Type u} (d : EdgeEquivData S) :
    RwEq
      (Path.trans d.edgePath (Path.refl d.flow2))
      d.edgePath :=
  rweq_of_step (Step.trans_refl_right d.edgePath)

/-- RwEq: edge equiv symm_symm. -/
theorem edgeEquiv_rweq_symm_symm {S : Type u} (d : EdgeEquivData S) :
    RwEq
      (Path.symm (Path.symm d.edgePath))
      d.edgePath :=
  rweq_of_step (Step.symm_symm d.edgePath)

/-! ## Flow Conservation -/

/-- Flow conservation data: inflow = outflow at a node. -/
structure FlowConservData where
  inflow : Nat
  outflow : Nat
  conservPath : Path inflow outflow

/-- Flow conservation path trans refl. -/
theorem flowConserv_trans_refl (d : FlowConservData) :
    Path.trans d.conservPath (Path.refl d.outflow) = d.conservPath := by
  simp

/-- RwEq: flow conservation inv cancel right. -/
theorem flowConserv_rweq_inv_right (d : FlowConservData) :
    RwEq
      (Path.trans d.conservPath (Path.symm d.conservPath))
      (Path.refl d.inflow) :=
  rweq_cmpA_inv_right d.conservPath

/-- RwEq: flow conservation symm_symm. -/
theorem flowConserv_rweq_symm_symm (d : FlowConservData) :
    RwEq
      (Path.symm (Path.symm d.conservPath))
      d.conservPath :=
  rweq_of_step (Step.symm_symm d.conservPath)

/-- RwEq: flow conservation refl trans. -/
theorem flowConserv_rweq_refl_trans (d : FlowConservData) :
    RwEq
      (Path.trans (Path.refl d.inflow) d.conservPath)
      d.conservPath :=
  rweq_of_step (Step.trans_refl_left d.conservPath)

/-! ## Routing -/

/-- Routing data: packet travels from source to destination via path. -/
structure RoutingData (S : Type u) where
  source : S
  destination : S
  routePath : Path source destination

/-- Route composition: combine two route segments. -/
def routeCompose {S : Type u} {a b c : S}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Route composition is associative. -/
theorem routeCompose_assoc {S : Type u} {a b c d : S}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    routeCompose (routeCompose p q) r =
    routeCompose p (routeCompose q r) := by
  simp [routeCompose]

/-- Route with refl on right is identity. -/
theorem routeCompose_refl_right {S : Type u} {a b : S} (p : Path a b) :
    routeCompose p (Path.refl b) = p := by
  simp [routeCompose]

/-- RwEq: routing inv cancel right. -/
theorem routing_rweq_inv_right {S : Type u} (d : RoutingData S) :
    RwEq
      (Path.trans d.routePath (Path.symm d.routePath))
      (Path.refl d.source) :=
  rweq_cmpA_inv_right d.routePath

/-- RwEq: routing symm_symm. -/
theorem routing_rweq_symm_symm {S : Type u} (d : RoutingData S) :
    RwEq
      (Path.symm (Path.symm d.routePath))
      d.routePath :=
  rweq_of_step (Step.symm_symm d.routePath)

/-! ## Network Capacity -/

/-- Capacity data: max flow equals min cut. -/
structure CapacityData where
  maxFlow : Nat
  minCut : Nat
  maxFlowMinCutPath : Path maxFlow minCut

/-- Max-flow min-cut path trans refl. -/
theorem capacity_trans_refl (d : CapacityData) :
    Path.trans d.maxFlowMinCutPath (Path.refl d.minCut) = d.maxFlowMinCutPath := by
  simp

/-- RwEq: capacity inv cancel right. -/
theorem capacity_rweq_inv_right (d : CapacityData) :
    RwEq
      (Path.trans d.maxFlowMinCutPath (Path.symm d.maxFlowMinCutPath))
      (Path.refl d.maxFlow) :=
  rweq_cmpA_inv_right d.maxFlowMinCutPath

/-- RwEq: capacity symm_symm. -/
theorem capacity_rweq_symm_symm (d : CapacityData) :
    RwEq
      (Path.symm (Path.symm d.maxFlowMinCutPath))
      d.maxFlowMinCutPath :=
  rweq_of_step (Step.symm_symm d.maxFlowMinCutPath)

/-! ## Protocol Equivalence -/

/-- Protocol equivalence: two protocols produce the same result. -/
structure ProtocolEquivData (S : Type u) where
  result1 : S
  result2 : S
  protocolPath : Path result1 result2

/-- Protocol equivalence path trans refl. -/
theorem protocol_trans_refl {S : Type u} (d : ProtocolEquivData S) :
    Path.trans d.protocolPath (Path.refl d.result2) = d.protocolPath := by
  simp

/-- RwEq: protocol inv cancel left. -/
theorem protocol_rweq_inv_left {S : Type u} (d : ProtocolEquivData S) :
    RwEq
      (Path.trans (Path.symm d.protocolPath) d.protocolPath)
      (Path.refl d.result2) :=
  rweq_cmpA_inv_left d.protocolPath

/-- RwEq: protocol symm_symm. -/
theorem protocol_rweq_symm_symm {S : Type u} (d : ProtocolEquivData S) :
    RwEq
      (Path.symm (Path.symm d.protocolPath))
      d.protocolPath :=
  rweq_of_step (Step.symm_symm d.protocolPath)

/-! ## Network Composition -/

/-- Composing two network paths. -/
theorem network_compose_assoc {S : Type u} {a b c d : S}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- congrArg for network maps. -/
theorem congrArg_network {A B : Type u} (f : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg f (Path.trans p (Path.refl y)) =
    Path.congrArg f p := by
  simp

/-- congrArg preserves network path composition. -/
theorem congrArg_network_compose {A B : Type u} (f : A → B)
    {x y z : A} (p : Path x y) (q : Path y z) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simp

/-- congrArg preserves network path symm. -/
theorem congrArg_network_symm {A B : Type u} (f : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp

end NetworkPaths
end Computation
end Path
end ComputationalPaths
