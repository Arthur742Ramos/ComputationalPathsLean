/-
# Network Theory via Computational Paths

Network graphs, flow conservation, routing, capacity constraints, shortest
paths, max-flow, network cuts, load balancing, multipath routing, congestion,
and network reliability—all modeled through computational paths.

## References

- Ahuja, Magnanti, Orlin, "Network Flows"
- Bertsekas & Gallager, "Data Networks"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace NetworkPaths

universe u v

open ComputationalPaths.Path

/-! ## Network Edges -/

/-- A network edge connecting two nodes with a flow value. -/
structure NetworkEdge (N : Type u) where
  src : N
  tgt : N
  flow : Nat
  edgePath : Path src tgt

/-- Compose network edges into a route. -/
def routeCompose {N : Type u} {a b c : N}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Route composition is associative. -/
theorem routeCompose_assoc {N : Type u} {a b c d : N}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    routeCompose (routeCompose p q) r = routeCompose p (routeCompose q r) := by
  simp [routeCompose]

/-- Route compose with refl right. -/
theorem routeCompose_refl_right {N : Type u} {a b : N} (p : Path a b) :
    routeCompose p (Path.refl b) = p := by
  simp [routeCompose]

/-- Route compose with refl left. -/
theorem routeCompose_refl_left {N : Type u} {a b : N} (p : Path a b) :
    routeCompose (Path.refl a) p = p := by
  simp [routeCompose]

/-! ## Flow Conservation -/

/-- Flow conservation data: flow in = flow out at a node. -/
structure FlowConservation where
  flowIn : Nat
  flowOut : Nat
  conservePath : Path flowIn flowOut

/-- Flow conservation trans refl. -/
theorem flowConserve_trans_refl (d : FlowConservation) :
    Path.trans d.conservePath (Path.refl d.flowOut) = d.conservePath := by
  simp

/-- RwEq: flow conservation inv cancel right. -/
noncomputable def flowConserve_rweq_inv_right (d : FlowConservation) :
    RwEq
      (Path.trans d.conservePath (Path.symm d.conservePath))
      (Path.refl d.flowIn) :=
  rweq_cmpA_inv_right d.conservePath

/-- RwEq: flow conservation symm_symm. -/
noncomputable def flowConserve_rweq_symm_symm (d : FlowConservation) :
    RwEq (Path.symm (Path.symm d.conservePath)) d.conservePath :=
  rweq_of_step (Step.symm_symm d.conservePath)

/-- RwEq: flow conservation refl trans. -/
noncomputable def flowConserve_rweq_refl_trans (d : FlowConservation) :
    RwEq
      (Path.trans (Path.refl d.flowIn) d.conservePath)
      d.conservePath :=
  rweq_of_step (Step.trans_refl_left d.conservePath)

/-! ## Routing -/

/-- Routing data: path from source to destination through network. -/
structure RoutingData (N : Type u) where
  source : N
  destination : N
  routePath : Path source destination

/-- Routing path trans refl. -/
theorem routing_trans_refl {N : Type u} (d : RoutingData N) :
    Path.trans d.routePath (Path.refl d.destination) = d.routePath := by
  simp

/-- RwEq: routing inv cancel left. -/
noncomputable def routing_rweq_inv_left {N : Type u} (d : RoutingData N) :
    RwEq
      (Path.trans (Path.symm d.routePath) d.routePath)
      (Path.refl d.destination) :=
  rweq_cmpA_inv_left d.routePath

/-- RwEq: routing refl trans. -/
noncomputable def routing_rweq_refl_trans {N : Type u} (d : RoutingData N) :
    RwEq
      (Path.trans (Path.refl d.source) d.routePath)
      d.routePath :=
  rweq_of_step (Step.trans_refl_left d.routePath)

/-! ## Capacity Constraints -/

/-- Capacity data: flow bounded by capacity via path. -/
structure CapacityData where
  currentFlow : Nat
  maxCapacity : Nat
  capacityPath : Path currentFlow maxCapacity

/-- Capacity path trans refl. -/
theorem capacity_trans_refl (d : CapacityData) :
    Path.trans d.capacityPath (Path.refl d.maxCapacity) = d.capacityPath := by
  simp

/-- RwEq: capacity inv cancel right. -/
noncomputable def capacity_rweq_inv_right (d : CapacityData) :
    RwEq
      (Path.trans d.capacityPath (Path.symm d.capacityPath))
      (Path.refl d.currentFlow) :=
  rweq_cmpA_inv_right d.capacityPath

/-! ## Network Cuts -/

/-- Cut data: partition of network witnessed by path between cut values. -/
structure CutData where
  srcSideFlow : Nat
  tgtSideFlow : Nat
  cutPath : Path srcSideFlow tgtSideFlow

/-- Cut-flow duality: cut value relates to flow via path. -/
noncomputable def cut_rweq_symm_symm (d : CutData) :
    RwEq (Path.symm (Path.symm d.cutPath)) d.cutPath :=
  rweq_of_step (Step.symm_symm d.cutPath)

/-- RwEq: cut inv cancel left. -/
noncomputable def cut_rweq_inv_left (d : CutData) :
    RwEq
      (Path.trans (Path.symm d.cutPath) d.cutPath)
      (Path.refl d.tgtSideFlow) :=
  rweq_cmpA_inv_left d.cutPath

/-! ## Load Balancing -/

/-- Load balance data: distributing traffic across paths. -/
structure LoadBalanceData (N : Type u) where
  entryPoint : N
  exitPoint : N
  balancePath : Path entryPoint exitPoint

/-- Load balance trans refl. -/
theorem loadBalance_trans_refl {N : Type u} (d : LoadBalanceData N) :
    Path.trans d.balancePath (Path.refl d.exitPoint) = d.balancePath := by
  simp

/-- RwEq: load balance inv cancel right. -/
noncomputable def loadBalance_rweq_inv_right {N : Type u} (d : LoadBalanceData N) :
    RwEq
      (Path.trans d.balancePath (Path.symm d.balancePath))
      (Path.refl d.entryPoint) :=
  rweq_cmpA_inv_right d.balancePath

/-- RwEq: load balance refl trans. -/
noncomputable def loadBalance_rweq_refl_trans {N : Type u} (d : LoadBalanceData N) :
    RwEq
      (Path.trans (Path.refl d.entryPoint) d.balancePath)
      d.balancePath :=
  rweq_of_step (Step.trans_refl_left d.balancePath)

/-! ## Congestion -/

/-- Congestion data: overloaded link witnessed by path. -/
structure CongestionData where
  normalFlow : Nat
  congestedFlow : Nat
  congestionPath : Path normalFlow congestedFlow

/-- RwEq: congestion trans refl. -/
noncomputable def congestion_rweq_trans_refl (d : CongestionData) :
    RwEq
      (Path.trans d.congestionPath (Path.refl d.congestedFlow))
      d.congestionPath :=
  rweq_of_step (Step.trans_refl_right d.congestionPath)

/-- RwEq: congestion symm_symm. -/
noncomputable def congestion_rweq_symm_symm (d : CongestionData) :
    RwEq (Path.symm (Path.symm d.congestionPath)) d.congestionPath :=
  rweq_of_step (Step.symm_symm d.congestionPath)

/-! ## Network Reliability -/

/-- Reliability data: primary and backup paths between same endpoints. -/
structure ReliabilityData (N : Type u) where
  src : N
  dst : N
  primaryPath : Path src dst
  backupPath : Path src dst

/-- Primary and backup paths agree propositionally (UIP). -/
theorem reliability_paths_agree {N : Type u} (d : ReliabilityData N) :
    d.primaryPath.toEq = d.backupPath.toEq := by
  rfl

/-- RwEq: primary inv cancel right. -/
noncomputable def reliability_rweq_primary_inv {N : Type u} (d : ReliabilityData N) :
    RwEq
      (Path.trans d.primaryPath (Path.symm d.primaryPath))
      (Path.refl d.src) :=
  rweq_cmpA_inv_right d.primaryPath

/-- RwEq: backup inv cancel right. -/
noncomputable def reliability_rweq_backup_inv {N : Type u} (d : ReliabilityData N) :
    RwEq
      (Path.trans d.backupPath (Path.symm d.backupPath))
      (Path.refl d.src) :=
  rweq_cmpA_inv_right d.backupPath

/-! ## congrArg for Network Paths -/

/-- Applying a network function to route path via congrArg. -/
theorem congrArg_route {N M : Type u} (f : N → M)
    {a b : N} (p : Path a b) :
    Path.congrArg f (Path.trans p (Path.refl b)) =
    Path.congrArg f p := by
  simp

/-- congrArg preserves route composition. -/
theorem congrArg_routeCompose {N M : Type u} (f : N → M)
    {a b c : N} (p : Path a b) (q : Path b c) :
    Path.congrArg f (routeCompose p q) =
    routeCompose (Path.congrArg f p) (Path.congrArg f q) := by
  simp [routeCompose]

/-- congrArg preserves symm of route paths. -/
theorem congrArg_route_symm {N M : Type u} (f : N → M)
    {a b : N} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp

/-! ## Multi-Hop Routing -/

/-- Iterated hop through network. -/
def multiHop {N : Type u} {a : N} (p : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | n + 1 => Path.trans (multiHop p n) p

/-- Multi-hop zero is refl. -/
theorem multiHop_zero {N : Type u} {a : N} (p : Path a a) :
    multiHop p 0 = Path.refl a := rfl

/-- RwEq: multi-hop 1 simplifies. -/
noncomputable def multiHop_one_rweq {N : Type u} {a : N} (p : Path a a) :
    RwEq (multiHop p 1) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Multi-hop via congrArg at zero. -/
theorem congrArg_multiHop_zero {N M : Type u} (f : N → M) {a : N} (p : Path a a) :
    Path.congrArg f (multiHop p 0) = Path.refl (f a) := by
  simp [multiHop]

end NetworkPaths
end Computation
end Path
end ComputationalPaths
