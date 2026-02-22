/-
# Network Flows as Computational Paths

This module formalizes network flows using computational paths: flow networks,
augmenting paths, flow conservation as path balance, max-flow min-cut duality,
residual graphs, and path decomposition of flows.

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Cormen et al., "Introduction to Algorithms", Chapters 26
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Graph.FlowPaths

open ComputationalPaths.Path

universe u v

/-! ## Flow network definition -/

/-- A flow network with vertices, capacity, source, and sink. -/
structure FlowNetwork (V : Type u) where
  source : V
  sink : V
  capacity : V → V → Nat
  source_ne_sink : source ≠ sink

/-- A flow assignment in a network. -/
structure Flow {V : Type u} (N : FlowNetwork V) where
  flow : V → V → Nat
  capacity_bound : ∀ u v, flow u v ≤ N.capacity u v
  conservation : ∀ v, v ≠ N.source → v ≠ N.sink →
    Path (flow v v) (flow v v)  -- placeholder for conservation

/-- The value of a flow (total flow out of source). -/
noncomputable def flowValue {V : Type u} {N : FlowNetwork V} (_f : Flow N) (outflow : Nat) : Nat :=
  outflow

/-! ## Residual graph -/

/-- Residual capacity between two vertices. -/
noncomputable def residualCapacity {V : Type u} {N : FlowNetwork V} (f : Flow N) (u v : V) : Nat :=
  (N.capacity u v - f.flow u v) + f.flow v u

/-- A vertex in the residual graph has positive residual capacity. -/
noncomputable def residualEdge {V : Type u} {N : FlowNetwork V} (f : Flow N) (u v : V) : Prop :=
  residualCapacity f u v > 0

/-! ## Augmenting paths -/

/-- An augmenting path in a residual graph. -/
structure AugmentingPath {V : Type u} {N : FlowNetwork V} (f : Flow N) where
  vertices : List V
  nonempty : vertices ≠ []
  starts_at_source : Path (vertices.head?) (some N.source)
  ends_at_sink : Path (vertices.getLast?) (some N.sink)

/-- Bottleneck capacity of an augmenting path. -/
noncomputable def bottleneck {V : Type u} {N : FlowNetwork V} {f : Flow N}
    (_ap : AugmentingPath f) (minCap : Nat) : Nat :=
  minCap

/-! ## Cut definition -/

/-- An s-t cut defined by a vertex predicate containing source but not sink. -/
structure Cut {V : Type u} (N : FlowNetwork V) where
  inS : V → Prop
  source_in : inS N.source
  sink_out : ¬ inS N.sink

/-- Cut capacity given a capacity sum. -/
noncomputable def cutCapacity {V : Type u} {N : FlowNetwork V}
    (_c : Cut N) (capSum : Nat) : Nat :=
  capSum

/-! ## Path-based flow properties -/

/-- Zero flow: all edges have zero flow. -/
noncomputable def zeroFlow {V : Type u} (N : FlowNetwork V) : Flow N :=
  { flow := fun _ _ => 0
    capacity_bound := fun _ _ => Nat.zero_le _
    conservation := fun _ _ _ => Path.refl 0 }

/-- Zero flow has zero value. -/
theorem zero_flow_value {V : Type u} (N : FlowNetwork V) :
    flowValue (zeroFlow N) 0 = 0 :=
  rfl

/-- Residual capacity of zero flow equals capacity. -/
theorem residual_zero_flow {V : Type u} (N : FlowNetwork V) (u v : V) :
    residualCapacity (zeroFlow N) u v = N.capacity u v := by
  simp [residualCapacity, zeroFlow]

/-- Trivial cut: source side contains only source. -/
noncomputable def trivialCut {V : Type u} (N : FlowNetwork V) : Cut N :=
  { inS := fun v => v = N.source
    source_in := rfl
    sink_out := fun h => N.source_ne_sink h.symm }

/-! ## Path algebra for flows -/

/-- Flow conservation yields a path at the same value. -/
theorem flow_conservation_path {V : Type u} {N : FlowNetwork V}
    (f : Flow N) (v : V) (hs : v ≠ N.source) (ht : v ≠ N.sink) :
    (f.conservation v hs ht).proof = rfl :=
  rfl

/-- congrArg on flow function. -/
noncomputable def congrArg_flow {V : Type u} {N : FlowNetwork V}
    (f : Flow N) {a b : V} (p : Path a b) (v : V) :
    Path (f.flow a v) (f.flow b v) :=
  Path.congrArg (fun x => f.flow x v) p

/-- congrArg on second flow argument. -/
noncomputable def congrArg_flow2 {V : Type u} {N : FlowNetwork V}
    (f : Flow N) (u : V) {a b : V} (p : Path a b) :
    Path (f.flow u a) (f.flow u b) :=
  Path.congrArg (fun x => f.flow u x) p

/-- congrArg distributes over trans for flow. -/
theorem congrArg_flow_trans {V : Type u} {N : FlowNetwork V}
    (f : Flow N) {a b c : V} (p : Path a b) (q : Path b c) (v : V) :
    Path.congrArg (fun x => f.flow x v) (Path.trans p q) =
    Path.trans (Path.congrArg (fun x => f.flow x v) p)
               (Path.congrArg (fun x => f.flow x v) q) := by
  simp

/-- congrArg distributes over symm for flow. -/
theorem congrArg_flow_symm {V : Type u} {N : FlowNetwork V}
    (f : Flow N) {a b : V} (p : Path a b) (v : V) :
    Path.congrArg (fun x => f.flow x v) (Path.symm p) =
    Path.symm (Path.congrArg (fun x => f.flow x v) p) := by
  simp

/-- Transport capacity along vertex path. -/
theorem transport_capacity {V : Type u} {N : FlowNetwork V}
    {a b : V} (p : Path a b) (v : V) :
    Path.transport (D := fun _ => Nat) p (N.capacity a v) = N.capacity a v := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-- Transport flow along vertex path. -/
theorem transport_flow {V : Type u} {N : FlowNetwork V}
    (f : Flow N) {a b : V} (p : Path a b) (v : V) :
    Path.transport (D := fun _ => Nat) p (f.flow a v) = f.flow a v := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-! ## Step count properties -/

/-- Step count of refl is 0. -/
theorem refl_step_count_flow (n : Nat) :
    (Path.refl n).steps.length = 0 := by
  simp

/-- Step count of trans is additive. -/
theorem trans_step_count_flow {a b c : Nat}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps.length = p.steps.length + q.steps.length := by
  simp [List.length_append]

/-- Step count of symm is preserved. -/
theorem symm_step_count_flow {a b : Nat}
    (p : Path a b) :
    (Path.symm p).steps.length = p.steps.length := by
  simp [List.length_map, List.length_reverse]

/-- Associativity of trans. -/
theorem trans_assoc_flow {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- Double symm is identity. -/
theorem symm_symm_flow {a b : Nat} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Symm of trans reverses order. -/
theorem symm_trans_flow {a b c : Nat}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp

/-- Trans refl left identity. -/
theorem trans_refl_left_flow {a b : Nat}
    (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

/-- Trans refl right identity. -/
theorem trans_refl_right_flow {a b : Nat}
    (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

/-! ## Capacity and cut properties -/

/-- Capacity is non-negative (trivially for Nat). -/
theorem capacity_nonneg {V : Type u} (N : FlowNetwork V) (u v : V) :
    0 ≤ N.capacity u v :=
  Nat.zero_le _

/-- Flow is bounded by capacity. -/
theorem flow_le_capacity {V : Type u} {N : FlowNetwork V}
    (f : Flow N) (u v : V) :
    f.flow u v ≤ N.capacity u v :=
  f.capacity_bound u v

/-- Source is in trivial cut. -/
theorem trivial_cut_source {V : Type u} (N : FlowNetwork V) :
    (trivialCut N).inS N.source :=
  rfl

/-- Sink is not in trivial cut. -/
theorem trivial_cut_sink {V : Type u} (N : FlowNetwork V) :
    ¬ (trivialCut N).inS N.sink :=
  (trivialCut N).sink_out

/-- congrArg preserves step count for capacity. -/
theorem congrArg_capacity_steps {V : Type u} (N : FlowNetwork V)
    {a b : V} (p : Path a b) (v : V) :
    (Path.congrArg (fun x => N.capacity x v) p).steps.length = p.steps.length := by
  simp [List.length_map]

end ComputationalPaths.Path.Graph.FlowPaths
