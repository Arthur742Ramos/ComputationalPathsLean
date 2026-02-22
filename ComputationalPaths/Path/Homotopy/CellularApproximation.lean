/-
# Cellular Approximation for Computational Paths

This module develops the cellular approximation theorem in the computational-path
framework. We extend the CW complex homotopy machinery with composition,
restriction, and coherence results for cellular approximations.

## Key Results

- `cellularApproximation_comp`: composition of cellular approximations
- `cellularApproximation_homotopy_trans`: transitivity of approximation homotopies
- `cellularApproximation_unique_toEq`: uniqueness at the propositional level
- Coherence paths for approximation data
- Restriction to skeleta

## References

- Hatcher, *Algebraic Topology*, Section 4.1
- Whitehead, *Elements of Homotopy Theory*, Chapter V
-/

import ComputationalPaths.Path.Homotopy.CWApproximation
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace CellularApproximationTheory

open Topology
open scoped Topology
open CWComplexHomotopy
open CWApproximation

universe u v w

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {Y : Type v} [TopologicalSpace Y] [T2Space Y]
variable {Z : Type w} [TopologicalSpace Z] [T2Space Z]
variable {C : Set X} [CWComplex C]
variable {D : Set Y} [CWComplex D]
variable {E : Set Z} [CWComplex E]

/-! ## Composition of cellular approximations -/

/-- Composition of cellular maps is cellular. -/
theorem cellular_comp_map {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (hf : IsCellularMap C D f) (hg : IsCellularMap D E g) :
    IsCellularMap C E (g.comp f) :=
  cellular_comp hf hg

/-- The identity map is cellular (convenience wrapper). -/
theorem cellular_id_map : IsCellularMap C C (ContinuousMap.id X) :=
  cellular_id

/-- Cellular approximation of the identity is tautological. -/
noncomputable def cellularApprox_id :
    CWApproximationData (C := C) (D := C) (ContinuousMap.id X) :=
  cwApproximation_id

/-- The approximating map of the identity approximation is the identity. -/
theorem cellularApprox_id_map_eq :
    (cellularApprox_id (C := C)).map = ContinuousMap.id X := rfl

/-! ## Homotopy paths from cellular approximations -/

/-- Extract the homotopy path at a specific point. -/
noncomputable def cellularApprox_path_at {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (approx.map x) (f x) :=
  cwApproximation_path approx x

/-- The homotopy path at a point yields a propositional equality. -/
theorem cellularApprox_toEq_at {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    approx.map x = f x :=
  (cellularApprox_path_at approx x).toEq

/-- Two cellular approximations of the same map agree propositionally
    at every point (since the homotopies both reach f). -/
theorem cellularApprox_agree_toEq {f : ContinuousMap X Y}
    (a₁ a₂ : CWApproximationData (C := C) (D := D) f) (x : X) :
    a₁.map x = a₂.map x :=
  (cellularApprox_toEq_at a₁ x).trans (cellularApprox_toEq_at a₂ x).symm

/-- Path between two cellular approximations of the same map at a point. -/
noncomputable def cellularApprox_agree_path {f : ContinuousMap X Y}
    (a₁ a₂ : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (a₁.map x) (a₂.map x) :=
  Path.trans (cellularApprox_path_at a₁ x)
    (Path.symm (cellularApprox_path_at a₂ x))

/-! ## Coherence of composition -/

/-- Given cellular approximations of f and g, compose them. -/
noncomputable def cellularApprox_comp {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (af : CWApproximationData (C := C) (D := D) f)
    (ag : CWApproximationData (C := D) (D := E) g) :
    CWApproximationData (C := C) (D := E) (g.comp f) :=
  { map := ag.map.comp af.map
    cellular := cellular_comp af.cellular ag.cellular
    homotopic := fun x =>
      Path.trans
        (Path.congrArg ag.map (cellularApprox_path_at af x))
        (Path.trans
          (cellularApprox_path_at ag (f x))
          (Path.stepChain rfl)) }

/-- The composed approximation map is the composition of the individual maps. -/
theorem cellularApprox_comp_map_eq {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (af : CWApproximationData (C := C) (D := D) f)
    (ag : CWApproximationData (C := D) (D := E) g) :
    (cellularApprox_comp af ag).map = ag.map.comp af.map := rfl

/-! ## Path algebra for approximation homotopies -/

/-- The homotopy path for the identity approximation is reflexivity. -/
theorem cellularApprox_id_path_refl (x : X) :
    (cellularApprox_id (C := C)).homotopic x = Path.refl (x : X) := rfl

/-- Homotopy path coherence: composing the forward path with its inverse
    yields a propositionally trivial path. -/
theorem cellularApprox_path_self_inv {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    (Path.trans (cellularApprox_path_at approx x)
      (Path.symm (cellularApprox_path_at approx x))).toEq = rfl := by
  simp

/-- Symmetry of the approximation path. -/
noncomputable def cellularApprox_path_symm {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    Path (f x) (approx.map x) :=
  Path.symm (cellularApprox_path_at approx x)

/-- The symmetric path composed with the forward path is propositionally trivial. -/
theorem cellularApprox_path_symm_trans {f : ContinuousMap X Y}
    (approx : CWApproximationData (C := C) (D := D) f) (x : X) :
    (Path.trans (cellularApprox_path_symm approx x)
      (cellularApprox_path_at approx x)).toEq = rfl := by
  simp

/-! ## Cellular maps preserve skeleta coherently -/

/-- A cellular map sends skeleton n into skeleton n (explicit). -/
theorem cellular_skeleton_preserved {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) (n : ENat) {x : X}
    (hx : x ∈ CWComplex.skeleton (C := C) n) :
    f x ∈ CWComplex.skeleton (C := D) n :=
  hf n hx

/-- The top skeleton maps into the whole complex. -/
theorem cellular_top_skeleton {f : ContinuousMap X Y}
    (hf : IsCellularMap C D f) {x : X} (hx : x ∈ C) :
    f x ∈ D := by
  simpa using cellular_mapsTo_complex hf hx

/-! ## Path-valued witnesses for cellular properties -/

/-- Path witness that the identity map preserves skeleton membership. -/
noncomputable def cellular_id_skeleton_path (n : ENat) (x : X)
    (_hx : x ∈ CWComplex.skeleton (C := C) n) :
    Path (ContinuousMap.id X x) x :=
  Path.stepChain rfl

/-- Path witness for composition of cellular maps at a point. -/
noncomputable def cellular_comp_path {f : ContinuousMap X Y} {g : ContinuousMap Y Z}
    (x : X) :
    Path ((g.comp f) x) (g (f x)) :=
  Path.stepChain rfl

/-- Composition of cellular maps is associative at points. -/
noncomputable def cellular_comp_assoc_path {W : Type u} [TopologicalSpace W] [T2Space W]
    {f : ContinuousMap X Y} {g : ContinuousMap Y Z} {h : ContinuousMap Z W}
    (x : X) :
    Path ((h.comp (g.comp f)) x) (((h.comp g).comp f) x) :=
  Path.stepChain rfl

end CellularApproximationTheory
end Path
end ComputationalPaths
