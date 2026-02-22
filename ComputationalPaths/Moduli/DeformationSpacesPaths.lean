import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Moduli deformation spaces with computational paths

This module encodes deformation-space specialization as explicit computational
paths, with primitive rewrite steps and induced `RwEq` normalization lemmas.
-/

namespace ComputationalPaths
namespace Moduli

open Path

universe u

/-- Deformation-space data with explicit paths between nearby fibers. -/
structure DeformationSpacePathData (X : Type u) where
  /-- Formal family of fibers indexed by a chart parameter. -/
  fiber : Nat → X
  /-- Distinguished special fiber. -/
  specialFiber : X
  /-- Specialization from parameter `0` to the special fiber. -/
  specialize : Path (fiber 0) specialFiber
  /-- One-step transition in the formal parameter direction. -/
  transition : ∀ n : Nat, Path (fiber (n + 1)) (fiber n)
  /-- Functorial transport along parameter paths. -/
  transport : ∀ {n m : Nat}, Path n m → Path (fiber n) (fiber m)

namespace DeformationSpacePathData

variable {X : Type u} (D : DeformationSpacePathData X)

/-- Iterated specialization from the `n`-th fiber to the special fiber. -/
def specializeFrom : (n : Nat) → Path (D.fiber n) D.specialFiber
  | 0 => D.specialize
  | n + 1 => Path.trans (D.transition n) (specializeFrom n)

/-- Closed loop induced by specializing and returning along the inverse path. -/
def specializeLoop (n : Nat) : Path (D.fiber (n + 1)) (D.fiber (n + 1)) :=
  Path.trans (D.specializeFrom (n + 1)) (Path.symm (D.specializeFrom (n + 1)))

/-- Primitive normalization steps for deformation-space path expressions. -/
inductive DeformationSpaceStep : {a b : X} → Path a b → Path a b → Type u
  | contract_right {a b : X} (p : Path a b) :
      DeformationSpaceStep (Path.trans p (Path.refl b)) p
  | contract_left {a b : X} (p : Path a b) :
      DeformationSpaceStep (Path.trans (Path.refl a) p) p

/-- Deformation-space primitive steps induce global rewrite equivalences. -/
noncomputable def DeformationSpaceStep.to_rweq {a b : X} {p q : Path a b}
    (h : DeformationSpaceStep p q) : RwEq p q := by
  cases h
  · exact rweq_of_step (Path.Step.trans_refl_right _)
  · exact rweq_of_step (Path.Step.trans_refl_left _)

noncomputable def specializeFrom_refl_right_rweq (n : Nat) :
    RwEq
      (Path.trans (D.specializeFrom n) (Path.refl D.specialFiber))
      (D.specializeFrom n) :=
  rweq_of_step (Path.Step.trans_refl_right (D.specializeFrom n))

noncomputable def specializeFrom_cancel_left (n : Nat) :
    RwEq
      (Path.trans (Path.symm (D.specializeFrom n)) (D.specializeFrom n))
      (Path.refl D.specialFiber) :=
  rweq_cmpA_inv_left (D.specializeFrom n)

noncomputable def specializeLoop_contract (n : Nat) :
    RwEq (D.specializeLoop n) (Path.refl (D.fiber (n + 1))) :=
  rweq_cmpA_inv_right (D.specializeFrom (n + 1))

/-- A section through the deformation family with explicit path lifts. -/
structure Section where
  value : Nat → X
  lift : ∀ n : Nat, Path (value n) (D.fiber n)

namespace Section

/-- Specialization of a section at parameter `0`. -/
def specializeAtZero (s : D.Section) : Path (s.value 0) D.specialFiber :=
  Path.trans (s.lift 0) D.specialize

noncomputable def specializeAtZero_refl_right_rweq (s : D.Section) :
    RwEq
      (Path.trans (specializeAtZero D s) (Path.refl D.specialFiber))
      (specializeAtZero D s) :=
  rweq_of_step (Path.Step.trans_refl_right (specializeAtZero D s))

noncomputable def specializeAtZero_cancel_left (s : D.Section) :
    RwEq
      (Path.trans (Path.symm (specializeAtZero D s)) (specializeAtZero D s))
      (Path.refl D.specialFiber) :=
  rweq_cmpA_inv_left (specializeAtZero D s)

end Section

end DeformationSpacePathData

/-- Constant deformation-space model on `Nat`. -/
def constantNatDeformation : DeformationSpacePathData Nat where
  fiber := fun _ => 0
  specialFiber := 0
  specialize := Path.refl 0
  transition := fun _ => Path.refl 0
  transport := fun {_ _} _ => Path.refl 0

end Moduli
end ComputationalPaths
