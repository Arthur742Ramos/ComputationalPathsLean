import ComputationalPaths.Path.Rewrite.RwEq
import Moduli.DeformationSpacesPaths

/-!
# Virtual fundamental classes with computational paths

This module models virtual fundamental classes as path-functorial assignments and
proves deformation-invariance normalization lemmas via `RwEq`.
-/

namespace ComputationalPaths
namespace Moduli

open Path

universe u v

/-- Path-level virtual fundamental class package. -/
structure VirtualFundamentalClassPathData (X : Type u) (V : Type v) where
  /-- Assignment sending a moduli point to its virtual class representative. -/
  classOf : X → V
  /-- Expected dimension associated to each moduli point. -/
  expectedDim : X → Int
  /-- Obstruction rank associated to each moduli point. -/
  obstructionRank : X → Nat
  /-- Functoriality of class assignment along computational paths. -/
  mapClass : ∀ {x y : X}, Path x y → Path (classOf x) (classOf y)
  /-- Functoriality of expected dimension along computational paths. -/
  mapDim : ∀ {x y : X}, Path x y → Path (expectedDim x) (expectedDim y)
  /-- Functoriality of obstruction rank along computational paths. -/
  mapRank : ∀ {x y : X}, Path x y → Path (obstructionRank x) (obstructionRank y)

/-- Primitive normalization steps for virtual-class path witnesses. -/
inductive VirtualFundamentalClassStep {V : Type v} :
    {a b : V} → Path a b → Path a b → Prop
  | contract_right {a b : V} (p : Path a b) :
      VirtualFundamentalClassStep (Path.trans p (Path.refl b)) p
  | contract_left {a b : V} (p : Path a b) :
      VirtualFundamentalClassStep (Path.trans (Path.refl a) p) p

/-- Primitive virtual-class steps induce `RwEq`. -/
theorem VirtualFundamentalClassStep.to_rweq {V : Type v} {a b : V} {p q : Path a b}
    (h : VirtualFundamentalClassStep p q) : RwEq p q := by
  cases h
  · exact rweq_of_step (Path.Step.trans_refl_right _)
  · exact rweq_of_step (Path.Step.trans_refl_left _)

namespace VirtualFundamentalClassPathData

variable {X : Type u} {V : Type v} (C : VirtualFundamentalClassPathData X V)

/-- Deformation invariance of virtual classes along specialization paths. -/
def deformationInvariantClass
    (D : DeformationSpacePathData X) (n : Nat) :
    Path (C.classOf (D.fiber n)) (C.classOf D.specialFiber) :=
  C.mapClass (D.specializeFrom n)

/-- Deformation invariance of expected dimensions along specialization paths. -/
def deformationInvariantDim
    (D : DeformationSpacePathData X) (n : Nat) :
    Path (C.expectedDim (D.fiber n)) (C.expectedDim D.specialFiber) :=
  C.mapDim (D.specializeFrom n)

/-- Deformation invariance of obstruction ranks along specialization paths. -/
def deformationInvariantRank
    (D : DeformationSpacePathData X) (n : Nat) :
    Path (C.obstructionRank (D.fiber n)) (C.obstructionRank D.specialFiber) :=
  C.mapRank (D.specializeFrom n)

@[simp] theorem deformationInvariantClass_refl_right_rweq
    (D : DeformationSpacePathData X) (n : Nat) :
    RwEq
      (Path.trans
        (C.deformationInvariantClass D n)
        (Path.refl (C.classOf D.specialFiber)))
      (C.deformationInvariantClass D n) :=
  rweq_of_step (Path.Step.trans_refl_right (C.deformationInvariantClass D n))

@[simp] theorem deformationInvariantClass_cancel_left
    (D : DeformationSpacePathData X) (n : Nat) :
    RwEq
      (Path.trans
        (Path.symm (C.deformationInvariantClass D n))
        (C.deformationInvariantClass D n))
      (Path.refl (C.classOf D.specialFiber)) :=
  rweq_cmpA_inv_left (C.deformationInvariantClass D n)

@[simp] theorem deformationInvariantDim_refl_right_rweq
    (D : DeformationSpacePathData X) (n : Nat) :
    RwEq
      (Path.trans
        (C.deformationInvariantDim D n)
        (Path.refl (C.expectedDim D.specialFiber)))
      (C.deformationInvariantDim D n) :=
  rweq_of_step (Path.Step.trans_refl_right (C.deformationInvariantDim D n))

@[simp] theorem deformationInvariantRank_refl_left_rweq
    (D : DeformationSpacePathData X) (n : Nat) :
    RwEq
      (Path.trans
        (Path.refl (C.obstructionRank (D.fiber n)))
        (C.deformationInvariantRank D n))
      (C.deformationInvariantRank D n) :=
  rweq_of_step (Path.Step.trans_refl_left (C.deformationInvariantRank D n))

end VirtualFundamentalClassPathData

/-- Trivial virtual class package on natural numbers. -/
def trivialNatVirtualClass : VirtualFundamentalClassPathData Nat Nat where
  classOf := fun x => x
  expectedDim := fun _ => 0
  obstructionRank := fun x => x
  mapClass := fun {x y} p => p
  mapDim := fun {_ _} _ => Path.refl 0
  mapRank := fun {x y} p => p

end Moduli
end ComputationalPaths
