/- 
# Intersection theory paths: cycle classes

This module packages cycle-class maps into Chow rings with explicit `Path.Step`
witnesses for rational equivalence and intersection compatibility.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Intersection.ChowRingsPaths

namespace ComputationalPaths
namespace Intersection

open Path

universe u v

/-- Cycle-class data valued in a Chow ring, with explicit step witnesses. -/
structure CycleClassPathData (Cycle : Type u) (R : Type v)
    (C : ChowRingPathData R) where
  cycleClass : Cycle → R
  rationalEq : Cycle → Cycle → Prop
  rationalEqPath :
    {z z' : Cycle} →
      rationalEq z z' →
      Path (cycleClass z) (cycleClass z')
  rationalEqStep :
    {z z' : Cycle} →
      (h : rationalEq z z') →
      Path.Step
        (Path.trans (rationalEqPath h) (Path.refl (cycleClass z')))
        (rationalEqPath h)
  addCycle : Cycle → Cycle → Cycle
  addClassPath :
    ∀ z w : Cycle,
      Path (cycleClass (addCycle z w)) (C.add (cycleClass z) (cycleClass w))
  addClassStep :
    ∀ z w : Cycle,
      Path.Step
        (Path.trans (Path.refl (cycleClass (addCycle z w))) (addClassPath z w))
        (addClassPath z w)
  intersectCycle : Cycle → Cycle → Cycle
  intersectionClassPath :
    ∀ z w : Cycle,
      Path (cycleClass (intersectCycle z w)) (C.mul (cycleClass z) (cycleClass w))
  intersectionClassStep :
    ∀ z w : Cycle,
      Path.Step
        (Path.trans (intersectionClassPath z w)
          (Path.refl (C.mul (cycleClass z) (cycleClass w))))
        (intersectionClassPath z w)

namespace CycleClassPathData

variable {Cycle : Type u} {R : Type v}
variable {C : ChowRingPathData R}
variable (D : CycleClassPathData Cycle R C)

@[simp] theorem rational_eq_rweq {z z' : Cycle} (h : D.rationalEq z z') :
    RwEq
      (Path.trans (D.rationalEqPath h) (Path.refl (D.cycleClass z')))
      (D.rationalEqPath h) :=
  rweq_of_step (D.rationalEqStep h)

@[simp] theorem add_class_rweq (z w : Cycle) :
    RwEq
      (Path.trans (Path.refl (D.cycleClass (D.addCycle z w))) (D.addClassPath z w))
      (D.addClassPath z w) :=
  rweq_of_step (D.addClassStep z w)

@[simp] theorem intersection_class_rweq (z w : Cycle) :
    RwEq
      (Path.trans (D.intersectionClassPath z w)
        (Path.refl (C.mul (D.cycleClass z) (D.cycleClass w))))
      (D.intersectionClassPath z w) :=
  rweq_of_step (D.intersectionClassStep z w)

@[simp] theorem intersection_class_cancel_rweq (z w : Cycle) :
    RwEq
      (Path.trans (Path.symm (D.intersectionClassPath z w)) (D.intersectionClassPath z w))
      (Path.refl (C.mul (D.cycleClass z) (D.cycleClass w))) :=
  rweq_cmpA_inv_left (D.intersectionClassPath z w)

end CycleClassPathData

/-- Trivial cycle-class package into the trivial Chow ring on `Nat`. -/
def trivialCycleClassPathData :
    CycleClassPathData Nat Nat trivialChowRingPathData where
  cycleClass := fun z => z
  rationalEq := fun z z' => z = z'
  rationalEqPath := fun h => Path.stepChain h
  rationalEqStep := fun h => Path.Step.trans_refl_right (Path.stepChain h)
  addCycle := Nat.add
  addClassPath := fun z w => Path.refl (z + w)
  addClassStep := fun z w => Path.Step.trans_refl_left (Path.refl (z + w))
  intersectCycle := Nat.mul
  intersectionClassPath := fun z w => Path.refl (z * w)
  intersectionClassStep := fun z w => Path.Step.trans_refl_right (Path.refl (z * w))

end Intersection
end ComputationalPaths
