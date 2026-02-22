/- 
# Intersection theory paths: Chow rings

This module packages Chow-ring operations with explicit `Path.Step` witnesses and
derived `RwEq` coherence lemmas for intersection products.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Intersection

open Path

universe u

/-- Chow-ring data with path-level witnesses for additive and multiplicative structure. -/
structure ChowRingPathData (R : Type u) where
  zero : R
  add : R → R → R
  mul : R → R → R
  grade : R → Nat
  addCommPath :
    ∀ x y : R,
      Path (add x y) (add y x)
  addCommStep :
    ∀ x y : R,
      Path.Step
        (Path.trans (addCommPath x y) (Path.refl (add y x)))
        (addCommPath x y)
  mulAssocPath :
    ∀ x y z : R,
      Path (mul (mul x y) z) (mul x (mul y z))
  mulAssocStep :
    ∀ x y z : R,
      Path.Step
        (Path.trans (Path.refl (mul (mul x y) z)) (mulAssocPath x y z))
        (mulAssocPath x y z)
  gradeAddPath :
    ∀ x y : R,
      Path (grade (add x y)) (grade (add y x))
  gradeAddStep :
    ∀ x y : R,
      Path.Step
        (Path.trans (gradeAddPath x y) (Path.refl (grade (add y x))))
        (gradeAddPath x y)
  intersectCommPath :
    ∀ x y : R,
      Path (mul x y) (mul y x)
  intersectCommStep :
    ∀ x y : R,
      Path.Step
        (Path.trans (Path.refl (mul x y)) (intersectCommPath x y))
        (intersectCommPath x y)

namespace ChowRingPathData

variable {R : Type u} (C : ChowRingPathData R)

noncomputable def add_comm_rweq (x y : R) :
    RwEq
      (Path.trans (C.addCommPath x y) (Path.refl (C.add y x)))
      (C.addCommPath x y) :=
  rweq_of_step (C.addCommStep x y)

noncomputable def mul_assoc_rweq (x y z : R) :
    RwEq
      (Path.trans (Path.refl (C.mul (C.mul x y) z)) (C.mulAssocPath x y z))
      (C.mulAssocPath x y z) :=
  rweq_of_step (C.mulAssocStep x y z)

noncomputable def grade_add_rweq (x y : R) :
    RwEq
      (Path.trans (C.gradeAddPath x y) (Path.refl (C.grade (C.add y x))))
      (C.gradeAddPath x y) :=
  rweq_of_step (C.gradeAddStep x y)

noncomputable def intersect_comm_rweq (x y : R) :
    RwEq
      (Path.trans (Path.refl (C.mul x y)) (C.intersectCommPath x y))
      (C.intersectCommPath x y) :=
  rweq_of_step (C.intersectCommStep x y)

noncomputable def intersect_comm_cancel_rweq (x y : R) :
    RwEq
      (Path.trans (Path.symm (C.intersectCommPath x y)) (C.intersectCommPath x y))
      (Path.refl (C.mul y x)) :=
  rweq_cmpA_inv_left (C.intersectCommPath x y)

end ChowRingPathData

/-- Trivial Chow-ring path package on `Nat`. -/
noncomputable def trivialChowRingPathData : ChowRingPathData Nat where
  zero := 0
  add := Nat.add
  mul := Nat.mul
  grade := fun _ => 0
  addCommPath := fun x y => Path.stepChain (Nat.add_comm x y)
  addCommStep := fun x y => Path.Step.trans_refl_right (Path.stepChain (Nat.add_comm x y))
  mulAssocPath := fun x y z => Path.stepChain (Nat.mul_assoc x y z)
  mulAssocStep := fun x y z => Path.Step.trans_refl_left (Path.stepChain (Nat.mul_assoc x y z))
  gradeAddPath := fun _ _ => Path.refl 0
  gradeAddStep := fun _ _ => Path.Step.trans_refl_right (Path.refl 0)
  intersectCommPath := fun x y => Path.stepChain (Nat.mul_comm x y)
  intersectCommStep := fun x y => Path.Step.trans_refl_left (Path.stepChain (Nat.mul_comm x y))

end Intersection
end ComputationalPaths
