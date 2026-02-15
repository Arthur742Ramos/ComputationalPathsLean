/- 
# Motivic cohomology paths: motivic complexes

This module packages motivic-complex data with explicit computational-path
witnesses and primitive `Path.Step` normalization infrastructure.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace MotivicCohomology

open Path

universe u

/-- Path package for a motivic complex over a base type `X`. -/
structure MotivicComplexPathData (X : Type u) where
  /-- Chosen base point of the underlying motivic space/scheme. -/
  base : X
  /-- Terms of the complex indexed cohomologically. -/
  term : Int → Type u
  /-- Zero cycle in each degree. -/
  zero : (n : Int) → term n
  /-- Addition on cycles in each degree. -/
  add : (n : Int) → term n → term n → term n
  /-- Differential `d_n : C^n → C^{n+1}`. -/
  differential : (n : Int) → term n → term (n + 1)
  /-- Right-unit normalization for addition. -/
  addZeroPath : ∀ (n : Int) (x : term n), Path (add n x (zero n)) x
  /-- Primitive rewrite witness for `addZeroPath`. -/
  addZeroStep :
    ∀ (n : Int) (x : term n),
      Path.Step
        (Path.trans (addZeroPath n x) (Path.refl x))
        (addZeroPath n x)
  /-- Chain condition witness `d ∘ d = 0`. -/
  dSquaredPath :
    ∀ (n : Int) (x : term n),
      Path (differential (n + 1) (differential n x)) (zero (n + 1 + 1))
  /-- Primitive rewrite witness for `dSquaredPath`. -/
  dSquaredStep :
    ∀ (n : Int) (x : term n),
      Path.Step
        (Path.trans (dSquaredPath n x) (Path.refl (zero (n + 1 + 1))))
        (dSquaredPath n x)

namespace MotivicComplexPathData

variable {X : Type u} (C : MotivicComplexPathData X)

@[simp] theorem addZero_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (C.addZeroPath n x) (Path.refl x))
      (C.addZeroPath n x) :=
  rweq_of_step (C.addZeroStep n x)

@[simp] theorem dSquared_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (C.dSquaredPath n x) (Path.refl (C.zero (n + 1 + 1))))
      (C.dSquaredPath n x) :=
  rweq_of_step (C.dSquaredStep n x)

@[simp] theorem dSquared_cancel_left_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (Path.symm (C.dSquaredPath n x)) (C.dSquaredPath n x))
      (Path.refl (C.zero (n + 1 + 1))) :=
  rweq_cmpA_inv_left (C.dSquaredPath n x)

@[simp] theorem dSquared_cancel_right_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (C.dSquaredPath n x) (Path.symm (C.dSquaredPath n x)))
      (Path.refl (C.differential (n + 1) (C.differential n x))) :=
  rweq_cmpA_inv_right (C.dSquaredPath n x)

/-- Canonical trivial motivic complex on `PUnit`. -/
def trivial (X : Type u) (x0 : X) : MotivicComplexPathData X where
  base := x0
  term := fun _ => PUnit
  zero := fun _ => PUnit.unit
  add := fun _ _ _ => PUnit.unit
  differential := fun _ _ => PUnit.unit
  addZeroPath := fun _ _ => Path.refl PUnit.unit
  addZeroStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  dSquaredPath := fun _ _ => Path.refl PUnit.unit
  dSquaredStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end MotivicComplexPathData

end MotivicCohomology
end ComputationalPaths
