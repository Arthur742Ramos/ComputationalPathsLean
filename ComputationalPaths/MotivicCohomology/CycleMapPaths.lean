/- 
# Motivic cohomology paths: cycle maps

This module records cycle-class map data from motivic complexes to target
cohomology theories, with explicit `Path.Step` rewrite infrastructure.
-/

import ComputationalPaths.MotivicCohomology.MotivicComplexPaths

namespace ComputationalPaths
namespace MotivicCohomology

open Path

universe u v

/-- Path package for a cycle map out of a motivic complex. -/
structure CycleMapPathData
    {X : Type u}
    (C : MotivicComplexPathData X)
    (H : Int → Type v) where
  /-- Zero class in target cohomology. -/
  cohZero : (n : Int) → H n
  /-- Target differential. -/
  cohDifferential : (n : Int) → H n → H (n + 1)
  /-- Cycle class map in each degree. -/
  cycleClass : (n : Int) → C.term n → H n
  /-- Chain-map compatibility witness. -/
  cycleMapPath :
    ∀ (n : Int) (x : C.term n),
      Path (cycleClass (n + 1) (C.differential n x))
           (cohDifferential n (cycleClass n x))
  /-- Primitive rewrite witness for chain-map compatibility. -/
  cycleMapStep :
    ∀ (n : Int) (x : C.term n),
      Path.Step
        (Path.trans (cycleMapPath n x)
          (Path.refl (cohDifferential n (cycleClass n x))))
        (cycleMapPath n x)
  /-- Zero-cycle compatibility witness. -/
  zeroMapPath :
    ∀ n : Int, Path (cycleClass n (C.zero n)) (cohZero n)
  /-- Primitive rewrite witness for `zeroMapPath`. -/
  zeroMapStep :
    ∀ n : Int,
      Path.Step
        (Path.trans (Path.refl (cycleClass n (C.zero n))) (zeroMapPath n))
        (zeroMapPath n)

namespace CycleMapPathData

variable {X : Type u} {H : Int → Type v}
variable {C : MotivicComplexPathData X} (M : CycleMapPathData C H)

noncomputable def cycleMap_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (M.cycleMapPath n x)
        (Path.refl (M.cohDifferential n (M.cycleClass n x))))
      (M.cycleMapPath n x) :=
  rweq_of_step (M.cycleMapStep n x)

noncomputable def zeroMap_rweq (n : Int) :
    RwEq
      (Path.trans (Path.refl (M.cycleClass n (C.zero n))) (M.zeroMapPath n))
      (M.zeroMapPath n) :=
  rweq_of_step (M.zeroMapStep n)

noncomputable def cycleMap_cancel_left_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (Path.symm (M.cycleMapPath n x)) (M.cycleMapPath n x))
      (Path.refl (M.cohDifferential n (M.cycleClass n x))) :=
  rweq_cmpA_inv_left (M.cycleMapPath n x)

noncomputable def cycleMap_cancel_right_rweq (n : Int) (x : C.term n) :
    RwEq
      (Path.trans (M.cycleMapPath n x) (Path.symm (M.cycleMapPath n x)))
      (Path.refl (M.cycleClass (n + 1) (C.differential n x))) :=
  rweq_cmpA_inv_right (M.cycleMapPath n x)

/-- Constant cycle map package sending everything to chosen zero classes. -/
def constant
    {X : Type u}
    (C : MotivicComplexPathData X)
    (H : Int → Type v)
    (hzero : ∀ n : Int, H n) :
    CycleMapPathData C H where
  cohZero := hzero
  cohDifferential := fun n _ => hzero (n + 1)
  cycleClass := fun n _ => hzero n
  cycleMapPath := fun n _ => Path.refl (hzero (n + 1))
  cycleMapStep := fun n _ => Path.Step.trans_refl_right (Path.refl (hzero (n + 1)))
  zeroMapPath := fun n => Path.refl (hzero n)
  zeroMapStep := fun n => Path.Step.trans_refl_left (Path.refl (hzero n))

end CycleMapPathData

end MotivicCohomology
end ComputationalPaths
