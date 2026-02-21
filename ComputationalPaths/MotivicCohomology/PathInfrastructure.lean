/- 
# Motivic cohomology path infrastructure

This module combines motivic-complex and cycle-map path packages into a single
infrastructure layer with explicit `Path.Step` normalization witnesses.
-/

import ComputationalPaths.MotivicCohomology.MotivicComplexPaths
import ComputationalPaths.MotivicCohomology.CycleMapPaths

namespace ComputationalPaths
namespace MotivicCohomology

open Path

universe u v

/-- Unified path infrastructure for motivic complexes and cycle maps. -/
structure MotivicCohomologyPathInfrastructure
    (X : Type u) (H : Int → Type v) where
  complex : MotivicComplexPathData X
  cycleMap : CycleMapPathData complex H
  /-- Compatibility witness after mapping a zero cycle and applying target `d`. -/
  zeroDifferentialPath :
    ∀ n : Int,
      Path (cycleMap.cohDifferential n (cycleMap.cycleClass n (complex.zero n)))
           (cycleMap.cohDifferential n (cycleMap.cohZero n))
  /-- Primitive rewrite witness for `zeroDifferentialPath`. -/
  zeroDifferentialStep :
    ∀ n : Int,
      Path.Step
        (Path.trans (zeroDifferentialPath n)
          (Path.refl (cycleMap.cohDifferential n (cycleMap.cohZero n))))
        (zeroDifferentialPath n)

namespace MotivicCohomologyPathInfrastructure

variable {X : Type u} {H : Int → Type v}
variable (I : MotivicCohomologyPathInfrastructure X H)

noncomputable def zeroDifferential_rweq (n : Int) :
    RwEq
      (Path.trans (I.zeroDifferentialPath n)
        (Path.refl (I.cycleMap.cohDifferential n (I.cycleMap.cohZero n))))
      (I.zeroDifferentialPath n) :=
  rweq_of_step (I.zeroDifferentialStep n)

noncomputable def zeroDifferential_cancel_left_rweq (n : Int) :
    RwEq
      (Path.trans (Path.symm (I.zeroDifferentialPath n)) (I.zeroDifferentialPath n))
      (Path.refl (I.cycleMap.cohDifferential n (I.cycleMap.cohZero n))) :=
  rweq_cmpA_inv_left (I.zeroDifferentialPath n)

/-- Trivial motivic cohomology infrastructure on `PUnit`. -/
def trivial (X : Type u) (x0 : X) :
    MotivicCohomologyPathInfrastructure X (fun _ => PUnit) where
  complex := MotivicComplexPathData.trivial X x0
  cycleMap := CycleMapPathData.constant (C := MotivicComplexPathData.trivial X x0)
    (H := fun _ => PUnit) (hzero := fun _ => PUnit.unit)
  zeroDifferentialPath := fun _ => Path.refl PUnit.unit
  zeroDifferentialStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end MotivicCohomologyPathInfrastructure

end MotivicCohomology
end ComputationalPaths
