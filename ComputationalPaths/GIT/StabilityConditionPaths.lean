import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Geometric invariant theory paths: stability conditions

This module packages GIT stability-condition style data with explicit
`Path.Step` witnesses for phase, semistability, and charge normalizations.
-/

namespace ComputationalPaths
namespace GIT
namespace StabilityConditionPaths

open Path

universe u

/-- Domain-specific rewrite tags for stability-condition coherence moves. -/
inductive StabilityConditionStep : Type
  | phaseShift
  | semistableShift
  | chargeNormalization
  | roundtrip

/-- Stability-condition package with computational-path witnesses. -/
structure StabilityConditionPathData (Obj : Type u) where
  shift : Obj → Int → Obj
  centralCharge : Obj → Int × Int
  phase : Obj → Int
  semistable : Obj → Prop
  phaseShiftPath :
    ∀ (E : Obj) (n : Int), Path (phase (shift E n)) (phase E)
  phaseShiftStep :
    ∀ (E : Obj) (n : Int),
      Path.Step
        (Path.trans (phaseShiftPath E n) (Path.refl (phase E)))
        (phaseShiftPath E n)
  semistableShiftPath :
    ∀ (E : Obj) (n : Int), Path (semistable (shift E n)) (semistable E)
  semistableShiftStep :
    ∀ (E : Obj) (n : Int),
      Path.Step
        (Path.trans
          (Path.refl (semistable (shift E n)))
          (semistableShiftPath E n))
        (semistableShiftPath E n)
  chargeShiftZeroPath :
    ∀ E : Obj, Path (centralCharge (shift E 0)) (centralCharge E)
  chargeShiftZeroStep :
    ∀ E : Obj,
      Path.Step
        (Path.trans (chargeShiftZeroPath E) (Path.refl (centralCharge E)))
        (chargeShiftZeroPath E)
  roundtripPath : ∀ E : Obj, Path (shift (shift E (1 : Int)) (-1)) E
  roundtripStep :
    ∀ E : Obj,
      Path.Step
        (Path.trans (roundtripPath E) (Path.refl E))
        (roundtripPath E)

namespace StabilityConditionPathData

variable {Obj : Type u} (S : StabilityConditionPathData Obj)

noncomputable def phase_shift_rweq (E : Obj) (n : Int) :
    RwEq
      (Path.trans (S.phaseShiftPath E n) (Path.refl (S.phase E)))
      (S.phaseShiftPath E n) :=
  rweq_of_step (S.phaseShiftStep E n)

noncomputable def semistable_shift_rweq (E : Obj) (n : Int) :
    RwEq
      (Path.trans
        (Path.refl (S.semistable (S.shift E n)))
        (S.semistableShiftPath E n))
      (S.semistableShiftPath E n) :=
  rweq_of_step (S.semistableShiftStep E n)

noncomputable def charge_shift_zero_rweq (E : Obj) :
    RwEq
      (Path.trans (S.chargeShiftZeroPath E) (Path.refl (S.centralCharge E)))
      (S.chargeShiftZeroPath E) :=
  rweq_of_step (S.chargeShiftZeroStep E)

noncomputable def roundtrip_rweq (E : Obj) :
    RwEq
      (Path.trans (S.roundtripPath E) (Path.refl E))
      (S.roundtripPath E) :=
  rweq_of_step (S.roundtripStep E)

/-- Roundtrip through a shift and inverse shift, then return via symmetry. -/
def phaseRoundtripPath (E : Obj) (n : Int) :
    Path (S.phase (S.shift E n)) (S.phase (S.shift E n)) :=
  Path.trans (S.phaseShiftPath E n) (Path.symm (S.phaseShiftPath E n))

noncomputable def phase_roundtrip_rweq (E : Obj) (n : Int) :
    RwEq
      (S.phaseRoundtripPath E n)
      (Path.refl (S.phase (S.shift E n))) :=
  rweq_cmpA_inv_right (S.phaseShiftPath E n)

noncomputable def roundtrip_cancel_rweq (E : Obj) :
    RwEq
      (Path.trans (Path.symm (S.roundtripPath E)) (S.roundtripPath E))
      (Path.refl E) :=
  rweq_cmpA_inv_left (S.roundtripPath E)

end StabilityConditionPathData

/-- Trivial stability-condition model with canonical Step witnesses. -/
def trivialStabilityConditionPathData : StabilityConditionPathData PUnit where
  shift := fun _ _ => PUnit.unit
  centralCharge := fun _ => (0, 0)
  phase := fun _ => 0
  semistable := fun _ => True
  phaseShiftPath := fun _ _ => Path.refl (0 : Int)
  phaseShiftStep := fun _ _ => Path.Step.trans_refl_right (Path.refl (0 : Int))
  semistableShiftPath := fun _ _ => Path.refl True
  semistableShiftStep := fun _ _ => Path.Step.trans_refl_left (Path.refl True)
  chargeShiftZeroPath := fun _ => Path.refl (0, 0)
  chargeShiftZeroStep := fun _ => Path.Step.trans_refl_right (Path.refl (0, 0))
  roundtripPath := fun _ => Path.refl PUnit.unit
  roundtripStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end StabilityConditionPaths
end GIT
end ComputationalPaths

