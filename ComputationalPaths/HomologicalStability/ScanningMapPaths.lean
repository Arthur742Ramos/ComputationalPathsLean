import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Homological stability paths: scanning maps

This module packages scanning-map coherence with explicit computational paths,
primitive `Path.Step` witnesses, and derived `RwEq` normalizations.
-/

namespace ComputationalPaths
namespace HomologicalStability
namespace ScanningMapPaths

open Path

universe u v

/-- Domain-specific rewrite steps for scanning-map coherence moves. -/
inductive ScanningStep {Y : Type v} :
    {a b : Y} → Path a b → Path a b → Prop where
  | right_unit {a b : Y} (p : Path a b) :
      ScanningStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : Y} (p : Path a b) :
      ScanningStep (Path.trans (Path.refl a) p) p
  | cancel {a b : Y} (p : Path a b) :
      ScanningStep (Path.trans (Path.symm p) p) (Path.refl b)

/-- Interpret scanning-specific steps as primitive path rewrite steps. -/
noncomputable def ScanningStep.toStep {Y : Type v} {a b : Y} {p q : Path a b}
    (s : ScanningStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .cancel p => Path.Step.symm_trans p

/-- Lift a domain-specific scanning step to rewrite equivalence. -/
noncomputable def rweq_of_scanning_step {Y : Type v} {a b : Y}
    {p q : Path a b} (s : ScanningStep p q) : RwEq p q :=
  rweq_of_step (ScanningStep.toStep s)

/-- Computational-path package for a scanning map in a stabilization sequence. -/
structure ScanningMapData (X : Type u) (Y : Type v) where
  sourceStabilize : X → X
  targetShift : Y → Y
  scan : X → Y
  commutationPath :
    ∀ x : X, Path (scan (sourceStabilize x)) (targetShift (scan x))
  commutationStep :
    ∀ x : X,
      ScanningStep
        (Path.trans (commutationPath x) (Path.refl (targetShift (scan x))))
        (commutationPath x)

namespace ScanningMapData

variable {X : Type u} {Y : Type v}
variable (S : ScanningMapData X Y)

noncomputable def commutation_rweq (x : X) :
    RwEq
      (Path.trans (S.commutationPath x) (Path.refl (S.targetShift (S.scan x))))
      (S.commutationPath x) :=
  rweq_of_scanning_step (S.commutationStep x)

/-- Left-unit normalization packaged as a domain-specific scanning step. -/
noncomputable def commutation_left_unit_step (x : X) :
    ScanningStep
      (Path.trans (Path.refl (S.scan (S.sourceStabilize x))) (S.commutationPath x))
      (S.commutationPath x) :=
  ScanningStep.left_unit (S.commutationPath x)

noncomputable def commutation_left_unit_rweq (x : X) :
    RwEq
      (Path.trans (Path.refl (S.scan (S.sourceStabilize x))) (S.commutationPath x))
      (S.commutationPath x) :=
  rweq_of_scanning_step (S.commutation_left_unit_step x)

noncomputable def commutation_cancel_rweq (x : X) :
    RwEq
      (Path.trans (Path.symm (S.commutationPath x)) (S.commutationPath x))
      (Path.refl (S.targetShift (S.scan x))) :=
  rweq_cmpA_inv_left (S.commutationPath x)

/-- Two-step scanning comparison path along two stabilization stages. -/
noncomputable def twoStepScanningPath (x : X) :
    Path
      (S.scan (S.sourceStabilize (S.sourceStabilize x)))
      (S.targetShift (S.targetShift (S.scan x))) :=
  Path.trans
    (S.commutationPath (S.sourceStabilize x))
    (Path.congrArg S.targetShift (S.commutationPath x))

noncomputable def two_step_rweq (x : X) :
    RwEq
      (Path.trans
        (S.twoStepScanningPath x)
        (Path.refl (S.targetShift (S.targetShift (S.scan x)))))
      (S.twoStepScanningPath x) :=
  rweq_cmpA_refl_right (S.twoStepScanningPath x)

end ScanningMapData

/-- Trivial model instantiating the scanning-map computational-path interface. -/
noncomputable def trivialScanningMapData : ScanningMapData PUnit PUnit where
  sourceStabilize := fun _ => PUnit.unit
  targetShift := fun _ => PUnit.unit
  scan := fun _ => PUnit.unit
  commutationPath := fun _ => Path.refl PUnit.unit
  commutationStep := fun _ => ScanningStep.right_unit (Path.refl PUnit.unit)

end ScanningMapPaths
end HomologicalStability
end ComputationalPaths
