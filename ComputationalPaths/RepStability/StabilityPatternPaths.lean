import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.RepStability.FIModulePaths

/-!
# Representation stability paths: stability patterns

This module records common representation-stability patterns with explicit
computational paths: central stability, detector idempotence, and periodicity.
-/

namespace ComputationalPaths
namespace RepStability
namespace StabilityPatternPaths

open Path

universe u

/-- Domain-specific rewrite tags for stability-pattern coherence moves. -/
inductive StabilityPatternStep : Type
  | shift
  | detect
  | periodic
  | central

/-- Iterated application of an endomap. -/
def stagedShift {Carrier : Type u} (f : Carrier → Carrier) : Nat → Carrier → Carrier
  | 0, x => x
  | n + 1, x => f (stagedShift f n x)

/-- Minimal computational-path interface for representation stability patterns. -/
structure StabilityPatternPathData (Carrier : Type u) where
  shift : Carrier → Carrier
  detectStable : Carrier → Carrier
  period : Nat
  centralStabilityPath :
    ∀ x : Carrier, Path (detectStable (shift x)) (shift (detectStable x))
  detectIdempotentPath :
    ∀ x : Carrier, Path (detectStable (detectStable x)) (detectStable x)
  periodicityPath :
    ∀ (n : Nat) (x : Carrier),
      Path (stagedShift shift (n + period) x) (stagedShift shift n x)

namespace StabilityPatternPathData

variable {Carrier : Type u}
variable (S : StabilityPatternPathData Carrier)

/-- Stage `n` of the shifted stability process. -/
def stage (n : Nat) (x : Carrier) : Carrier :=
  stagedShift S.shift n x

@[simp] theorem stage_zero (x : Carrier) :
    S.stage 0 x = x := rfl

@[simp] theorem stage_succ (n : Nat) (x : Carrier) :
    S.stage (n + 1) x = S.shift (S.stage n x) := rfl

/-- Central-stability witness transported to stage `n`. -/
def centralAtStage (n : Nat) (x : Carrier) :
    Path (S.detectStable (S.shift (S.stage n x)))
      (S.shift (S.detectStable (S.stage n x))) :=
  S.centralStabilityPath (S.stage n x)

/-- Composite path: idempotent detection followed by central stability. -/
def centralDetectPath (x : Carrier) :
    Path (S.detectStable (S.detectStable (S.shift x)))
      (S.shift (S.detectStable x)) :=
  Path.trans
    (S.detectIdempotentPath (S.shift x))
    (S.centralStabilityPath x)

@[simp] theorem centralDetect_rweq (x : Carrier) :
    RwEq
      (Path.trans
        (S.centralDetectPath x)
        (Path.refl (S.shift (S.detectStable x))))
      (S.centralDetectPath x) :=
  rweq_cmpA_refl_right (S.centralDetectPath x)

@[simp] theorem centralDetect_cancel_rweq (x : Carrier) :
    RwEq
      (Path.trans (Path.symm (S.centralDetectPath x)) (S.centralDetectPath x))
      (Path.refl (S.shift (S.detectStable x))) :=
  rweq_cmpA_inv_left (S.centralDetectPath x)

/-- Step witness: right-unit normalization for detector idempotence. -/
def detectIdempotent_step (x : Carrier) :
    Path.Step
      (Path.trans (S.detectIdempotentPath x) (Path.refl (S.detectStable x)))
      (S.detectIdempotentPath x) :=
  Path.Step.trans_refl_right (S.detectIdempotentPath x)

@[simp] theorem detectIdempotent_rweq (x : Carrier) :
    RwEq
      (Path.trans (S.detectIdempotentPath x) (Path.refl (S.detectStable x)))
      (S.detectIdempotentPath x) :=
  rweq_of_step (S.detectIdempotent_step x)

/-- Step witness: left-unit normalization for periodicity coherence. -/
def periodicity_step (n : Nat) (x : Carrier) :
    Path.Step
      (Path.trans (Path.refl (S.stage (n + S.period) x)) (S.periodicityPath n x))
      (S.periodicityPath n x) :=
  Path.Step.trans_refl_left (S.periodicityPath n x)

@[simp] theorem periodicity_rweq (n : Nat) (x : Carrier) :
    RwEq
      (Path.trans (Path.refl (S.stage (n + S.period) x)) (S.periodicityPath n x))
      (S.periodicityPath n x) :=
  rweq_of_step (S.periodicity_step n x)

/-- Two-period contraction obtained by composing periodicity twice. -/
def periodicityDoublePath (n : Nat) (x : Carrier) :
    Path (S.stage ((n + S.period) + S.period) x) (S.stage n x) :=
  Path.trans (S.periodicityPath (n + S.period) x) (S.periodicityPath n x)

@[simp] theorem periodicityDouble_rweq (n : Nat) (x : Carrier) :
    RwEq
      (Path.trans
        (Path.refl (S.stage ((n + S.period) + S.period) x))
        (S.periodicityDoublePath n x))
      (S.periodicityDoublePath n x) :=
  rweq_cmpA_refl_left (S.periodicityDoublePath n x)

@[simp] theorem periodicityDouble_cancel_rweq (n : Nat) (x : Carrier) :
    RwEq
      (Path.trans
        (Path.symm (S.periodicityDoublePath n x))
        (S.periodicityDoublePath n x))
      (Path.refl (S.stage n x)) :=
  rweq_cmpA_inv_left (S.periodicityDoublePath n x)

@[simp] theorem periodicity_cancel_rweq (n : Nat) (x : Carrier) :
    RwEq
      (Path.trans (Path.symm (S.periodicityPath n x)) (S.periodicityPath n x))
      (Path.refl (S.stage n x)) :=
  rweq_cmpA_inv_left (S.periodicityPath n x)

end StabilityPatternPathData

open FIModulePaths

/-- Coarse stability pattern extracted from an FI-module stabilization map. -/
def coarsePatternOfFIModule {Carrier : Type u}
    (F : FIModulePathData Carrier) : StabilityPatternPathData Carrier where
  shift := F.stabilize F.stableRange
  detectStable := fun x => x
  period := 0
  centralStabilityPath := fun x => Path.refl (F.stabilize F.stableRange x)
  detectIdempotentPath := fun x => Path.refl x
  periodicityPath := fun n x =>
    Path.refl (stagedShift (F.stabilize F.stableRange) n x)

/-- Trivial model instantiating the stability-pattern computational interface. -/
def trivialStabilityPatternPathData : StabilityPatternPathData PUnit where
  shift := fun _ => PUnit.unit
  detectStable := fun _ => PUnit.unit
  period := 0
  centralStabilityPath := fun _ => Path.refl PUnit.unit
  detectIdempotentPath := fun _ => Path.refl PUnit.unit
  periodicityPath := fun _ _ => Path.refl PUnit.unit

end StabilityPatternPaths
end RepStability
end ComputationalPaths
