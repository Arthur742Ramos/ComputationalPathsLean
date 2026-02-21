import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.HomologicalStability.ScanningMapPaths

/-!
# Homological stability paths: Quillen homology

This module records Quillen-homology flavored coherence data with explicit
computational paths, primitive step witnesses, and compatibility with scanning
maps from `ScanningMapPaths`.
-/

namespace ComputationalPaths
namespace HomologicalStability
namespace QuillenHomologyPaths

open Path
open ScanningMapPaths

universe u v

/-- Domain-specific rewrite steps for Quillen-homology coherence moves. -/
inductive QuillenHomologyStep {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop where
  | right_unit {a b : A} (p : Path a b) :
      QuillenHomologyStep (Path.trans p (Path.refl b)) p
  | left_unit {a b : A} (p : Path a b) :
      QuillenHomologyStep (Path.trans (Path.refl a) p) p
  | cancel {a b : A} (p : Path a b) :
      QuillenHomologyStep (Path.trans (Path.symm p) p) (Path.refl b)

/-- Interpret Quillen-homology domain steps as primitive path steps. -/
def QuillenHomologyStep.toStep {A : Type u} {a b : A} {p q : Path a b}
    (s : QuillenHomologyStep p q) : Path.Step p q :=
  match s with
  | .right_unit p => Path.Step.trans_refl_right p
  | .left_unit p => Path.Step.trans_refl_left p
  | .cancel p => Path.Step.symm_trans p

/-- Lift a Quillen-homology domain step to rewrite equivalence. -/
noncomputable def rweq_of_quillen_step {A : Type u} {a b : A}
    {p q : Path a b} (s : QuillenHomologyStep p q) : RwEq p q :=
  rweq_of_step (QuillenHomologyStep.toStep s)

/-- Minimal Quillen-homology path package over a carrier type. -/
structure QuillenHomologyPathData (A : Type u) where
  derive : A → A
  indecomposables : A → A
  stabilize : A → A
  linearizationPath :
    ∀ x : A, Path (indecomposables (derive x)) (stabilize (indecomposables x))
  stabilizationPath :
    ∀ x : A, Path (derive (stabilize x)) (stabilize (derive x))
  linearizationStep :
    ∀ x : A,
      QuillenHomologyStep
        (Path.trans (linearizationPath x) (Path.refl (stabilize (indecomposables x))))
        (linearizationPath x)

namespace QuillenHomologyPathData

variable {A : Type u}
variable (Q : QuillenHomologyPathData A)

noncomputable def linearization_rweq (x : A) :
    RwEq
      (Path.trans
        (Q.linearizationPath x)
        (Path.refl (Q.stabilize (Q.indecomposables x))))
      (Q.linearizationPath x) :=
  rweq_of_quillen_step (Q.linearizationStep x)

/-- Transport of Quillen-homology classes along stabilization. -/
def stabilizationTransport (x : A) :
    Path
      (Q.indecomposables (Q.derive (Q.stabilize x)))
      (Q.indecomposables (Q.stabilize (Q.derive x))) :=
  Path.congrArg Q.indecomposables (Q.stabilizationPath x)

/-- Left-unit normalization for the stabilization comparison. -/
def stabilization_left_unit_step (x : A) :
    QuillenHomologyStep
      (Path.trans (Path.refl (Q.derive (Q.stabilize x))) (Q.stabilizationPath x))
      (Q.stabilizationPath x) :=
  QuillenHomologyStep.left_unit (Q.stabilizationPath x)

noncomputable def stabilization_left_unit_rweq (x : A) :
    RwEq
      (Path.trans (Path.refl (Q.derive (Q.stabilize x))) (Q.stabilizationPath x))
      (Q.stabilizationPath x) :=
  rweq_of_quillen_step (Q.stabilization_left_unit_step x)

/-- Round-trip path for Quillen linearization. -/
def linearizationRoundTrip (x : A) :
    Path
      (Q.stabilize (Q.indecomposables x))
      (Q.stabilize (Q.indecomposables x)) :=
  Path.trans (Path.symm (Q.linearizationPath x)) (Q.linearizationPath x)

noncomputable def linearizationRoundTrip_rweq (x : A) :
    RwEq
      (Q.linearizationRoundTrip x)
      (Path.refl (Q.stabilize (Q.indecomposables x))) := by
  unfold linearizationRoundTrip
  exact rweq_of_quillen_step (QuillenHomologyStep.cancel (Q.linearizationPath x))

end QuillenHomologyPathData

/-- Compatibility package linking scanning maps and Quillen homology paths. -/
structure ScanningQuillenBridge (X : Type u) (Y : Type v) where
  scanning : ScanningMapData X Y
  quillen : QuillenHomologyPathData Y

namespace ScanningQuillenBridge

variable {X : Type u} {Y : Type v}
variable (B : ScanningQuillenBridge X Y)

/-- Quillen linearization path evaluated on scanned points. -/
def scanLinearizationPath (x : X) :
    Path
      (B.quillen.indecomposables (B.quillen.derive (B.scanning.scan x)))
      (B.quillen.stabilize (B.quillen.indecomposables (B.scanning.scan x))) :=
  B.quillen.linearizationPath (B.scanning.scan x)

noncomputable def scanLinearization_cancel_rweq (x : X) :
    RwEq
      (Path.trans (Path.symm (B.scanLinearizationPath x)) (B.scanLinearizationPath x))
      (Path.refl (B.quillen.stabilize (B.quillen.indecomposables (B.scanning.scan x)))) :=
  rweq_cmpA_inv_left (B.scanLinearizationPath x)

/-- Stabilized scanning map comparison in Quillen homology. -/
def stabilizedScanningPath (x : X) :
    Path
      (B.quillen.stabilize (B.scanning.scan (B.scanning.sourceStabilize x)))
      (B.quillen.stabilize (B.scanning.targetShift (B.scanning.scan x))) :=
  Path.trans
    (Path.congrArg B.quillen.stabilize (B.scanning.commutationPath x))
    (Path.refl (B.quillen.stabilize (B.scanning.targetShift (B.scanning.scan x))))

noncomputable def stabilizedScanning_rweq (x : X) :
    RwEq
      (B.stabilizedScanningPath x)
      (Path.congrArg B.quillen.stabilize (B.scanning.commutationPath x)) := by
  unfold stabilizedScanningPath
  exact rweq_cmpA_refl_right
    (Path.congrArg B.quillen.stabilize (B.scanning.commutationPath x))

noncomputable def stabilizedScanning_cancel_rweq (x : X) :
    RwEq
      (Path.trans (Path.symm (B.stabilizedScanningPath x)) (B.stabilizedScanningPath x))
      (Path.refl (B.quillen.stabilize (B.scanning.targetShift (B.scanning.scan x)))) :=
  rweq_cmpA_inv_left (B.stabilizedScanningPath x)

end ScanningQuillenBridge

/-- Trivial model instantiating the Quillen-homology path interface. -/
def trivialQuillenHomologyPathData : QuillenHomologyPathData PUnit where
  derive := fun _ => PUnit.unit
  indecomposables := fun _ => PUnit.unit
  stabilize := fun _ => PUnit.unit
  linearizationPath := fun _ => Path.refl PUnit.unit
  stabilizationPath := fun _ => Path.refl PUnit.unit
  linearizationStep := fun _ => QuillenHomologyStep.right_unit (Path.refl PUnit.unit)

/-- Trivial bridge between scanning maps and Quillen homology. -/
def trivialScanningQuillenBridge : ScanningQuillenBridge PUnit PUnit where
  scanning := ScanningMapPaths.trivialScanningMapData
  quillen := trivialQuillenHomologyPathData

end QuillenHomologyPaths
end HomologicalStability
end ComputationalPaths
