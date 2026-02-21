import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Symplectic duality paths: 3d mirror symmetry

This module packages a minimal 3d mirror-symmetry interface with explicit
computational paths. Higgs/Coulomb round-trips and mass/FI compatibility are
tracked with `Path`, normalized by `Path.Step`, and compared by `RwEq`.
-/

namespace ComputationalPaths
namespace SymplecticDuality
namespace Mirror3DPaths

open Path

universe u v

/-- Domain-specific rewrite tags for 3d mirror-symmetry coherence moves. -/
inductive Mirror3DStep : Type
  | higgsRoundTrip
  | coulombRoundTrip
  | massFI
  | parameterTransport

/-- Minimal computational-path data for 3d mirror symmetry. -/
structure Mirror3DPathData (Higgs : Type u) (Coulomb : Type v) where
  mirrorToCoulomb : Higgs → Coulomb
  mirrorToHiggs : Coulomb → Higgs
  massShift : Higgs → Higgs
  fiShift : Coulomb → Coulomb
  higgsRoundTripPath :
    ∀ h : Higgs, Path (mirrorToHiggs (mirrorToCoulomb h)) h
  coulombRoundTripPath :
    ∀ c : Coulomb, Path (mirrorToCoulomb (mirrorToHiggs c)) c
  massFIPath :
    ∀ h : Higgs,
      Path (mirrorToCoulomb (massShift h)) (fiShift (mirrorToCoulomb h))
  higgsRoundTripStep :
    ∀ h : Higgs,
      Path.Step
        (Path.trans (higgsRoundTripPath h) (Path.refl h))
        (higgsRoundTripPath h)
  coulombRoundTripStep :
    ∀ c : Coulomb,
      Path.Step
        (Path.trans (coulombRoundTripPath c) (Path.refl c))
        (coulombRoundTripPath c)
  massFIStep :
    ∀ h : Higgs,
      Path.Step
        (Path.trans
          (massFIPath h)
          (Path.refl (fiShift (mirrorToCoulomb h))))
        (massFIPath h)
  mirrorMap :
    {a b : Higgs} → Path a b → Path (mirrorToCoulomb a) (mirrorToCoulomb b)
  mirrorMapStep :
    {a b : Higgs} → (p : Path a b) →
      Path.Step
        (Path.trans (mirrorMap p) (Path.refl (mirrorToCoulomb b)))
        (mirrorMap p)

namespace Mirror3DPathData

variable {Higgs : Type u} {Coulomb : Type v}
variable (M : Mirror3DPathData Higgs Coulomb)

/-- Composite path from mass deformation to Coulomb dualization data. -/
def dualizedMassPath (h : Higgs) :
    Path (M.mirrorToCoulomb (M.massShift h))
      (M.mirrorToCoulomb (M.mirrorToHiggs (M.fiShift (M.mirrorToCoulomb h)))) :=
  Path.trans
    (M.massFIPath h)
    (Path.symm (M.coulombRoundTripPath (M.fiShift (M.mirrorToCoulomb h))))

/-- Step witness: right-unit normalization for Higgs round-trip coherence. -/
def higgsRoundTrip_step (h : Higgs) :
    Path.Step
      (Path.trans (M.higgsRoundTripPath h) (Path.refl h))
      (M.higgsRoundTripPath h) :=
  M.higgsRoundTripStep h

@[simp] theorem higgsRoundTrip_rweq (h : Higgs) :
    RwEq
      (Path.trans (M.higgsRoundTripPath h) (Path.refl h))
      (M.higgsRoundTripPath h) :=
  rweq_of_step (M.higgsRoundTrip_step h)

/-- Step witness: right-unit normalization for Coulomb round-trip coherence. -/
def coulombRoundTrip_step (c : Coulomb) :
    Path.Step
      (Path.trans (M.coulombRoundTripPath c) (Path.refl c))
      (M.coulombRoundTripPath c) :=
  M.coulombRoundTripStep c

@[simp] theorem coulombRoundTrip_rweq (c : Coulomb) :
    RwEq
      (Path.trans (M.coulombRoundTripPath c) (Path.refl c))
      (M.coulombRoundTripPath c) :=
  rweq_of_step (M.coulombRoundTrip_step c)

/-- Step witness: right-unit normalization for mass/FI mirror compatibility. -/
def massFI_step (h : Higgs) :
    Path.Step
      (Path.trans
        (M.massFIPath h)
        (Path.refl (M.fiShift (M.mirrorToCoulomb h))))
      (M.massFIPath h) :=
  M.massFIStep h

@[simp] theorem massFI_rweq (h : Higgs) :
    RwEq
      (Path.trans
        (M.massFIPath h)
        (Path.refl (M.fiShift (M.mirrorToCoulomb h))))
      (M.massFIPath h) :=
  rweq_of_step (M.massFI_step h)

/-- Step witness: right-unit normalization for mapped Higgs paths. -/
def mirrorMap_step {a b : Higgs} (p : Path a b) :
    Path.Step
      (Path.trans (M.mirrorMap p) (Path.refl (M.mirrorToCoulomb b)))
      (M.mirrorMap p) :=
  M.mirrorMapStep p

@[simp] theorem mirrorMap_rweq {a b : Higgs} (p : Path a b) :
    RwEq
      (Path.trans (M.mirrorMap p) (Path.refl (M.mirrorToCoulomb b)))
      (M.mirrorMap p) :=
  rweq_of_step (M.mirrorMap_step p)

/-- Step witness: right-unit normalization for the dualized mass comparison. -/
def dualizedMass_step (h : Higgs) :
    Path.Step
      (Path.trans
        (M.dualizedMassPath h)
        (Path.refl
          (M.mirrorToCoulomb (M.mirrorToHiggs (M.fiShift (M.mirrorToCoulomb h))))))
      (M.dualizedMassPath h) :=
  Path.Step.trans_refl_right (M.dualizedMassPath h)

@[simp] theorem dualizedMass_rweq (h : Higgs) :
    RwEq
      (Path.trans
        (M.dualizedMassPath h)
        (Path.refl
          (M.mirrorToCoulomb (M.mirrorToHiggs (M.fiShift (M.mirrorToCoulomb h))))))
      (M.dualizedMassPath h) :=
  rweq_of_step (M.dualizedMass_step h)

@[simp] theorem dualizedMass_cancel_rweq (h : Higgs) :
    RwEq
      (Path.trans (Path.symm (M.dualizedMassPath h)) (M.dualizedMassPath h))
      (Path.refl
        (M.mirrorToCoulomb (M.mirrorToHiggs (M.fiShift (M.mirrorToCoulomb h))))) :=
  rweq_cmpA_inv_left (M.dualizedMassPath h)

end Mirror3DPathData

/-- Trivial model instantiating the 3d mirror-symmetry path interface. -/
def trivialMirror3DPathData : Mirror3DPathData PUnit PUnit where
  mirrorToCoulomb := fun _ => PUnit.unit
  mirrorToHiggs := fun _ => PUnit.unit
  massShift := fun _ => PUnit.unit
  fiShift := fun _ => PUnit.unit
  higgsRoundTripPath := fun _ => Path.refl PUnit.unit
  coulombRoundTripPath := fun _ => Path.refl PUnit.unit
  massFIPath := fun _ => Path.refl PUnit.unit
  higgsRoundTripStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  coulombRoundTripStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  massFIStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  mirrorMap := fun p => p
  mirrorMapStep := fun p => Path.Step.trans_refl_right p

end Mirror3DPaths
end SymplecticDuality
end ComputationalPaths
