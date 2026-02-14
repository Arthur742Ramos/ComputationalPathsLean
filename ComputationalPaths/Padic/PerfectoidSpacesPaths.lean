import ComputationalPaths.Path.Rewrite.RwEq

/-!
# p-adic geometry paths: perfectoid spaces

This module packages perfectoid-space tilting data with explicit `Path.Step`
witnesses and derived `RwEq` normalization lemmas.
-/

namespace ComputationalPaths
namespace Padic

open Path

universe u v

/-- Perfectoid-space data with explicit step-level tilting witnesses. -/
structure PerfectoidSpacePathData (X : Type u) (R : Type v) where
  tilt : X → X
  untilt : X → X
  sectionVal : X → R
  sharp : X → R
  tiltRoundTripPath : ∀ x : X, Path (untilt (tilt x)) x
  untiltRoundTripPath : ∀ x : X, Path (tilt (untilt x)) x
  sharpCompatPath : ∀ x : X, Path (sharp (tilt x)) (sectionVal x)
  tiltRoundTripStep :
    ∀ x : X,
      Path.Step
        (Path.trans (tiltRoundTripPath x) (Path.refl x))
        (tiltRoundTripPath x)
  untiltRoundTripStep :
    ∀ x : X,
      Path.Step
        (Path.trans (Path.refl (tilt (untilt x))) (untiltRoundTripPath x))
        (untiltRoundTripPath x)
  sharpCompatStep :
    ∀ x : X,
      Path.Step
        (Path.trans (sharpCompatPath x) (Path.refl (sectionVal x)))
        (sharpCompatPath x)

namespace PerfectoidSpacePathData

variable {X : Type u} {R : Type v} (P : PerfectoidSpacePathData X R)

@[simp] theorem tilt_roundtrip_rweq (x : X) :
    RwEq
      (Path.trans (P.tiltRoundTripPath x) (Path.refl x))
      (P.tiltRoundTripPath x) :=
  rweq_of_step (P.tiltRoundTripStep x)

@[simp] theorem untilt_roundtrip_rweq (x : X) :
    RwEq
      (Path.trans (Path.refl (P.tilt (P.untilt x))) (P.untiltRoundTripPath x))
      (P.untiltRoundTripPath x) :=
  rweq_of_step (P.untiltRoundTripStep x)

@[simp] theorem sharp_compat_rweq (x : X) :
    RwEq
      (Path.trans (P.sharpCompatPath x) (Path.refl (P.sectionVal x)))
      (P.sharpCompatPath x) :=
  rweq_of_step (P.sharpCompatStep x)

@[simp] theorem tilt_cancel_rweq (x : X) :
    RwEq
      (Path.trans (Path.symm (P.tiltRoundTripPath x)) (P.tiltRoundTripPath x))
      (Path.refl x) :=
  rweq_cmpA_inv_left (P.tiltRoundTripPath x)

@[simp] theorem untilt_cancel_rweq (x : X) :
    RwEq
      (Path.trans (P.untiltRoundTripPath x) (Path.symm (P.untiltRoundTripPath x)))
      (Path.refl (P.tilt (P.untilt x))) :=
  rweq_cmpA_inv_right (P.untiltRoundTripPath x)

end PerfectoidSpacePathData

/-- Trivial perfectoid-space path data on `PUnit`. -/
def trivialPerfectoidSpacePathData : PerfectoidSpacePathData PUnit PUnit where
  tilt := fun _ => PUnit.unit
  untilt := fun _ => PUnit.unit
  sectionVal := fun _ => PUnit.unit
  sharp := fun _ => PUnit.unit
  tiltRoundTripPath := fun _ => Path.refl PUnit.unit
  untiltRoundTripPath := fun _ => Path.refl PUnit.unit
  sharpCompatPath := fun _ => Path.refl PUnit.unit
  tiltRoundTripStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  untiltRoundTripStep := fun _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)
  sharpCompatStep := fun _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end Padic
end ComputationalPaths
