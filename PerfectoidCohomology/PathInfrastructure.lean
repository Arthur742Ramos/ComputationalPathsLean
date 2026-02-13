/- 
# Perfectoid cohomology path infrastructure

This module combines almost-vanishing and tilting-equivalence path packages
for perfectoid cohomology, with explicit `Path.Step` normalization witnesses.
-/

import PerfectoidCohomology.AlmostVanishingPaths
import PerfectoidCohomology.TiltingEquivalencePaths

namespace ComputationalPaths
namespace PerfectoidCohomology

open Path

universe u v w

/-- Unified path infrastructure for perfectoid cohomology and its tilt. -/
structure PerfectoidCohomologyPathInfrastructure
    (R : Type u)
    (H : Int → Type v)
    (Htilt : Int → Type w) where
  almost : AlmostVanishingPathData R H
  almostTilt : AlmostVanishingPathData R Htilt
  tilting : TiltingEquivalencePathData almost almostTilt
  /-- Transport of almost vanishing through the tilting equivalence. -/
  vanishingTransportPath :
    ∀ (n : Int) (ε : R) (x : H n),
      almost.ideal ε →
      Path
        (tilting.toTilt (n + 1) (almost.differential n (almost.scalar ε n x)))
        (almostTilt.zero (n + 1))
  /-- Primitive rewrite witness for `vanishingTransportPath`. -/
  vanishingTransportStep :
    ∀ (n : Int) (ε : R) (x : H n) (hε : almost.ideal ε),
      Path.Step
        (Path.trans
          (vanishingTransportPath n ε x hε)
          (Path.refl (almostTilt.zero (n + 1))))
        (vanishingTransportPath n ε x hε)

namespace PerfectoidCohomologyPathInfrastructure

variable {R : Type u} {H : Int → Type v} {Htilt : Int → Type w}
variable (I : PerfectoidCohomologyPathInfrastructure R H Htilt)

@[simp] theorem vanishingTransport_rweq
    (n : Int) (ε : R) (x : H n) (hε : I.almost.ideal ε) :
    RwEq
      (Path.trans
        (I.vanishingTransportPath n ε x hε)
        (Path.refl (I.almostTilt.zero (n + 1))))
      (I.vanishingTransportPath n ε x hε) :=
  rweq_of_step (I.vanishingTransportStep n ε x hε)

@[simp] theorem mapDifferential_rweq (n : Int) (x : H n) :
    RwEq
      (Path.trans
        (I.tilting.mapDifferentialPath n x)
        (Path.refl (I.almostTilt.differential n (I.tilting.toTilt n x))))
      (I.tilting.mapDifferentialPath n x) :=
  TiltingEquivalencePathData.mapDifferential_rweq (T := I.tilting) n x

@[simp] theorem vanishingTransport_cancel_right_rweq
    (n : Int) (ε : R) (x : H n) (hε : I.almost.ideal ε) :
    RwEq
      (Path.trans
        (I.vanishingTransportPath n ε x hε)
        (Path.symm (I.vanishingTransportPath n ε x hε)))
      (Path.refl (I.tilting.toTilt (n + 1) (I.almost.differential n (I.almost.scalar ε n x)))) :=
  rweq_cmpA_inv_right (I.vanishingTransportPath n ε x hε)

/-- Canonical trivial perfectoid cohomology infrastructure on `PUnit`. -/
def trivial (R : Type u) :
    PerfectoidCohomologyPathInfrastructure R (fun _ => PUnit) (fun _ => PUnit) where
  almost := AlmostVanishingPathData.trivial R
  almostTilt := AlmostVanishingPathData.trivial R
  tilting := by
    simpa using (TiltingEquivalencePathData.trivial R)
  vanishingTransportPath := fun _ _ _ _ => Path.refl PUnit.unit
  vanishingTransportStep := fun _ _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end PerfectoidCohomologyPathInfrastructure

end PerfectoidCohomology
end ComputationalPaths
