/- 
# Perfectoid cohomology paths: tilting equivalence

This module packages cohomological tilting equivalences with explicit
`Path.Step` witnesses for round-trip and differential compatibility paths.
-/

import ComputationalPaths.PerfectoidCohomology.AlmostVanishingPaths

namespace ComputationalPaths
namespace PerfectoidCohomology

open Path

universe u v w

/-- Path package for cohomological tilting equivalence data. -/
structure TiltingEquivalencePathData
    {R : Type u}
    {H : Int → Type v}
    {Htilt : Int → Type w}
    (A : AlmostVanishingPathData R H)
    (Atilt : AlmostVanishingPathData R Htilt) where
  toTilt : (n : Int) → H n → Htilt n
  fromTilt : (n : Int) → Htilt n → H n
  toFromPath : ∀ (n : Int) (x : Htilt n), Path (toTilt n (fromTilt n x)) x
  fromToPath : ∀ (n : Int) (x : H n), Path (fromTilt n (toTilt n x)) x
  toFromStep :
    ∀ (n : Int) (x : Htilt n),
      Path.Step
        (Path.trans (toFromPath n x) (Path.refl x))
        (toFromPath n x)
  fromToStep :
    ∀ (n : Int) (x : H n),
      Path.Step
        (Path.trans (fromToPath n x) (Path.refl x))
        (fromToPath n x)
  mapDifferentialPath :
    ∀ (n : Int) (x : H n),
      Path
        (toTilt (n + 1) (A.differential n x))
        (Atilt.differential n (toTilt n x))
  mapDifferentialStep :
    ∀ (n : Int) (x : H n),
      Path.Step
        (Path.trans
          (mapDifferentialPath n x)
          (Path.refl (Atilt.differential n (toTilt n x))))
        (mapDifferentialPath n x)

namespace TiltingEquivalencePathData

variable {R : Type u} {H : Int → Type v} {Htilt : Int → Type w}
variable {A : AlmostVanishingPathData R H}
variable {Atilt : AlmostVanishingPathData R Htilt}
variable (T : TiltingEquivalencePathData A Atilt)

@[simp] theorem toFrom_rweq (n : Int) (x : Htilt n) :
    RwEq (Path.trans (T.toFromPath n x) (Path.refl x)) (T.toFromPath n x) :=
  rweq_of_step (T.toFromStep n x)

@[simp] theorem fromTo_rweq (n : Int) (x : H n) :
    RwEq (Path.trans (T.fromToPath n x) (Path.refl x)) (T.fromToPath n x) :=
  rweq_of_step (T.fromToStep n x)

@[simp] theorem mapDifferential_rweq (n : Int) (x : H n) :
    RwEq
      (Path.trans
        (T.mapDifferentialPath n x)
        (Path.refl (Atilt.differential n (T.toTilt n x))))
      (T.mapDifferentialPath n x) :=
  rweq_of_step (T.mapDifferentialStep n x)

@[simp] theorem fromTo_cancel_right_rweq (n : Int) (x : H n) :
    RwEq
      (Path.trans (T.fromToPath n x) (Path.symm (T.fromToPath n x)))
      (Path.refl (T.fromTilt n (T.toTilt n x))) :=
  rweq_cmpA_inv_right (T.fromToPath n x)

/-- Canonical trivial tilting equivalence package on `PUnit`. -/
def trivial (R : Type u) :
    TiltingEquivalencePathData
      (AlmostVanishingPathData.trivial R)
      (AlmostVanishingPathData.trivial R) where
  toTilt := fun _ _ => PUnit.unit
  fromTilt := fun _ _ => PUnit.unit
  toFromPath := fun _ _ => Path.refl PUnit.unit
  fromToPath := fun _ _ => Path.refl PUnit.unit
  toFromStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  fromToStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  mapDifferentialPath := fun _ _ => Path.refl PUnit.unit
  mapDifferentialStep := fun _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end TiltingEquivalencePathData

end PerfectoidCohomology
end ComputationalPaths
