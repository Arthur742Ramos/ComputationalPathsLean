/- 
# Perfectoid cohomology paths: almost vanishing

This module packages almost-vanishing behavior in perfectoid cohomology with
explicit `Path.Step` rewrite witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace PerfectoidCohomology

open Path

universe u v

/-- Path package for almost-vanishing classes in perfectoid cohomology. -/
structure AlmostVanishingPathData (R : Type u) (H : Int → Type v) where
  /-- Zero class in each degree. -/
  zero : (n : Int) → H n
  /-- Scalar action by almost-ideal elements. -/
  scalar : R → (n : Int) → H n → H n
  /-- Cohomological differential. -/
  differential : (n : Int) → H n → H (n + 1)
  /-- Chosen ideal controlling almost vanishing. -/
  ideal : R → Prop
  /-- Almost-vanishing witness after scalar action and differential. -/
  almostVanishingPath :
    ∀ (n : Int) (ε : R) (x : H n),
      ideal ε → Path (differential n (scalar ε n x)) (zero (n + 1))
  /-- Primitive rewrite witness for `almostVanishingPath`. -/
  almostVanishingStep :
    ∀ (n : Int) (ε : R) (x : H n) (hε : ideal ε),
      Path.Step
        (Path.trans (almostVanishingPath n ε x hε) (Path.refl (zero (n + 1))))
        (almostVanishingPath n ε x hε)
  /-- Scalar action preserves the zero class. -/
  scalarZeroPath :
    ∀ (n : Int) (ε : R), ideal ε → Path (scalar ε n (zero n)) (zero n)
  /-- Primitive rewrite witness for `scalarZeroPath`. -/
  scalarZeroStep :
    ∀ (n : Int) (ε : R) (hε : ideal ε),
      Path.Step
        (Path.trans (Path.refl (scalar ε n (zero n))) (scalarZeroPath n ε hε))
        (scalarZeroPath n ε hε)

namespace AlmostVanishingPathData

variable {R : Type u} {H : Int → Type v}
variable (A : AlmostVanishingPathData R H)

noncomputable def almostVanishing_rweq
    (n : Int) (ε : R) (x : H n) (hε : A.ideal ε) :
    RwEq
      (Path.trans (A.almostVanishingPath n ε x hε) (Path.refl (A.zero (n + 1))))
      (A.almostVanishingPath n ε x hε) :=
  rweq_of_step (A.almostVanishingStep n ε x hε)

noncomputable def scalarZero_rweq
    (n : Int) (ε : R) (hε : A.ideal ε) :
    RwEq
      (Path.trans (Path.refl (A.scalar ε n (A.zero n))) (A.scalarZeroPath n ε hε))
      (A.scalarZeroPath n ε hε) :=
  rweq_of_step (A.scalarZeroStep n ε hε)

noncomputable def almostVanishing_cancel_left_rweq
    (n : Int) (ε : R) (x : H n) (hε : A.ideal ε) :
    RwEq
      (Path.trans
        (Path.symm (A.almostVanishingPath n ε x hε))
        (A.almostVanishingPath n ε x hε))
      (Path.refl (A.zero (n + 1))) :=
  rweq_cmpA_inv_left (A.almostVanishingPath n ε x hε)

/-- Canonical trivial almost-vanishing package on `PUnit`. -/
def trivial (R : Type u) : AlmostVanishingPathData R (fun _ => PUnit) where
  zero := fun _ => PUnit.unit
  scalar := fun _ _ _ => PUnit.unit
  differential := fun _ _ => PUnit.unit
  ideal := fun _ => True
  almostVanishingPath := fun _ _ _ _ => Path.refl PUnit.unit
  almostVanishingStep := fun _ _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  scalarZeroPath := fun _ _ _ => Path.refl PUnit.unit
  scalarZeroStep := fun _ _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

end AlmostVanishingPathData

end PerfectoidCohomology
end ComputationalPaths
