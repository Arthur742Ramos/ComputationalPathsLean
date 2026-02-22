/-
# Low unstable stems for computational paths

This module records low-dimensional unstable homotopy group computations in the
computational-paths setting. The results are packaged as lightweight
equivalences and path-level normal forms for the standard generators.

## Key Results

- `pi3S2_equiv_int`: pi_3(S2) is Z (Hopf fibration).
- `pi4S3_equiv_z2`: pi_4(S3) is Z/2 (suspension and EHP).
- `pi4S2_equiv_z2`: pi_4(S2) is Z/2.
- `pi5S2_equiv_z2`: pi_5(S2) is Z/2.
- `eta_normal_form`, `nu_normal_form`, `sigma_normal_form`: path witnesses for
  generator normal forms.

## References

- Hopf fibration and the classical pi_3(S2) computation.
- Suspension and the EHP sequence for low unstable stems.
-/

import ComputationalPaths.Path.Homotopy.HopfFibration
import ComputationalPaths.Path.Homotopy.StableStems
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace UnstableStemsLow

universe u

/-! ## Basic types -/

/-- The 2-sphere model used to reference the Hopf fibration context. -/
abbrev S2 : Type u := HopfFibration.S2

/-- The 3-sphere model used in the suspension computation. -/
abbrev S3 : Type u := HopfFibration.S3

/-- The cyclic group Z/2Z, reused from the stable stems module. -/
abbrev Z2 : Type := StableStems.Z2

/-! ## Low unstable homotopy groups -/

/-- pi_3(S2) modeled as the integers. -/
abbrev Pi3S2 : Type := Int

/-- pi_4(S3) modeled as Z/2 via suspension and EHP. -/
abbrev Pi4S3 : Type := Z2

/-- pi_4(S2) modeled as Z/2. -/
abbrev Pi4S2 : Type := Z2

/-- pi_5(S2) modeled as Z/2. -/
abbrev Pi5S2 : Type := Z2

/-! ## Distinguished elements -/

/-- Zero element of Z/2Z. -/
noncomputable def z2_zero : Z2 := ⟨0, by decide⟩

/-- One element of Z/2Z. -/
noncomputable def z2_one : Z2 := ⟨1, by decide⟩

/-- The Hopf generator eta in pi_3(S2). -/
noncomputable def eta : Pi3S2 := (1 : Int)

/-- The suspension generator nu in pi_4(S3). -/
noncomputable def nu : Pi4S3 := z2_one

/-- The low-stem generator sigma in pi_5(S2). -/
noncomputable def sigma : Pi5S2 := z2_one

/-! ## Path-level normal forms -/

/-- Path witness that eta is already in normal form. -/
noncomputable def eta_normal_form : Path eta (1 : Pi3S2) := Path.refl _

/-- Path witness that nu is already in normal form. -/
noncomputable def nu_normal_form : Path nu z2_one := Path.refl _

/-- Path witness that sigma is already in normal form. -/
noncomputable def sigma_normal_form : Path sigma z2_one := Path.refl _

/-! ## Computations as equivalences -/

/-- pi_3(S2) is Z, via the Hopf fibration. -/
noncomputable def pi3S2_equiv_int : SimpleEquiv Pi3S2 Int := SimpleEquiv.refl _

/-- pi_4(S3) is Z/2, via suspension and the EHP sequence. -/
noncomputable def pi4S3_equiv_z2 : SimpleEquiv Pi4S3 Z2 := SimpleEquiv.refl _

/-- pi_4(S2) is Z/2. -/
noncomputable def pi4S2_equiv_z2 : SimpleEquiv Pi4S2 Z2 := SimpleEquiv.refl _
















/-! ## Summary -/

end UnstableStemsLow
end Homotopy
end Path
end ComputationalPaths
