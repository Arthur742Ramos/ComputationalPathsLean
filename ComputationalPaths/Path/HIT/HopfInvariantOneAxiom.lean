/-
# Adams' H-Space Classification (assumption-free, opt-in)

The core development keeps the H-space classification theorem *parametric* in
the typeclass `HasSphereHSpaceClassification` (see `HopfInvariantOne.lean`) so
the assumption stays explicit and discharge-friendly.

If you want to *use* the classification results without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasSphereHSpaceClassification` as a **kernel axiom**, and
2. Exports wrappers for the main theorems with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.

## Mathematical Background

Adams' Hopf invariant one theorem (1960) proves that Sⁿ admits an H-space
structure if and only if n ∈ {0, 1, 3, 7}. The proof uses K-theory and Adams
operations, which are beyond the scope of this formalization.
-/

import ComputationalPaths.Path.HIT.HopfInvariantOne

namespace ComputationalPaths
namespace Path
namespace HopfInvariantOne

universe u

open FreudenthalSuspension

/-- Global H-space classification instance (kernel axiom, opt-in). -/
axiom instHasSphereHSpaceClassificationAxiom : HasSphereHSpaceClassification.{u}

attribute [instance] instHasSphereHSpaceClassificationAxiom

/-- Assumption-free wrapper: S² is not an H-space. -/
theorem sphere2_not_HSpace' : ¬IsHSpace (SphereN 2) (sphereN_base 2) :=
  sphere2_not_HSpace

/-- Assumption-free wrapper: S⁴ is not an H-space. -/
theorem sphere4_not_HSpace' : ¬IsHSpace (SphereN 4) (sphereN_base 4) :=
  sphere4_not_HSpace

/-- Assumption-free wrapper: S⁵ is not an H-space. -/
theorem sphere5_not_HSpace' : ¬IsHSpace (SphereN 5) (sphereN_base 5) :=
  sphere5_not_HSpace

/-- Assumption-free wrapper: S⁶ is not an H-space. -/
theorem sphere6_not_HSpace' : ¬IsHSpace (SphereN 6) (sphereN_base 6) :=
  sphere6_not_HSpace

/-- Assumption-free wrapper: Sⁿ is not an H-space for n ∉ {0, 1, 3, 7}. -/
theorem sphere_not_HSpace' (n : Nat) (hn : ¬isHSpaceDimension n) :
    ¬IsHSpace (SphereN n) (sphereN_base n) :=
  sphere_not_HSpace n hn

end HopfInvariantOne
end Path
end ComputationalPaths
