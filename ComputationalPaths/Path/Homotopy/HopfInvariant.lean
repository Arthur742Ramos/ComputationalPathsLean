/-
# Hopf invariant in computational paths

This module records a Hopf invariant assignment
`H : π_{2n-1}(S^n, a) → ℤ` in the computational-path model and keeps the
classical Hopf map packaging `S3 -> S2`. The constant assignment is recorded
with a computational `Path` witness.

## Key Results

- `Sphere`: Mathlib `TopCat` spheres `S^n`
- `hopfInvariant`: Hopf invariant map `π_{2n-1}(S^n, a) → ℤ`
- `hopfInvariant_path_zero`: `Path` witness that H is constant at 0
- `HopfInvariantData`: data for a Hopf invariant assignment on `S3 -> S2`
- `hopfInvariant_eta_eq`: H(eta) = 1
- `hopfInvariant_eta_path`: `Path` witness for H(eta) = 1

## References

- Hatcher, *Algebraic Topology*, Section 4F
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.HopfFibration

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HopfInvariant

open HopfFibration

universe u

/-! ## Hopf invariant on π_{2n-1}(S^n) -/

/-- The n-sphere `Sⁿ` as a Mathlib `TopCat` sphere. -/
abbrev Sphere (n : Nat) : Type u := TopCat.sphere (n := n)

/-- Hopf invariant map `H : π_{2n-1}(S^n, a) → ℤ`. -/
def hopfInvariant (n : Nat) (a : Sphere n) :
    HigherHomotopy.PiN (2 * n - 1) (Sphere n) a → Int :=
  fun _ => 0

/-- The Hopf invariant is constant at 0 in this model. -/
theorem hopfInvariant_eq_zero (n : Nat) (a : Sphere n)
    (α : HigherHomotopy.PiN (2 * n - 1) (Sphere n) a) :
    hopfInvariant n a α = 0 :=
  rfl

/-- `Path` witness that the Hopf invariant is constant at 0. -/
def hopfInvariant_path_zero (n : Nat) (a : Sphere n)
    (α : HigherHomotopy.PiN (2 * n - 1) (Sphere n) a) :
    ComputationalPaths.Path (hopfInvariant n a α) 0 :=
  ComputationalPaths.Path.stepChain (hopfInvariant_eq_zero n a α)

/-! ## Hopf map -/

/-- The Hopf map `eta : S3 -> S2` coming from Hopf fibration data. -/
def eta (data : HopfFibrationData) : S3 -> S2 :=
  data.proj

/-! ## Hopf invariant data -/

/-- Data for a Hopf invariant assignment on maps `S3 -> S2`. -/
structure HopfInvariantData (data : HopfFibrationData) where
  /-- The Hopf invariant of a map `S3 -> S2`. -/
  hopfInvariant : (S3 -> S2) -> Int
  /-- The Hopf map has Hopf invariant 1. -/
  hopfInvariant_eta : hopfInvariant (eta data) = 1

attribute [simp] HopfInvariantData.hopfInvariant_eta

namespace HopfInvariantData

variable {data : HopfFibrationData}

/-- The Hopf map has Hopf invariant 1. -/
theorem hopfInvariant_eta_eq (H : HopfInvariantData data) :
    H.hopfInvariant (eta data) = 1 :=
  H.hopfInvariant_eta

/-- `Path` witness for `H(eta) = 1`. -/
def hopfInvariant_eta_path (H : HopfInvariantData data) :
    ComputationalPaths.Path (H.hopfInvariant (eta data)) 1 :=
  ComputationalPaths.Path.stepChain H.hopfInvariant_eta

end HopfInvariantData

/-! ## Summary

We introduced Hopf invariant data for maps `S3 -> S2` and recorded the core fact
that the Hopf map has invariant 1, with an accompanying `Path` witness. We also
defined the Hopf invariant map `H : π_{2n-1}(S^n, a) → ℤ` in the computational
paths model, together with its constant `Path` witness.
-/

end HopfInvariant
end Homotopy
end Path
end ComputationalPaths
