/-
# Hopf invariant for the Hopf map

This module packages a Hopf invariant assignment for maps `S3 -> S2` and records
that the Hopf map `eta` has invariant 1. The key equality is available both as
an `Eq` proof and as a computational `Path` witness.

## Key Results

- `HopfInvariantData`: data for a Hopf invariant assignment on `S3 -> S2`
- `hopfInvariant_eta_eq`: H(eta) = 1
- `hopfInvariant_eta_path`: `Path` witness for H(eta) = 1

## References

- Hatcher, *Algebraic Topology*, Section 4F
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HopfFibration

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HopfInvariant

open HopfFibration

universe u

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
  ComputationalPaths.Path.ofEq H.hopfInvariant_eta

end HopfInvariantData

/-! ## Summary

We introduced Hopf invariant data for maps `S3 -> S2` and recorded the core fact
that the Hopf map has invariant 1, with an accompanying `Path` witness.
-/

end HopfInvariant
end Homotopy
end Path
end ComputationalPaths
