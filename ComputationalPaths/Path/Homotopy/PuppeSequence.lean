/- 
# Puppe Sequence for Computational Paths

This module packages the Puppe sequence associated to a map `f : A → B` using
the cofiber construction already available in the computational-paths library.

## Key Results

- `PuppeSequence`: the sequence data
- `puppeSequence`: the Puppe sequence `A → B → Cofiber f → Suspension A`
- `PuppeSequenceExact`: composite-trivial exactness data
- `puppe_exact_left`, `puppe_exact_right`: explicit Path witnesses

## References

- HoTT Book, Chapter 8 (cofiber sequences and Puppe constructions)
-/

import ComputationalPaths.Path.Homotopy.CofiberSequence

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace PuppeSequence

open CofiberSequence
open SuspensionLoop

universe u

variable {A B : Type u}

/-! ## Puppe sequence data -/

/-- Alias for the Puppe sequence data coming from the cofiber construction. -/
abbrev PuppeSequence (A B : Type u) (f : A → B) : Type u :=
  CofiberSequence.PuppeSequence A B f

/-- The Puppe sequence `A → B → Cofiber f → Suspension A`. -/
def puppeSequence (f : A → B) : PuppeSequence A B f :=
  CofiberSequence.puppeSequence (A := A) (B := B) f

/-! ## Exactness (composite is trivial) -/

/-- Alias for the composite-trivial exactness data of the Puppe sequence. -/
abbrev PuppeSequenceExact (A B : Type u) (f : A → B) : Type u :=
  CofiberSequence.CofiberSequenceExact A B f

/-- Exactness data for the Puppe sequence: composites are null. -/
def puppeSequence_exact (f : A → B) : PuppeSequenceExact A B f :=
  CofiberSequence.cofiberSequence_exact (A := A) (B := B) f

/-- The composite `A → B → Cofiber f` is null via the glue paths. -/
def puppe_exact_left (f : A → B) (a : A) :
    Path
      (cofiberInclusion (A := A) (B := B) f (f a))
      (Cofiber.basepoint (A := A) (B := B) (f := f)) :=
  (puppeSequence_exact (A := A) (B := B) f).exact_left a

/-- The composite `B → Cofiber f → Suspension A` is constant at north. -/
def puppe_exact_right (f : A → B) (b : B) :
    Path
      (cofiberToSuspension (A := A) (B := B) f
        (cofiberInclusion (A := A) (B := B) f b))
      (Suspension.north (X := A)) :=
  (puppeSequence_exact (A := A) (B := B) f).exact_right b

/-! ## Summary

We packaged the Puppe sequence for a map `f : A → B` using the existing cofiber
construction and recorded the composite-triviality paths.
-/

end PuppeSequence
end Homotopy
end Path
end ComputationalPaths
