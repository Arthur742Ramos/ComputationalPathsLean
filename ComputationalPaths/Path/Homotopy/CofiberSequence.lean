/- 
# Cofiber Sequences for Computational Paths

This module defines mapping cones (cofibers) using computational pushouts and
packages the Puppe sequence `A → B → Cofiber f → ΣA`. We also record the
composite-trivial exactness statements for the cofiber sequence.

## Key Results

- `MappingCone` / `Cofiber`: the cofiber of `f : A → B`
- `cofiberToSuspension`: canonical map `Cofiber f → ΣA`
- `puppeSequence`: the Puppe sequence data
- `cofiberSequence_exact`: composite maps are null

## References

- HoTT Book, Chapter 8 (cofiber sequences and Puppe constructions)
- Computational paths pushout constructions
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace CofiberSequence

open CompPath
open SuspensionLoop

universe u

variable {A B : Type u}

/-! ## Mapping Cone (Cofiber) -/

/-- The mapping cone (cofiber) of `f : A → B` as a pushout of `B` and `1` along `A`. -/
def MappingCone (f : A → B) : Type u :=
  Pushout B PUnit' A f (fun _ => PUnit'.unit)

/-- Alias for the mapping cone. -/
abbrev Cofiber (f : A → B) : Type u := MappingCone f

namespace Cofiber

variable (f : A → B)

/-- Inclusion of `B` into the cofiber. -/
def inl (b : B) : Cofiber f :=
  Pushout.inl (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) b

/-- The basepoint of the cofiber (the cone point). -/
def basepoint : Cofiber f :=
  Pushout.inr (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- The gluing path identifying `f a` with the cone point. -/
def glue (a : A) :
    Path (inl (f := f) (f a)) (basepoint (f := f)) :=
  Pushout.glue (A := B) (B := PUnit') (C := A) (f := f) (g := fun _ => PUnit'.unit) a

end Cofiber

/-! ## Puppe sequence maps -/

/-- Canonical map `B → Cofiber f`. -/
def cofiberInclusion (f : A → B) : B → Cofiber f :=
  Cofiber.inl (f := f)

/-- Canonical map `Cofiber f → ΣA`, sending `B` to north and the cone point to south. -/
def cofiberToSuspension (f : A → B) : Cofiber f → Suspension A :=
  Quot.lift
    (fun s =>
      match s with
      | Sum.inl _ => Suspension.north (X := A)
      | Sum.inr _ => Suspension.south (X := A))
    (by
      intro x y h
      cases h with
      | glue a =>
          exact
            Quot.sound
              (PushoutCompPathRel.glue
                (A := PUnit') (B := PUnit') (C := A)
                (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) a))

/-- The Puppe sequence data for a map `f : A → B`. -/
structure PuppeSequence (A B : Type u) (f : A → B) where
  /-- The inclusion `B → Cofiber f`. -/
  toCofiber : B → Cofiber f
  /-- The connecting map `Cofiber f → ΣA`. -/
  toSuspension : Cofiber f → Suspension A

/-- The Puppe sequence `A → B → Cofiber f → ΣA`. -/
def puppeSequence (f : A → B) : PuppeSequence A B f where
  toCofiber := cofiberInclusion (A := A) (B := B) f
  toSuspension := cofiberToSuspension (A := A) (B := B) f

/-! ## Exactness (composite is trivial) -/

/-- Exactness data for the cofiber sequence: composites are null. -/
structure CofiberSequenceExact (A B : Type u) (f : A → B) where
  /-- The composite `A → B → Cofiber f` is null via the glue paths. -/
  exact_left :
    ∀ a,
      Path
        (cofiberInclusion (A := A) (B := B) f (f a))
        (Cofiber.basepoint (A := A) (B := B) (f := f))
  /-- The composite `B → Cofiber f → ΣA` is the constant map to north. -/
  exact_right :
    ∀ b,
      Path
        (cofiberToSuspension (A := A) (B := B) f
          (cofiberInclusion (A := A) (B := B) f b))
        (Suspension.north (X := A))

/-- The cofiber sequence attached to `f` is exact in the composite-trivial sense. -/
def cofiberSequence_exact (f : A → B) : CofiberSequenceExact A B f := by
  refine { exact_left := ?_, exact_right := ?_ }
  · intro a
    exact Cofiber.glue (A := A) (B := B) (f := f) a
  · intro b
    change Path (Suspension.north (X := A)) (Suspension.north (X := A))
    exact Path.refl _

/-! ## Summary -/

end CofiberSequence
end Homotopy
end Path
end ComputationalPaths
