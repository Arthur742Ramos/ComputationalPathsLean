/-
# Mapping cylinder via computational paths

This module defines the mapping cylinder of a map `f : A → B` using the
computational pushout construction. The mapping cylinder is the pushout of
the cylinder `A × Interval` and `B` along `A`, where `A` includes into the
cylinder at the left endpoint of the interval.

## Key Results

- `Interval`: two-point interval type
- `Cylinder`: product `A × Interval`
- `MappingCylinder`: mapping cylinder as a pushout
- `MappingCylinder.inCylinder` and `MappingCylinder.inTarget`: canonical inclusions
- `MappingCylinder.bottom`, `MappingCylinder.top`: endpoint embeddings of `A`
- `MappingCylinder.glue`: path identifying the bottom with `f`

## References

- HoTT Book, Chapter 6 (mapping cylinders)
- Computational paths pushout construction
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Interval and cylinder -/

/-- The interval with two endpoints. -/
inductive Interval : Type u
  | /-- Left endpoint. -/ left : Interval
  | /-- Right endpoint. -/ right : Interval

/-- The cylinder over `A`, defined as `A × Interval`. -/
abbrev Cylinder (A : Type u) : Type u := A × Interval

/-! ## Mapping cylinder -/

variable {A B : Type u}

/-- The mapping cylinder of `f : A → B`. -/
def MappingCylinder (f : A → B) : Type u :=
  Pushout (Cylinder A) B A (fun a => (a, Interval.left)) f

namespace MappingCylinder

variable {A B : Type u} (f : A → B)

/-- Include the cylinder into the mapping cylinder. -/
def inCylinder : Cylinder A → MappingCylinder f :=
  Pushout.inl (A := Cylinder A) (B := B) (C := A)
    (f := fun a => (a, Interval.left)) (g := f)

/-- Include the target `B` into the mapping cylinder. -/
def inTarget : B → MappingCylinder f :=
  Pushout.inr (A := Cylinder A) (B := B) (C := A)
    (f := fun a => (a, Interval.left)) (g := f)

/-- The bottom embedding of `A` at the left endpoint. -/
def bottom (a : A) : MappingCylinder f :=
  inCylinder (f := f) (a, Interval.left)

/-- The top embedding of `A` at the right endpoint. -/
def top (a : A) : MappingCylinder f :=
  inCylinder (f := f) (a, Interval.right)

/-- The gluing path identifying `bottom a` with `f a` in the mapping cylinder. -/
def glue (a : A) :
    Path (bottom (f := f) a) (inTarget (f := f) (f a)) :=
  Pushout.glue (A := Cylinder A) (B := B) (C := A)
    (f := fun a => (a, Interval.left)) (g := f) a

end MappingCylinder

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
