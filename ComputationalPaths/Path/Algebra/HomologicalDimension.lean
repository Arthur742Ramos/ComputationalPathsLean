/-
# Homological Dimension for Path Chain Complexes

This module defines a lightweight notion of homological dimension for the
three-term chain complexes in `HomologicalAlgebra`. Dimension bounds are
witnessed by computational paths, so truncation data is explicit.

## Key Definitions

- `IsZeroHom`: Path-based zero map predicate.
- `HomologicalDimension`: dimension bounds for `ChainComplex3`.
- `trivialComplex`: the zero complex as a dimension-0 example.

## References

- Weibel, "An Introduction to Homological Algebra"
- Hatcher, "Algebraic Topology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u

/-! ## Zero maps -/

/-- A pointed hom is zero if every element is path-equal to the basepoint. -/
def IsZeroHom {A B : PointedSet.{u}} (f : PointedHom A B) : Type u :=
  ∀ x : A.carrier, Path (f.toFun x) B.zero

/-- The constant zero map is path-zero. -/
def zeroHomIsZero {A B : PointedSet.{u}} : IsZeroHom (zeroHom A B) := by
  intro x
  exact Path.ofEq rfl

/-! ## Homological dimension for 3-term complexes -/

/-- Homological dimension bounds for a 3-term chain complex. -/
inductive HomologicalDimension (C : ChainComplex3.{u}) : Nat → Type u
  /-- Concentrated in degree 0 (both differentials are zero). -/
  | dim0 : IsZeroHom C.d₁ → IsZeroHom C.d₂ → HomologicalDimension C 0
  /-- Concentrated in degrees 0 and 1 (top differential is zero). -/
  | dim1 : IsZeroHom C.d₂ → HomologicalDimension C 1
  /-- Default bound for a 3-term complex. -/
  | dim2 : HomologicalDimension C 2

/-- Dimension 0 implies dimension 1 by forgetting the lower differential. -/
def dim1OfDim0 {C : ChainComplex3.{u}} :
    HomologicalDimension C 0 → HomologicalDimension C 1 := by
  intro h
  cases h with
  | dim0 _ h₂ => exact HomologicalDimension.dim1 h₂

/-- Dimension 1 implies dimension 2 by forgetting the truncation data. -/
def dim2OfDim1 {C : ChainComplex3.{u}} :
    HomologicalDimension C 1 → HomologicalDimension C 2 := by
  intro _
  exact HomologicalDimension.dim2

/-! ## Trivial complex example -/

private def trivialPointed : PointedSet.{u} where
  carrier := PUnit
  zero := PUnit.unit

/-- The zero 3-term chain complex on `PUnit`. -/
def trivialComplex : ChainComplex3.{u} where
  C₂ := trivialPointed
  C₁ := trivialPointed
  C₀ := trivialPointed
  d₂ := zeroHom _ _
  d₁ := zeroHom _ _
  dd_zero := by
    intro _
    rfl

/-- The trivial complex has homological dimension 0. -/
def trivialDimension0 : HomologicalDimension trivialComplex 0 :=
  HomologicalDimension.dim0 zeroHomIsZero zeroHomIsZero

/-! ## Summary -/

/-!
We defined a Path-valued zero-map predicate and used it to express
homological dimension bounds for three-term chain complexes, with a
trivial example of dimension 0.
-/

end Algebra
end Path
end ComputationalPaths
