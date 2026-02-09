/-
# Universal Property of Free Groups (Mathlib)

This module re-exports Mathlib's universal property of free groups and records
its specialization to the fundamental group `π₁(A, a)` from computational paths.

## Key Results

- `freeGroupUniversal`: equivalence between generator maps and homomorphisms.
- `freeGroupUniversal_unique`: uniqueness of the induced homomorphism.
- `piOneFreeGroupLift`: free-group map into `π₁(A, a)`.

## References

- Mathlib: `GroupTheory/FreeGroup/Basic`
- Hatcher, *Algebraic Topology*, Section 1.2
-/

import Mathlib/GroupTheory/FreeGroup
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace FreeGroupUniversal

universe u v

/-! ## Universal property of free groups -/

section UniversalProperty

variable {α : Type u} {G : Type v} [Group G]

/-- The universal property of the free group on `α`, packaged as an equivalence. -/
abbrev freeGroupUniversal : (α → G) ≃ (_root_.FreeGroup α →* G) :=
  _root_.FreeGroup.lift

/-- The universal lift agrees with the generator map on `FreeGroup.of`. -/
@[simp] theorem freeGroupUniversal_apply_of (f : α → G) (a : α) :
    freeGroupUniversal (α := α) (G := G) f (_root_.FreeGroup.of a) = f a := by
  simpa using (_root_.FreeGroup.lift_apply_of (f := f) (x := a))

/-- Uniqueness: a homomorphism out of a free group is determined by its values on generators. -/
theorem freeGroupUniversal_unique (f : α → G) (g : _root_.FreeGroup α →* G)
    (hg : ∀ a, g (_root_.FreeGroup.of a) = f a) :
    g = freeGroupUniversal (α := α) (G := G) f := by
  ext x
  exact _root_.FreeGroup.lift_unique (f := f) g hg

end UniversalProperty

/-! ## Application to fundamental groups -/

section PiOneApplication

variable {A : Type u} {a : A}

local instance : Group (π₁(A, a)) where
  mul := PiOne.mul
  mul_assoc := PiOne.mul_assoc
  one := PiOne.id
  one_mul := PiOne.id_mul
  mul_one := PiOne.mul_id
  inv := PiOne.inv
  inv_mul_cancel := PiOne.mul_left_inv

/-- The universal homomorphism from the free group on `ι` into `π₁(A, a)`. -/
def piOneFreeGroupLift {ι : Type v} (f : ι → π₁(A, a)) :
    _root_.FreeGroup ι →* π₁(A, a) :=
  _root_.FreeGroup.lift f

/-- The free-group lift to `π₁(A, a)` agrees with the generator map. -/
@[simp] theorem piOneFreeGroupLift_of {ι : Type v} (f : ι → π₁(A, a)) (i : ι) :
    piOneFreeGroupLift (A := A) (a := a) f (_root_.FreeGroup.of i) = f i := by
  simpa using (_root_.FreeGroup.lift_apply_of (f := f) (x := i))

/-- Uniqueness of the free-group lift into `π₁(A, a)`. -/
theorem piOneFreeGroupLift_unique {ι : Type v} (f : ι → π₁(A, a))
    (g : _root_.FreeGroup ι →* π₁(A, a))
    (hg : ∀ i, g (_root_.FreeGroup.of i) = f i) :
    g = piOneFreeGroupLift (A := A) (a := a) f := by
  ext x
  exact _root_.FreeGroup.lift_unique (f := f) g hg

end PiOneApplication

/-! ## Summary

We packaged Mathlib's universal property for free groups and recorded the
specialized lift into the computational-path fundamental group `π₁(A, a)`.
-/

end FreeGroupUniversal
end Algebra
end Path
end ComputationalPaths
