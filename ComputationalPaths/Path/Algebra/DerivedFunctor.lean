/-
# Derived Functors via Computational Paths

This module packages minimal derived-functor interfaces for pointed sets in the
computational-paths setting. We model long exact sequences using 3-term chain
complexes and express functoriality/universality through `Path` witnesses.

## Key Definitions

- `LongExactSequence`: a 3-term long exact sequence with Path exactness.
- `DeltaFunctor`: sends short exact sequences to long exact sequences.
- `UniversalDeltaFunctor`: delta functor with a universality condition.
- `LeftDerivedFunctor`, `RightDerivedFunctor`: derived functors with resolutions.

## References

- Weibel, "An Introduction to Homological Algebra"
- Mac Lane, "Homology"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra

open HomologicalAlgebra

universe u

/-! ## Utility -/

/-- The one-point pointed set. -/
def unitPointed : PointedSet.{u} where
  carrier := PUnit
  zero := PUnit.unit

/-- The constant 3-term chain complex on the unit pointed set. -/
def unitComplex : ChainComplex3.{u} where
  C₂ := unitPointed
  C₁ := unitPointed
  C₀ := unitPointed
  d₂ := zeroHom unitPointed unitPointed
  d₁ := zeroHom unitPointed unitPointed
  dd_zero := fun _ => rfl

/-! ## Long exact sequences -/

/-- A 3-term long exact sequence with a connecting morphism and Path exactness. -/
structure LongExactSequence where
  /-- The underlying chain complex. -/
  complex : ChainComplex3.{u}
  /-- The connecting morphism C₀ → C₂. -/
  delta : PointedHom complex.C₀ complex.C₂
  /-- Exactness at C₁. -/
  exact₁ : ∀ x, Path (complex.d₁.toFun (complex.d₂.toFun x)) complex.C₀.zero
  /-- Exactness at C₀. -/
  exact₂ : ∀ x, Path (delta.toFun (complex.d₁.toFun x)) complex.C₂.zero

/-- The trivial long exact sequence on PUnit. -/
def trivialLongExact : LongExactSequence.{u} where
  complex := unitComplex
  delta := zeroHom unitPointed unitPointed
  exact₁ := fun _ => Path.refl _
  exact₂ := fun _ => Path.refl _

/-! ## Delta functors -/

/-- Delta functor data from short exact sequences to long exact sequences. -/
structure DeltaFunctor where
  /-- Object map on short exact sequences. -/
  mapObj : ShortExact.{u} → LongExactSequence.{u}

/-- Universality data for delta functors. -/
structure UniversalDeltaFunctor extends DeltaFunctor.{u} where
  /-- Universal comparison with any other delta functor. -/
  universal :
    ∀ (F : DeltaFunctor.{u}) (S : ShortExact.{u}),
      ChainMap3 (mapObj S).complex (F.mapObj S).complex

/-! ## Derived functors -/

/-- Left derived functor data with a chosen resolution. -/
structure LeftDerivedFunctor where
  /-- Underlying object map. -/
  obj : PointedSet.{u} → PointedSet.{u}
  /-- Resolution for each object. -/
  resolution : PointedSet.{u} → ChainComplex3.{u}
  /-- Augmentation from the resolution. -/
  augment : ∀ A, PointedHom (resolution A).C₀ (obj A)
  /-- Functoriality on morphisms. -/
  map : ∀ {A B}, PointedHom A B → ChainMap3 (resolution A) (resolution B)
  /-- Identity law. -/
  map_id : ∀ A, Path (map (PointedHom.id A)) (ChainMap3.id (resolution A))

/-- Right derived functor data with a chosen coresolution. -/
structure RightDerivedFunctor where
  /-- Underlying object map. -/
  obj : PointedSet.{u} → PointedSet.{u}
  /-- Coresolution for each object. -/
  coresolution : PointedSet.{u} → ChainComplex3.{u}
  /-- Coaugmentation into the coresolution. -/
  coaugment : ∀ A, PointedHom (obj A) (coresolution A).C₂
  /-- Functoriality on morphisms. -/
  map : ∀ {A B}, PointedHom A B → ChainMap3 (coresolution A) (coresolution B)
  /-- Identity law. -/
  map_id : ∀ A, Path (map (PointedHom.id A)) (ChainMap3.id (coresolution A))

/-! ## Trivial instances -/

/-- The trivial delta functor. -/
def DeltaFunctor.trivial : DeltaFunctor.{u} where
  mapObj := fun _ => trivialLongExact

/-- The trivial universal delta functor. -/
def UniversalDeltaFunctor.trivial : UniversalDeltaFunctor.{u} where
  mapObj := fun _ => trivialLongExact
  universal := fun F S =>
    { f₂ := zeroHom unitPointed (F.mapObj S).complex.C₂
      f₁ := zeroHom unitPointed (F.mapObj S).complex.C₁
      f₀ := zeroHom unitPointed (F.mapObj S).complex.C₀
      comm₂₁ := by intro x; simp [zeroHom, (F.mapObj S).complex.d₂.map_zero]
      comm₁₀ := by intro x; simp [zeroHom, (F.mapObj S).complex.d₁.map_zero] }

/-- The trivial left derived functor. -/
def LeftDerivedFunctor.trivial : LeftDerivedFunctor.{u} where
  obj := fun _ => unitPointed
  resolution := fun _ => unitComplex
  augment := fun _ => zeroHom unitPointed unitPointed
  map := fun _ => ChainMap3.id unitComplex
  map_id := fun _ => Path.stepChain rfl

/-- The trivial right derived functor. -/
def RightDerivedFunctor.trivial : RightDerivedFunctor.{u} where
  obj := fun _ => unitPointed
  coresolution := fun _ => unitComplex
  coaugment := fun _ => zeroHom unitPointed unitPointed
  map := fun _ => ChainMap3.id unitComplex
  map_id := fun _ => Path.stepChain rfl

/-! ## Basic properties (stubs) -/

theorem unitPointed_zero_path :
    Nonempty (Path unitPointed.zero PUnit.unit) := by
  sorry

theorem unitComplex_C₂_path :
    Nonempty (Path unitComplex.C₂ unitPointed) := by
  sorry

theorem unitComplex_C₁_path :
    Nonempty (Path unitComplex.C₁ unitPointed) := by
  sorry

theorem unitComplex_C₀_path :
    Nonempty (Path unitComplex.C₀ unitPointed) := by
  sorry

theorem trivialLongExact_complex_path :
    Nonempty (Path trivialLongExact.complex unitComplex) := by
  sorry

theorem trivialLongExact_delta_path :
    Nonempty (Path trivialLongExact.delta (zeroHom unitPointed unitPointed)) := by
  sorry

theorem trivialLongExact_exact₁_unit :
    Nonempty
      (Path (trivialLongExact.complex.d₁.toFun (trivialLongExact.complex.d₂.toFun PUnit.unit))
        trivialLongExact.complex.C₀.zero) := by
  sorry

theorem trivialLongExact_exact₂_unit :
    Nonempty
      (Path (trivialLongExact.delta.toFun (trivialLongExact.complex.d₁.toFun PUnit.unit))
        trivialLongExact.complex.C₂.zero) := by
  sorry

theorem deltaFunctor_trivial_mapObj (S : ShortExact.{u}) :
    Nonempty (Path (DeltaFunctor.trivial.mapObj S) trivialLongExact) := by
  sorry

theorem universalDeltaFunctor_trivial_mapObj (S : ShortExact.{u}) :
    Nonempty (Path (UniversalDeltaFunctor.trivial.mapObj S) trivialLongExact) := by
  sorry

theorem leftDerivedFunctor_trivial_obj (A : PointedSet.{u}) :
    Nonempty (Path (LeftDerivedFunctor.trivial.obj A) unitPointed) := by
  sorry

theorem leftDerivedFunctor_trivial_resolution (A : PointedSet.{u}) :
    Nonempty (Path (LeftDerivedFunctor.trivial.resolution A) unitComplex) := by
  sorry

theorem leftDerivedFunctor_trivial_map_natural
    (A B : PointedSet.{u}) (f : PointedHom A B) :
    Nonempty (Path (LeftDerivedFunctor.trivial.map f) (ChainMap3.id unitComplex)) := by
  sorry

theorem rightDerivedFunctor_trivial_obj (A : PointedSet.{u}) :
    Nonempty (Path (RightDerivedFunctor.trivial.obj A) unitPointed) := by
  sorry

theorem rightDerivedFunctor_trivial_map_natural
    (A B : PointedSet.{u}) (f : PointedHom A B) :
    Nonempty (Path (RightDerivedFunctor.trivial.map f) (ChainMap3.id unitComplex)) := by
  sorry

/-! ## Summary

We introduced long exact sequence data, delta functors with universality,
and minimal left/right derived functor interfaces equipped with trivial
instances.
-/

end Algebra
end Path
end ComputationalPaths
