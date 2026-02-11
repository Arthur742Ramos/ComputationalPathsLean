/-
# Homotopical Algebra Interfaces

This module records lightweight homotopical algebra data for model categories of
computational paths. We package Quillen model categories, homotopy categories,
derived functors, Quillen equivalences, and transferred model structures using
`Path`-based witnesses, with axioms recorded as data (no new axioms).

## Key Results

- `QuillenModelCategory`: alias for the model category structure.
- `Ho`: homotopy category of a model category.
- `HoFunctor`, `LeftDerivedFunctor`, `RightDerivedFunctor`: derived functor data.
- `QuillenEquivalence`: Quillen equivalence data.
- `TransferredModelStructure`: transferred model structure data.

## References

- Quillen, *Homotopical Algebra*
- Hovey, *Model Categories*
- Hirschhorn, *Model Categories and Their Localizations*
-/

import ComputationalPaths.Path.ModelCategory
import ComputationalPaths.Path.Homotopy.QuillenAdjunction
import ComputationalPaths.Path.Homotopy.LocalizationCategory

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HomotopicalAlgebra

universe u v

open Homotopy.QuillenAdjunction
open Homotopy.LocalizationCategory

/-! ## Quillen model categories -/

/-- A Quillen model category on computational paths. -/
abbrev QuillenModelCategory (A : Type u) : Type u :=
  ModelCategory A

/-! ## Homotopy category Ho(C) -/

/-- The homotopy category Ho(C) of a model category, via path localization. -/
abbrev Ho {A : Type u} (_M : ModelCategory A) : StrictCategory A :=
  homotopyCategory A

/-! ## Homotopy-category functors -/

/-- A functor between homotopy categories with a fixed object map. -/
structure HoFunctor (A : Type u) (B : Type v) (F : A → B) where
  /-- Action on localized paths. -/
  map : {a b : A} → PathRwQuot A a b → PathRwQuot B (F a) (F b)
  /-- Preservation of identities. -/
  map_id : ∀ a,
    Path (map (PathRwQuot.refl (A := A) a))
      (PathRwQuot.refl (A := B) (F a))
  /-- Preservation of composition. -/
  map_comp : ∀ {a b c : A} (p : PathRwQuot A a b) (q : PathRwQuot A b c),
    Path (map (PathRwQuot.trans p q))
      (PathRwQuot.trans (map p) (map q))

namespace HoFunctor

/-- Identity functor on a homotopy category. -/
def id (A : Type u) : HoFunctor A A (fun x => x) where
  map := fun p => p
  map_id := fun _ => Path.refl _
  map_comp := fun _ _ => Path.refl _

end HoFunctor

/-! ## Derived functor data -/

/-- Left derived functor data for a model functor. -/
structure LeftDerivedFunctor {A : Type u} {B : Type v}
    (M : ModelCategory A) (N : ModelCategory B) (F : ModelFunctor M N) where
  /-- The induced functor on Ho(C). -/
  hoFunctor : HoFunctor A B F.obj
  /-- Placeholder for the derived functor laws. -/
  derived : True

/-- Right derived functor data for a model functor. -/
structure RightDerivedFunctor {A : Type u} {B : Type v}
    (M : ModelCategory A) (N : ModelCategory B) (F : ModelFunctor M N) where
  /-- The induced functor on Ho(C). -/
  hoFunctor : HoFunctor A B F.obj
  /-- Placeholder for the derived functor laws. -/
  derived : True

/-- Derived adjunction data induced by a Quillen adjunction. -/
structure DerivedAdjunction {A : Type u} {B : Type v}
    (M : ModelCategory A) (N : ModelCategory B) (adj : QuillenAdjunction M N) where
  /-- Left derived functor. -/
  leftDerived : HoFunctor A B adj.left.obj
  /-- Right derived functor. -/
  rightDerived : HoFunctor B A adj.right.obj
  /-- Placeholder for the derived adjunction laws. -/
  derived_adjunction : True

/-! ## Quillen equivalences -/

/-- A Quillen equivalence between model categories. -/
structure QuillenEquivalence {A : Type u} {B : Type v}
    (M : ModelCategory A) (N : ModelCategory B) where
  /-- Underlying Quillen adjunction. -/
  adjunction : QuillenAdjunction M N
  /-- Placeholder for the equivalence on homotopy categories. -/
  derived_equivalence : True

/-- Identity Quillen equivalence. -/
def identityQuillenEquivalence {A : Type u} (M : ModelCategory A) :
    QuillenEquivalence M M where
  adjunction := identityQuillenAdjunction (M := M)
  derived_equivalence := trivial

/-! ## Transferred model structures -/

/-- Data for a transferred model structure along an adjunction. -/
structure TransferredModelStructure (A : Type u) (B : Type v) where
  /-- The source model category. -/
  source : ModelCategory A
  /-- The target model category. -/
  target : ModelCategory B
  /-- The left adjoint functor. -/
  left : ModelFunctor source target
  /-- The right adjoint functor. -/
  right : ModelFunctor target source
  /-- The underlying adjunction data. -/
  adjunction : ModelAdjunction source target left right
  /-- Placeholder for transfer conditions. -/
  transfer : True

/-! ## Summary -/

/-!
We introduced a compact homotopical algebra interface for computational paths,
including Quillen model categories, homotopy categories, derived functor data,
Quillen equivalences, and transferred model structures.
-/

end HomotopicalAlgebra
end Algebra
end Path
end ComputationalPaths
