/-
# Derived Categories and Perverse Sheaves

This module introduces lightweight data structures for derived categories,
triangulated structure, derived functors, t-structures, and perverse sheaves
in the computational paths setting. The emphasis is on compositional data
needed by later constructions rather than full formalization.

## Key Results

- `DerivedCategory`: triangulated category with a class of quasi-isomorphisms
- `DerivedFunctor`: exact functor preserving quasi-isomorphisms
- `TStructure` and `TStructure.heart`: t-structures and their hearts
- `PerverseSheaf`: objects of the heart with a perversity function

## References

- Gelfand-Manin, "Methods of Homological Algebra"
- Beilinson-Bernstein-Deligne, "Perverse Sheaves"
- Kashiwara-Schapira, "Sheaves on Manifolds"
-/

import ComputationalPaths.Path.Homotopy.StableCategory
import ComputationalPaths.Path.Category.LocalizationPaths
import ComputationalPaths.Path.Homotopy.GeneralizedHomology

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace DerivedCategory

open Homotopy
open Homotopy.StableCategory
open Category.LocalizationPaths
open Homotopy.GeneralizedHomology
open PointedMapCategory

universe u v

/-! ## Derived categories -/

/-- A derived category: a triangulated category with a class of quasi-isomorphisms. -/
structure DerivedCategory where
  /-- The underlying triangulated category. -/
  triangulated : TriangulatedCategory.{u}
  /-- Predicate selecting quasi-isomorphisms. -/
  quasiIso :
    ∀ {X Y : triangulated.cat.Obj}, triangulated.cat.Hom X Y → Prop

/-- The underlying pre-additive category of a derived category. -/
def DerivedCategory.cat (D : DerivedCategory.{u}) :
    PreAdditiveCategory.{u} :=
  D.triangulated.cat

/-- The shift functor of a derived category. -/
def DerivedCategory.shift (D : DerivedCategory.{u}) :
    ShiftFunctor D.triangulated.cat :=
  D.triangulated.shift

/-! ## Derived functors -/

/-- A derived functor: an exact functor preserving quasi-isomorphisms. -/
structure DerivedFunctor (D E : DerivedCategory.{u}) where
  /-- The underlying exact functor. -/
  exact : ExactFunctor D.triangulated E.triangulated
  /-- Quasi-isomorphisms are preserved. -/
  preserves_quasiIso :
    ∀ {X Y : D.triangulated.cat.Obj} (f : D.triangulated.cat.Hom X Y),
      D.quasiIso f → E.quasiIso (exact.mapHom f)

/-- Identity derived functor. -/
def DerivedFunctor.id (D : DerivedCategory.{u}) : DerivedFunctor D D where
  exact := ExactFunctor.id D.triangulated
  preserves_quasiIso := by
    intro _ _ _ h
    simpa using h

/-- Left derived functor (data-level alias). -/
def leftDerived {D E : DerivedCategory.{u}} (F : DerivedFunctor D E) :
    DerivedFunctor D E :=
  F

/-- Right derived functor (data-level alias). -/
def rightDerived {D E : DerivedCategory.{u}} (F : DerivedFunctor D E) :
    DerivedFunctor D E :=
  F

/-! ## T-structures -/

/-- A t-structure on a derived category. -/
structure TStructure (D : DerivedCategory.{u}) where
  /-- Non-positive part. -/
  le : D.triangulated.cat.Obj → Prop
  /-- Non-negative part. -/
  ge : D.triangulated.cat.Obj → Prop
  /-- Closure of the non-positive part under shift. -/
  shift_closed_le :
    ∀ X, le X → le (D.triangulated.shift.shiftObj X)
  /-- Closure of the non-negative part under shift. -/
  shift_closed_ge :
    ∀ X, ge X → ge (D.triangulated.shift.shiftObj X)
  /-- Orthogonality between the two halves (recorded as data). -/
  orthogonal : ∀ {X Y}, le X → ge Y → True
  /-- Left truncation. -/
  truncLeft : D.triangulated.cat.Obj → D.triangulated.cat.Obj
  /-- Right truncation. -/
  truncRight : D.triangulated.cat.Obj → D.triangulated.cat.Obj
  /-- Left truncation lands in the non-positive part. -/
  truncLeft_le : ∀ X, le (truncLeft X)
  /-- Right truncation lands in the non-negative part. -/
  truncRight_ge : ∀ X, ge (truncRight X)

/-- The heart of a t-structure. -/
def TStructure.heart {D : DerivedCategory.{u}} (T : TStructure D) : Type u :=
  { X : D.triangulated.cat.Obj // T.le X ∧ T.ge X }

/-- The trivial t-structure with all objects in both halves. -/
def TStructure.trivial (D : DerivedCategory.{u}) : TStructure D where
  le := fun _ => True
  ge := fun _ => True
  shift_closed_le := by
    intro _ _
    trivial
  shift_closed_ge := by
    intro _ _
    trivial
  orthogonal := by
    intro _ _ _ _
    trivial
  truncLeft := fun X => X
  truncRight := fun X => X
  truncLeft_le := by
    intro _
    trivial
  truncRight_ge := by
    intro _
    trivial

/-! ## Perverse sheaves -/

/-- A perversity function (toy model). -/
def Perversity : Type := Nat → Int

/-- A perverse sheaf: an object of the heart with a perversity function. -/
structure PerverseSheaf {D : DerivedCategory.{u}} (T : TStructure D) where
  /-- Underlying object in the heart. -/
  heartObj : T.heart
  /-- Perversity function. -/
  perversity : Perversity

/-- The underlying object of a perverse sheaf. -/
def PerverseSheaf.object {D : DerivedCategory.{u}} {T : TStructure D}
    (P : PerverseSheaf T) : D.triangulated.cat.Obj :=
  P.heartObj.val

/-- The underlying object lies in the heart. -/
theorem perverseSheaf_in_heart {D : DerivedCategory.{u}} {T : TStructure D}
    (P : PerverseSheaf T) :
    T.le P.object ∧ T.ge P.object :=
  P.heartObj.property

/-! ## Cross-module path dependencies -/

/-- Derived localization composition coherence inherited from
`Category/LocalizationPaths`. -/
def derived_localization_comp_path
    {C : Type u} (L : LeftExactLocalization C)
    {a b c : C} (p : Path a b) (q : Path b c) :
    RwEq (L.preserves_product (Path.trans p q))
         (Path.trans (L.preserves_product p) (L.preserves_product q)) :=
  rweq_trans (left_exact_preserves_comp_rweq L p q) (RwEq.refl _)

/-- Derived homology functor composition coherence inherited from
`Homology/GeneralizedHomology`. -/
def derived_homology_comp_path
    (E : GeneralizedHomologyTheory.{u, v})
    {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    Path (E.map (PtdMap.comp g f) n) ((E.map g n) ∘ (E.map f n)) :=
  Path.trans (GeneralizedHomologyTheory.map_comp_path E g f n) (Path.refl _)

/-! ## Summary

We introduced data-level definitions for derived categories, derived functors,
t-structures, and perverse sheaves, all grounded in the existing triangulated
category infrastructure.
-/

end DerivedCategory
end Algebra
end Path
end ComputationalPaths
