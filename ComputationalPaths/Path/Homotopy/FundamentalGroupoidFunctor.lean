/-
# Fundamental Groupoid Functor

This module packages the fundamental groupoid as a functor. We record the
groupoid category whose objects are points and morphisms are path classes, and
we show that functions induce functors between these groupoids.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `FundamentalGroupoidCategory` | The strict groupoid with points as objects and path classes as morphisms |
| `fundamentalGroupoid_isGroupoid` | The underlying strict category is a groupoid |
| `FundamentalGroupoidFunctor` | Functors between fundamental groupoids |
| `fundamentalGroupoidFunctor` | The functor induced by a function |
| `fundamentalGroupoidMap_idFun` | Identity functions act trivially on morphisms |
| `fundamentalGroupoidMap_compFun` | Composition of functions composes morphism maps |

## References

- HoTT Book, Chapter 2
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoid

namespace ComputationalPaths
namespace Path

universe u

/-! ## Fundamental groupoid category -/

section FundamentalGroupoidCategory

variable (A : Type u)

/-- The fundamental groupoid category on A.

Objects are points of A and morphisms are path equivalence classes. -/
noncomputable abbrev FundamentalGroupoidCategory : StrictGroupoid A := FundamentalGroupoid A

/-- The fundamental groupoid category is a groupoid in the categorical sense. -/
theorem fundamentalGroupoid_isGroupoid :
    StrictCategory.IsGroupoid ((FundamentalGroupoid A).toStrictCategory) := by
  exact StrictGroupoid.toStrictCategory_isGroupoid (A := A)
    (G := FundamentalGroupoid A)

end FundamentalGroupoidCategory

/-! ## Functors between fundamental groupoids -/

/-- A functor between fundamental groupoids. -/
structure FundamentalGroupoidFunctor (A : Type u) (B : Type u) where
  /-- Action on objects. -/
  obj : A → B
  /-- Action on morphisms (path classes). -/
  map : {a b : A} →
    FundamentalGroupoid.Hom A a b →
    FundamentalGroupoid.Hom B (obj a) (obj b)
  /-- Preservation of identity morphisms. -/
  map_id : ∀ a, map (FundamentalGroupoid.id' A a) =
    FundamentalGroupoid.id' B (obj a)
  /-- Preservation of composition. -/
  map_comp :
    ∀ {a b c : A} (p : FundamentalGroupoid.Hom A a b)
      (q : FundamentalGroupoid.Hom A b c),
      map (FundamentalGroupoid.comp' A p q) =
        FundamentalGroupoid.comp' B (map p) (map q)

/-! ## Functor induced by a function -/

section FundamentalGroupoidFunctoriality

variable {A : Type u} {B : Type u}

/-- A function induces a functor between fundamental groupoids. -/
noncomputable def fundamentalGroupoidFunctor (f : A → B) : FundamentalGroupoidFunctor A B where
  obj := f
  map := fun p => fundamentalGroupoidMap f p
  map_id := by
    intro a
    exact fundamentalGroupoidMap_id (A := A) (B := B) f a
  map_comp := by
    intro a b c p q
    exact fundamentalGroupoidMap_comp (A := A) (B := B) f p q

/-- Identity functions act trivially on morphisms in the fundamental groupoid. -/
theorem fundamentalGroupoidMap_idFun (A : Type u) {a b : A}
    (p : FundamentalGroupoid.Hom A a b) :
    fundamentalGroupoidMap (A := A) (B := A) id p = p := by
  simp [fundamentalGroupoidMap]

/-- Composition of functions composes the induced morphism maps. -/
theorem fundamentalGroupoidMap_compFun' {A : Type u} {B : Type u} {C : Type u}
    (f : A → B) (g : B → C) {a a' : A}
    (p : FundamentalGroupoid.Hom A a a') :
    fundamentalGroupoidMap g (fundamentalGroupoidMap f p) =
      fundamentalGroupoidMap (Function.comp g f) p := by
  simp [fundamentalGroupoidMap]

end FundamentalGroupoidFunctoriality

namespace FundamentalGroupoidFunctor

variable {A : Type u} {B : Type u} {C : Type u}

/-- The identity functor on the fundamental groupoid. -/
noncomputable def id (A : Type u) : FundamentalGroupoidFunctor A A :=
  fundamentalGroupoidFunctor (A := A) (B := A) _root_.id

/-- Composition of fundamental groupoid functors. -/
noncomputable def comp (F : FundamentalGroupoidFunctor A B)
    (G : FundamentalGroupoidFunctor B C) : FundamentalGroupoidFunctor A C where
  obj := fun a => G.obj (F.obj a)
  map := fun p => G.map (F.map p)
  map_id := by
    intro a
    calc
      G.map (F.map (FundamentalGroupoid.id' A a)) =
          G.map (FundamentalGroupoid.id' B (F.obj a)) := by
            rw [F.map_id]
      _ = FundamentalGroupoid.id' C (G.obj (F.obj a)) := by
            rw [G.map_id]
  map_comp := by
    intro a b c p q
    calc
      G.map (F.map (FundamentalGroupoid.comp' A p q)) =
          G.map (FundamentalGroupoid.comp' B (F.map p) (F.map q)) := by
            rw [F.map_comp]
      _ = FundamentalGroupoid.comp' C (G.map (F.map p)) (G.map (F.map q)) := by
            rw [G.map_comp]

end FundamentalGroupoidFunctor

/-! ## Summary

1. The fundamental groupoid category has points as objects and path classes as
   morphisms, and it is a strict groupoid.
2. Functors between fundamental groupoids preserve identity and composition.
3. Functions between types induce functors on fundamental groupoids.
-/

end Path
end ComputationalPaths
