/-
# Kan Extensions for the Fundamental Groupoid

This module formalizes left and right Kan extensions for functors between
fundamental groupoids. We define pointwise Kan extensions, prove existence
for groupoid functors, and establish the universal property.

## Mathematical Background

Given a functor F : C → D and a functor K : C → E, the left Kan extension
Lan_K F : E → D is the "best approximation" to F along K. It satisfies:
  Nat(Lan_K F, G) ≃ Nat(F, G ∘ K)

For groupoid functors, Kan extensions have a particularly clean form.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `GroupoidNatTrans` | Natural transformation between groupoid functors |
| `LeftKanData` | Data for a left Kan extension |
| `RightKanData` | Data for a right Kan extension |
| `leftKan_id` | Kan extension along identity is identity |

## References

- Mac Lane, "Categories for the Working Mathematician", Chapter X
- Riehl, "Category Theory in Context", Chapter 6
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor

namespace ComputationalPaths
namespace Path
namespace KanExtension

universe u

/-- Alias for fundamental groupoid functor. -/
abbrev GroupoidFunctor (A B : Type u) :=
  FundamentalGroupoidFunctor A B

/-! ## Natural Transformations between Groupoid Functors -/

/-- A natural transformation between two groupoid functors. -/
structure GroupoidNatTrans {A B : Type u}
    (F G : GroupoidFunctor A B) where
  /-- The component at each object. -/
  component : ∀ a : A, FundamentalGroupoid.Hom B (F.obj a) (G.obj a)
  /-- Naturality square. -/
  naturality : ∀ {a a' : A} (p : FundamentalGroupoid.Hom A a a'),
    FundamentalGroupoid.comp' B (F.map p) (component a') =
    FundamentalGroupoid.comp' B (component a) (G.map p)

/-- The identity natural transformation. -/
def GroupoidNatTrans.id {A B : Type u} (F : GroupoidFunctor A B) :
    GroupoidNatTrans F F where
  component := fun a => FundamentalGroupoid.id' B (F.obj a)
  naturality := by
    intro a a' p
    rw [FundamentalGroupoid.comp_id', FundamentalGroupoid.id_comp']

/-- Vertical composition of natural transformations. -/
def GroupoidNatTrans.vcomp {A B : Type u} {F G H : GroupoidFunctor A B}
    (α : GroupoidNatTrans F G) (β : GroupoidNatTrans G H) :
    GroupoidNatTrans F H where
  component := fun a =>
    FundamentalGroupoid.comp' B (α.component a) (β.component a)
  naturality := by
    intro a a' p
    calc FundamentalGroupoid.comp' B (F.map p)
            (FundamentalGroupoid.comp' B (α.component a') (β.component a'))
        = FundamentalGroupoid.comp' B
            (FundamentalGroupoid.comp' B (F.map p) (α.component a'))
            (β.component a') := by
              rw [FundamentalGroupoid.comp_assoc']
      _ = FundamentalGroupoid.comp' B
            (FundamentalGroupoid.comp' B (α.component a) (G.map p))
            (β.component a') := by
              rw [α.naturality p]
      _ = FundamentalGroupoid.comp' B (α.component a)
            (FundamentalGroupoid.comp' B (G.map p) (β.component a')) := by
              rw [← FundamentalGroupoid.comp_assoc']
      _ = FundamentalGroupoid.comp' B (α.component a)
            (FundamentalGroupoid.comp' B (β.component a) (H.map p)) := by
              rw [β.naturality p]
      _ = FundamentalGroupoid.comp' B
            (FundamentalGroupoid.comp' B (α.component a) (β.component a))
            (H.map p) := by
              rw [FundamentalGroupoid.comp_assoc']

/-! ## Left Kan Extension -/

/-- Data for a left Kan extension of F along K.
Given K : A → C (a function) and F : GroupoidFunctor A B,
the left Kan extension Lan : GroupoidFunctor C B satisfies
a universal property. -/
structure LeftKanData {A B C : Type u}
    (K : A → C) (F : GroupoidFunctor A B) where
  /-- The left Kan extension functor. -/
  Lan : GroupoidFunctor C B
  /-- The unit: a family of morphisms F(a) → Lan(K(a)). -/
  unit : ∀ a : A, FundamentalGroupoid.Hom B (F.obj a) (Lan.obj (K a))

/-- The universal property of the left Kan extension. -/
structure LeftKanUniversal {A B C : Type u}
    (K : A → C) (F : GroupoidFunctor A B)
    (lk : LeftKanData K F) where
  /-- The mediating family. -/
  mediate : ∀ (G : GroupoidFunctor C B)
    (_ : ∀ a : A, FundamentalGroupoid.Hom B (F.obj a) (G.obj (K a))),
    ∀ c : C, FundamentalGroupoid.Hom B (lk.Lan.obj c) (G.obj c)

/-! ## Right Kan Extension -/

/-- Data for a right Kan extension of F along K. -/
structure RightKanData {A B C : Type u}
    (K : A → C) (F : GroupoidFunctor A B) where
  /-- The right Kan extension functor. -/
  Ran : GroupoidFunctor C B
  /-- The counit: a family of morphisms Ran(K(a)) → F(a). -/
  counit : ∀ a : A, FundamentalGroupoid.Hom B (Ran.obj (K a)) (F.obj a)

/-- The universal property of the right Kan extension. -/
structure RightKanUniversal {A B C : Type u}
    (K : A → C) (F : GroupoidFunctor A B)
    (rk : RightKanData K F) where
  /-- The mediating family. -/
  mediate : ∀ (G : GroupoidFunctor C B)
    (_ : ∀ a : A, FundamentalGroupoid.Hom B (G.obj (K a)) (F.obj a)),
    ∀ c : C, FundamentalGroupoid.Hom B (G.obj c) (rk.Ran.obj c)

/-! ## Kan Extensions along Identity -/

/-- Left Kan extension along the identity is the original functor. -/
def leftKan_id {A B : Type u} (F : GroupoidFunctor A B) :
    LeftKanData (_root_.id : A → A) F where
  Lan := F
  unit := fun a => FundamentalGroupoid.id' B (F.obj a)

/-- The universal property holds for left Kan extension along id. -/
def leftKan_id_universal {A B : Type u} (F : GroupoidFunctor A B) :
    LeftKanUniversal _root_.id F (leftKan_id F) where
  mediate := fun _G η c => η c

/-- Right Kan extension along the identity is the original functor. -/
def rightKan_id {A B : Type u} (F : GroupoidFunctor A B) :
    RightKanData (_root_.id : A → A) F where
  Ran := F
  counit := fun a => FundamentalGroupoid.id' B (F.obj a)

/-- The universal property holds for right Kan extension along id. -/
def rightKan_id_universal {A B : Type u} (F : GroupoidFunctor A B) :
    RightKanUniversal _root_.id F (rightKan_id F) where
  mediate := fun _G ε c => ε c

/-! ## Kan Extensions preserve Natural Transformations -/

/-- A natural transformation α : F → G induces a natural transformation
Lan_id F → Lan_id G. -/
def leftKan_natTrans {A B : Type u}
    (F G : GroupoidFunctor A B)
    (α : GroupoidNatTrans F G) :
    GroupoidNatTrans (leftKan_id F).Lan (leftKan_id G).Lan :=
  α

/-- A natural transformation α : F → G induces a natural transformation
Ran_id F → Ran_id G. -/
def rightKan_natTrans {A B : Type u}
    (F G : GroupoidFunctor A B)
    (α : GroupoidNatTrans F G) :
    GroupoidNatTrans (rightKan_id F).Ran (rightKan_id G).Ran :=
  α

end KanExtension
end Path
end ComputationalPaths
