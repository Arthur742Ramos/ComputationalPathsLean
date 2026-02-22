/-
# Derived Functors in Homotopy

This module defines homotopy classes of maps using computational paths and
shows that any map on functions that respects homotopy factors uniquely
through the homotopy quotient. We also package the derived pre- and
post-composition operations on homotopy classes.

## Key Results
- `HomotopyRel` / `HomotopyClass`: homotopy relation and quotient on maps.
- `HomotopyLocalizationMap`: maps that respect homotopy and their derived lift.
- `precompose` / `postcompose`: derived functors on homotopy classes.

## References
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace DerivedFunctorHomotopy

open HoTT

universe u v w

/-! ## Homotopy relation on maps -/

/-- Two maps are related when there exists a computational homotopy between them. -/
noncomputable def HomotopyRel {A : Type u} {B : Type v} (f g : A → B) : Prop :=
  Nonempty (FunHomotopy f g)

/-- Homotopy relation is reflexive. -/
theorem homotopyRel_refl {A : Type u} {B : Type v} (f : A → B) :
    HomotopyRel f f :=
  ⟨homotopy_refl (f := f)⟩

/-- Homotopy relation is symmetric. -/
theorem homotopyRel_symm {A : Type u} {B : Type v} {f g : A → B} :
    HomotopyRel f g → HomotopyRel g f := by
  intro h
  rcases h with ⟨H⟩
  exact ⟨homotopy_symm H⟩

/-- Homotopy relation is transitive. -/
theorem homotopyRel_trans {A : Type u} {B : Type v} {f g h : A → B} :
    HomotopyRel f g → HomotopyRel g h → HomotopyRel f h := by
  intro hfg hgh
  rcases hfg with ⟨Hfg⟩
  rcases hgh with ⟨Hgh⟩
  exact ⟨homotopy_trans Hfg Hgh⟩

/-- Homotopy relation forms an equivalence. -/
theorem homotopyRel_equiv {A : Type u} {B : Type v} :
    Equivalence (@HomotopyRel A B) where
  refl := fun f => homotopyRel_refl (A := A) (B := B) f
  symm := by
    intro f g h
    exact homotopyRel_symm (A := A) (B := B) (f := f) (g := g) h
  trans := by
    intro f g h hfg hgh
    exact homotopyRel_trans (A := A) (B := B) (f := f) (g := g) (h := h) hfg hgh

/-- The setoid of maps modulo homotopy. -/
noncomputable def homotopySetoid (A : Type u) (B : Type v) : Setoid (A → B) where
  r := HomotopyRel (A := A) (B := B)
  iseqv := homotopyRel_equiv (A := A) (B := B)

/-- Homotopy classes of maps. -/
noncomputable def HomotopyClass (A : Type u) (B : Type v) : Type (max u v) :=
  Quotient (homotopySetoid A B)

/-- The homotopy class of a map. -/
noncomputable def homotopyClass {A : Type u} {B : Type v} (f : A → B) :
    HomotopyClass A B :=
  Quotient.mk _ f

/-- Homotopic maps determine the same homotopy class. -/
theorem homotopyClass_eq {A : Type u} {B : Type v} {f g : A → B}
    (H : FunHomotopy f g) : homotopyClass f = homotopyClass g := by
  apply Quotient.sound
  exact ⟨H⟩

/-! ## Localization of homotopy classes -/

/-- Maps on functions that respect homotopy. -/
structure HomotopyLocalizationMap (A : Type u) (B : Type v) (C : Type w) where
  /-- Action on maps. -/
  map : (A → B) → C
  /-- Homotopic maps are sent to equal values. -/
  respects :
    ∀ {f g : A → B}, HomotopyRel (A := A) (B := B) f g → map f = map g

namespace HomotopyLocalizationMap

variable {A : Type u} {B : Type v} {C : Type w}

/-- Lift a homotopy-respecting map to homotopy classes. -/
noncomputable def lift (F : HomotopyLocalizationMap A B C) :
    HomotopyClass A B → C :=
  Quotient.lift F.map (fun _ _ h => F.respects h)

/-- The lift agrees with the original map on representatives. -/
@[simp] theorem lift_mk (F : HomotopyLocalizationMap A B C) (f : A → B) :
    lift F (homotopyClass f) = F.map f := rfl

end HomotopyLocalizationMap

/-- The derived map on homotopy classes. -/
noncomputable def derivedMap {A : Type u} {B : Type v} {C : Type w}
    (F : HomotopyLocalizationMap A B C) : HomotopyClass A B → C :=
  HomotopyLocalizationMap.lift F

/-! ## Universal property -/

/-- Universal property of the homotopy localization. -/
theorem homotopyLocalization_universal {A : Type u} {B : Type v} {C : Type w}
    (F : HomotopyLocalizationMap A B C) :
    ∃ g : HomotopyClass A B → C,
      (∀ f : A → B, g (homotopyClass f) = F.map f) ∧
      (∀ g' : HomotopyClass A B → C,
        (∀ f : A → B, g' (homotopyClass f) = F.map f) →
        ∀ x, g' x = g x) := by
  refine ⟨HomotopyLocalizationMap.lift F, ?_⟩
  refine And.intro ?_ ?_
  · intro f
    exact HomotopyLocalizationMap.lift_mk (F := F) f
  · intro g' hg' x
    refine Quotient.inductionOn x (fun f => ?_)
    have h1 := hg' f
    have h2 := HomotopyLocalizationMap.lift_mk (F := F) f
    exact h1.trans h2.symm

/-! ## Derived pre/post composition -/

/-- Precomposition preserves homotopies. -/
noncomputable def homotopy_precompose {A : Type u} {B : Type v} {C : Type w} (f : A → B)
    {g h : B → C} (H : FunHomotopy g h) :
    FunHomotopy (fun a => g (f a)) (fun a => h (f a)) :=
  fun a => H (f a)

/-- Postcomposition preserves homotopies. -/
noncomputable def homotopy_postcompose {A : Type u} {B : Type v} {C : Type w} (g : B → C)
    {f h : A → B} (H : FunHomotopy f h) :
    FunHomotopy (fun a => g (f a)) (fun a => g (h a)) :=
  fun a => ap g (H a)

/-- Derived precomposition on homotopy classes. -/
noncomputable def precompose {A : Type u} {B : Type v} {C : Type w} (f : A → B) :
    HomotopyClass B C → HomotopyClass A C :=
  HomotopyLocalizationMap.lift (A := B) (B := C) (C := HomotopyClass A C)
    { map := fun g => homotopyClass (fun a => g (f a))
      respects := by
        intro g h hgh
        rcases hgh with ⟨H⟩
        exact homotopyClass_eq (homotopy_precompose (f := f) H) }

/-- Derived postcomposition on homotopy classes. -/
noncomputable def postcompose {A : Type u} {B : Type v} {C : Type w} (g : B → C) :
    HomotopyClass A B → HomotopyClass A C :=
  HomotopyLocalizationMap.lift (A := A) (B := B) (C := HomotopyClass A C)
    { map := fun f => homotopyClass (fun a => g (f a))
      respects := by
        intro f h hfh
        rcases hfh with ⟨H⟩
        exact homotopyClass_eq (homotopy_postcompose (g := g) H) }

/-! ## Summary

We define homotopy classes of maps using computational paths, prove the
universal property for homotopy-respecting maps, and derive pre/post
composition functors on homotopy classes.
-/

end DerivedFunctorHomotopy
end Homotopy
end Path
end ComputationalPaths
