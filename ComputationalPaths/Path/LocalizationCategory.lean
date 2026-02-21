/-
# Localization of the Path Category

This module formalizes the localization of the path category at weak
equivalences.  Here the weak equivalences are rewrite equalities (`RwEq`) on
computational paths, so localization is implemented by the rewrite quotient
`PathRwQuot`.  We record the universal property of the quotient and show that
the localized category retains a strict groupoid structure.

## Key Results

- `pathLocalization`: the localized (strict) category on a type `A`
- `localize`: the canonical localization map on paths
- `localization_universal`: universal property for maps respecting `RwEq`
- `pathLocalization_isGroupoid`: localization preserves groupoid structure

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- HoTT Book, Chapter 2 (path groupoids)
-/

import ComputationalPaths.Path.Groupoid

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Localization data -/

/-- The path category on a type `A`, viewed as a weak category of paths. -/
abbrev pathCategory (A : Type u) : WeakCategory A :=
  WeakCategory.identity A

/-- Weak equivalences in the path category are rewrite equalities. -/
abbrev pathWeakEquiv {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  RwEq p q

/-- The localization of the path category at rewrite equalities. -/
abbrev pathLocalization (A : Type u) : StrictCategory A :=
  StrictCategory.quotient A

/-- The localized groupoid obtained from the path category. -/
abbrev pathLocalizationGroupoid (A : Type u) : StrictGroupoid A :=
  StrictGroupoid.quotient A

/-! ## The localization map -/

/-- Localize a path by passing to its rewrite quotient. -/
def localize {A : Type u} {a b : A} (p : Path a b) : PathRwQuot A a b :=
  Quot.mk _ p

/-- Localization identifies rewrite-equivalent paths. -/
noncomputable def localize_respects_rweq {A : Type u} {a b : A}
    {p q : Path a b} (h : RwEq p q) :
    localize (A := A) p = localize (A := A) q :=
  Quot.sound h

/-- Localization preserves reflexive paths. -/
@[simp] theorem localize_refl {A : Type u} (a : A) :
    localize (A := A) (Path.refl a) = PathRwQuot.refl (A := A) a := rfl

/-- Localization preserves path composition. -/
@[simp] theorem localize_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    localize (A := A) (Path.trans p q) =
      PathRwQuot.trans (A := A) (localize p) (localize q) :=
  rfl

/-- Localization preserves path inversion. -/
@[simp] theorem localize_symm {A : Type u} {a b : A}
    (p : Path a b) :
    localize (A := A) (Path.symm p) =
      PathRwQuot.symm (A := A) (localize p) :=
  rfl

/-! ## Universal property -/

/-- A map on paths that respects rewrite equality. -/
structure PathLocalizationMap (A : Type u) (Hom : A → A → Type v) where
  /-- Action on paths. -/
  map : {a b : A} → Path a b → Hom a b
  /-- Rewrite-equal paths map to equal morphisms. -/
  respects :
    ∀ {a b : A} {p q : Path a b}, RwEq p q → map p = map q

namespace PathLocalizationMap

variable {A : Type u} {Hom : A → A → Type v}

/-- Lift a map on paths to the localization. -/
def lift (F : PathLocalizationMap A Hom) {a b : A} :
    PathRwQuot A a b → Hom a b :=
  Quot.lift (fun p => F.map p) (fun _ _ h => F.respects h)

/-- The lift agrees with the original map on representatives. -/
@[simp] theorem lift_mk (F : PathLocalizationMap A Hom) {a b : A} (p : Path a b) :
    lift (F := F) (Quot.mk _ p) = F.map p := rfl

end PathLocalizationMap

/-- Universal property of the localization: maps respecting `RwEq` factor uniquely. -/
theorem localization_universal {A : Type u} {Hom : A → A → Type v}
    (F : PathLocalizationMap A Hom) :
    ∃ g : {a b : A} → PathRwQuot A a b → Hom a b,
      (∀ {a b : A} (p : Path a b), g (localize p) = F.map p) ∧
      (∀ g' : {a b : A} → PathRwQuot A a b → Hom a b,
        (∀ {a b : A} (p : Path a b), g' (localize p) = F.map p) →
        ∀ {a b : A} (x : PathRwQuot A a b), g' x = g x) := by
  refine ⟨PathLocalizationMap.lift F, ?_⟩
  constructor
  · intro a b p
    simpa [localize] using
      (PathLocalizationMap.lift_mk (F := F) (a := a) (b := b) p)
  · intro g' hg' a b x
    refine Quot.inductionOn x (fun p => ?_)
    simpa [localize, PathLocalizationMap.lift_mk] using
      (hg' (a := a) (b := b) p)

/-! ## Groupoid preservation -/

/-- The localized path category is a strict groupoid. -/
theorem pathLocalization_isGroupoid (A : Type u) :
    StrictCategory.IsGroupoid ((pathLocalizationGroupoid A).toStrictCategory) :=
  StrictGroupoid.quotient_isGroupoid (A := A)

/-! ## Summary -/

/-!
We formalized the localization of the path category at rewrite equivalences,
proved its universal property via `Quot.lift`, and recorded that the localized
category is a strict groupoid.
-/

end Path
end ComputationalPaths
