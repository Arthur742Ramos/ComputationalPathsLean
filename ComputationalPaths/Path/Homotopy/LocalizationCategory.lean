/-
# Localization of categories via computational paths

This module provides a homotopy-facing view of the localization of the path
category. We repackage the localization map and its universal property inside
the homotopy namespace, and relate the localized groupoid to the fundamental
groupoid.

## Key Results

- `homotopyCategory`: localized strict category on a type.
- `homotopyGroupoid`: localized strict groupoid on a type.
- `homotopyLocalize`: localization map on paths.
- `homotopyLocalization_universal`: universal property of localization.
- `homotopyGroupoid_eq_fundamental`: identification with the fundamental groupoid.

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.LocalizationCategory
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LocalizationCategory

universe u v

/-! ## Homotopy localization -/

/-- The homotopy category on a type `A`, obtained by localizing paths at `RwEq`. -/
abbrev homotopyCategory (A : Type u) : StrictCategory A :=
  pathLocalization A

/-- The homotopy groupoid on a type `A`, obtained by localizing paths at `RwEq`. -/
abbrev homotopyGroupoid (A : Type u) : StrictGroupoid A :=
  pathLocalizationGroupoid A

/-- The localization map on paths used in the homotopy category. -/
abbrev homotopyLocalize {A : Type u} {a b : A} (p : Path a b) :
    PathRwQuot A a b :=
  localize p

/-- Homotopy localization identifies rewrite-equivalent paths. -/
theorem homotopyLocalize_respects_rweq {A : Type u} {a b : A}
    {p q : Path a b} (h : RwEq p q) :
    homotopyLocalize (A := A) p = homotopyLocalize (A := A) q :=
  localize_respects_rweq (A := A) (a := a) (b := b) (p := p) (q := q) h

/-- Universal property of homotopy localization. -/
theorem homotopyLocalization_universal {A : Type u} {Hom : A → A → Type v}
    (F : PathLocalizationMap A Hom) :
    ∃ g : {a b : A} → PathRwQuot A a b → Hom a b,
      (∀ {a b : A} (p : Path a b), g (homotopyLocalize p) = F.map p) ∧
      (∀ g' : {a b : A} → PathRwQuot A a b → Hom a b,
        (∀ {a b : A} (p : Path a b), g' (homotopyLocalize p) = F.map p) →
        ∀ {a b : A} (x : PathRwQuot A a b), g' x = g x) := by
  simpa [homotopyLocalize] using (localization_universal (F := F))

/-- The homotopy groupoid is definitionally the fundamental groupoid. -/
theorem homotopyGroupoid_eq_fundamental (A : Type u) :
    homotopyGroupoid A = FundamentalGroupoid A := rfl

/-- The homotopy category is the underlying strict category of the fundamental groupoid. -/
theorem homotopyCategory_eq_fundamental (A : Type u) :
    homotopyCategory A = (FundamentalGroupoid A).toStrictCategory := rfl

/-! ## Summary -/

/-!
We repackaged the path localization for homotopy use, recorded the universal
property, and related the localized groupoid to the fundamental groupoid.
-/

end LocalizationCategory
end Homotopy
end Path
end ComputationalPaths
