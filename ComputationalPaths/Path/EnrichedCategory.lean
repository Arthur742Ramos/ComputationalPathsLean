/-
# Groupoid-enriched categories of computational paths

This module packages a minimal notion of category enriched over groupoids.
The structure reuses the weak bicategory interface and adds inversion and
interchange laws for 2-cells. We then show that computational paths form a
groupoid-enriched category, with coherence inherited from the path bicategory.
-/

import ComputationalPaths.Path.Bicategory

namespace ComputationalPaths
namespace Path

universe u v w

/-! ## Groupoid-enriched categories -/

/-- A category enriched over groupoids: a weak bicategory whose 2-cells are
invertible and satisfy the interchange law. -/
structure GroupoidEnrichedCategory (Obj : Type u)
    extends WeakBicategory (Obj := Obj) where
  /-- Inversion of 2-cells in each hom-groupoid. -/
  inv₂ :
    ∀ {a b : Obj} {f g : Hom a b}, TwoCell f g → TwoCell g f
  /-- Vertical composition is associative. -/
  vcomp_assoc :
    ∀ {a b : Obj} {f g h i : Hom a b}
      (η : TwoCell f g) (θ : TwoCell g h) (ι : TwoCell h i),
      vcomp (vcomp η θ) ι = vcomp η (vcomp θ ι)
  /-- Left identity for vertical composition. -/
  vcomp_left_id :
    ∀ {a b : Obj} {f g : Hom a b} (η : TwoCell f g),
      vcomp (id₂ f) η = η
  /-- Right identity for vertical composition. -/
  vcomp_right_id :
    ∀ {a b : Obj} {f g : Hom a b} (η : TwoCell f g),
      vcomp η (id₂ g) = η
  /-- Left inverse for vertical composition. -/
  vcomp_left_inv :
    ∀ {a b : Obj} {f g : Hom a b} (η : TwoCell f g),
      vcomp (inv₂ η) η = id₂ g
  /-- Right inverse for vertical composition. -/
  vcomp_right_inv :
    ∀ {a b : Obj} {f g : Hom a b} (η : TwoCell f g),
      vcomp η (inv₂ η) = id₂ f
  /-- Interchange law: horizontal composition is functorial. -/
  interchange :
    ∀ {a b c : Obj} {f0 f1 f2 : Hom a b} {g0 g1 g2 : Hom b c}
      (η₁ : TwoCell f0 f1) (η₂ : TwoCell f1 f2)
      (θ₁ : TwoCell g0 g1) (θ₂ : TwoCell g1 g2),
      vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
        hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂)

/-! ## The path category enriched over groupoids -/

section PathEnriched

variable (A : Type u)

/-- The groupoid-enriched category of computational paths on a type `A`. -/
def pathGroupoidEnriched (A : Type u) : GroupoidEnrichedCategory (Obj := A) where
  toWeakBicategory := weakBicategory A
  inv₂ := fun {a b} {f g} η => RwEq.symm η
  vcomp_assoc := by
    intro a b f g h i η θ ι
    apply Subsingleton.elim
  vcomp_left_id := by
    intro a b f g η
    apply Subsingleton.elim
  vcomp_right_id := by
    intro a b f g η
    apply Subsingleton.elim
  vcomp_left_inv := by
    intro a b f g η
    apply Subsingleton.elim
  vcomp_right_inv := by
    intro a b f g η
    apply Subsingleton.elim
  interchange := by
    intro a b c f0 f1 f2 g0 g1 g2 η₁ η₂ θ₁ θ₂
    exact
      TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

end PathEnriched

/-! ## Summary -/

/-!
We introduced a groupoid-enriched category structure and instantiated it for
computational paths, using the existing bicategorical coherence lemmas.
-/

end Path
end ComputationalPaths
