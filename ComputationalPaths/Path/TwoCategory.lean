/-
# Path 2-Category Structure

This module packages the 2-category structure of computational paths by
combining the bicategorical primitives with the double-groupoid interchange law.
We make the 0/1/2-cells explicit and record the vertical/horizontal unit laws.

## Key Results

- `TwoCategory`: a 2-category interface extending `WeakBicategory`.
- `pathTwoCategory`: the computational-path 2-category.
- `pathTwoCategory_to_weakBicategory`: compatibility with `weakBicategory`.

## References

- Leinster, "Higher Operads, Higher Categories"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.BicategoryDerived
import ComputationalPaths.Path.DoubleGroupoid

namespace ComputationalPaths
namespace Path

/-! ## Two-category interface -/

universe u v w

/-- A locally strict 2-category: a weak bicategory equipped with strict vertical
composition laws, horizontal unit laws, and the interchange law. -/
structure TwoCategory (Obj : Type u) extends WeakBicategory (Obj := Obj) where
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
  /-- Horizontal composition with a right identity 2-cell. -/
  hcomp_id_left :
    ∀ {a b c : Obj} {f g : Hom a b} {h : Hom b c}
      (η : TwoCell f g),
      hcomp η (id₂ h) = whiskerRight h η
  /-- Horizontal composition with a left identity 2-cell. -/
  hcomp_id_right :
    ∀ {a b c : Obj} {f : Hom a b} {g h : Hom b c}
      (η : TwoCell g h),
      hcomp (id₂ f) η = whiskerLeft f η
  /-- Interchange law between vertical and horizontal composition. -/
  interchange :
    ∀ {a b c : Obj} {f₀ f₁ f₂ : Hom a b} {g₀ g₁ g₂ : Hom b c}
      (η₁ : TwoCell f₀ f₁) (η₂ : TwoCell f₁ f₂)
      (θ₁ : TwoCell g₀ g₁) (θ₂ : TwoCell g₁ g₂),
      vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
        hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂)

/-! ## Path 2-category -/

/-- 0-cells in the path 2-category are points of the underlying type. -/
abbrev Path0Cell (A : Type u) : Type u :=
  A

/-- 1-cells in the path 2-category are computational paths. -/
abbrev Path1Cell {A : Type u} (a b : A) : Type u :=
  Path a b

/-- 2-cells in the path 2-category are rewrite equalities. -/
abbrev Path2Cell {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  TwoCell (A := A) (a := a) (b := b) p q

/-- The 2-category carried by computational paths. -/
def pathTwoCategory (A : Type u) : TwoCategory (Obj := A) where
  toWeakBicategory := weakBicategory A
  vcomp_assoc := by
    intro a b f g h i η θ ι
    apply Subsingleton.elim
  vcomp_left_id := by
    intro a b f g η
    apply Subsingleton.elim
  vcomp_right_id := by
    intro a b f g η
    apply Subsingleton.elim
  hcomp_id_left := by
    intro a b c f g h η
    exact
      (BicategoryDerived.hcomp_id_left (A := A) (a := a) (b := b) (c := c)
        (f := f) (g := g) (h := h) η)
  hcomp_id_right := by
    intro a b c f g h η
    exact
      (BicategoryDerived.hcomp_id_right (A := A) (a := a) (b := b) (c := c)
        (f := f) (g := g) (h := h) η)
  interchange := by
    intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
    exact
      (DoubleGroupoid.pathDoubleGroupoid (A := A)).interchange
        (a := a) (b := b) (c := c)
        (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
        (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- The underlying bicategory of the path 2-category is the standard path bicategory. -/
@[simp] theorem pathTwoCategory_to_weakBicategory (A : Type u) :
    (pathTwoCategory A).toWeakBicategory = weakBicategory A := by
  rfl

/-! ## Summary -/

/-!
We introduced a strict 2-category interface, instantiated it for computational
paths, and connected the resulting structure to the existing path bicategory.
-/

end Path
end ComputationalPaths
