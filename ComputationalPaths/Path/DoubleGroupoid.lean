/-
# Double Groupoid Structure on Computational Paths

This module packages the double groupoid structure implicit in computational
paths.  Squares are rewrite-equality 2-cells between paths, vertical
composition is rewrite transitivity, and horizontal composition is the usual
bicategory horizontal composition.  We record the interchange law and connect
the resulting structure to the existing path bicategory.

## Key Results

- `DoubleGroupoid`: a weak two-groupoid with an explicit interchange law
- `pathDoubleGroupoid`: the computational-path double groupoid instance
- `pathDoubleGroupoid_to_weakBicategory`: connection to the path bicategory

## References

- Leinster, "Higher Operads, Higher Categories"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.BicategoryDerived

namespace ComputationalPaths
namespace Path

/-! ## Double groupoid interface -/

universe u' v w

/-- A double groupoid is a weak 2-groupoid equipped with an explicit
interchange law for composing squares horizontally and vertically. -/
structure DoubleGroupoid (Obj : Type u') extends WeakTwoGroupoid Obj where
  /-- Interchange law for squares. -/
  interchange :
    ∀ {a b c : Obj} {f₀ f₁ f₂ : Hom a b} {g₀ g₁ g₂ : Hom b c}
      (η₁ : TwoCell f₀ f₁) (η₂ : TwoCell f₁ f₂)
      (θ₁ : TwoCell g₀ g₁) (θ₂ : TwoCell g₁ g₂),
      vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
        hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂)

namespace DoubleGroupoid

open TwoCell

universe u

variable {A : Type u}
variable {a b c : A}

/-! ## Double groupoid operations on paths -/

/-- Vertical composition of squares in the path double groupoid. -/
@[simp] noncomputable def squareVComp {p q r : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q)
    (θ : TwoCell (A := A) (a := a) (b := b) q r) :
    TwoCell (A := A) (a := a) (b := b) p r :=
  TwoCell.comp (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) η θ

/-- Horizontal composition of squares in the path double groupoid. -/
@[simp] noncomputable def squareHComp {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans f h) (Path.trans g k) :=
  TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) (k := k) η θ

/-- Interchange law for path squares, expressed using double groupoid
compositions. -/
@[simp] theorem square_interchange
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    squareVComp (squareHComp η₁ θ₁) (squareHComp η₂ θ₂) =
      squareHComp (squareVComp η₁ η₂) (squareVComp θ₁ θ₂) :=
  TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
    (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- The computational-path double groupoid. -/
noncomputable def pathDoubleGroupoid (A : Type u) : DoubleGroupoid (Obj := A) where
  toWeakTwoGroupoid := weakTwoGroupoid A
  interchange := by
    intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
    exact TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
      (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- The underlying path bicategory of the double groupoid is the standard
weak bicategory of computational paths. -/
@[simp] theorem pathDoubleGroupoid_to_weakBicategory (A : Type u) :
    (pathDoubleGroupoid A).toWeakBicategory = weakBicategory A := by
  rfl

end DoubleGroupoid

/-! ## Summary -/

/-!
We package a double groupoid structure for computational paths, record the
interchange law for horizontal/vertical composition of squares, and show that
the resulting structure recovers the existing path bicategory.
-/

end Path
end ComputationalPaths
