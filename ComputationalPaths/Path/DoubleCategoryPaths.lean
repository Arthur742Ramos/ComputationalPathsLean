/-
# Double Category Structure on Computational Paths

This module packages the double category structure implicit in computational
paths. Squares are rewrite-equality 2-cells, vertical composition is rewrite
transitivity, and horizontal composition is bicategorical horizontal
composition. We record the interchange law and connect the structure to the
existing path 2-category.

## Key Results

- `DoubleCategory`: a double category interface with interchange
- `pathDoubleCategory`: the computational-path double category instance
- `pathDoubleCategory_to_twoCategory`: connection to the path 2-category

## References

- Leinster, "Higher Operads, Higher Categories"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.BicategoryDerived
import ComputationalPaths.Path.TwoCategory

namespace ComputationalPaths
namespace Path

/-! ## Double category interface -/

universe u v w

/-- A double category is a weak bicategory equipped with an explicit interchange
law for composing squares horizontally and vertically. -/
structure DoubleCategory (Obj : Type u) extends WeakBicategory (Obj := Obj) where
  /-- Interchange law for squares. -/
  interchange :
    ∀ {a b c : Obj} {f₀ f₁ f₂ : Hom a b} {g₀ g₁ g₂ : Hom b c}
      (η₁ : TwoCell f₀ f₁) (η₂ : TwoCell f₁ f₂)
      (θ₁ : TwoCell g₀ g₁) (θ₂ : TwoCell g₁ g₂),
      vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
        hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂)

namespace DoubleCategory

open TwoCell

universe u'

variable {A : Type u'}
variable {a b c : A}

/-! ## Double category operations on paths -/

/-- Vertical composition of squares in the path double category. -/
@[simp] def squareVComp {p q r : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q)
    (θ : TwoCell (A := A) (a := a) (b := b) q r) :
    TwoCell (A := A) (a := a) (b := b) p r :=
  TwoCell.comp (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) η θ

/-- Horizontal composition of squares in the path double category. -/
@[simp] def squareHComp {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans f h) (Path.trans g k) :=
  TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) (k := k) η θ

/-- Interchange law for path squares, expressed using double category
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

/-- The computational-path double category. -/
def pathDoubleCategory (A : Type u') : DoubleCategory (Obj := A) where
  toWeakBicategory := weakBicategory A
  interchange := by
    intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
    exact TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
      (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- The path double category recovers the path 2-category. -/
@[simp] theorem pathDoubleCategory_to_twoCategory (A : Type u') :
    (pathTwoCategory A).toWeakBicategory =
      (pathDoubleCategory A).toWeakBicategory := by
  rfl

end DoubleCategory

/-! ## Summary -/

/-!
We packaged the double category structure carried by computational paths, added
explicit vertical and horizontal compositions of squares, proved the interchange
law, and related the resulting structure to the existing path 2-category.
-/

end Path
end ComputationalPaths
