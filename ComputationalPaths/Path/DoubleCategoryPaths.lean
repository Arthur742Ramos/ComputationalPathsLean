/-
# Double Category Structure on Computational Paths

This module packages the double category structure implicit in computational
paths. Squares are rewrite-equality 2-cells, vertical composition is rewrite
transitivity, and horizontal composition is bicategorical horizontal
composition. We record the interchange law and connect the structure to the
existing path 2-category.

## Key Results

- `PathSquare`: rewrite-equality squares between computational paths
- `DoubleCategory`: the path-based double category interface with interchange
- `pathDoubleCategory`: the computational-path double category instance
- `pathDoubleCategory_to_twoCategory`: interchange compatibility with the path 2-category

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

/-- Squares between computational paths are rewrite equalities. -/
abbrev PathSquare {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  TwoCell (A := A) (a := a) (b := b) p q

/-- A double category on computational paths records the interchange law for
horizontal and vertical composition of squares. -/
structure DoubleCategory (A : Type u) where
  /-- Interchange law for squares. -/
  interchange :
    ∀ {a b c : A} {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
      (η₁ : PathSquare (A := A) (a := a) (b := b) f₀ f₁)
      (η₂ : PathSquare (A := A) (a := a) (b := b) f₁ f₂)
      (θ₁ : PathSquare (A := A) (a := b) (b := c) g₀ g₁)
      (θ₂ : PathSquare (A := A) (a := b) (b := c) g₁ g₂),
      TwoCell.comp (A := A) (a := a) (b := c)
          (p := Path.trans f₀ g₀) (q := Path.trans f₁ g₁) (r := Path.trans f₂ g₂)
          (TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
            (f := f₀) (g := f₁) (h := g₀) (k := g₁) η₁ θ₁)
          (TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
            (f := f₁) (g := f₂) (h := g₁) (k := g₂) η₂ θ₂)
        =
        TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
          (f := f₀) (g := f₂) (h := g₀) (k := g₂)
          (TwoCell.comp (A := A) (a := a) (b := b)
            (p := f₀) (q := f₁) (r := f₂) η₁ η₂)
          (TwoCell.comp (A := A) (a := b) (b := c)
            (p := g₀) (q := g₁) (r := g₂) θ₁ θ₂)

namespace DoubleCategory

open TwoCell

universe u'

variable {A : Type u'}
variable {a b c : A}

/-! ## Double category operations on paths -/

/-- Vertical composition of squares in the path double category. -/
@[simp] noncomputable def squareVComp {p q r : Path a b}
    (η : PathSquare (A := A) (a := a) (b := b) p q)
    (θ : PathSquare (A := A) (a := a) (b := b) q r) :
    PathSquare (A := A) (a := a) (b := b) p r :=
  TwoCell.comp (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) η θ

/-- Horizontal composition of squares in the path double category. -/
@[simp] noncomputable def squareHComp {f g : Path a b} {h k : Path b c}
    (η : PathSquare (A := A) (a := a) (b := b) f g)
    (θ : PathSquare (A := A) (a := b) (b := c) h k) :
    PathSquare (A := A) (a := a) (b := c)
      (Path.trans f h) (Path.trans g k) :=
  TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) (k := k) η θ

/-- Interchange law for path squares, expressed using double category
compositions. -/
@[simp] theorem square_interchange
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : PathSquare (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : PathSquare (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : PathSquare (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : PathSquare (A := A) (a := b) (b := c) g₁ g₂) :
    squareVComp (squareHComp η₁ θ₁) (squareHComp η₂ θ₂) =
      squareHComp (squareVComp η₁ η₂) (squareVComp θ₁ θ₂) :=
  TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
    (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- The computational-path double category. -/
noncomputable def pathDoubleCategory (A : Type u') : DoubleCategory A where
  interchange := by
    intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
    exact TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
      (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- The path double category's interchange law agrees with the path 2-category. -/
@[simp] theorem pathDoubleCategory_to_twoCategory (A : Type u') :
    ∀ {a b c : A} {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
      (η₁ : PathSquare (A := A) (a := a) (b := b) f₀ f₁)
      (η₂ : PathSquare (A := A) (a := a) (b := b) f₁ f₂)
      (θ₁ : PathSquare (A := A) (a := b) (b := c) g₀ g₁)
      (θ₂ : PathSquare (A := A) (a := b) (b := c) g₁ g₂),
      (pathDoubleCategory A).interchange
          (a := a) (b := b) (c := c)
          (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
          (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
          η₁ η₂ θ₁ θ₂ =
        (pathTwoCategory A).interchange
          (a := a) (b := b) (c := c)
          (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
          (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
          η₁ η₂ θ₁ θ₂ := by
  intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
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
