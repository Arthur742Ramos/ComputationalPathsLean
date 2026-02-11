/-
# Double Categories via Computational Paths

This module formalizes the path-based double category by exposing explicit
horizontal/vertical morphisms, squares, and their compositions.  We also record
derived double-category constructions such as companion/conjoint/connection
pairs and a folding map into the path 2-category.

## Key Results

- `HorizHom`/`VertHom`: explicit horizontal and vertical morphisms (paths).
- `Square`: path-based squares (rewrite equalities).
- `squareVComp`/`squareHComp`: vertical and horizontal square compositions.
- `square_interchange`: interchange law for square compositions.
- `companionPair`/`conjointPair`/`connectionPair`: derived square data.
- `foldingSquare`: folding map into path 2-cells.

## References

- Leinster, "Higher Operads, Higher Categories"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.DoubleCategoryPaths
import ComputationalPaths.Path.TwoCategory

namespace ComputationalPaths
namespace Path
namespace Category

/-! ## Double category data -/

universe u

/-- Horizontal morphisms in the path double category are computational paths. -/
abbrev HorizHom {A : Type u} (a b : A) : Type u :=
  Path a b

/-- Vertical morphisms in the path double category are computational paths. -/
abbrev VertHom {A : Type u} (a b : A) : Type u :=
  Path a b

/-- Squares (2-cells) in the path double category are rewrite equalities. -/
abbrev Square {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  PathSquare (A := A) (a := a) (b := b) p q

/-! ## Composition of squares -/

variable {A : Type u} {a b c : A}

/-- Vertical composition of squares. -/
@[simp] def squareVComp {p q r : Path a b}
    (eta : Square (A := A) (a := a) (b := b) p q)
    (theta : Square (A := A) (a := a) (b := b) q r) :
    Square (A := A) (a := a) (b := b) p r :=
  DoubleCategory.squareVComp (A := A) (a := a) (b := b)
    (p := p) (q := q) (r := r) eta theta

/-- Horizontal composition of squares. -/
@[simp] def squareHComp {f g : Path a b} {h k : Path b c}
    (eta : Square (A := A) (a := a) (b := b) f g)
    (theta : Square (A := A) (a := b) (b := c) h k) :
    Square (A := A) (a := a) (b := c)
      (Path.trans f h) (Path.trans g k) :=
  DoubleCategory.squareHComp (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) (k := k) eta theta

/-- Interchange law for squares, expressed using `squareVComp`/`squareHComp`. -/
@[simp] theorem square_interchange
    {f0 f1 f2 : Path a b} {g0 g1 g2 : Path b c}
    (eta1 : Square (A := A) (a := a) (b := b) f0 f1)
    (eta2 : Square (A := A) (a := a) (b := b) f1 f2)
    (theta1 : Square (A := A) (a := b) (b := c) g0 g1)
    (theta2 : Square (A := A) (a := b) (b := c) g1 g2) :
    squareVComp (squareHComp eta1 theta1) (squareHComp eta2 theta2) =
      squareHComp (squareVComp eta1 eta2) (squareVComp theta1 theta2) :=
  DoubleCategory.square_interchange (A := A) (a := a) (b := b) (c := c)
    eta1 eta2 theta1 theta2

/-! ## Derived pairs -/

/-- Companion pair data for a path. -/
structure CompanionPair {A : Type u} {a b : A} (f : Path a b) : Prop where
  /-- Unit square for the companion. -/
  unit :
    Square (A := A) (a := a) (b := a)
      (Path.trans f (Path.symm f)) (Path.refl a)
  /-- Counit square for the companion. -/
  counit :
    Square (A := A) (a := b) (b := b)
      (Path.trans (Path.symm f) f) (Path.refl b)

/-- Conjoint pair data for a path. -/
structure ConjointPair {A : Type u} {a b : A} (f : Path a b) : Prop where
  /-- Unit square for the conjoint. -/
  unit :
    Square (A := A) (a := b) (b := b)
      (Path.trans (Path.symm f) f) (Path.refl b)
  /-- Counit square for the conjoint. -/
  counit :
    Square (A := A) (a := a) (b := a)
      (Path.trans f (Path.symm f)) (Path.refl a)

/-- Connection pair data for a path. -/
structure ConnectionPair {A : Type u} {a b : A} (f : Path a b) : Prop where
  /-- Left unit connection. -/
  left :
    Square (A := A) (a := a) (b := b)
      (Path.trans (Path.refl a) f) f
  /-- Right unit connection. -/
  right :
    Square (A := A) (a := a) (b := b)
      (Path.trans f (Path.refl b)) f

/-- Every path has a canonical companion pair. -/
@[simp] def companionPair {a b : A} (f : Path a b) :
    CompanionPair (A := A) (a := a) (b := b) f where
  unit := rweq_cmpA_inv_right f
  counit := rweq_cmpA_inv_left f

/-- Every path has a canonical conjoint pair. -/
@[simp] def conjointPair {a b : A} (f : Path a b) :
    ConjointPair (A := A) (a := a) (b := b) f where
  unit := rweq_cmpA_inv_left f
  counit := rweq_cmpA_inv_right f

/-- Every path has a canonical connection pair. -/
@[simp] def connectionPair {a b : A} (f : Path a b) :
    ConnectionPair (A := A) (a := a) (b := b) f where
  left := rweq_cmpA_refl_left f
  right := rweq_cmpA_refl_right f

/-! ## Folding to the path 2-category -/

/-- Folding map from squares to 2-cells in the path 2-category. -/
@[simp] def foldingSquare {A : Type u} {a b : A} {p q : Path a b} :
    Square (A := A) (a := a) (b := b) p q ->
      Path2Cell (A := A) (a := a) (b := b) p q :=
  fun eta => eta

/-- Folding respects vertical composition. -/
@[simp] theorem foldingSquare_vcomp {p q r : Path a b}
    (eta : Square (A := A) (a := a) (b := b) p q)
    (theta : Square (A := A) (a := a) (b := b) q r) :
    foldingSquare (squareVComp eta theta) =
      TwoCell.comp (A := A) (a := a) (b := b)
        (p := p) (q := q) (r := r) eta theta :=
  rfl

/-- Folding respects horizontal composition. -/
@[simp] theorem foldingSquare_hcomp {f g : Path a b} {h k : Path b c}
    (eta : Square (A := A) (a := a) (b := b) f g)
    (theta : Square (A := A) (a := b) (b := c) h k) :
    foldingSquare (squareHComp eta theta) =
      TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
        (f := f) (g := g) (h := h) (k := k) eta theta :=
  rfl

/-! ## Summary -/

/-!
We exposed the path-based double category data, provided square compositions and
interchange, and recorded derived companion/conjoint/connection pairs alongside
a folding map into the path 2-category.
-/

end Category
end Path
end ComputationalPaths
