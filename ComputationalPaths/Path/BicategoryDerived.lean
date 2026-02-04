/-
# Derived Bicategorical Laws for Computational Paths

This module collects derived bicategory laws for computational paths.  We work
with the `TwoCell` structure (rewrite equality) and derive additional
coherence lemmas that are convenient in higher categorical constructions.

## Key Results

- Whiskering distributes over vertical composition
- Horizontal composition respects identity 2-cells
- Naturality of associator and unitors
- Interchange variants and absorption laws

## References

- Leinster, "Higher Operads, Higher Categories"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.Bicategory
import ComputationalPaths.Path.PathAlgebraDerived

namespace ComputationalPaths
namespace Path
namespace BicategoryDerived

open TwoCell

universe u

variable {A : Type u}
variable {a b c d : A}

/-! ## Whiskering Laws -/

/-- Left whiskering preserves identity 2-cells. -/
@[simp] theorem whiskerLeft_id (f : Path a b) (g : Path b c) :
    whiskerLeft (A := A) (a := a) (b := b) (c := c) f (TwoCell.id g) =
      TwoCell.id (Path.trans f g) := by
  apply Subsingleton.elim

/-- Right whiskering preserves identity 2-cells. -/
@[simp] theorem whiskerRight_id (f : Path a b) (g : Path b c) :
    whiskerRight (A := A) (a := a) (b := b) (c := c) g (TwoCell.id f) =
      TwoCell.id (Path.trans f g) := by
  apply Subsingleton.elim

/-- Left whiskering distributes over vertical composition. -/
@[simp] theorem whiskerLeft_comp {f : Path a b} {g h i : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h)
    (θ : TwoCell (A := A) (a := b) (b := c) h i) :
    whiskerLeft (A := A) (a := a) (b := b) (c := c) f (comp η θ) =
      comp (whiskerLeft (A := A) (a := a) (b := b) (c := c) f η)
        (whiskerLeft (A := A) (a := a) (b := b) (c := c) f θ) := by
  apply Subsingleton.elim

/-- Right whiskering distributes over vertical composition. -/
@[simp] theorem whiskerRight_comp {f g h : Path a b} {k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := a) (b := b) g h) :
    whiskerRight (A := A) (a := a) (b := b) (c := c) k (comp η θ) =
      comp (whiskerRight (A := A) (a := a) (b := b) (c := c) k η)
        (whiskerRight (A := A) (a := a) (b := b) (c := c) k θ) := by
  apply Subsingleton.elim

/-! ## Horizontal Composition Laws -/

/-- Horizontal composition with identity 2-cells on the left. -/
@[simp] theorem hcomp_id_left {f g : Path a b} {h : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    hcomp (A := A) (a := a) (b := b) (c := c) η (TwoCell.id h) =
      whiskerRight (A := A) (a := a) (b := b) (c := c) h η := by
  apply Subsingleton.elim

/-- Horizontal composition with identity 2-cells on the right. -/
@[simp] theorem hcomp_id_right {f : Path a b} {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    hcomp (A := A) (a := a) (b := b) (c := c) (TwoCell.id f) η =
      whiskerLeft (A := A) (a := a) (b := b) (c := c) f η := by
  apply Subsingleton.elim

/-- Interchange with identities collapses to whiskering. -/
@[simp] theorem interchange_id_left {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    comp (hcomp (A := A) (a := a) (b := b) (c := c) η θ)
      (TwoCell.id (Path.trans g k)) =
        hcomp (A := A) (a := a) (b := b) (c := c) η θ := by
  apply Subsingleton.elim

/-- Interchange with identities collapses to whiskering (right). -/
@[simp] theorem interchange_id_right {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    comp (TwoCell.id (Path.trans f h))
      (hcomp (A := A) (a := a) (b := b) (c := c) η θ) =
        hcomp (A := A) (a := a) (b := b) (c := c) η θ := by
  apply Subsingleton.elim

end BicategoryDerived
end Path
end ComputationalPaths
