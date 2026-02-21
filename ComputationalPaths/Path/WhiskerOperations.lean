/-
# Whiskering Operations for 2-Cells

This module isolates left/right whiskering for 2-cells (rewrite equalities) and
records the corresponding naturality and interchange laws.

## Key Results

- `whiskerLeft` / `whiskerRight`: whiskering operations for 2-cells
- `whiskerLeft_respects_rweq` / `whiskerRight_respects_rweq`: preservation of rewrite equivalence
- `whiskerLeft_natural` / `whiskerRight_natural`: naturality with respect to vertical composition
- `interchange_law`: interchange law for horizontal/vertical composition
- `godement_interchange`: Godement interchange for whiskering composites
-/

import ComputationalPaths.Path.BicategoryDerived

namespace ComputationalPaths
namespace Path
namespace WhiskerOperations

open TwoCell

universe u

variable {A : Type u}
variable {a b c d : A}

/-! ## Whiskering Operations -/

/-- Left whiskering of 2-cells. -/
@[simp] def whiskerLeft (f : Path a b) {g h : Path b c}
    (eta : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f h) :=
  TwoCell.whiskerLeft (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) eta

/-- Right whiskering of 2-cells. -/
@[simp] def whiskerRight {f g : Path a b} (h : Path b c)
    (eta : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f h) (Path.trans g h) :=
  TwoCell.whiskerRight (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) eta

/-! ## Preservation of Rewrite Equivalence -/

/-- Left whiskering preserves rewrite equivalence. -/
theorem whiskerLeft_respects_rweq {f : Path a b} {g h : Path b c}
    (eta : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f h) :=
  whiskerLeft (A := A) (a := a) (b := b) (c := c) f eta

/-- Right whiskering preserves rewrite equivalence. -/
theorem whiskerRight_respects_rweq {f g : Path a b} {h : Path b c}
    (eta : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f h) (Path.trans g h) :=
  whiskerRight (A := A) (a := a) (b := b) (c := c) h eta

/-! ## Naturality -/

/-- Left whiskering is natural with respect to vertical composition. -/
@[simp] theorem whiskerLeft_natural {f : Path a b} {g h i : Path b c}
    (eta : TwoCell (A := A) (a := b) (b := c) g h)
    (theta : TwoCell (A := A) (a := b) (b := c) h i) :
    whiskerLeft (A := A) (a := a) (b := b) (c := c) f (comp eta theta) =
      comp (whiskerLeft (A := A) (a := a) (b := b) (c := c) f eta)
        (whiskerLeft (A := A) (a := a) (b := b) (c := c) f theta) := by
  simp

/-- Right whiskering is natural with respect to vertical composition. -/
@[simp] theorem whiskerRight_natural {f g h : Path a b} {k : Path b c}
    (eta : TwoCell (A := A) (a := a) (b := b) f g)
    (theta : TwoCell (A := A) (a := a) (b := b) g h) :
    whiskerRight (A := A) (a := a) (b := b) (c := c) k (comp eta theta) =
      comp (whiskerRight (A := A) (a := a) (b := b) (c := c) k eta)
        (whiskerRight (A := A) (a := a) (b := b) (c := c) k theta) := by
  simp

/-- Left whiskering preserves identity 2-cells. -/
@[simp] theorem whiskerLeft_id_natural (f : Path a b) (g : Path b c) :
    whiskerLeft (A := A) (a := a) (b := b) (c := c) f (TwoCell.id g) =
      TwoCell.id (Path.trans f g) := by
  simp

/-- Right whiskering preserves identity 2-cells. -/
@[simp] theorem whiskerRight_id_natural (f : Path a b) (g : Path b c) :
    whiskerRight (A := A) (a := a) (b := b) (c := c) g (TwoCell.id f) =
      TwoCell.id (Path.trans f g) := by
  simp

/-! ## Interchange Law -/

/-- Interchange law for horizontal and vertical composition. -/
theorem interchange_law
    {f0 f1 f2 : Path a b} {g0 g1 g2 : Path b c}
    (eta1 : TwoCell (A := A) (a := a) (b := b) f0 f1)
    (eta2 : TwoCell (A := A) (a := a) (b := b) f1 f2)
    (theta1 : TwoCell (A := A) (a := b) (b := c) g0 g1)
    (theta2 : TwoCell (A := A) (a := b) (b := c) g1 g2) :
    TwoCell.comp (TwoCell.hcomp (A := A) (a := a) (b := b) (c := c) eta1 theta1)
        (TwoCell.hcomp (A := A) (a := a) (b := b) (c := c) eta2 theta2) =
  TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
        (TwoCell.comp (A := A) (a := a) (b := b)
          (p := f0) (q := f1) (r := f2) eta1 eta2)
        (TwoCell.comp (A := A) (a := b) (b := c)
          (p := g0) (q := g1) (r := g2) theta1 theta2) := by
  simp [TwoCell.comp, TwoCell.hcomp]

/-- Godement interchange: the two whiskering composites agree. -/
@[simp] theorem godement_interchange
    {f f' : Path a b} {g g' : Path b c}
    (eta : TwoCell (A := A) (a := a) (b := b) f f')
    (theta : TwoCell (A := A) (a := b) (b := c) g g') :
    comp (whiskerRight (A := A) (a := a) (b := b) (c := c) g eta)
        (whiskerLeft (A := A) (a := a) (b := b) (c := c) f' theta) =
      comp (whiskerLeft (A := A) (a := a) (b := b) (c := c) f theta)
        (whiskerRight (A := A) (a := a) (b := b) (c := c) g' eta) := by
  apply proof_irrel

end WhiskerOperations
end Path
end ComputationalPaths
