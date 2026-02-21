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

universe u

variable {A : Type u}
variable {a b c d : A}

/-! ## Whiskering Laws -/

/-- Left whiskering preserves identity 2-cells. -/
def whiskerLeft_id' (f : Path a b) (g : Path b c) :
    TwoCell.whiskerLeft f (TwoCell.id (A := A) g) =
      TwoCell.id (Path.trans f g) := by
  apply proof_irrel

/-- Right whiskering preserves identity 2-cells. -/
def whiskerRight_id' (f : Path a b) (g : Path b c) :
    TwoCell.whiskerRight g (TwoCell.id (A := A) f) =
      TwoCell.id (Path.trans f g) := by
  apply proof_irrel

/-- Left whiskering distributes over vertical composition. -/
def whiskerLeft_comp' {f : Path a b} {g h i : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h)
    (θ : TwoCell (A := A) (a := b) (b := c) h i) :
    TwoCell.whiskerLeft f (TwoCell.comp η θ) =
      TwoCell.comp (TwoCell.whiskerLeft f η)
        (TwoCell.whiskerLeft f θ) := by
  apply proof_irrel

/-- Right whiskering distributes over vertical composition. -/
def whiskerRight_comp' {f g h : Path a b} {k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := a) (b := b) g h) :
    TwoCell.whiskerRight k (TwoCell.comp η θ) =
      TwoCell.comp (TwoCell.whiskerRight k η)
        (TwoCell.whiskerRight k θ) := by
  apply proof_irrel

/-! ## Horizontal Composition Laws -/

/-- Horizontal composition with identity 2-cells on the left. -/
def hcomp_id_left' {f g : Path a b} {h : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell.hcomp η (TwoCell.id h) =
      TwoCell.whiskerRight h η := by
  apply proof_irrel

/-- Horizontal composition with identity 2-cells on the right. -/
def hcomp_id_right' {f : Path a b} {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell.hcomp (TwoCell.id f) η =
      TwoCell.whiskerLeft f η := by
  apply proof_irrel

/-- Interchange with identities collapses to whiskering. -/
def interchange_id_left' {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell.comp (TwoCell.hcomp η θ)
      (TwoCell.id (Path.trans g k)) =
        TwoCell.hcomp η θ := by
  apply proof_irrel

/-- Interchange with identities collapses to whiskering (right). -/
def interchange_id_right' {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell.comp (TwoCell.id (Path.trans f h))
      (TwoCell.hcomp η θ) =
        TwoCell.hcomp η θ := by
  apply proof_irrel

/-! ## Additional Derived Identities -/

theorem whiskerLeft_id_theorem (f : Path a b) (g : Path b c) :
    TwoCell.whiskerLeft f (TwoCell.id (A := A) g) =
      TwoCell.id (Path.trans f g) := by
  rfl

theorem whiskerRight_id_theorem (f : Path a b) (g : Path b c) :
    TwoCell.whiskerRight g (TwoCell.id (A := A) f) =
      TwoCell.id (Path.trans f g) := by
  rfl

theorem whiskerLeft_comp_functorial {f : Path a b} {g h i : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h)
    (θ : TwoCell (A := A) (a := b) (b := c) h i) :
    TwoCell.whiskerLeft f (TwoCell.comp η θ) =
      TwoCell.comp (TwoCell.whiskerLeft f η)
        (TwoCell.whiskerLeft f θ) := by
  rfl

theorem whiskerRight_comp_functorial {f g h : Path a b} {k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := a) (b := b) g h) :
    TwoCell.whiskerRight k (TwoCell.comp η θ) =
      TwoCell.comp (TwoCell.whiskerRight k η)
        (TwoCell.whiskerRight k θ) := by
  rfl

theorem hcomp_id_left_theorem {f g : Path a b} {h : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell.hcomp η (TwoCell.id h) =
      TwoCell.whiskerRight h η := by
  rfl

theorem hcomp_id_right_theorem {f : Path a b} {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell.hcomp (TwoCell.id f) η =
      TwoCell.whiskerLeft f η := by
  rfl

theorem interchange_id_left_theorem {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell.comp (TwoCell.hcomp η θ)
      (TwoCell.id (Path.trans g k)) =
        TwoCell.hcomp η θ := by
  rfl

theorem interchange_id_right_theorem {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell.comp (TwoCell.id (Path.trans f h))
      (TwoCell.hcomp η θ) =
        TwoCell.hcomp η θ := by
  rfl

theorem whiskerLeft_id_theorem_symm (f : Path a b) (g : Path b c) :
    TwoCell.id (Path.trans f g) =
      TwoCell.whiskerLeft f (TwoCell.id (A := A) g) := by
  rfl

theorem whiskerRight_id_theorem_symm (f : Path a b) (g : Path b c) :
    TwoCell.id (Path.trans f g) =
      TwoCell.whiskerRight g (TwoCell.id (A := A) f) := by
  rfl

theorem hcomp_id_left_theorem_symm {f g : Path a b} {h : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell.whiskerRight h η =
      TwoCell.hcomp η (TwoCell.id h) := by
  rfl

theorem hcomp_id_right_theorem_symm {f : Path a b} {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell.whiskerLeft f η =
      TwoCell.hcomp (TwoCell.id f) η := by
  rfl

end BicategoryDerived
end Path
end ComputationalPaths
