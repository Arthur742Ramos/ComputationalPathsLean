/-
# Bicategory Paths for Computational Paths

This module packages bicategory-level structure carried by computational paths,
reusing the primitive 2-cell operations from `Path.Bicategory` and derived
lemmas from `Path.BicategoryDerived`.

## Key Results

- `Path2Cell`: 2-cells are rewrite equalities between paths.
- `vcomp`/`hcomp`: vertical and horizontal composition of 2-cells.
- `interchange`: functoriality of horizontal composition.
- `pentagon_coherence`/`triangle_identity`: associator and unitor coherences.
- `leftUnitor_naturality`/`rightUnitor_naturality`: unitors are natural.
-/

import ComputationalPaths.Path.Bicategory
import ComputationalPaths.Path.BicategoryDerived

namespace ComputationalPaths
namespace Path
namespace Category

open TwoCell

universe u

variable {A : Type u}
variable {a b c d : A}

/-! ## 2-cells and composition -/

/-- 2-cells between paths are rewrite equalities (`RwEq`). -/
abbrev Path2Cell {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  TwoCell (A := A) (a := a) (b := b) p q

/-- Vertical composition of 2-cells. -/
@[simp] def vcomp {p q r : Path a b}
    (η : Path2Cell (A := A) p q)
    (θ : Path2Cell (A := A) q r) :
    Path2Cell (A := A) p r :=
  TwoCell.comp (A := A) (a := a) (b := b) (p := p) (q := q) (r := r) η θ

/-- Horizontal composition of 2-cells. -/
@[simp] def hcomp {f g : Path a b} {h k : Path b c}
    (η : Path2Cell (A := A) f g)
    (θ : Path2Cell (A := A) h k) :
    Path2Cell (A := A) (Path.trans f h) (Path.trans g k) :=
  TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
    (f := f) (g := g) (h := h) (k := k) η θ

/-! ## Interchange and functoriality -/

/-- Interchange law: horizontal composition is functorial with respect to vertical
composition. -/
@[simp] theorem interchange
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : Path2Cell (A := A) f₀ f₁)
    (η₂ : Path2Cell (A := A) f₁ f₂)
    (θ₁ : Path2Cell (A := A) g₀ g₁)
    (θ₂ : Path2Cell (A := A) g₁ g₂) :
    vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
      hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂) := by
  exact
    (TwoCell.comp_hcomp_hcomp (A := A) (a := a) (b := b) (c := c)
      (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
      (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
      (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂))

/-- Functoriality of horizontal composition (alternate orientation). -/
@[simp] theorem hcomp_functorial
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : Path2Cell (A := A) f₀ f₁)
    (η₂ : Path2Cell (A := A) f₁ f₂)
    (θ₁ : Path2Cell (A := A) g₀ g₁)
    (θ₂ : Path2Cell (A := A) g₁ g₂) :
    hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂) =
      vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) := by
  exact Eq.symm (interchange (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂))

/-- RwEq interchange law: horizontal (`rweq_trans_congr`) and vertical
composition commute. -/
@[simp] theorem interchange_rweq
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : RwEq (A := A) f₀ f₁)
    (η₂ : RwEq (A := A) f₁ f₂)
    (θ₁ : RwEq (A := A) g₀ g₁)
    (θ₂ : RwEq (A := A) g₁ g₂) :
    Nonempty (RwEq (Path.trans f₀ g₀) (Path.trans f₂ g₂)) :=
  ⟨rweq_trans_congr (RwEq.trans η₁ η₂) (RwEq.trans θ₁ θ₂)⟩

/-! ## Coherence laws -/

/-- Pentagon coherence for the associator 2-cell. -/
@[simp] theorem pentagon_coherence
    {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path2Cell (A := A)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  exact
    (TwoCell.pentagon (A := A) (a := a) (b := b) (c := c) (d := d) (e := e)
      p q r s)

/-- Triangle identity for unitors. -/
@[simp] theorem triangle_identity
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path2Cell (A := A)
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) := by
  exact (TwoCell.triangle (A := A) (a := a) (b := b) (c := c) p q)

/-! ## Naturality of unitors -/

/-- Naturality of the left unitor with respect to a 2-cell. -/
@[simp] theorem leftUnitor_naturality {p q : Path a b}
    (η : Path2Cell (A := A) p q) :
    Path2Cell (A := A) (Path.trans (Path.refl a) p) q := by
  exact
    vcomp
      (TwoCell.whiskerLeft (A := A) (a := a) (b := a) (c := b)
        (f := Path.refl a) (g := p) (h := q) η)
      (TwoCell.leftUnitor (A := A) (a := a) (b := b) q)

/-- Naturality of the right unitor with respect to a 2-cell. -/
@[simp] theorem rightUnitor_naturality {p q : Path a b}
    (η : Path2Cell (A := A) p q) :
    Path2Cell (A := A) (Path.trans p (Path.refl b)) q := by
  exact
    vcomp
      (TwoCell.whiskerRight (A := A) (a := a) (b := b) (c := b)
        (f := p) (g := q) (h := Path.refl b) η)
      (TwoCell.rightUnitor (A := A) (a := a) (b := b) q)

/-! ## Summary -/

/-!
We assembled a lightweight bicategory layer for computational paths, providing
explicit 2-cell operations, interchange, and basic coherence/naturality laws.
-/

/-! ## RwEq whiskering -/

/-- Left whiskering for Path2Cell: precomposing a 2-cell with a 1-cell. -/
@[simp] def whiskerLeft' (f : Path a b) {g h : Path b c}
    (η : Path2Cell (A := A) g h) :
    Path2Cell (A := A) (Path.trans f g) (Path.trans f h) :=
  TwoCell.whiskerLeft (A := A) (a := a) (b := b) (c := c) f η

/-- Right whiskering for Path2Cell: postcomposing a 2-cell with a 1-cell. -/
@[simp] def whiskerRight' {f g : Path a b} (h : Path b c)
    (η : Path2Cell (A := A) f g) :
    Path2Cell (A := A) (Path.trans f h) (Path.trans g h) :=
  TwoCell.whiskerRight (A := A) (a := a) (b := b) (c := c) h η

/-- Whiskering distributes over vertical composition (left). -/
@[simp] theorem whiskerLeft_vcomp (f : Path a b) {g h k : Path b c}
    (η : Path2Cell (A := A) g h) (θ : Path2Cell (A := A) h k) :
    whiskerLeft' (A := A) f (vcomp η θ) = vcomp (whiskerLeft' f η) (whiskerLeft' f θ) := by
  apply Subsingleton.elim

/-- Whiskering distributes over vertical composition (right). -/
@[simp] theorem whiskerRight_vcomp {f g h : Path a b} (k : Path b c)
    (η : Path2Cell (A := A) f g) (θ : Path2Cell (A := A) g h) :
    whiskerRight' (A := A) k (vcomp η θ) = vcomp (whiskerRight' k η) (whiskerRight' k θ) := by
  apply Subsingleton.elim

/-- RwEq interchange: horizontal and vertical composition commute. -/
@[simp] theorem rweq_interchange
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : Path2Cell (A := A) f₀ f₁)
    (η₂ : Path2Cell (A := A) f₁ f₂)
    (θ₁ : Path2Cell (A := A) g₀ g₁)
    (θ₂ : Path2Cell (A := A) g₁ g₂) :
    vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
      hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂) :=
  interchange (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- Associator naturality: given 2-cells `η : p ⇒ p'`, `θ : q ⇒ q'`,
`ψ : r ⇒ r'`, the associator is natural in all three arguments.
Both composites yield the same 2-cell
`(p ⬝ q) ⬝ r ⇒ p' ⬝ (q' ⬝ r')`. -/
theorem assoc_naturality {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (η : Path2Cell (A := A) p p') (θ : Path2Cell (A := A) q q')
    (ψ : Path2Cell (A := A) r r') :
    vcomp (hcomp (hcomp η θ) ψ)
      (TwoCell.assoc p' q' r') =
      vcomp (TwoCell.assoc p q r)
        (hcomp η (hcomp θ ψ)) := by
  apply Subsingleton.elim

end Category
end Path
end ComputationalPaths
