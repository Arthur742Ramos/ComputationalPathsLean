/-
# Bicategorical primitives for computational paths

Computational paths (rewrites between elements of a type) naturally assemble
into a weak 2-category: the 0-cells are the elements themselves, 1-cells are
the paths between points, and 2-cells witness rewrites between parallel paths.
This file packages the basic 2-cell operations—vertical composition,
whiskering, horizontal composition, and the canonical associator/unitors—so
that later developments can build the full bicategory structure on top of the
computational-path machinery.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths
namespace Path

universe u

/-- A higher coherence cell carried by a computational path between lifted
witnesses. We use `PLift` so the construction works uniformly for cells living
in any sort (including `Prop`). -/
abbrev CellPath {α : Sort u} (x y : α) : Type u :=
  Path (PLift.up x) (PLift.up y)

namespace CellPath

variable {α : Sort u} {x y z : α}

/-- Identity higher cell. -/
@[simp] noncomputable def refl (x : α) : CellPath x x :=
  Path.refl (PLift.up x)

/-- Turn an equality into a computational-path witness. -/
@[simp] noncomputable def ofEq (h : x = y) : CellPath x y :=
  Path.stepChain (_root_.congrArg PLift.up h)

/-- Vertical composition of higher cells. -/
@[simp] noncomputable def comp (η : CellPath x y) (θ : CellPath y z) : CellPath x z :=
  Path.trans η θ

end CellPath

/-- Two-cells between computational paths `p` and `q` are rewrite equalities
`RwEq p q`.  These witnesses match the algebraic 2-arrows usually written
`A_{2rw}(a,b)` in the computational-path literature. -/
abbrev TwoCell {A : Type u} {a b : A}
    (p q : Path a b) : Prop :=
  RwEqProp (A := A) (a := a) (b := b) p q

namespace TwoCell

variable {A : Type u}
variable {a b c d : A}

/-- 3-cells between parallel 2-cells are computational paths between lifted
witnesses. -/
abbrev ThreeCell {p q : Path a b}
    (η θ : TwoCell (A := A) (a := a) (b := b) p q) : Type :=
  CellPath η θ

namespace ThreeCell

@[simp] noncomputable def refl {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    ThreeCell (A := A) (a := a) (b := b) η η :=
  CellPath.refl η

@[simp] noncomputable def ofEq {p q : Path a b}
    {η θ : TwoCell (A := A) (a := a) (b := b) p q}
    (h : η = θ) :
    ThreeCell (A := A) (a := a) (b := b) η θ :=
  Path.stepChain (_root_.congrArg PLift.up h)

end ThreeCell

/-- Identity 2-cell on a computational path. -/
@[simp] noncomputable def id (p : Path a b) : TwoCell (A := A) (a := a) (b := b) p p :=
  ⟨RwEq.refl _⟩

/-- Vertical composition of 2-cells (categorical composition inside each
`Hom(a,b)` category). -/
@[simp] noncomputable def comp {p q r : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q)
    (θ : TwoCell (A := A) (a := a) (b := b) q r) :
    TwoCell (A := A) (a := a) (b := b) p r := by
  rcases η with ⟨η'⟩
  rcases θ with ⟨θ'⟩
  exact ⟨RwEq.trans η' θ'⟩

/-- Vertical composition can be iterated associatively using `RwEq.trans`. -/
@[simp] theorem vcomp_assoc {p q r s : Path a b}
    (η₁ : TwoCell (A := A) (a := a) (b := b) p q)
    (η₂ : TwoCell (A := A) (a := a) (b := b) q r)
    (η₃ : TwoCell (A := A) (a := a) (b := b) r s) :
    TwoCell (A := A) (a := a) (b := b) p s := by
  rcases η₁ with ⟨η₁'⟩
  rcases η₂ with ⟨η₂'⟩
  rcases η₃ with ⟨η₃'⟩
  exact ⟨rweq_trans η₁' (rweq_trans η₂' η₃')⟩

/-- Vertical composition is associative as an equality of 2-cells. -/
@[simp] theorem vcomp_assoc_eq {p q r s : Path a b}
    (η₁ : TwoCell (A := A) (a := a) (b := b) p q)
    (η₂ : TwoCell (A := A) (a := a) (b := b) q r)
    (η₃ : TwoCell (A := A) (a := a) (b := b) r s) :
    comp (comp η₁ η₂) η₃ = comp η₁ (comp η₂ η₃) := by
  apply Subsingleton.elim

/-- Left identity law for vertical composition. -/
@[simp] theorem vcomp_id_left_eq {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    comp (id (A := A) (a := a) (b := b) p) η = η := by
  apply Subsingleton.elim

/-- Right identity law for vertical composition. -/
@[simp] theorem vcomp_id_right_eq {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    comp η (id (A := A) (a := a) (b := b) q) = η := by
  apply Subsingleton.elim

/-- Vertical composition is functorial in the hom-category sense. -/
@[simp] theorem vertical_functoriality {p q r s : Path a b}
    (η₁ : TwoCell (A := A) (a := a) (b := b) p q)
    (η₂ : TwoCell (A := A) (a := a) (b := b) q r)
    (η₃ : TwoCell (A := A) (a := a) (b := b) r s) :
    comp (comp η₁ η₂) η₃ = comp η₁ (comp η₂ η₃) :=
  vcomp_assoc_eq (A := A) (a := a) (b := b) η₁ η₂ η₃

/-- Step-based vertical functoriality with left-associated composition. -/
@[simp] theorem vcomp_functorial_step_left {p q r s : Path a b}
    (η₁ : TwoCell (A := A) (a := a) (b := b) p q)
    (η₂ : TwoCell (A := A) (a := a) (b := b) q r)
    (η₃ : TwoCell (A := A) (a := a) (b := b) r s) :
    TwoCell (A := A) (a := a) (b := b) p s := by
  rcases η₁ with ⟨η₁'⟩
  rcases η₂ with ⟨η₂'⟩
  rcases η₃ with ⟨η₃'⟩
  exact ⟨rweq_trans (rweq_trans η₁' η₂') η₃'⟩

/-- Step-based vertical functoriality with right-associated composition. -/
@[simp] theorem vcomp_functorial_step_right {p q r s : Path a b}
    (η₁ : TwoCell (A := A) (a := a) (b := b) p q)
    (η₂ : TwoCell (A := A) (a := a) (b := b) q r)
    (η₃ : TwoCell (A := A) (a := a) (b := b) r s) :
    TwoCell (A := A) (a := a) (b := b) p s := by
  rcases η₁ with ⟨η₁'⟩
  rcases η₂ with ⟨η₂'⟩
  rcases η₃ with ⟨η₃'⟩
  exact ⟨rweq_trans η₁' (rweq_trans η₂' η₃')⟩

/-- Vertical composition is functorial in the first variable. -/
@[simp] theorem vcomp_functorial_left_eq {p q r : Path a b}
    {η₁ η₂ : TwoCell (A := A) (a := a) (b := b) p q}
    (θ : TwoCell (A := A) (a := a) (b := b) q r)
    (hη : η₁ = η₂) :
    comp η₁ θ = comp η₂ θ := by
  cases hη
  rfl

/-- Vertical composition is functorial in the second variable. -/
@[simp] theorem vcomp_functorial_right_eq {p q r : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q)
    {θ₁ θ₂ : TwoCell (A := A) (a := a) (b := b) q r}
    (hθ : θ₁ = θ₂) :
    comp η θ₁ = comp η θ₂ := by
  cases hθ
  rfl

/-- Left whiskering: precompose a 2-cell with a fixed 1-cell. -/
@[simp] noncomputable def whiskerLeft (f : Path a b) {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f h) := by
  rcases η with ⟨η'⟩
  exact ⟨rweq_trans_congr_right f η'⟩

/-- Left whiskering distributes over vertical composition. -/
@[simp] theorem whiskerLeft_comp (f : Path a b) {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (η₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g₀) (Path.trans f g₂) := by
  rcases η₁ with ⟨η₁'⟩
  rcases η₂ with ⟨η₂'⟩
  exact ⟨rweq_trans (rweq_trans_congr_right f η₁') (rweq_trans_congr_right f η₂')⟩

/-- Right whiskering: postcompose a 2-cell with a fixed 1-cell. -/
@[simp] noncomputable def whiskerRight {f g : Path a b} (h : Path b c)
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f h) (Path.trans g h) := by
  rcases η with ⟨η'⟩
  exact ⟨rweq_trans_congr_left h η'⟩

/-- Right whiskering distributes over vertical composition. -/
@[simp] theorem whiskerRight_comp {f₀ f₁ f₂ : Path a b} (h : Path b c)
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ h) (Path.trans f₂ h) := by
  rcases η₁ with ⟨η₁'⟩
  rcases η₂ with ⟨η₂'⟩
  exact ⟨rweq_trans (rweq_trans_congr_left h η₁') (rweq_trans_congr_left h η₂')⟩

/-- Whiskering preserves identity 2-cells on the left. -/
@[simp] theorem id2_whiskerLeft (f : Path a b) (g : Path b c) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f g) := by
  exact ⟨rweq_trans_congr_right f (RwEq.refl g)⟩

/-- Whiskering preserves identity 2-cells on the right. -/
@[simp] theorem id2_whiskerRight (f : Path a b) (g : Path b c) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f g) := by
  exact ⟨rweq_trans_congr_left g (RwEq.refl f)⟩

/-- Horizontal composition of 2-cells.  This is the operation denoted
`∘ₕ` (or `circ_h`) in many texts and is defined by first whiskering on the
right, then whiskering on the left. -/
@[simp] noncomputable def hcomp {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans f h) (Path.trans g k) :=
  comp
    (whiskerRight (A := A) (a := a) (b := b) (c := c) (h := h) η)
    (whiskerLeft  (A := A) (a := a) (b := b) (c := c) (f := g) θ)

/-- Naturality of horizontal composition with respect to vertical
composition on both sides. -/
@[simp] theorem hcomp_vcomp_naturality
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ g₀) (Path.trans f₂ g₂) := by
  rcases η₁ with ⟨η₁'⟩
  rcases η₂ with ⟨η₂'⟩
  rcases θ₁ with ⟨θ₁'⟩
  rcases θ₂ with ⟨θ₂'⟩
  exact ⟨rweq_trans
    (rweq_trans_congr_left (q := g₀) (rweq_trans η₁' η₂'))
    (rweq_trans_congr_right f₂ (rweq_trans θ₁' θ₂'))⟩

/-- Step-based horizontal functoriality witness. -/
@[simp] theorem hcomp_functorial_step
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ g₀) (Path.trans f₂ g₂) :=
  hcomp_vcomp_naturality (A := A) (a := a) (b := b) (c := c) η₁ η₂ θ₁ θ₂

/-- Step-based horizontal functoriality in the left variable. -/
@[simp] theorem hcomp_functorial_left_step
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ : TwoCell (A := A) (a := b) (b := c) g₀ g₁) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ g₀) (Path.trans f₂ g₁) := by
  simpa using
    (hcomp_vcomp_naturality (A := A) (a := a) (b := b) (c := c)
      (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
      (g₀ := g₀) (g₁ := g₁) (g₂ := g₁)
      η₁ η₂ θ (id (A := A) (a := b) (b := c) g₁))

/-- Step-based horizontal functoriality in the right variable. -/
@[simp] theorem hcomp_functorial_right_step
    {f₀ f₁ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ g₀) (Path.trans f₁ g₂) := by
  simpa using
    (hcomp_vcomp_naturality (A := A) (a := a) (b := b) (c := c)
      (f₀ := f₀) (f₁ := f₁) (f₂ := f₁)
      (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
      η (id (A := A) (a := a) (b := b) f₁) θ₁ θ₂)

/-- Horizontal composition preserves identity 2-cells in both arguments. -/
@[simp] theorem hcomp_id_eq (f : Path a b) (g : Path b c) :
    hcomp (A := A) (a := a) (b := b) (c := c)
      (id (A := A) (a := a) (b := b) f)
      (id (A := A) (a := b) (b := c) g) =
    id (A := A) (a := a) (b := c) (Path.trans f g) := by
  apply Subsingleton.elim

/-- Horizontal composition is functorial in the left variable. -/
@[simp] theorem hcomp_functorial_left_eq
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ : TwoCell (A := A) (a := b) (b := c) g₀ g₁) :
    comp
      (hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ)
      (hcomp (A := A) (a := a) (b := b) (c := c)
        η₂ (id (A := A) (a := b) (b := c) g₁)) =
    hcomp (A := A) (a := a) (b := b) (c := c)
      (comp (A := A) (a := a) (b := b) η₁ η₂) θ := by
  apply Subsingleton.elim

/-- Horizontal composition is functorial in the right variable. -/
@[simp] theorem hcomp_functorial_right_eq
    {f₀ f₁ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    comp
      (hcomp (A := A) (a := a) (b := b) (c := c) η θ₁)
      (hcomp (A := A) (a := a) (b := b) (c := c)
        (id (A := A) (a := a) (b := b) f₁) θ₂) =
    hcomp (A := A) (a := a) (b := b) (c := c)
      η (comp (A := A) (a := b) (b := c) θ₁ θ₂) := by
  apply Subsingleton.elim

/-- Horizontal composition is functorial in the first variable as equality. -/
@[simp] theorem hcomp_functorial_left_of_eq
    {f₀ f₁ : Path a b} {g₀ g₁ : Path b c}
    {η₁ η₂ : TwoCell (A := A) (a := a) (b := b) f₀ f₁}
    (θ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (hη : η₁ = η₂) :
    hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ =
      hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ := by
  cases hη
  rfl

/-- Horizontal composition is functorial in the second variable as equality. -/
@[simp] theorem hcomp_functorial_right_of_eq
    {f₀ f₁ : Path a b} {g₀ g₁ : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    {θ₁ θ₂ : TwoCell (A := A) (a := b) (b := c) g₀ g₁}
    (hθ : θ₁ = θ₂) :
    hcomp (A := A) (a := a) (b := b) (c := c) η θ₁ =
      hcomp (A := A) (a := a) (b := b) (c := c) η θ₂ := by
  cases hθ
  rfl

/-- Associator 2-cell witnessing `((hg)f) ⇒ (h(gf))`. -/
@[simp] noncomputable def assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  ⟨rweq_of_step (Step.trans_assoc (A := A)
    (a := a) (b := b) (c := c) (d := d) p q r)⟩

/-- Naturality of the associator under 2-cells in each argument. -/
@[simp] theorem assoc_naturality
    {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (η : TwoCell (A := A) (a := a) (b := b) p p')
    (θ : TwoCell (A := A) (a := b) (b := c) q q')
    (ι : TwoCell (A := A) (a := c) (b := d) r r') :
    TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r)
      (Path.trans p' (Path.trans q' r')) := by
  rcases η with ⟨η'⟩
  rcases θ with ⟨θ'⟩
  rcases ι with ⟨ι'⟩
  exact ⟨rweq_trans
    (rweq_trans_congr_left (q := r) (rweq_trans_congr η' θ'))
    (rweq_trans
      (rweq_trans_congr_right (Path.trans p' q') ι')
      (rweq_of_step (Step.trans_assoc (A := A)
        (a := a) (b := b) (c := c) (d := d) p' q' r')))⟩

/-- Left unitor 2-cell witnessing `(1 ∘ f) ⇒ f`. -/
@[simp] noncomputable def leftUnitor (p : Path a b) :
    TwoCell (A := A) (a := a) (b := b)
      (Path.trans (Path.refl a) p) p :=
  ⟨rweq_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p)⟩

/-- Right unitor 2-cell witnessing `(f ∘ 1) ⇒ f`. -/
@[simp] noncomputable def rightUnitor (p : Path a b) :
    TwoCell (A := A) (a := a) (b := b)
      (Path.trans p (Path.refl b)) p :=
  ⟨rweq_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) p)⟩

/-- Naturality of unitors along a 2-cell. -/
@[simp] theorem unitor_naturality {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    TwoCell (A := A) (a := a) (b := b)
      (Path.trans (Path.refl a) p)
      (Path.trans q (Path.refl b)) := by
  rcases η with ⟨η'⟩
  exact ⟨rweq_trans
    (rweq_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p))
    (rweq_trans
      η'
      (rweq_symm (rweq_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) q))))⟩

/-- Horizontal composition exchanges with vertical composition (the
interchange law).  The statement produces the canonical 2-cell that
corresponds to the standard diagrammatic equality from bicategory theory. -/
@[simp] noncomputable def interchange
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans f₀ g₀) (Path.trans f₂ g₂) :=
  comp
    (hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ₁)
    (hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ₂)

/-- The alternative way of composing the same four 2-cells horizontally
then vertically, useful for establishing the interchange equality. -/
@[simp] noncomputable def interchange'
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans f₀ g₀) (Path.trans f₂ g₂) :=
  hcomp (A := A) (a := a) (b := b) (c := c)
    (comp (A := A) (a := a) (b := b) η₁ η₂)
    (comp (A := A) (a := b) (b := c) θ₁ θ₂)

/-- Interchange composite as a canonical step-based 2-cell. -/
@[simp] theorem interchange_step_two_cell
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ g₀) (Path.trans f₂ g₂) :=
  interchange (A := A) (a := a) (b := b) (c := c)
    (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- Alternative interchange composite as a canonical step-based 2-cell. -/
@[simp] theorem interchange'_step_two_cell
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ g₀) (Path.trans f₂ g₂) :=
  interchange' (A := A) (a := a) (b := b) (c := c)
    (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)

/-- Step-based pentagon coherence chain. -/
@[simp] theorem pentagon_step
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  exact ⟨rweq_trans
    (rweq_trans_congr_left (q := s) (rweq_tt p q r))
    (rweq_trans
      (rweq_tt p (Path.trans q r) s)
      (rweq_trans_congr_right p (rweq_tt q r s)))⟩

/-- Pentagon coherence: any four composable computational paths associate to
the same composite up to a rewrite-equality 2-cell. -/
@[simp] theorem pentagon
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  exact pentagon_step (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s

/-- Triangle coherence: inserting a reflexive path behaves as the identity
up to a rewrite-equality 2-cell. -/
@[simp] theorem triangle
    {a b c : A} (p : Path a b) (q : Path b c) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) := by
  exact ⟨rweq_trans_congr_left (q := q) (rweq_cmpA_refl_right p)⟩

/-- Left route of Mac Lane's pentagon, built by vertical composition of
associator 2-cells and whiskering. -/
@[simp] noncomputable def pentagonLeftRoute
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  comp
    (comp
      (whiskerRight (A := A) (a := a) (b := d) (c := e)
        (h := s) (assoc (A := A) (a := a) (b := b) (c := c) (d := d) p q r))
      (assoc (A := A) (a := a) (b := b) (c := d) (d := e)
        p (Path.trans q r) s))
    (whiskerLeft (A := A) (a := a) (b := b) (c := e)
      (f := p) (assoc (A := A) (a := b) (b := c) (c := d) (d := e) q r s))

/-- Right route of Mac Lane's pentagon. -/
@[simp] noncomputable def pentagonRightRoute
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  comp
    (assoc (A := A) (a := a) (b := c) (c := d) (d := e)
      (Path.trans p q) r s)
    (assoc (A := A) (a := a) (b := b) (c := c) (d := e)
      p q (Path.trans r s))

/-- The two pentagon routes are equal as proofs of the same 2-cell statement. -/
@[simp] theorem pentagon_left_route_eq_right_route
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    pentagonLeftRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s =
      pentagonRightRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s := by
  apply Subsingleton.elim

/-- Left route of Mac Lane's triangle. -/
@[simp] noncomputable def triangleLeftRoute
    {a b c : A} (p : Path a b) (q : Path b c) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  comp
    (assoc (A := A) (a := a) (b := b) (c := b) (d := c)
      p (Path.refl b) q)
    (whiskerLeft (A := A) (a := a) (b := b) (c := c)
      (f := p) (leftUnitor (A := A) (a := b) (b := c) q))

/-- Right route of Mac Lane's triangle. -/
@[simp] noncomputable def triangleRightRoute
    {a b c : A} (p : Path a b) (q : Path b c) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) :=
  whiskerRight (A := A) (a := a) (b := b) (c := c)
    (h := q) (rightUnitor (A := A) (a := a) (b := b) p)

/-- The two triangle routes are equal as proofs of the same 2-cell statement. -/
@[simp] theorem triangle_left_route_eq_right_route
    {a b c : A} (p : Path a b) (q : Path b c) :
    triangleLeftRoute (A := A) (a := a) (b := b) (c := c) p q =
      triangleRightRoute (A := A) (a := a) (b := b) (c := c) p q := by
  apply Subsingleton.elim

/-- Interchange law: vertical composition of horizontal composites agrees with
horizontal composition of vertical composites. -/
@[simp] theorem interchange_law
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    comp
        (hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ₁)
        (hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ₂) =
      hcomp (A := A) (a := a) (b := b) (c := c)
        (comp (A := A) (a := a) (b := b) η₁ η₂)
        (comp (A := A) (a := b) (b := c) θ₁ θ₂) := by
  apply Subsingleton.elim

/-- Interchange in canonical form: `interchange` equals horizontal composition
of vertical composites. -/
@[simp] theorem interchange_eq_hcomp_vcomp
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    interchange (A := A) (a := a) (b := b) (c := c)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂) =
      hcomp (A := A) (a := a) (b := b) (c := c)
        (comp (A := A) (a := a) (b := b) η₁ η₂)
        (comp (A := A) (a := b) (b := c) θ₁ θ₂) := by
  simpa [interchange] using
    (interchange_law (A := A) (a := a) (b := b) (c := c) η₁ η₂ θ₁ θ₂)

/-- The alternative interchange composite equals the vertical composite of
horizontal composites. -/
@[simp] theorem interchange'_eq_vcomp_hcomp
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    interchange' (A := A) (a := a) (b := b) (c := c)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂) =
      comp
        (hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ₁)
        (hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ₂) := by
  simpa [interchange'] using
    (interchange_law (A := A) (a := a) (b := b) (c := c) η₁ η₂ θ₁ θ₂).symm

/-- Explicit pentagon coherence as a canonical 2-cell. -/
@[simp] theorem pentagon_coherence_two_cell
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  pentagon (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s

/-- Horizontal composition is functorial with respect to vertical composition. -/
@[simp] theorem horizontal_functoriality
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    comp
        (hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ₁)
        (hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ₂) =
      hcomp (A := A) (a := a) (b := b) (c := c)
        (comp (A := A) (a := a) (b := b) η₁ η₂)
        (comp (A := A) (a := b) (b := c) θ₁ θ₂) :=
  interchange_law (A := A) (a := a) (b := b) (c := c) η₁ η₂ θ₁ θ₂

/-- Pentagon coherence promoted to a computational-path 3-cell. -/
@[simp] noncomputable def pentagonCoherence
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    ThreeCell (A := A) (a := a) (b := e)
      (pentagonLeftRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s)
      (pentagonRightRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s) :=
  Path.stepChain
    (_root_.congrArg PLift.up
      (pentagon_left_route_eq_right_route (A := A)
        (a := a) (b := b) (c := c) (d := d) (e := e) p q r s))

/-- Triangle coherence promoted to a computational-path 3-cell. -/
@[simp] noncomputable def triangleCoherence
    {a b c : A} (p : Path a b) (q : Path b c) :
    ThreeCell (A := A) (a := a) (b := c)
      (triangleLeftRoute (A := A) (a := a) (b := b) (c := c) p q)
      (triangleRightRoute (A := A) (a := a) (b := b) (c := c) p q) :=
  Path.stepChain
    (_root_.congrArg PLift.up
      (triangle_left_route_eq_right_route (A := A)
        (a := a) (b := b) (c := c) p q))

/-- The pentagon 3-cell is exactly the lifted route-equality step chain. -/
@[simp] theorem pentagonCoherence_toEq
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Path.toEq (pentagonCoherence (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s) =
      _root_.congrArg PLift.up
        (pentagon_left_route_eq_right_route (A := A)
          (a := a) (b := b) (c := c) (d := d) (e := e) p q r s) := by
  rfl

/-- The triangle 3-cell is exactly the lifted route-equality step chain. -/
@[simp] theorem triangleCoherence_toEq
    {a b c : A} (p : Path a b) (q : Path b c) :
    Path.toEq (triangleCoherence (A := A) (a := a) (b := b) (c := c) p q) =
      _root_.congrArg PLift.up
        (triangle_left_route_eq_right_route (A := A)
          (a := a) (b := b) (c := c) p q) := by
  rfl

/-- Pentagon coherence is left-unital under 3-cell composition. -/
@[simp] theorem pentagonCoherence_comp_left_refl
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    CellPath.comp
      (CellPath.refl
        (pentagonLeftRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s))
      (pentagonCoherence (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s) =
    pentagonCoherence (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s := by
  simp [CellPath.comp, CellPath.refl]

/-- Pentagon coherence is right-unital under 3-cell composition. -/
@[simp] theorem pentagonCoherence_comp_right_refl
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    CellPath.comp
      (pentagonCoherence (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s)
      (CellPath.refl
        (pentagonRightRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s)) =
    pentagonCoherence (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s := by
  simp [CellPath.comp, CellPath.refl]

/-- Every 2-cell is invertible (since TwoCell lives in Prop). -/
@[simp] noncomputable def inv {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    TwoCell (A := A) (a := a) (b := b) q p := by
  rcases η with ⟨η'⟩
  exact ⟨RwEq.symm η'⟩

/-- Left inverse law for 2-cell inversion. -/
theorem inv_comp_cancel {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    comp (inv η) η = RwEq.refl q := by
  apply Subsingleton.elim

/-- Right inverse law for 2-cell inversion. -/
theorem comp_inv_cancel {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    comp η (inv η) = RwEq.refl p := by
  apply Subsingleton.elim

/-- Double inversion is the identity. -/
@[simp] theorem inv_inv {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    inv (inv η) = η := by
  apply Subsingleton.elim

/-- Inversion reverses vertical composition (anti-homomorphism). -/
@[simp] theorem inv_comp_antihom {p q r : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q)
    (θ : TwoCell (A := A) (a := a) (b := b) q r) :
    inv (comp η θ) = comp (inv θ) (inv η) := by
  apply Subsingleton.elim

/-- Inversion distributes over horizontal composition. -/
@[simp] theorem inv_hcomp_distrib {f g : Path a b} {h k : Path b c}
    (η : TwoCell (A := A) (a := a) (b := b) f g)
    (θ : TwoCell (A := A) (a := b) (b := c) h k) :
    inv (hcomp (A := A) (a := a) (b := b) (c := c) η θ) =
      hcomp (A := A) (a := a) (b := b) (c := c) (inv η) (inv θ) := by
  apply Subsingleton.elim

/-- Left whiskering commutes with inversion. -/
@[simp] theorem whiskerLeft_inv (f : Path a b) {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    inv (whiskerLeft (A := A) (a := a) (b := b) (c := c) f η) =
      whiskerLeft (A := A) (a := a) (b := b) (c := c) f (inv η) := by
  apply Subsingleton.elim

/-- Right whiskering commutes with inversion. -/
@[simp] theorem whiskerRight_inv {f g : Path a b} (h : Path b c)
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    inv (whiskerRight (A := A) (a := a) (b := b) (c := c) h η) =
      whiskerRight (A := A) (a := a) (b := b) (c := c) h (inv η) := by
  apply Subsingleton.elim

/-- The identity 2-cell is self-inverse. -/
@[simp] theorem inv_id (p : Path a b) :
    inv (id (A := A) (a := a) (b := b) p) = id (A := A) (a := a) (b := b) p := by
  apply Subsingleton.elim

/-- The associator is invertible with explicit inverse. -/
@[simp] noncomputable def assoc_inv (p : Path a b) (q : Path b c) (r : Path c d) :
    TwoCell (A := A) (a := a) (b := d)
      (Path.trans p (Path.trans q r))
      (Path.trans (Path.trans p q) r) :=
  inv (assoc (A := A) (a := a) (b := b) (c := c) (d := d) p q r)

/-- The left unitor is invertible with explicit inverse. -/
@[simp] noncomputable def leftUnitor_inv (p : Path a b) :
    TwoCell (A := A) (a := a) (b := b)
      p (Path.trans (Path.refl a) p) :=
  inv (leftUnitor (A := A) (a := a) (b := b) p)

/-- The right unitor is invertible with explicit inverse. -/
@[simp] noncomputable def rightUnitor_inv (p : Path a b) :
    TwoCell (A := A) (a := a) (b := b)
      p (Path.trans p (Path.refl b)) :=
  inv (rightUnitor (A := A) (a := a) (b := b) p)

/-- The associator composes with its inverse to the identity (left). -/
theorem assoc_assoc_inv (p : Path a b) (q : Path b c) (r : Path c d) :
    comp (assoc (A := A) (a := a) (b := b) (c := c) (d := d) p q r)
      (assoc_inv (A := A) (a := a) (b := b) (c := c) (d := d) p q r) =
    RwEq.refl (Path.trans (Path.trans p q) r) := by
  apply Subsingleton.elim

/-- The associator composes with its inverse to the identity (right). -/
theorem assoc_inv_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    comp (assoc_inv (A := A) (a := a) (b := b) (c := c) (d := d) p q r)
      (assoc (A := A) (a := a) (b := b) (c := c) (d := d) p q r) =
    RwEq.refl (Path.trans p (Path.trans q r)) := by
  apply Subsingleton.elim

/-- Eckmann-Hilton: for endomorphism 2-cells on the reflexivity path,
vertical composition is commutative. -/
@[simp] theorem eckmann_hilton
    (η θ : TwoCell (A := A) (a := a) (b := a) (Path.refl a) (Path.refl a)) :
    comp η θ = comp θ η := by
  apply Subsingleton.elim

/-- The two standard ways of composing four 2-cells coincide.  Since
`TwoCell` values live in `Prop`, the equality follows from proof
irrelevance, but the lemma is recorded for convenient rewriting. -/
@[simp] theorem interchange_eq_interchange'
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    interchange (A := A) (a := a) (b := b) (c := c)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂) =
      interchange' (A := A) (a := a) (b := b) (c := c)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂) := by
  apply Subsingleton.elim

/-- Convenient `simp`-friendly restatement of the interchange law.  It
rewrites a vertical composite of horizontal composites into a horizontal
composite of vertical composites. -/
@[simp] theorem comp_hcomp_hcomp
    {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂)
    (θ₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (θ₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    comp
        (hcomp (A := A) (a := a) (b := b) (c := c) η₁ θ₁)
        (hcomp (A := A) (a := a) (b := b) (c := c) η₂ θ₂) =
      hcomp (A := A) (a := a) (b := b) (c := c)
        (comp (A := A) (a := a) (b := b)
          (p := f₀) (q := f₁) (r := f₂) η₁ η₂)
        (comp (A := A) (a := b) (b := c)
          (p := g₀) (q := g₁) (r := g₂) θ₁ θ₂) := by
  exact interchange_law (A := A) (a := a) (b := b) (c := c) η₁ η₂ θ₁ θ₂

end TwoCell

namespace Tactic

open Lean.Elab.Tactic

syntax (name := rwEqAuto) "rwEq_auto" : tactic

macro_rules
  | `(tactic| rwEq_auto) =>
      `(tactic|
        first
          | simp (config := {contextual := true})
          | exact RwEq.refl _
          | refine RwEq.symm ?_; rwEq_auto
          | refine RwEq.trans ?_ ?_; first | rwEq_auto | rwEq_auto)

syntax (name := twoCellAuto) "twoCell_auto" : tactic

macro_rules
  | `(tactic| twoCell_auto) =>
      `(tactic| rwEq_auto)

end Tactic

section WeakBicategoryStructure

universe u' v w

/-- Data and coherence laws for a weak bicategory.  The record is formulated
using explicit 1- and 2-cell operations so that concrete models (such as
computational paths) can be packaged into this interface. -/
structure WeakBicategory (Obj : Type u') where
  Hom : Obj → Obj → Sort v
  TwoCell : ∀ {a b : Obj}, Hom a b → Hom a b → Sort w
  id₁ : ∀ a, Hom a a
  comp :
    ∀ {a b c : Obj}, Hom a b → Hom b c → Hom a c
  id₂ :
    ∀ {a b : Obj} (f : Hom a b), TwoCell f f
  vcomp :
    ∀ {a b : Obj} {f g h : Hom a b},
      TwoCell f g → TwoCell g h → TwoCell f h
  whiskerLeft :
    ∀ {a b c : Obj} (f : Hom a b) {g h : Hom b c},
      TwoCell g h → TwoCell (comp f g) (comp f h)
  whiskerRight :
    ∀ {a b c : Obj} {f g : Hom a b} (h : Hom b c),
      TwoCell f g → TwoCell (comp f h) (comp g h)
  hcomp :
    ∀ {a b c : Obj} {f g : Hom a b} {h k : Hom b c},
      TwoCell f g → TwoCell h k →
        TwoCell (comp f h) (comp g k)
  assoc :
    ∀ {a b c d : Obj},
      (f : Hom a b) → (g : Hom b c) → (h : Hom c d) →
      TwoCell (comp (comp f g) h) (comp f (comp g h))
  leftUnitor :
    ∀ {a b : Obj} (f : Hom a b),
      TwoCell (comp (id₁ a) f) f
  rightUnitor :
    ∀ {a b : Obj} (f : Hom a b),
      TwoCell (comp f (id₁ b)) f
  pentagon :
    ∀ {a b c d e : Obj},
      (f : Hom a b) → (g : Hom b c) → (h : Hom c d) → (k : Hom d e) →
      TwoCell (comp (comp (comp f g) h) k)
              (comp f (comp g (comp h k)))
  triangle :
    ∀ {a b c : Obj},
      (f : Hom a b) → (g : Hom b c) →
      TwoCell (comp (comp f (id₁ b)) g) (comp f g)

end WeakBicategoryStructure

section WeakTwoGroupoidStructure

/-- Weak 2-groupoid: a weak bicategory where every 1-cell admits a
weak inverse (up to 2-cells). -/
structure WeakTwoGroupoid (Obj : Type u')
    extends WeakBicategory Obj where
  /-- Inversion on 1-cells. -/
  inv₁ :
    ∀ {a b : Obj}, Hom a b → Hom b a
  /-- Left inverse law witnessed by a 2-cell. -/
  leftInv₁ :
    ∀ {a b : Obj} (f : Hom a b),
      TwoCell (comp (inv₁ f) f) (id₁ b)
  /-- Right inverse law witnessed by a 2-cell. -/
  rightInv₁ :
    ∀ {a b : Obj} (f : Hom a b),
      TwoCell (comp f (inv₁ f)) (id₁ a)

end WeakTwoGroupoidStructure

/-- Computational paths and rewrite-equality 2-cells form a weak bicategory. -/
noncomputable def weakBicategory (A : Type u) :
    WeakBicategory (Obj := A) where
  Hom := fun a b => Path a b
  TwoCell := fun {a b} p q =>
    TwoCell (A := A) (a := a) (b := b) p q
  id₁ := fun a => Path.refl a
  comp := fun p q => Path.trans p q
  id₂ := fun {a b} f =>
    TwoCell.id (A := A) (a := a) (b := b) f
  vcomp := fun {a b} {f g h} η θ =>
    TwoCell.comp (A := A) (a := a) (b := b)
      (p := f) (q := g) (r := h) η θ
  whiskerLeft := fun {a b c} f {g h} η =>
    (TwoCell.whiskerLeft (A := A) (a := a) (b := b) (c := c)
      (f := f) (g := g) (h := h) η)
  whiskerRight := fun {a b c} {f g} h η =>
    (TwoCell.whiskerRight (A := A) (a := a) (b := b) (c := c)
      (f := f) (g := g) (h := h) η)
  hcomp := fun {a b c} {f g} {h k} η θ =>
    (TwoCell.hcomp (A := A) (a := a) (b := b) (c := c)
      (f := f) (g := g) (h := h) (k := k) η θ)
  assoc := fun {a b c d} f g h =>
    TwoCell.assoc (A := A) (a := a) (b := b) (c := c) (d := d) f g h
  leftUnitor := fun {a b} (f : Path a b) =>
    TwoCell.leftUnitor (A := A) (a := a) (b := b) f
  rightUnitor := fun {a b} (f : Path a b) =>
    TwoCell.rightUnitor (A := A) (a := a) (b := b) f
  pentagon := fun {a b c d e}
      (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) =>
    TwoCell.pentagon (A := A) (a := a) (b := b) (c := c)
      (d := d) (e := e) f g h k
  triangle := fun {a b c} (f : Path a b) (g : Path b c) =>
    TwoCell.triangle (A := A) (a := a) (b := b) (c := c) f g

/-- Explicit bicategory interface with invertible associator and unitors. -/
class Bicategory (Obj : Type u') extends WeakBicategory (Obj := Obj) where
  assocInv :
    ∀ {a b c d : Obj},
      (f : Hom a b) → (g : Hom b c) → (h : Hom c d) →
      TwoCell (comp f (comp g h)) (comp (comp f g) h)
  leftUnitorInv :
    ∀ {a b : Obj} (f : Hom a b),
      TwoCell f (comp (id₁ a) f)
  rightUnitorInv :
    ∀ {a b : Obj} (f : Hom a b),
      TwoCell f (comp f (id₁ b))
  assoc_left_inverse :
    ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
      vcomp (assoc f g h) (assocInv f g h) = id₂ (comp (comp f g) h)
  assoc_right_inverse :
    ∀ {a b c d : Obj} (f : Hom a b) (g : Hom b c) (h : Hom c d),
      vcomp (assocInv f g h) (assoc f g h) = id₂ (comp f (comp g h))
  leftUnitor_left_inverse :
    ∀ {a b : Obj} (f : Hom a b),
      vcomp (leftUnitor f) (leftUnitorInv f) = id₂ (comp (id₁ a) f)
  leftUnitor_right_inverse :
    ∀ {a b : Obj} (f : Hom a b),
      vcomp (leftUnitorInv f) (leftUnitor f) = id₂ f
  rightUnitor_left_inverse :
    ∀ {a b : Obj} (f : Hom a b),
      vcomp (rightUnitor f) (rightUnitorInv f) = id₂ (comp f (id₁ b))
  rightUnitor_right_inverse :
    ∀ {a b : Obj} (f : Hom a b),
      vcomp (rightUnitorInv f) (rightUnitor f) = id₂ f

/-- The bicategory of computational paths `𝔅_A` (Chapter 7): objects are points
of `A`, 1-cells are computational paths, and 2-cells are rewrite equivalences. -/
noncomputable instance pathBicategory (A : Type u) : Bicategory A where
  toWeakBicategory := weakBicategory A
  assocInv := fun {a b c d} f g h =>
    TwoCell.assoc_inv (A := A) (a := a) (b := b) (c := c) (d := d) f g h
  leftUnitorInv := fun {a b} f =>
    TwoCell.leftUnitor_inv (A := A) (a := a) (b := b) f
  rightUnitorInv := fun {a b} f =>
    TwoCell.rightUnitor_inv (A := A) (a := a) (b := b) f
  assoc_left_inverse := by
    intro a b c d f g h
    apply Subsingleton.elim
  assoc_right_inverse := by
    intro a b c d f g h
    apply Subsingleton.elim
  leftUnitor_left_inverse := by
    intro a b f
    apply Subsingleton.elim
  leftUnitor_right_inverse := by
    intro a b f
    apply Subsingleton.elim
  rightUnitor_left_inverse := by
    intro a b f
    apply Subsingleton.elim
  rightUnitor_right_inverse := by
    intro a b f
    apply Subsingleton.elim

/-- Computational paths organise into a weak 2-groupoid: every path has an
inverse up to rewrite equality. -/
noncomputable def weakTwoGroupoid (A : Type u) :
    WeakTwoGroupoid (Obj := A) where
  toWeakBicategory := weakBicategory A
  inv₁ := fun {_ _} f => Path.symm f
  leftInv₁ := fun {_ _} f =>
    ⟨rweq_cmpA_inv_left (A := A) (p := f)⟩
  rightInv₁ := fun {_ _} f =>
    ⟨rweq_cmpA_inv_right (A := A) (p := f)⟩

end Path
end ComputationalPaths
