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
@[simp] def refl (x : α) : CellPath x x :=
  Path.refl (PLift.up x)

/-- Turn an equality into a computational-path witness. -/
@[simp] def ofEq (h : x = y) : CellPath x y :=
  Path.stepChain (_root_.congrArg PLift.up h)

/-- Vertical composition of higher cells. -/
@[simp] def comp (η : CellPath x y) (θ : CellPath y z) : CellPath x z :=
  Path.trans η θ

end CellPath

/-- Two-cells between computational paths `p` and `q` are rewrite equalities
`RwEq p q`.  These witnesses match the algebraic 2-arrows usually written
`A_{2rw}(a,b)` in the computational-path literature. -/
abbrev TwoCell {A : Type u} {a b : A}
    (p q : Path a b) : Prop :=
  RwEq (A := A) (a := a) (b := b) p q

namespace TwoCell

variable {A : Type u}
variable {a b c d : A}

/-- 3-cells between parallel 2-cells are computational paths between lifted
witnesses. -/
abbrev ThreeCell {p q : Path a b}
    (η θ : TwoCell (A := A) (a := a) (b := b) p q) : Type :=
  CellPath η θ

namespace ThreeCell

@[simp] def refl {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    ThreeCell (A := A) (a := a) (b := b) η η :=
  CellPath.refl η

@[simp] def ofEq {p q : Path a b}
    {η θ : TwoCell (A := A) (a := a) (b := b) p q}
    (h : η = θ) :
    ThreeCell (A := A) (a := a) (b := b) η θ :=
  Path.stepChain (_root_.congrArg PLift.up h)

end ThreeCell

/-- Identity 2-cell on a computational path. -/
@[simp] def id (p : Path a b) : TwoCell (A := A) (a := a) (b := b) p p :=
  RwEq.refl _

/-- Vertical composition of 2-cells (categorical composition inside each
`Hom(a,b)` category). -/
@[simp] def comp {p q r : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q)
    (θ : TwoCell (A := A) (a := a) (b := b) q r) :
    TwoCell (A := A) (a := a) (b := b) p r :=
  RwEq.trans η θ

/-- Vertical composition can be iterated associatively using `RwEq.trans`. -/
@[simp] theorem vcomp_assoc {p q r s : Path a b}
    (η₁ : TwoCell (A := A) (a := a) (b := b) p q)
    (η₂ : TwoCell (A := A) (a := a) (b := b) q r)
    (η₃ : TwoCell (A := A) (a := a) (b := b) r s) :
    TwoCell (A := A) (a := a) (b := b) p s := by
  exact rweq_trans η₁ (rweq_trans η₂ η₃)

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

/-- Left whiskering: precompose a 2-cell with a fixed 1-cell. -/
@[simp] def whiskerLeft (f : Path a b) {g h : Path b c}
    (η : TwoCell (A := A) (a := b) (b := c) g h) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f h) :=
  rweq_trans_congr_right f η

/-- Left whiskering distributes over vertical composition. -/
@[simp] theorem whiskerLeft_comp (f : Path a b) {g₀ g₁ g₂ : Path b c}
    (η₁ : TwoCell (A := A) (a := b) (b := c) g₀ g₁)
    (η₂ : TwoCell (A := A) (a := b) (b := c) g₁ g₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g₀) (Path.trans f g₂) := by
  exact rweq_trans (rweq_trans_congr_right f η₁) (rweq_trans_congr_right f η₂)

/-- Right whiskering: postcompose a 2-cell with a fixed 1-cell. -/
@[simp] def whiskerRight {f g : Path a b} (h : Path b c)
    (η : TwoCell (A := A) (a := a) (b := b) f g) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f h) (Path.trans g h) :=
  rweq_trans_congr_left h η

/-- Right whiskering distributes over vertical composition. -/
@[simp] theorem whiskerRight_comp {f₀ f₁ f₂ : Path a b} (h : Path b c)
    (η₁ : TwoCell (A := A) (a := a) (b := b) f₀ f₁)
    (η₂ : TwoCell (A := A) (a := a) (b := b) f₁ f₂) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f₀ h) (Path.trans f₂ h) := by
  exact rweq_trans (rweq_trans_congr_left h η₁) (rweq_trans_congr_left h η₂)

/-- Whiskering preserves identity 2-cells on the left. -/
@[simp] theorem id2_whiskerLeft (f : Path a b) (g : Path b c) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f g) := by
  exact rweq_trans_congr_right f (RwEq.refl g)

/-- Whiskering preserves identity 2-cells on the right. -/
@[simp] theorem id2_whiskerRight (f : Path a b) (g : Path b c) :
    TwoCell (A := A) (a := a) (b := c) (Path.trans f g) (Path.trans f g) := by
  exact rweq_trans_congr_left g (RwEq.refl f)

/-- Horizontal composition of 2-cells.  This is the operation denoted
`∘ₕ` (or `circ_h`) in many texts and is defined by first whiskering on the
right, then whiskering on the left. -/
@[simp] def hcomp {f g : Path a b} {h k : Path b c}
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
  apply rweq_trans
  · exact rweq_trans_congr_left (q := g₀) (rweq_trans η₁ η₂)
  · exact rweq_trans_congr_right f₂ (rweq_trans θ₁ θ₂)

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

/-- Associator 2-cell witnessing `((hg)f) ⇒ (h(gf))`. -/
@[simp] def assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc (A := A)
    (a := a) (b := b) (c := c) (d := d) p q r)

/-- Naturality of the associator under 2-cells in each argument. -/
@[simp] theorem assoc_naturality
    {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (η : TwoCell (A := A) (a := a) (b := b) p p')
    (θ : TwoCell (A := A) (a := b) (b := c) q q')
    (ι : TwoCell (A := A) (a := c) (b := d) r r') :
    TwoCell (A := A) (a := a) (b := d)
      (Path.trans (Path.trans p q) r)
      (Path.trans p' (Path.trans q' r')) := by
  apply rweq_trans
  · exact rweq_trans_congr_left (q := r) (rweq_trans_congr η θ)
  apply rweq_trans
  · exact rweq_trans_congr_right (Path.trans p' q') ι
  · exact assoc (A := A) (a := a) (b := b) (c := c) (d := d) p' q' r'

/-- Left unitor 2-cell witnessing `(1 ∘ f) ⇒ f`. -/
@[simp] def leftUnitor (p : Path a b) :
    TwoCell (A := A) (a := a) (b := b)
      (Path.trans (Path.refl a) p) p :=
  rweq_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p)

/-- Right unitor 2-cell witnessing `(f ∘ 1) ⇒ f`. -/
@[simp] def rightUnitor (p : Path a b) :
    TwoCell (A := A) (a := a) (b := b)
      (Path.trans p (Path.refl b)) p :=
  rweq_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) p)

/-- Naturality of unitors along a 2-cell. -/
@[simp] theorem unitor_naturality {p q : Path a b}
    (η : TwoCell (A := A) (a := a) (b := b) p q) :
    TwoCell (A := A) (a := a) (b := b)
      (Path.trans (Path.refl a) p)
      (Path.trans q (Path.refl b)) := by
  apply rweq_trans
  · exact rweq_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p)
  apply rweq_trans
  · exact η
  · exact rweq_symm (rweq_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) q))

/-- Horizontal composition exchanges with vertical composition (the
interchange law).  The statement produces the canonical 2-cell that
corresponds to the standard diagrammatic equality from bicategory theory. -/
@[simp] def interchange
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
@[simp] def interchange'
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

/-- Pentagon coherence: any four composable computational paths associate to
the same composite up to a rewrite-equality 2-cell. -/
@[simp] theorem pentagon
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  apply rweq_trans (rweq_trans_congr_left (q := s) (rweq_tt p q r))
  apply rweq_trans (rweq_tt p (Path.trans q r) s)
  exact rweq_trans_congr_right p (rweq_tt q r s)

/-- Triangle coherence: inserting a reflexive path behaves as the identity
up to a rewrite-equality 2-cell. -/
@[simp] theorem triangle
    {a b c : A} (p : Path a b) (q : Path b c) :
    TwoCell (A := A) (a := a) (b := c)
      (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p q) := by
  exact rweq_trans_congr_left (q := q) (rweq_cmpA_refl_right p)

/-- Left route of Mac Lane's pentagon, built by vertical composition of
associator 2-cells and whiskering. -/
@[simp] def pentagonLeftRoute
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
@[simp] def pentagonRightRoute
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
@[simp] def triangleLeftRoute
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
@[simp] def triangleRightRoute
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
@[simp] def pentagonCoherence
    {a b c d e : A}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    ThreeCell (A := A) (a := a) (b := e)
      (pentagonLeftRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s)
      (pentagonRightRoute (A := A) (a := a) (b := b) (c := c) (d := d) (e := e) p q r s) := by
  exact ThreeCell.ofEq
    (pentagon_left_route_eq_right_route (A := A)
      (a := a) (b := b) (c := c) (d := d) (e := e) p q r s)

/-- Triangle coherence promoted to a computational-path 3-cell. -/
@[simp] def triangleCoherence
    {a b c : A} (p : Path a b) (q : Path b c) :
    ThreeCell (A := A) (a := a) (b := c)
      (triangleLeftRoute (A := A) (a := a) (b := b) (c := c) p q)
      (triangleRightRoute (A := A) (a := a) (b := b) (c := c) p q) := by
  exact ThreeCell.ofEq
    (triangle_left_route_eq_right_route (A := A)
      (a := a) (b := b) (c := c) p q)

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
def weakBicategory (A : Type u) :
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

/-- Computational paths organise into a weak 2-groupoid: every path has an
inverse up to rewrite equality. -/
def weakTwoGroupoid (A : Type u) :
    WeakTwoGroupoid (Obj := A) where
  toWeakBicategory := weakBicategory A
  inv₁ := fun {_ _} f => Path.symm f
  leftInv₁ := fun {_ _} f =>
    rweq_cmpA_inv_left (A := A) (p := f)
  rightInv₁ := fun {_ _} f =>
    rweq_cmpA_inv_right (A := A) (p := f)

end Path
end ComputationalPaths
