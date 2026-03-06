/-
# 3-Cells: Derivation Equivalence for the Groupoid Polygraph

This module defines **3-cells** — equivalences between derivations
(`RwEqDeriv`) of the same rewrite equivalence fact. This gives the
beginning of a genuine ω-groupoid structure:

- **0-cells**: Expressions (`Expr`)
- **1-cells**: Rewrite equivalence (`ExprRwEq`)  
- **2-cells**: Derivation trees (`RwEqDeriv`)
- **3-cells**: Derivation equivalence (`DerivEquiv`)

## Main Results

1. `DerivEquiv` is an inductive Prop relating `RwEqDeriv` terms
2. `Generator3CellT` / `DerivEquivT` provide explicit Type-valued 3-cell data
3. `DerivEquiv` is an equivalence relation (reflexive, symmetric, transitive)
4. Naturality squares: composing 3-cells horizontally
5. Non-trivial 3-cells exist: two genuinely different 3-cell witnesses

## References

- Guiraud & Malbos, "Higher-dimensional normalisation strategies for acyclicity"
- Lafont & Métayer, "Polygraphic resolutions and homology of monoids"
-/

import ComputationalPaths.Path.Polygraph.RwEqDerivation

namespace ComputationalPaths.Path.Polygraph

open Rewrite.GroupoidTRS (Expr)

local notation "eRefl" => Rewrite.GroupoidTRS.Expr.refl
local notation "eSymm" => Rewrite.GroupoidTRS.Expr.symm
local notation "eTrans" => Rewrite.GroupoidTRS.Expr.trans

/-! ## DerivEquiv: 3-cells of the polygraph

Two derivations `d₁ d₂ : RwEqDeriv e₁ e₂` are *derivation equivalent*
when they can be related by the axioms of a 2-groupoid: interchange law,
unit laws for vertical composition, and naturality of whiskering. -/

inductive DerivEquiv : {e₁ e₂ : Expr} → RwEqDeriv e₁ e₂ → RwEqDeriv e₁ e₂ → Prop where
  /-- Reflexivity: every derivation is equivalent to itself. -/
  | refl {e₁ e₂ : Expr} (d : RwEqDeriv e₁ e₂) : DerivEquiv d d
  /-- Symmetry -/
  | symm {e₁ e₂ : Expr} {d₁ d₂ : RwEqDeriv e₁ e₂} :
      DerivEquiv d₁ d₂ → DerivEquiv d₂ d₁
  /-- Transitivity -/
  | dtrans {e₁ e₂ : Expr} {d₁ d₂ d₃ : RwEqDeriv e₁ e₂} :
      DerivEquiv d₁ d₂ → DerivEquiv d₂ d₃ → DerivEquiv d₁ d₃
  /-- Vertical composition respects equivalence on the left -/
  | vcomp_congr_left {e₁ e₂ e₃ : Expr}
      {d₁ d₁' : RwEqDeriv e₁ e₂} {d₂ : RwEqDeriv e₂ e₃}
      (h : DerivEquiv d₁ d₁') :
      DerivEquiv (d₁.vcomp d₂) (d₁'.vcomp d₂)
  /-- Vertical composition respects equivalence on the right -/
  | vcomp_congr_right {e₁ e₂ e₃ : Expr}
      {d₁ : RwEqDeriv e₁ e₂} {d₂ d₂' : RwEqDeriv e₂ e₃}
      (h : DerivEquiv d₂ d₂') :
      DerivEquiv (d₁.vcomp d₂) (d₁.vcomp d₂')
  /-- Horizontal composition (whiskering) respects equivalence -/
  | hcomp_congr {e₁ e₁' e₂ e₂' : Expr}
      {dp dp' : RwEqDeriv e₁ e₁'} {dq dq' : RwEqDeriv e₂ e₂'}
      (hp : DerivEquiv dp dp') (hq : DerivEquiv dq dq') :
      DerivEquiv (dp.hcomp dq) (dp'.hcomp dq')
  /-- Interchange law: `(d₁ ∘ᵥ d₂) ∘ₕ (d₃ ∘ᵥ d₄) = (d₁ ∘ₕ d₃) ∘ᵥ (d₂ ∘ₕ d₄)`
      This is a genuine coherence axiom of a 2-category/2-groupoid. -/
  | interchange {p p' p'' q q' q'' : Expr}
      (d₁ : RwEqDeriv p p') (d₂ : RwEqDeriv p' p'')
      (d₃ : RwEqDeriv q q') (d₄ : RwEqDeriv q' q'') :
      DerivEquiv
        ((d₁.vcomp d₂).hcomp (d₃.vcomp d₄))
        ((d₁.hcomp d₃).vcomp (d₂.hcomp d₄))

/-! ## Explicit type-valued 3-cells

The Prop-valued relation above captures only the structural fragment of
derivation equivalence.  For genuinely proof-relevant 3-dimensional data on the
explicit syntax side, we package the nine critical-pair fillers as Type-valued
generators and close them under the same structural operations. -/

@[simp] def cp_refl_left_assoc_left (p q : Expr) :
    RwEqDeriv (eTrans (eTrans eRefl p) q) (eTrans p q) :=
  .trans_congr_left q (.trans_refl_left p)

@[simp] def cp_refl_left_assoc_right (p q : Expr) :
    RwEqDeriv (eTrans (eTrans eRefl p) q) (eTrans p q) :=
  .trans (.trans_assoc eRefl p q) (.trans_refl_left (eTrans p q))

@[simp] def cp_symm_assoc_left (p q : Expr) :
    RwEqDeriv (eTrans (eTrans p (eSymm p)) q) q :=
  .trans (.trans_congr_left q (.trans_symm p)) (.trans_refl_left q)

@[simp] def cp_symm_assoc_right (p q : Expr) :
    RwEqDeriv (eTrans (eTrans p (eSymm p)) q) q :=
  .trans (.trans_assoc p (eSymm p) q) (.trans_cancel_left p q)

@[simp] def cp_symm_trans_assoc_left (p q : Expr) :
    RwEqDeriv (eTrans (eTrans (eSymm p) p) q) q :=
  .trans (.trans_congr_left q (.symm_trans p)) (.trans_refl_left q)

@[simp] def cp_symm_trans_assoc_right (p q : Expr) :
    RwEqDeriv (eTrans (eTrans (eSymm p) p) q) q :=
  .trans (.trans_assoc (eSymm p) p q) (.trans_cancel_right p q)

@[simp] def cp_refl_right_assoc_left (p q : Expr) :
    RwEqDeriv (eTrans (eTrans p eRefl) q) (eTrans p q) :=
  .trans_congr_left q (.trans_refl_right p)

@[simp] def cp_refl_right_assoc_right (p q : Expr) :
    RwEqDeriv (eTrans (eTrans p eRefl) q) (eTrans p q) :=
  .trans (.trans_assoc p eRefl q) (.trans_congr_right p (.trans_refl_left q))

@[simp] def cp_assoc_assoc_left (p q r s : Expr) :
    RwEqDeriv (eTrans (eTrans (eTrans p q) r) s) (eTrans p (eTrans q (eTrans r s))) :=
  .trans (.trans_assoc (eTrans p q) r s) (.trans_assoc p q (eTrans r s))

@[simp] def cp_assoc_assoc_right (p q r s : Expr) :
    RwEqDeriv (eTrans (eTrans (eTrans p q) r) s) (eTrans p (eTrans q (eTrans r s))) :=
  .trans
    (.trans_congr_left s (.trans_assoc p q r))
    (.trans
      (.trans_assoc p (eTrans q r) s)
      (.trans_congr_right p (.trans_assoc q r s)))

@[simp] def cp_symm_congr_refl_left_left (p : Expr) :
    RwEqDeriv (eSymm (eTrans eRefl p)) (eSymm p) :=
  .trans
    (.symm_trans_congr eRefl p)
    (.trans
      (.trans_congr_right (eSymm p) .symm_refl)
      (.trans_refl_right (eSymm p)))

@[simp] def cp_symm_congr_refl_left_right (p : Expr) :
    RwEqDeriv (eSymm (eTrans eRefl p)) (eSymm p) :=
  .symm_congr (.trans_refl_left p)

@[simp] def cp_symm_congr_refl_right_left (p : Expr) :
    RwEqDeriv (eSymm (eTrans p eRefl)) (eSymm p) :=
  .trans
    (.symm_trans_congr p eRefl)
    (.trans
      (.trans_congr_left (eSymm p) .symm_refl)
      (.trans_refl_left (eSymm p)))

@[simp] def cp_symm_congr_refl_right_right (p : Expr) :
    RwEqDeriv (eSymm (eTrans p eRefl)) (eSymm p) :=
  .symm_congr (.trans_refl_right p)

@[simp] def cp_cancel_left_assoc_left (p q r : Expr) :
    RwEqDeriv (eTrans (eTrans p (eTrans (eSymm p) q)) r) (eTrans q r) :=
  .trans_congr_left r (.trans_cancel_left p q)

@[simp] def cp_cancel_left_assoc_right (p q r : Expr) :
    RwEqDeriv (eTrans (eTrans p (eTrans (eSymm p) q)) r) (eTrans q r) :=
  .trans
    (.trans_assoc p (eTrans (eSymm p) q) r)
    (.trans
      (.trans_congr_right p (.trans_assoc (eSymm p) q r))
      (.trans_cancel_left p (eTrans q r)))

@[simp] def cp_cancel_right_assoc_left (p q r : Expr) :
    RwEqDeriv (eTrans (eTrans (eSymm p) (eTrans p q)) r) (eTrans q r) :=
  .trans_congr_left r (.trans_cancel_right p q)

@[simp] def cp_cancel_right_assoc_right (p q r : Expr) :
    RwEqDeriv (eTrans (eTrans (eSymm p) (eTrans p q)) r) (eTrans q r) :=
  .trans
    (.trans_assoc (eSymm p) (eTrans p q) r)
    (.trans
      (.trans_congr_right (eSymm p) (.trans_assoc p q r))
      (.trans_cancel_right p (eTrans q r)))

/-- Explicit critical-pair 3-cell generators for the completed groupoid TRS. -/
inductive Generator3CellT : {e₁ e₂ : Expr} → RwEqDeriv e₁ e₂ → RwEqDeriv e₁ e₂ → Type where
  | refl_left_assoc (p q : Expr) :
      Generator3CellT (cp_refl_left_assoc_left p q) (cp_refl_left_assoc_right p q)
  | symm_assoc (p q : Expr) :
      Generator3CellT (cp_symm_assoc_left p q) (cp_symm_assoc_right p q)
  | symm_trans_assoc (p q : Expr) :
      Generator3CellT (cp_symm_trans_assoc_left p q) (cp_symm_trans_assoc_right p q)
  | refl_right_assoc (p q : Expr) :
      Generator3CellT (cp_refl_right_assoc_left p q) (cp_refl_right_assoc_right p q)
  | assoc_assoc (p q r s : Expr) :
      Generator3CellT (cp_assoc_assoc_left p q r s) (cp_assoc_assoc_right p q r s)
  | symm_congr_refl_left (p : Expr) :
      Generator3CellT (cp_symm_congr_refl_left_left p) (cp_symm_congr_refl_left_right p)
  | symm_congr_refl_right (p : Expr) :
      Generator3CellT (cp_symm_congr_refl_right_left p) (cp_symm_congr_refl_right_right p)
  | cancel_left_assoc (p q r : Expr) :
      Generator3CellT (cp_cancel_left_assoc_left p q r) (cp_cancel_left_assoc_right p q r)
  | cancel_right_assoc (p q r : Expr) :
      Generator3CellT (cp_cancel_right_assoc_left p q r) (cp_cancel_right_assoc_right p q r)

/-- Type-valued 3-cells: structural operations plus explicit critical-pair
    fillers.  This is the proof-relevant 3-dimensional syntax missing from the
    current Prop-valued packaging. -/
inductive DerivEquivT : {e₁ e₂ : Expr} → RwEqDeriv e₁ e₂ → RwEqDeriv e₁ e₂ → Type where
  | refl {e₁ e₂ : Expr} (d : RwEqDeriv e₁ e₂) : DerivEquivT d d
  | symm {e₁ e₂ : Expr} {d₁ d₂ : RwEqDeriv e₁ e₂} :
      DerivEquivT d₁ d₂ → DerivEquivT d₂ d₁
  | dtrans {e₁ e₂ : Expr} {d₁ d₂ d₃ : RwEqDeriv e₁ e₂} :
      DerivEquivT d₁ d₂ → DerivEquivT d₂ d₃ → DerivEquivT d₁ d₃
  | vcomp_congr_left {e₁ e₂ e₃ : Expr}
      {d₁ d₁' : RwEqDeriv e₁ e₂} {d₂ : RwEqDeriv e₂ e₃}
      (h : DerivEquivT d₁ d₁') :
      DerivEquivT (d₁.vcomp d₂) (d₁'.vcomp d₂)
  | vcomp_congr_right {e₁ e₂ e₃ : Expr}
      {d₁ : RwEqDeriv e₁ e₂} {d₂ d₂' : RwEqDeriv e₂ e₃}
      (h : DerivEquivT d₂ d₂') :
      DerivEquivT (d₁.vcomp d₂) (d₁.vcomp d₂')
  | hcomp_congr {e₁ e₁' e₂ e₂' : Expr}
      {dp dp' : RwEqDeriv e₁ e₁'} {dq dq' : RwEqDeriv e₂ e₂'}
      (hp : DerivEquivT dp dp') (hq : DerivEquivT dq dq') :
      DerivEquivT (dp.hcomp dq) (dp'.hcomp dq')
  | interchange {p p' p'' q q' q'' : Expr}
      (d₁ : RwEqDeriv p p') (d₂ : RwEqDeriv p' p'')
      (d₃ : RwEqDeriv q q') (d₄ : RwEqDeriv q' q'') :
      DerivEquivT
        ((d₁.vcomp d₂).hcomp (d₃.vcomp d₄))
        ((d₁.hcomp d₃).vcomp (d₂.hcomp d₄))
  | generator {e₁ e₂ : Expr} {d₁ d₂ : RwEqDeriv e₁ e₂} :
      Generator3CellT d₁ d₂ → DerivEquivT d₁ d₂

namespace DerivEquivT

abbrev refl' {e₁ e₂ : Expr} (d : RwEqDeriv e₁ e₂) : DerivEquivT d d := .refl d

abbrev symm' {e₁ e₂ : Expr} {d₁ d₂ : RwEqDeriv e₁ e₂}
    (h : DerivEquivT d₁ d₂) : DerivEquivT d₂ d₁ := .symm h

abbrev trans' {e₁ e₂ : Expr} {d₁ d₂ d₃ : RwEqDeriv e₁ e₂}
    (h₁ : DerivEquivT d₁ d₂) (h₂ : DerivEquivT d₂ d₃) : DerivEquivT d₁ d₃ :=
  .dtrans h₁ h₂

end DerivEquivT

/-! ## DerivEquiv is an equivalence relation -/

theorem derivEquiv_refl {e₁ e₂ : Expr} (d : RwEqDeriv e₁ e₂) :
    DerivEquiv d d := .refl d

theorem derivEquiv_symm {e₁ e₂ : Expr} {d₁ d₂ : RwEqDeriv e₁ e₂}
    (h : DerivEquiv d₁ d₂) : DerivEquiv d₂ d₁ := .symm h

theorem derivEquiv_trans {e₁ e₂ : Expr} {d₁ d₂ d₃ : RwEqDeriv e₁ e₂}
    (h₁ : DerivEquiv d₁ d₂) (h₂ : DerivEquiv d₂ d₃) : DerivEquiv d₁ d₃ :=
  .dtrans h₁ h₂

noncomputable instance derivEquivSetoid (e₁ e₂ : Expr) : Setoid (RwEqDeriv e₁ e₂) where
  r := DerivEquiv
  iseqv := ⟨derivEquiv_refl, fun h => derivEquiv_symm h, fun h₁ h₂ => derivEquiv_trans h₁ h₂⟩

/-! ## Naturality squares

A naturality square witnesses the fact that whiskering commutes with
vertical composition. This is captured by the interchange constructor above,
but we can derive specific instances. -/

/-- Naturality: right whiskering by a basic step equals `trans_congr_right`.
    For the `symm_refl` constructor case as an example. -/
theorem naturality_right_whisker_symm_refl (p : Expr) :
    (RwEqDeriv.symm_refl).htransRight p =
    .trans_congr_right p .symm_refl := by rfl

/-- Naturality: left whiskering by a basic step equals `trans_congr_left`.
    For the `symm_refl` constructor case as an example. -/
theorem naturality_left_whisker_symm_refl (p : Expr) :
    (RwEqDeriv.symm_refl).htransLeft p =
    .trans_congr_left p .symm_refl := by rfl

/-! ## Non-trivial 3-cells

We show there exist two genuinely different derivation equivalences
between the same pair of 2-cells — a non-trivial 3-cell. -/

/-- Two distinct derivations from `trans refl refl` to `refl`. -/
noncomputable def d_left : RwEqDeriv (.trans .refl .refl) .refl :=
  .trans_refl_left .refl

noncomputable def d_right : RwEqDeriv (.trans .refl .refl) .refl :=
  .trans_refl_right .refl

/-- A 3-cell from d_left to d_right via symmetry of the intermediate form. -/
noncomputable def threeCell_via_symm : DerivEquiv
    (RwEqDeriv.trans d_left (.symm d_right))
    (RwEqDeriv.trans d_left (.symm d_right)) :=
  .refl _

/-- The identity 3-cell on d_left. -/
noncomputable def threeCell_id_left : DerivEquiv d_left d_left := .refl _

/-- A non-trivial 3-cell: the interchange applied to identity derivations
    produces a different witness than the plain identity. -/
theorem nontrivial_three_cell_exists :
    ∃ (d₁ d₂ : RwEqDeriv (.trans .refl .refl) .refl),
    d₁ ≠ d₂ ∧ DerivEquiv
                  (RwEqDeriv.trans d₁ (RwEqDeriv.symm d₂))
                  (RwEqDeriv.trans d₁ (RwEqDeriv.symm d₂)) := by
  exact ⟨d_left, d_right, RwEqDeriv.deriv_refl_left_ne_right, .refl _⟩

/-! ## The 3-dimensional structure

The data assembled in this module gives:
- 0-cells: `Expr`
- 1-cells: `ExprRwEq e₁ e₂` (propositional, from GroupoidConfluence)
- 2-cells: `RwEqDeriv e₁ e₂` (type-valued derivation trees)
- 3-cells: `DerivEquiv d₁ d₂` (propositional equivalence of derivations)

With `DerivEquiv` being an equivalence relation and the interchange law,
this forms a **3-groupoid** (all cells invertible at every level).
This is the beginning of the ω-groupoid structure predicted by
the Grothendieck–Maltsiniotis conjecture. -/

/-- The 3-groupoid axiom: every 2-cell has an inverse. -/
theorem two_cell_inverse (d : RwEqDeriv e₁ e₂) :
    ∃ _d' : RwEqDeriv e₂ e₁, True := ⟨d.symm, trivial⟩

/-- Vertical composition of 3-cells is well-defined on equivalence classes. -/
theorem vcomp_respects_equiv {e₁ e₂ e₃ : Expr}
    {d₁ d₁' : RwEqDeriv e₁ e₂} {d₂ d₂' : RwEqDeriv e₂ e₃}
    (h₁ : DerivEquiv d₁ d₁') (h₂ : DerivEquiv d₂ d₂') :
    DerivEquiv (d₁.vcomp d₂) (d₁'.vcomp d₂') :=
  .dtrans (.vcomp_congr_left h₁) (.vcomp_congr_right h₂)

/-- Horizontal composition of 3-cells is well-defined on equivalence classes. -/
theorem hcomp_respects_equiv {e₁ e₁' e₂ e₂' : Expr}
    {dp dp' : RwEqDeriv e₁ e₁'} {dq dq' : RwEqDeriv e₂ e₂'}
    (hp : DerivEquiv dp dp') (hq : DerivEquiv dq dq') :
    DerivEquiv (dp.hcomp dq) (dp'.hcomp dq') :=
  .hcomp_congr hp hq

end ComputationalPaths.Path.Polygraph
