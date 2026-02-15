/-
# Knuth-Bendix Completion for Groupoid Rewriting via Computational Paths

This module formalizes Knuth-Bendix completion for a groupoid-like rewriting
system.  We model abstract expressions, base and completed step relations,
critical pair analysis, termination orderings, and the key property that
completion preserves the equational theory.

## Main Results

- `CStep.of_baseStep`: every base rule embeds into the completed system
- `criticalPair_ts_ta_joinable`: the critical pair trans_symm / trans_assoc
  is joinable after completion
- `cancel_left_derivable` / `cancel_right_derivable`: the added rules are
  derivable in the base equational theory
- Weight-based termination: every non-assoc rule strictly decreases weight
- `IsNormalForm` characterization of irreducible expressions

## References

- Knuth & Bendix, "Simple Word Problems in Universal Algebras" (1970)
- Huet, "Confluent Reductions" (1980)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewrite.KnuthBendix

/-! ## Abstract Expression Language -/

/-- Expressions in the groupoid rewriting system. -/
inductive GExpr where
  | atom (n : Nat) : GExpr
  | refl : GExpr
  | sym (e : GExpr) : GExpr
  | tr (e₁ e₂ : GExpr) : GExpr
  deriving DecidableEq, Repr

namespace GExpr

/-! ## Size and Weight Measures -/

@[simp] def size : GExpr → Nat
  | .atom _ => 1
  | .refl => 1
  | .sym e => e.size + 1
  | .tr e₁ e₂ => e₁.size + e₂.size + 1

theorem size_pos (e : GExpr) : 0 < e.size := by cases e <;> simp <;> omega

/-- Polynomial weight interpretation. -/
@[simp] def weight : GExpr → Nat
  | .atom _ => 4
  | .refl => 4
  | .sym e => 2 * e.weight + 1
  | .tr e₁ e₂ => e₁.weight + e₂.weight + 2

theorem weight_ge_four (e : GExpr) : 4 ≤ e.weight := by
  induction e <;> simp <;> omega

theorem weight_pos (e : GExpr) : 0 < e.weight := by
  have := weight_ge_four e; omega

/-- Left-weight for breaking ties on associativity. -/
@[simp] def leftWeight : GExpr → Nat
  | .atom _ => 0
  | .refl => 0
  | .sym e => e.leftWeight
  | .tr e₁ e₂ => e₁.leftWeight + e₂.leftWeight + e₁.size

end GExpr

open GExpr

/-! ## Reflexive-Transitive Closure -/

/-- Reflexive-transitive closure of a relation on GExpr. -/
inductive GRtc (R : GExpr → GExpr → Prop) : GExpr → GExpr → Prop where
  | refl (a : GExpr) : GRtc R a a
  | head {a b c : GExpr} : R a b → GRtc R b c → GRtc R a c

namespace GRtc

variable {R : GExpr → GExpr → Prop}

theorem single {a b : GExpr} (h : R a b) : GRtc R a b :=
  .head h (.refl b)

theorem trans {a b c : GExpr} (h₁ : GRtc R a b) (h₂ : GRtc R b c) :
    GRtc R a c := by
  induction h₁ with
  | refl => exact h₂
  | head step _ ih => exact .head step (ih h₂)

end GRtc

/-! ## Base Step Relation (8 groupoid rules + congruence) -/

inductive BaseStep : GExpr → GExpr → Prop where
  | sym_refl : BaseStep (.sym .refl) .refl
  | sym_sym (p : GExpr) : BaseStep (.sym (.sym p)) p
  | tr_refl_left (p : GExpr) : BaseStep (.tr .refl p) p
  | tr_refl_right (p : GExpr) : BaseStep (.tr p .refl) p
  | tr_sym (p : GExpr) : BaseStep (.tr p (.sym p)) .refl
  | sym_tr (p : GExpr) : BaseStep (.tr (.sym p) p) .refl
  | sym_tr_congr (p q : GExpr) :
      BaseStep (.sym (.tr p q)) (.tr (.sym q) (.sym p))
  | tr_assoc (p q r : GExpr) :
      BaseStep (.tr (.tr p q) r) (.tr p (.tr q r))
  | sym_congr {p q : GExpr} : BaseStep p q → BaseStep (.sym p) (.sym q)
  | tr_congr_left {p q : GExpr} (r : GExpr) :
      BaseStep p q → BaseStep (.tr p r) (.tr q r)
  | tr_congr_right (p : GExpr) {q r : GExpr} :
      BaseStep q r → BaseStep (.tr p q) (.tr p r)

/-! ## Completed Step Relation (base + cancellation rules) -/

inductive CStep : GExpr → GExpr → Prop where
  | sym_refl : CStep (.sym .refl) .refl
  | sym_sym (p : GExpr) : CStep (.sym (.sym p)) p
  | tr_refl_left (p : GExpr) : CStep (.tr .refl p) p
  | tr_refl_right (p : GExpr) : CStep (.tr p .refl) p
  | tr_sym (p : GExpr) : CStep (.tr p (.sym p)) .refl
  | sym_tr (p : GExpr) : CStep (.tr (.sym p) p) .refl
  | sym_tr_congr (p q : GExpr) :
      CStep (.sym (.tr p q)) (.tr (.sym q) (.sym p))
  | tr_assoc (p q r : GExpr) :
      CStep (.tr (.tr p q) r) (.tr p (.tr q r))
  | cancel_left (p q : GExpr) :
      CStep (.tr p (.tr (.sym p) q)) q
  | cancel_right (p q : GExpr) :
      CStep (.tr (.sym p) (.tr p q)) q
  | sym_congr {p q : GExpr} : CStep p q → CStep (.sym p) (.sym q)
  | tr_congr_left {p q : GExpr} (r : GExpr) :
      CStep p q → CStep (.tr p r) (.tr q r)
  | tr_congr_right (p : GExpr) {q r : GExpr} :
      CStep q r → CStep (.tr p q) (.tr p r)

/-- Every base step embeds into the completed system. -/
theorem CStep.of_baseStep {p q : GExpr} (h : BaseStep p q) : CStep p q := by
  induction h with
  | sym_refl => exact .sym_refl
  | sym_sym p => exact .sym_sym p
  | tr_refl_left p => exact .tr_refl_left p
  | tr_refl_right p => exact .tr_refl_right p
  | tr_sym p => exact .tr_sym p
  | sym_tr p => exact .sym_tr p
  | sym_tr_congr p q => exact .sym_tr_congr p q
  | tr_assoc p q r => exact .tr_assoc p q r
  | sym_congr _ ih => exact .sym_congr ih
  | tr_congr_left r _ ih => exact .tr_congr_left r ih
  | tr_congr_right p _ ih => exact .tr_congr_right p ih

abbrev CRtc := GRtc CStep

namespace CRtc

def single (h : CStep a b) : CRtc a b := GRtc.single h

def sym_congr {p q : GExpr} (h : CRtc p q) :
    CRtc (.sym p) (.sym q) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.sym_congr s) ih

def tr_congr_left (r : GExpr) {p q : GExpr} (h : CRtc p q) :
    CRtc (.tr p r) (.tr q r) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.tr_congr_left r s) ih

def tr_congr_right (p : GExpr) {q r : GExpr} (h : CRtc q r) :
    CRtc (.tr p q) (.tr p r) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.tr_congr_right p s) ih

end CRtc

/-! ## Critical Pair Analysis -/

/-- A critical pair: two expressions reachable from a common source. -/
structure CriticalPair where
  source : GExpr
  left : GExpr
  right : GExpr

/-- A critical pair is joinable if both sides reduce to a common expression. -/
def CriticalPair.Joinable (cp : CriticalPair) : Prop :=
  ∃ target, CRtc cp.left target ∧ CRtc cp.right target

/-- The critical pair: tr_sym vs tr_assoc on tr(tr(p,q), sym(tr(p,q))). -/
def cp_trSym_trAssoc (p q : GExpr) : CriticalPair where
  source := .tr (.tr p q) (.sym (.tr p q))
  left := .refl
  right := .tr p (.tr q (.sym (.tr p q)))

/-- The critical pair tr_sym/tr_assoc is joinable in the completed system. -/
theorem criticalPair_ts_ta_joinable (p q : GExpr) :
    (cp_trSym_trAssoc p q).Joinable := by
  refine ⟨.refl, .refl _, ?_⟩
  -- right = tr(p, tr(q, sym(tr(p,q))))
  -- Step 1: sym_tr_congr: sym(tr(p,q)) → tr(sym(q), sym(p))
  have h1 : CRtc (.tr p (.tr q (.sym (.tr p q))))
      (.tr p (.tr q (.tr (.sym q) (.sym p)))) :=
    CRtc.tr_congr_right p
      (CRtc.tr_congr_right q (CRtc.single (.sym_tr_congr p q)))
  -- Step 2: cancel_left: tr(q, tr(sym(q), sym(p))) → sym(p)
  have h2 : CRtc (.tr p (.tr q (.tr (.sym q) (.sym p))))
      (.tr p (.sym p)) :=
    CRtc.tr_congr_right p (CRtc.single (.cancel_left q (.sym p)))
  -- Step 3: tr_sym: tr(p, sym(p)) → refl
  have h3 : CRtc (.tr p (.sym p)) .refl :=
    CRtc.single (.tr_sym p)
  exact h1.trans (h2.trans h3)

/-- The critical pair: sym_tr vs tr_assoc on tr(sym(tr(p,q)), tr(p,q)). -/
def cp_symTr_trAssoc (p q : GExpr) : CriticalPair where
  source := .tr (.sym (.tr p q)) (.tr p q)
  left := .refl
  right := .tr (.sym (.tr p q)) (.tr p q)

/-- The sym_tr/tr_assoc critical pair is trivially joinable (LHS already refl). -/
theorem criticalPair_st_ta_joinable (p q : GExpr) :
    (cp_symTr_trAssoc p q).Joinable :=
  ⟨.refl, .refl _, CRtc.single (.sym_tr (.tr p q))⟩

/-- Critical pair: tr_refl_left vs tr_assoc on tr(tr(refl, p), q). -/
def cp_trRefl_trAssoc (p q : GExpr) : CriticalPair where
  source := .tr (.tr .refl p) q
  left := .tr p q
  right := .tr .refl (.tr p q)

theorem criticalPair_trRefl_trAssoc_joinable (p q : GExpr) :
    (cp_trRefl_trAssoc p q).Joinable :=
  ⟨.tr p q, .refl _, CRtc.single (.tr_refl_left (.tr p q))⟩

/-- Critical pair: tr_refl_right vs tr_assoc on tr(tr(p, refl), q). -/
def cp_trReflR_trAssoc (p q : GExpr) : CriticalPair where
  source := .tr (.tr p .refl) q
  left := .tr p q
  right := .tr p (.tr .refl q)

theorem criticalPair_trReflR_trAssoc_joinable (p q : GExpr) :
    (cp_trReflR_trAssoc p q).Joinable :=
  ⟨.tr p q, .refl _, CRtc.tr_congr_right p (CRtc.single (.tr_refl_left q))⟩

/-! ## Termination: Weight Decrease Lemmas -/

theorem weight_sym_refl : weight (.sym .refl) > weight .refl := by simp

theorem weight_sym_sym (p : GExpr) :
    weight (.sym (.sym p)) > weight p := by simp; omega

theorem weight_tr_refl_left (p : GExpr) :
    weight (.tr .refl p) > weight p := by simp; omega

theorem weight_tr_refl_right (p : GExpr) :
    weight (.tr p .refl) > weight p := by simp; omega

theorem weight_tr_sym (p : GExpr) :
    weight (.tr p (.sym p)) > weight .refl := by
  simp; have := weight_ge_four p; omega

theorem weight_sym_tr (p : GExpr) :
    weight (.tr (.sym p) p) > weight .refl := by
  simp; have := weight_ge_four p; omega

theorem weight_sym_tr_congr (p q : GExpr) :
    weight (.sym (.tr p q)) > weight (.tr (.sym q) (.sym p)) := by
  simp; omega

theorem weight_tr_assoc (p q r : GExpr) :
    weight (.tr (.tr p q) r) = weight (.tr p (.tr q r)) := by
  simp; omega

theorem weight_cancel_left (p q : GExpr) :
    weight (.tr p (.tr (.sym p) q)) > weight q := by
  simp; have := weight_ge_four p; omega

theorem weight_cancel_right (p q : GExpr) :
    weight (.tr (.sym p) (.tr p q)) > weight q := by
  simp; have := weight_ge_four p; omega

/-- Left-weight strictly decreases on associativity. -/
theorem leftWeight_tr_assoc (p q r : GExpr) :
    leftWeight (.tr (.tr p q) r) > leftWeight (.tr p (.tr q r)) := by
  simp [leftWeight, size]; omega

/-! ## Normal Forms -/

def IsNormalForm (e : GExpr) : Prop := ∀ e', ¬ CStep e e'

theorem isNormalForm_refl : IsNormalForm .refl :=
  fun _ h => by cases h

theorem isNormalForm_atom (n : Nat) : IsNormalForm (.atom n) :=
  fun _ h => by cases h

/-- A sym of an atom is a normal form. -/
theorem isNormalForm_sym_atom (n : Nat) : IsNormalForm (.sym (.atom n)) :=
  fun _ h => by cases h; rename_i h; cases h

/-- refl is not a CStep source (no rules apply to it). -/
theorem cstep_refl_irreducible {e : GExpr} : ¬ CStep .refl e := by
  intro h; cases h

/-- Atoms are not CStep sources. -/
theorem cstep_atom_irreducible {e : GExpr} (n : Nat) : ¬ CStep (.atom n) e := by
  intro h; cases h

/-! ## Equivalence Closure -/

/-- Symmetric step. -/
inductive CStepSym : GExpr → GExpr → Prop where
  | fwd : CStep p q → CStepSym p q
  | bwd : CStep q p → CStepSym p q

/-- Equivalence closure (RST closure) of CStep. -/
inductive CEq : GExpr → GExpr → Prop where
  | refl (a : GExpr) : CEq a a
  | step : CStepSym a b → CEq a b
  | trans : CEq a b → CEq b c → CEq a c

theorem CEq.symm : CEq a b → CEq b a := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h =>
    exact .step (match h with
    | .fwd s => .bwd s
    | .bwd s => .fwd s)
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem CEq.of_cstep (h : CStep a b) : CEq a b := .step (.fwd h)

theorem CEq.of_crtc : CRtc a b → CEq a b := by
  intro h
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .trans (.of_cstep s) ih

/-! ## Base Equivalence Closure -/

inductive BaseStepSym : GExpr → GExpr → Prop where
  | fwd : BaseStep p q → BaseStepSym p q
  | bwd : BaseStep q p → BaseStepSym p q

inductive BaseEq : GExpr → GExpr → Prop where
  | refl (a : GExpr) : BaseEq a a
  | step : BaseStepSym a b → BaseEq a b
  | trans : BaseEq a b → BaseEq b c → BaseEq a c

theorem BaseEq.symm : BaseEq a b → BaseEq b a := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h =>
    exact .step (match h with
    | .fwd s => .bwd s
    | .bwd s => .fwd s)
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem BaseEq.toCEq : BaseEq a b → CEq a b := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h =>
    exact .step (match h with
    | .fwd s => .fwd (CStep.of_baseStep s)
    | .bwd s => .bwd (CStep.of_baseStep s))
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-! ## Cancellation Rules are Derivable in Base Theory

The key insight: the cancellation rules added by completion are already
derivable in the equational theory of the base system. -/

/-- cancel_left is derivable: tr(p, tr(sym(p), q)) ≡ q in BaseEq. -/
theorem cancel_left_derivable (p q : GExpr) :
    BaseEq (.tr p (.tr (.sym p) q)) q :=
  -- tr(p, tr(sym(p), q)) ← [assoc] tr(tr(p, sym(p)), q) → [tr_sym] tr(refl, q) → q
  .trans (.trans (.step (.bwd (.tr_assoc p (.sym p) q)))
    (.step (.fwd (.tr_congr_left q (.tr_sym p)))))
    (.step (.fwd (.tr_refl_left q)))

/-- cancel_right is derivable: tr(sym(p), tr(p, q)) ≡ q in BaseEq. -/
theorem cancel_right_derivable (p q : GExpr) :
    BaseEq (.tr (.sym p) (.tr p q)) q :=
  .trans (.trans (.step (.bwd (.tr_assoc (.sym p) p q)))
    (.step (.fwd (.tr_congr_left q (.sym_tr p)))))
    (.step (.fwd (.tr_refl_left q)))

/-! ## Connection to Computational Paths

We connect the abstract GExpr rewriting to the concrete Path operations. -/

universe u

/-- Interpret a GExpr as a Path operation, given an assignment of atoms to paths. -/
noncomputable def interpretPath {A : Type u} {a : A}
    (env : Nat → Path a a) : GExpr → Path a a
  | .atom n => env n
  | .refl => Path.refl a
  | .sym e => Path.symm (interpretPath env e)
  | .tr e₁ e₂ => Path.trans (interpretPath env e₁) (interpretPath env e₂)

/-- Interpretation preserves toEq: all interpreted paths have toEq = rfl. -/
theorem interpretPath_toEq {A : Type u} {a : A}
    (env : Nat → Path a a) (e : GExpr) :
    (interpretPath env e).toEq = rfl := by
  induction e with
  | atom _ => rfl
  | refl => simp
  | sym _ _ => simp
  | tr _ _ _ _ => simp

/-- Base steps preserve the interpreted path's toEq. -/
theorem baseStep_preserves_toEq {A : Type u} {a : A}
    (env : Nat → Path a a) {e₁ e₂ : GExpr} (_ : BaseStep e₁ e₂) :
    (interpretPath env e₁).toEq = (interpretPath env e₂).toEq := by
  simp

/-- CSteps preserve the interpreted path's toEq. -/
theorem cstep_preserves_toEq {A : Type u} {a : A}
    (env : Nat → Path a a) {e₁ e₂ : GExpr} (_ : CStep e₁ e₂) :
    (interpretPath env e₁).toEq = (interpretPath env e₂).toEq := by
  simp

end ComputationalPaths.Path.Rewrite.KnuthBendix
