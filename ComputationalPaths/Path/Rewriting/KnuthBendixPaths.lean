/-
# Knuth-Bendix Completion via Structural Computational Paths

This module formalizes Knuth-Bendix completion where critical pairs are
path divergences, completion steps generate new path equalities,
orientation uses termination orders, and the completed system is
connected to the computational-path rewrite system via congrArg/transport.

## Main constructions

- `KBExpr`: groupoid-style expressions
- `KBBaseStep` / `KBCStep`: base and completed rewrite steps
- Critical pair analysis with path witnesses
- Weight-based termination ordering
- Derivability of completion rules in base equational theory
- Interpretation into computational Paths via congrArg

## References

- Knuth & Bendix, "Simple Word Problems in Universal Algebras" (1970)
- Huet, "Confluent Reductions" (1980)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.KnuthBendixPaths

open ComputationalPaths.Path

universe u

/-! ## Expression Language -/

/-- Expressions in the groupoid rewriting system. -/
inductive KBExpr where
  | atom (n : Nat) : KBExpr
  | refl : KBExpr
  | sym (e : KBExpr) : KBExpr
  | tr (e₁ e₂ : KBExpr) : KBExpr
  deriving DecidableEq, Repr

namespace KBExpr

@[simp] def size : KBExpr → Nat
  | .atom _ => 1
  | .refl => 1
  | .sym e => e.size + 1
  | .tr e₁ e₂ => e₁.size + e₂.size + 1

theorem size_pos (e : KBExpr) : 0 < e.size := by cases e <;> simp <;> omega

/-- Polynomial weight for termination ordering. -/
@[simp] def weight : KBExpr → Nat
  | .atom _ => 4
  | .refl => 4
  | .sym e => 2 * e.weight + 1
  | .tr e₁ e₂ => e₁.weight + e₂.weight + 2

theorem weight_ge_four (e : KBExpr) : 4 ≤ e.weight := by
  induction e <;> simp <;> omega

theorem weight_pos (e : KBExpr) : 0 < e.weight := by
  have := weight_ge_four e; omega

/-- Left-weight for breaking ties on associativity. -/
@[simp] def leftWeight : KBExpr → Nat
  | .atom _ => 0
  | .refl => 0
  | .sym e => e.leftWeight
  | .tr e₁ e₂ => e₁.leftWeight + e₂.leftWeight + e₁.size

end KBExpr

open KBExpr

/-! ## Reflexive-Transitive Closure -/

inductive KBRtc (R : KBExpr → KBExpr → Prop) : KBExpr → KBExpr → Prop where
  | refl (a : KBExpr) : KBRtc R a a
  | head {a b c : KBExpr} : R a b → KBRtc R b c → KBRtc R a c

namespace KBRtc

variable {R : KBExpr → KBExpr → Prop}

theorem single {a b : KBExpr} (h : R a b) : KBRtc R a b :=
  .head h (.refl b)

theorem trans {a b c : KBExpr} (h₁ : KBRtc R a b) (h₂ : KBRtc R b c) :
    KBRtc R a c := by
  induction h₁ with
  | refl => exact h₂
  | head step _ ih => exact .head step (ih h₂)

end KBRtc

/-! ## Base Step Relation (8 groupoid rules + congruence) -/

inductive KBBaseStep : KBExpr → KBExpr → Prop where
  | sym_refl : KBBaseStep (.sym .refl) .refl
  | sym_sym (p : KBExpr) : KBBaseStep (.sym (.sym p)) p
  | tr_refl_left (p : KBExpr) : KBBaseStep (.tr .refl p) p
  | tr_refl_right (p : KBExpr) : KBBaseStep (.tr p .refl) p
  | tr_sym (p : KBExpr) : KBBaseStep (.tr p (.sym p)) .refl
  | sym_tr (p : KBExpr) : KBBaseStep (.tr (.sym p) p) .refl
  | sym_tr_congr (p q : KBExpr) :
      KBBaseStep (.sym (.tr p q)) (.tr (.sym q) (.sym p))
  | tr_assoc (p q r : KBExpr) :
      KBBaseStep (.tr (.tr p q) r) (.tr p (.tr q r))
  | sym_congr {p q : KBExpr} : KBBaseStep p q → KBBaseStep (.sym p) (.sym q)
  | tr_congr_left {p q : KBExpr} (r : KBExpr) :
      KBBaseStep p q → KBBaseStep (.tr p r) (.tr q r)
  | tr_congr_right (p : KBExpr) {q r : KBExpr} :
      KBBaseStep q r → KBBaseStep (.tr p q) (.tr p r)

/-! ## Completed Step Relation (base + cancellation rules) -/

inductive KBCStep : KBExpr → KBExpr → Prop where
  | sym_refl : KBCStep (.sym .refl) .refl
  | sym_sym (p : KBExpr) : KBCStep (.sym (.sym p)) p
  | tr_refl_left (p : KBExpr) : KBCStep (.tr .refl p) p
  | tr_refl_right (p : KBExpr) : KBCStep (.tr p .refl) p
  | tr_sym (p : KBExpr) : KBCStep (.tr p (.sym p)) .refl
  | sym_tr (p : KBExpr) : KBCStep (.tr (.sym p) p) .refl
  | sym_tr_congr (p q : KBExpr) :
      KBCStep (.sym (.tr p q)) (.tr (.sym q) (.sym p))
  | tr_assoc (p q r : KBExpr) :
      KBCStep (.tr (.tr p q) r) (.tr p (.tr q r))
  | cancel_left (p q : KBExpr) :
      KBCStep (.tr p (.tr (.sym p) q)) q
  | cancel_right (p q : KBExpr) :
      KBCStep (.tr (.sym p) (.tr p q)) q
  | sym_congr {p q : KBExpr} : KBCStep p q → KBCStep (.sym p) (.sym q)
  | tr_congr_left {p q : KBExpr} (r : KBExpr) :
      KBCStep p q → KBCStep (.tr p r) (.tr q r)
  | tr_congr_right (p : KBExpr) {q r : KBExpr} :
      KBCStep q r → KBCStep (.tr p q) (.tr p r)

/-- Every base step embeds into the completed system. -/
theorem KBCStep.of_baseStep {p q : KBExpr} (h : KBBaseStep p q) : KBCStep p q := by
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

abbrev KBCRtc := KBRtc KBCStep

namespace KBCRtc

def single (h : KBCStep a b) : KBCRtc a b := KBRtc.single h

def sym_congr {p q : KBExpr} (h : KBCRtc p q) :
    KBCRtc (.sym p) (.sym q) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.sym_congr s) ih

def tr_congr_left (r : KBExpr) {p q : KBExpr} (h : KBCRtc p q) :
    KBCRtc (.tr p r) (.tr q r) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.tr_congr_left r s) ih

def tr_congr_right (p : KBExpr) {q r : KBExpr} (h : KBCRtc q r) :
    KBCRtc (.tr p q) (.tr p r) := by
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .head (.tr_congr_right p s) ih

end KBCRtc

/-! ## Critical Pair Analysis -/

structure KBCriticalPair where
  source : KBExpr
  left : KBExpr
  right : KBExpr

def KBCriticalPair.Joinable (cp : KBCriticalPair) : Prop :=
  ∃ target, KBCRtc cp.left target ∧ KBCRtc cp.right target

/-- Critical pair: tr_sym vs tr_assoc on tr(tr(p,q), sym(tr(p,q))). -/
def cp_trSym_trAssoc (p q : KBExpr) : KBCriticalPair where
  source := .tr (.tr p q) (.sym (.tr p q))
  left := .refl
  right := .tr p (.tr q (.sym (.tr p q)))

theorem criticalPair_ts_ta_joinable (p q : KBExpr) :
    (cp_trSym_trAssoc p q).Joinable := by
  refine ⟨.refl, .refl _, ?_⟩
  have h1 : KBCRtc (.tr p (.tr q (.sym (.tr p q))))
      (.tr p (.tr q (.tr (.sym q) (.sym p)))) :=
    KBCRtc.tr_congr_right p
      (KBCRtc.tr_congr_right q (KBCRtc.single (.sym_tr_congr p q)))
  have h2 : KBCRtc (.tr p (.tr q (.tr (.sym q) (.sym p))))
      (.tr p (.sym p)) :=
    KBCRtc.tr_congr_right p (KBCRtc.single (.cancel_left q (.sym p)))
  have h3 : KBCRtc (.tr p (.sym p)) .refl :=
    KBCRtc.single (.tr_sym p)
  exact h1.trans (h2.trans h3)

/-- Critical pair: sym_tr vs tr_assoc. -/
def cp_symTr_trAssoc (p q : KBExpr) : KBCriticalPair where
  source := .tr (.sym (.tr p q)) (.tr p q)
  left := .refl
  right := .tr (.sym (.tr p q)) (.tr p q)

theorem criticalPair_st_ta_joinable (p q : KBExpr) :
    (cp_symTr_trAssoc p q).Joinable :=
  ⟨.refl, .refl _, KBCRtc.single (.sym_tr (.tr p q))⟩

/-- Critical pair: tr_refl_left vs tr_assoc. -/
def cp_trRefl_trAssoc (p q : KBExpr) : KBCriticalPair where
  source := .tr (.tr .refl p) q
  left := .tr p q
  right := .tr .refl (.tr p q)

theorem criticalPair_trRefl_trAssoc_joinable (p q : KBExpr) :
    (cp_trRefl_trAssoc p q).Joinable :=
  ⟨.tr p q, .refl _, KBCRtc.single (.tr_refl_left (.tr p q))⟩

/-- Critical pair: tr_refl_right vs tr_assoc. -/
def cp_trReflR_trAssoc (p q : KBExpr) : KBCriticalPair where
  source := .tr (.tr p .refl) q
  left := .tr p q
  right := .tr p (.tr .refl q)

theorem criticalPair_trReflR_trAssoc_joinable (p q : KBExpr) :
    (cp_trReflR_trAssoc p q).Joinable :=
  ⟨.tr p q, .refl _, KBCRtc.tr_congr_right p (KBCRtc.single (.tr_refl_left q))⟩

/-! ## Weight-Based Termination -/

theorem weight_sym_refl : weight (.sym .refl) > weight .refl := by simp

theorem weight_sym_sym (p : KBExpr) :
    weight (.sym (.sym p)) > weight p := by simp; omega

theorem weight_tr_refl_left (p : KBExpr) :
    weight (.tr .refl p) > weight p := by simp; omega

theorem weight_tr_refl_right (p : KBExpr) :
    weight (.tr p .refl) > weight p := by simp; omega

theorem weight_tr_sym (p : KBExpr) :
    weight (.tr p (.sym p)) > weight .refl := by
  simp; have := weight_ge_four p; omega

theorem weight_sym_tr (p : KBExpr) :
    weight (.tr (.sym p) p) > weight .refl := by
  simp; have := weight_ge_four p; omega

theorem weight_sym_tr_congr (p q : KBExpr) :
    weight (.sym (.tr p q)) > weight (.tr (.sym q) (.sym p)) := by
  simp; omega

theorem weight_cancel_left (p q : KBExpr) :
    weight (.tr p (.tr (.sym p) q)) > weight q := by
  simp; have := weight_ge_four p; omega

theorem weight_cancel_right (p q : KBExpr) :
    weight (.tr (.sym p) (.tr p q)) > weight q := by
  simp; have := weight_ge_four p; omega

/-- Left-weight strictly decreases on associativity. -/
theorem leftWeight_tr_assoc (p q r : KBExpr) :
    leftWeight (.tr (.tr p q) r) > leftWeight (.tr p (.tr q r)) := by
  simp [leftWeight, size]; omega

/-! ## Normal Forms -/

def KBIsNF (e : KBExpr) : Prop := ∀ e', ¬ KBCStep e e'

theorem isNormalForm_refl : KBIsNF .refl :=
  fun _ h => by cases h

theorem isNormalForm_atom (n : Nat) : KBIsNF (.atom n) :=
  fun _ h => by cases h

theorem isNormalForm_sym_atom (n : Nat) : KBIsNF (.sym (.atom n)) :=
  fun _ h => by cases h; rename_i h; cases h

theorem cstep_refl_irreducible {e : KBExpr} : ¬ KBCStep .refl e := by
  intro h; cases h

theorem cstep_atom_irreducible {e : KBExpr} (n : Nat) : ¬ KBCStep (.atom n) e := by
  intro h; cases h

/-! ## Equivalence Closure -/

inductive KBStepSym : KBExpr → KBExpr → Prop where
  | fwd : KBCStep p q → KBStepSym p q
  | bwd : KBCStep q p → KBStepSym p q

inductive KBEq : KBExpr → KBExpr → Prop where
  | refl (a : KBExpr) : KBEq a a
  | step : KBStepSym a b → KBEq a b
  | trans : KBEq a b → KBEq b c → KBEq a c

theorem KBEq.symm : KBEq a b → KBEq b a := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h =>
    exact .step (match h with
    | .fwd s => .bwd s
    | .bwd s => .fwd s)
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem KBEq.of_cstep (h : KBCStep a b) : KBEq a b := .step (.fwd h)

theorem KBEq.of_crtc : KBCRtc a b → KBEq a b := by
  intro h
  induction h with
  | refl => exact .refl _
  | head s _ ih => exact .trans (.of_cstep s) ih

/-! ## Base Equivalence and Derivability -/

inductive KBBaseStepSym : KBExpr → KBExpr → Prop where
  | fwd : KBBaseStep p q → KBBaseStepSym p q
  | bwd : KBBaseStep q p → KBBaseStepSym p q

inductive KBBaseEq : KBExpr → KBExpr → Prop where
  | refl (a : KBExpr) : KBBaseEq a a
  | step : KBBaseStepSym a b → KBBaseEq a b
  | trans : KBBaseEq a b → KBBaseEq b c → KBBaseEq a c

theorem KBBaseEq.symm : KBBaseEq a b → KBBaseEq b a := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h =>
    exact .step (match h with
    | .fwd s => .bwd s
    | .bwd s => .fwd s)
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem KBBaseEq.toKBEq : KBBaseEq a b → KBEq a b := by
  intro h
  induction h with
  | refl => exact .refl _
  | step h =>
    exact .step (match h with
    | .fwd s => .fwd (KBCStep.of_baseStep s)
    | .bwd s => .bwd (KBCStep.of_baseStep s))
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2

/-- cancel_left is derivable in base equational theory. -/
theorem cancel_left_derivable (p q : KBExpr) :
    KBBaseEq (.tr p (.tr (.sym p) q)) q :=
  .trans (.trans (.step (.bwd (.tr_assoc p (.sym p) q)))
    (.step (.fwd (.tr_congr_left q (.tr_sym p)))))
    (.step (.fwd (.tr_refl_left q)))

/-- cancel_right is derivable in base equational theory. -/
theorem cancel_right_derivable (p q : KBExpr) :
    KBBaseEq (.tr (.sym p) (.tr p q)) q :=
  .trans (.trans (.step (.bwd (.tr_assoc (.sym p) p q)))
    (.step (.fwd (.tr_congr_left q (.sym_tr p)))))
    (.step (.fwd (.tr_refl_left q)))

/-! ## Interpretation into Computational Paths -/

/-- Interpret a KBExpr as a Path a a (loop paths). -/
noncomputable def interpretPath {A : Type u} {a : A}
    (env : Nat → ComputationalPaths.Path a a) : KBExpr → ComputationalPaths.Path a a
  | .atom n => env n
  | .refl => ComputationalPaths.Path.refl a
  | .sym e => ComputationalPaths.Path.symm (interpretPath env e)
  | .tr e₁ e₂ => ComputationalPaths.Path.trans (interpretPath env e₁) (interpretPath env e₂)

/-- All loop paths have toEq = rfl. -/
theorem interpretPath_toEq {A : Type u} {a : A}
    (env : Nat → ComputationalPaths.Path a a) (e : KBExpr) :
    (interpretPath env e).toEq = rfl := by
  induction e with
  | atom _ => rfl
  | refl => simp
  | sym _ _ => simp
  | tr _ _ _ _ => simp

/-- Base steps preserve toEq of interpretation. -/
theorem baseStep_preserves_toEq {A : Type u} {a : A}
    (env : Nat → ComputationalPaths.Path a a) {e₁ e₂ : KBExpr} (_ : KBBaseStep e₁ e₂) :
    (interpretPath env e₁).toEq = (interpretPath env e₂).toEq := by
  simp

/-- Completed steps preserve toEq. -/
theorem cstep_preserves_toEq {A : Type u} {a : A}
    (env : Nat → ComputationalPaths.Path a a) {e₁ e₂ : KBExpr} (_ : KBCStep e₁ e₂) :
    (interpretPath env e₁).toEq = (interpretPath env e₂).toEq := by
  simp

/-! ## Path-based Termination Ordering -/

/-- A termination ordering on KBExpr using weight + leftWeight as tiebreaker. -/
def kbOrder (a b : KBExpr) : Prop :=
  a.weight < b.weight ∨ (a.weight = b.weight ∧ a.leftWeight < b.leftWeight)

/-- kbOrder is weight-decreasing with leftWeight tiebreaker. -/
theorem kbOrder_subrel_weight (h : kbOrder a b) : a.weight ≤ b.weight := by
  cases h with
  | inl h => omega
  | inr h => omega

/-! ## Transport along Path-equality -/

/-- Transport a property through a path between KBExprs. -/
def transportKBProp (P : KBExpr → Prop) {s t : KBExpr}
    (p : ComputationalPaths.Path s t) (h : P s) : P t :=
  ComputationalPaths.Path.transport (D := fun x => P x) p h

@[simp] theorem transportKBProp_refl (P : KBExpr → Prop) (e : KBExpr) (h : P e) :
    transportKBProp P (ComputationalPaths.Path.refl e) h = h := rfl

/-- congrArg for KBExpr size along paths. -/
def sizePathEq {s t : KBExpr}
    (p : ComputationalPaths.Path s t) :
    ComputationalPaths.Path s.size t.size :=
  ComputationalPaths.Path.congrArg KBExpr.size p

/-- congrArg for KBExpr weight along paths. -/
def weightPathEq {s t : KBExpr}
    (p : ComputationalPaths.Path s t) :
    ComputationalPaths.Path s.weight t.weight :=
  ComputationalPaths.Path.congrArg KBExpr.weight p

@[simp] theorem sizePathEq_refl (e : KBExpr) :
    sizePathEq (ComputationalPaths.Path.refl e) =
      ComputationalPaths.Path.refl e.size := by
  simp [sizePathEq]

@[simp] theorem weightPathEq_refl (e : KBExpr) :
    weightPathEq (ComputationalPaths.Path.refl e) =
      ComputationalPaths.Path.refl e.weight := by
  simp [weightPathEq]

@[simp] theorem sizePathEq_trans {s t u : KBExpr}
    (p : ComputationalPaths.Path s t) (q : ComputationalPaths.Path t u) :
    sizePathEq (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (sizePathEq p) (sizePathEq q) := by
  simp [sizePathEq]

@[simp] theorem weightPathEq_trans {s t u : KBExpr}
    (p : ComputationalPaths.Path s t) (q : ComputationalPaths.Path t u) :
    weightPathEq (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (weightPathEq p) (weightPathEq q) := by
  simp [weightPathEq]

@[simp] theorem sizePathEq_symm {s t : KBExpr}
    (p : ComputationalPaths.Path s t) :
    sizePathEq (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (sizePathEq p) := by
  simp [sizePathEq]

@[simp] theorem weightPathEq_symm {s t : KBExpr}
    (p : ComputationalPaths.Path s t) :
    weightPathEq (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (weightPathEq p) := by
  simp [weightPathEq]

end ComputationalPaths.Path.Rewriting.KnuthBendixPaths
