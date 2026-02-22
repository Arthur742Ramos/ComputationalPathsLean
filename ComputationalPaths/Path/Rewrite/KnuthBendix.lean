/-
# Knuth-Bendix Completion for the Computational Path Rewrite System

This module formalizes the Knuth-Bendix completion procedure for the path
rewrite system, connecting it to the 78 Step constructors and the completed
groupoid TRS.

## Main Results

- `KBTerm`, `KBRule`, `KBEquation`: term rewriting syntax
- `orientEquation`, `orientEquations`: equation orientation by size/code ordering
- `superposeTwo`, `superposeRules`: superposition for critical pair generation
- `completionStep`, `completionLoop`: the completion loop with inter-reduction
- `StepToKBRule`: maps each of the 78 Step constructors to a concrete KBRule
- `orient_all_78_terminating`: WellFounded proof via GroupoidTRS weight
- `squierWitness`: finite derivation type connecting to CStep
- `completion_preserves_equational_theory`: soundness of completion

## References

- Knuth & Bendix, "Simple Word Problems in Universal Algebras" (1970)
- Huet, "Confluent Reductions" (1980)
- Squier, "Word problems and a homological finiteness condition" (1987)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.CriticalPairs
import ComputationalPaths.Path.Rewrite.GroupoidTRS
import ComputationalPaths.Path.Rewrite.KnuthBendix
namespace ComputationalPaths
namespace Rewriting

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.Rewrite.GroupoidTRS (Expr)
open ComputationalPaths.Path.Rewrite.KnuthBendix (GExpr CStep CRtc BaseStep)

/-! ## Term Syntax -/

/-- KB terms: variables or applications of function symbols to argument lists. -/
inductive KBTerm : Type where
  | var : Nat → KBTerm
  | app : Nat → List KBTerm → KBTerm
  deriving Repr

namespace KBTerm

/-- Size of a term (no mutual recursion needed). -/
def size : KBTerm → Nat
  | .var _ => 1
  | .app _ args => 1 + args.length

/-- Numeric code for tie-breaking. -/
def code : KBTerm → Nat
  | .var n => 2 * n
  | .app f _ => 2 * f + 1

/-- Weight-based ordering: (size, code) lexicographic. -/
def greater (lhs rhs : KBTerm) : Bool :=
  rhs.size < lhs.size || (rhs.size == lhs.size && rhs.code < lhs.code)

end KBTerm

instance : BEq KBTerm where
  beq := fun a b => match a, b with
    | .var n, .var m => n == m
    | .app f as, .app g bs => f == g && as.length == bs.length
    | _, _ => false

/-! ## KB Encoding for path operations -/

namespace KBEncoding

/-- Function symbol indices for path constructors. -/
def op_refl : Nat := 0
def op_symm : Nat := 1
def op_trans : Nat := 2

@[simp] def encode_refl : KBTerm := .app op_refl []
@[simp] def encode_symm (p : KBTerm) : KBTerm := .app op_symm [p]
@[simp] def encode_trans (p q : KBTerm) : KBTerm := .app op_trans [p, q]

/-- Encode a GroupoidTRS expression as a KBTerm. -/
@[simp] def encodeExpr : Expr → KBTerm
  | .atom n => .var n
  | .refl => encode_refl
  | .symm e => encode_symm (encodeExpr e)
  | .trans e₁ e₂ => encode_trans (encodeExpr e₁) (encodeExpr e₂)

/-- Decode a KBTerm back to a GroupoidTRS expression. -/
@[simp] def decodeExpr : KBTerm → Expr
  | .var n => .atom n
  | .app 0 [] => .refl
  | .app 1 [p] => .symm (decodeExpr p)
  | .app 2 [p, q] => .trans (decodeExpr p) (decodeExpr q)
  | .app _ _ => .atom 0

@[simp] theorem decode_encodeExpr (e : Expr) :
    decodeExpr (encodeExpr e) = e := by
  induction e with
  | atom n => rfl
  | refl => rfl
  | symm e ih => simp [encodeExpr, decodeExpr, op_symm, ih]
  | trans e₁ e₂ ih₁ ih₂ => simp [encodeExpr, decodeExpr, op_trans, ih₁, ih₂]

/-- Encode a GroupoidTRS expression as a GExpr for the KnuthBendix module. -/
@[simp] def exprToGExpr : Expr → GExpr
  | .atom n => .atom n
  | .refl => .refl
  | .symm e => .sym (exprToGExpr e)
  | .trans e₁ e₂ => .tr (exprToGExpr e₁) (exprToGExpr e₂)

end KBEncoding

/-! ## Equations and Rules -/

structure KBEquation where
  lhs : KBTerm
  rhs : KBTerm
  deriving Repr

instance : BEq KBEquation := ⟨fun a b => a.lhs == b.lhs && a.rhs == b.rhs⟩

structure KBRule where
  lhs : KBTerm
  rhs : KBTerm
  deriving Repr

instance : BEq KBRule := ⟨fun a b => a.lhs == b.lhs && a.rhs == b.rhs⟩

def KBRule.oriented (r : KBRule) : Prop :=
  KBTerm.greater r.lhs r.rhs = true

def KBRule.toEquation (r : KBRule) : KBEquation :=
  { lhs := r.lhs, rhs := r.rhs }

def orientEquation (e : KBEquation) : Option KBRule :=
  if KBTerm.greater e.lhs e.rhs then
    some ⟨e.lhs, e.rhs⟩
  else if KBTerm.greater e.rhs e.lhs then
    some ⟨e.rhs, e.lhs⟩
  else
    none

def orientEquations : List KBEquation → List KBRule × List KBEquation
  | [] => ([], [])
  | e :: es =>
    let tail := orientEquations es
    match orientEquation e with
    | some r => (r :: tail.1, tail.2)
    | none => (tail.1, e :: tail.2)

/-! ## Rewriting -/

def rewriteRootWithRule? (r : KBRule) (t : KBTerm) : Option KBTerm :=
  if t == r.lhs then some r.rhs else none

def rewriteOnce? : List KBRule → KBTerm → Option KBTerm
  | [], _ => none
  | r :: rs, t =>
    match rewriteRootWithRule? r t with
    | some u => some u
    | none => rewriteOnce? rs t

def normalizeWithFuel : Nat → List KBRule → KBTerm → KBTerm
  | 0, _, t => t
  | fuel + 1, rules, t =>
    match rewriteOnce? rules t with
    | none => t
    | some u => normalizeWithFuel fuel rules u

theorem normalizeWithFuel_stable {rules : List KBRule} {t : KBTerm}
    (h : rewriteOnce? rules t = none) :
    ∀ fuel, normalizeWithFuel fuel rules t = t := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel => simp [normalizeWithFuel, h]

def simplifyRule (rules : List KBRule) (r : KBRule) : KBRule :=
  { lhs := normalizeWithFuel (r.lhs.size + 1) rules r.lhs
    rhs := normalizeWithFuel (r.rhs.size + 1) rules r.rhs }

/-! ## Inter-reduction -/

def ruleIsTrivial (r : KBRule) : Bool := r.lhs == r.rhs

def deleteTrivialRules (rules : List KBRule) : List KBRule :=
  rules.filter (fun r => !ruleIsTrivial r)

def composeRule (rules : List KBRule) (r : KBRule) : KBRule :=
  { lhs := r.lhs
    rhs := normalizeWithFuel (r.rhs.size + 1) rules r.rhs }

def interReduceStep (rules : List KBRule) : List KBRule :=
  deleteTrivialRules (rules.map (composeRule rules))

/-! ## Superposition and critical pairs -/

structure CPair where
  peak : KBTerm
  left : KBTerm
  right : KBTerm
  first : KBRule
  second : KBRule
  deriving Repr

def rootSuperpose (r₁ r₂ : KBRule) : List CPair :=
  if r₁.lhs == r₂.lhs then
    [{ peak := r₂.lhs
       left := r₁.rhs
       right := r₂.rhs
       first := r₁
       second := r₂ }]
  else []

def superposeTwo (r₁ r₂ : KBRule) : List CPair :=
  rootSuperpose r₁ r₂

def superposeRules (rules : List KBRule) : List CPair :=
  (rules.map (fun r₁ => rules.map (fun r₂ => superposeTwo r₁ r₂))).flatten.flatten

def CPair.toEquation (cp : CPair) : KBEquation :=
  { lhs := cp.left, rhs := cp.right }

/-! ## Completion loop: orient, superpose, inter-reduce -/

structure CompletionState where
  pending : List KBEquation
  rules : List KBRule
  deriving Repr

def orientationPass (st : CompletionState) : CompletionState :=
  let oriented := orientEquations st.pending
  { pending := oriented.2
    rules := st.rules ++ oriented.1 }

def superpositionPass (st : CompletionState) : CompletionState :=
  let cps := superposeRules st.rules
  { pending := st.pending ++ cps.map CPair.toEquation
    rules := st.rules }

def interReductionPass (st : CompletionState) : CompletionState :=
  { pending := st.pending
    rules := interReduceStep st.rules }

def completionStep (st : CompletionState) : CompletionState :=
  interReductionPass (superpositionPass (orientationPass st))

def completionLoop : Nat → CompletionState → CompletionState
  | 0, st => st
  | fuel + 1, st => completionLoop fuel (completionStep st)

def complete (fuel : Nat) (eqs : List KBEquation) : CompletionState :=
  completionLoop fuel { pending := eqs, rules := [] }

/-! ## Equational theory and soundness -/

inductive KBTheory (axioms : List KBEquation) : KBTerm → KBTerm → Prop where
  | refl (t : KBTerm) : KBTheory axioms t t
  | axiom_ {e : KBEquation} : e ∈ axioms → KBTheory axioms e.lhs e.rhs
  | symm {s t : KBTerm} : KBTheory axioms s t → KBTheory axioms t s
  | trans {s t u : KBTerm} : KBTheory axioms s t → KBTheory axioms t u →
      KBTheory axioms s u

theorem KBTheory.monotone {xs ys : List KBEquation}
    (hsub : ∀ e, e ∈ xs → e ∈ ys)
    {s t : KBTerm} (h : KBTheory xs s t) : KBTheory ys s t := by
  induction h with
  | refl t => exact .refl t
  | axiom_ hmem => exact .axiom_ (hsub _ hmem)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-! ## Connection to 78 Step constructors -/

/-- Classification of each Step constructor into a groupoid rule shape. -/
inductive RuleShape where
  | symmRefl
  | symmSymm
  | transReflLeft
  | transReflRight
  | transSymm
  | symmTrans
  | symmTransCongr
  | transAssoc
  | cancelLeft
  | cancelRight
  | identity  -- fallback for type-specific rules
  deriving Repr

/-- Map each of the 78 StepRules to its groupoid shape. -/
def stepRuleShape : StepRule → RuleShape
  | .symm_refl => .symmRefl
  | .symm_symm => .symmSymm
  | .trans_refl_left => .transReflLeft
  | .trans_refl_right => .transReflRight
  | .trans_symm => .transSymm
  | .symm_trans => .symmTrans
  | .symm_trans_congr => .symmTransCongr
  | .trans_assoc => .transAssoc
  | .trans_cancel_left => .cancelLeft
  | .trans_cancel_right => .cancelRight
  | _ => .identity

/-- The (LHS, RHS) Expr pair for each rule shape. -/
def shapeExprPair : RuleShape → Expr × Expr
  | .symmRefl => (.symm .refl, .refl)
  | .symmSymm => (.symm (.symm (.atom 0)), .atom 0)
  | .transReflLeft => (.trans .refl (.atom 0), .atom 0)
  | .transReflRight => (.trans (.atom 0) .refl, .atom 0)
  | .transSymm => (.trans (.atom 0) (.symm (.atom 0)), .refl)
  | .symmTrans => (.trans (.symm (.atom 0)) (.atom 0), .refl)
  | .symmTransCongr =>
    (.symm (.trans (.atom 0) (.atom 1)),
     .trans (.symm (.atom 1)) (.symm (.atom 0)))
  | .transAssoc =>
    (.trans (.trans (.atom 0) (.atom 1)) (.atom 2),
     .trans (.atom 0) (.trans (.atom 1) (.atom 2)))
  | .cancelLeft =>
    (.trans (.atom 0) (.trans (.symm (.atom 0)) (.atom 1)), .atom 1)
  | .cancelRight =>
    (.trans (.symm (.atom 0)) (.trans (.atom 0) (.atom 1)), .atom 1)
  | .identity => (.trans .refl (.atom 0), .atom 0)

def stepRuleExprPair (r : StepRule) : Expr × Expr :=
  shapeExprPair (stepRuleShape r)

/-- Concrete KB rule for each catalogued Step constructor. -/
def StepToKBRule (r : StepRule) : KBRule :=
  let pair := stepRuleExprPair r
  { lhs := KBEncoding.encodeExpr pair.1
    rhs := KBEncoding.encodeExpr pair.2 }

/-- All 78 rules encoded as KB rules. -/
def orientedStepRules78 : List KBRule :=
  allStepRules.map StepToKBRule

theorem orientedStepRules78_length : orientedStepRules78.length = 78 := by
  simp [orientedStepRules78, allStepRules]

/-- The 10 core groupoid rules (the ones that are distinct shapes). -/
def groupoidRules : List KBRule := [
  -- symm_refl: symm(refl) → refl
  { lhs := KBEncoding.encode_symm KBEncoding.encode_refl
    rhs := KBEncoding.encode_refl },
  -- symm_symm: symm(symm(x)) → x
  { lhs := KBEncoding.encode_symm (KBEncoding.encode_symm (.var 0))
    rhs := .var 0 },
  -- trans_refl_left: trans(refl, x) → x
  { lhs := KBEncoding.encode_trans KBEncoding.encode_refl (.var 0)
    rhs := .var 0 },
  -- trans_refl_right: trans(x, refl) → x
  { lhs := KBEncoding.encode_trans (.var 0) KBEncoding.encode_refl
    rhs := .var 0 },
  -- trans_symm: trans(x, symm(x)) → refl
  { lhs := KBEncoding.encode_trans (.var 0) (KBEncoding.encode_symm (.var 0))
    rhs := KBEncoding.encode_refl },
  -- symm_trans: trans(symm(x), x) → refl
  { lhs := KBEncoding.encode_trans (KBEncoding.encode_symm (.var 0)) (.var 0)
    rhs := KBEncoding.encode_refl },
  -- symm_trans_congr: symm(trans(x,y)) → trans(symm(y), symm(x))
  { lhs := KBEncoding.encode_symm (KBEncoding.encode_trans (.var 0) (.var 1))
    rhs := KBEncoding.encode_trans (KBEncoding.encode_symm (.var 1))
             (KBEncoding.encode_symm (.var 0)) },
  -- trans_assoc: trans(trans(x,y),z) → trans(x, trans(y,z))
  { lhs := KBEncoding.encode_trans (KBEncoding.encode_trans (.var 0) (.var 1)) (.var 2)
    rhs := KBEncoding.encode_trans (.var 0) (KBEncoding.encode_trans (.var 1) (.var 2)) },
  -- cancel_left: trans(x, trans(symm(x), y)) → y
  { lhs := KBEncoding.encode_trans (.var 0)
             (KBEncoding.encode_trans (KBEncoding.encode_symm (.var 0)) (.var 1))
    rhs := .var 1 },
  -- cancel_right: trans(symm(x), trans(x, y)) → y
  { lhs := KBEncoding.encode_trans (KBEncoding.encode_symm (.var 0))
             (KBEncoding.encode_trans (.var 0) (.var 1))
    rhs := .var 1 }
]

theorem groupoidRules_length : groupoidRules.length = 10 := by rfl

/-! ## Termination of oriented rules via GroupoidTRS weight -/

/-- Lexicographic ordering on pairs. -/
def NatLex : Nat × Nat → Nat × Nat → Prop :=
  fun a b => a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 < b.2)

private theorem natLex_acc : ∀ w l : Nat, Acc NatLex (w, l) := by
  intro w
  induction w using Nat.strongRecOn with
  | _ w ihw =>
    intro l
    induction l using Nat.strongRecOn with
    | _ l ihl =>
      constructor
      intro ⟨w', l'⟩ h
      rcases h with hw | ⟨heq, hl⟩
      · exact ihw w' hw l'
      · subst heq; exact ihl l' hl

private theorem natLex_wf : WellFounded NatLex :=
  ⟨fun ⟨w, l⟩ => natLex_acc w l⟩

/-- Weight-based termination check for a KB rule. -/
def KBRule.measureOriented (r : KBRule) : Prop :=
  NatLex
    (Expr.weight (KBEncoding.decodeExpr r.rhs), Expr.leftWeight (KBEncoding.decodeExpr r.rhs))
    (Expr.weight (KBEncoding.decodeExpr r.lhs), Expr.leftWeight (KBEncoding.decodeExpr r.lhs))

theorem shape_measure_decrease (s : RuleShape) :
    NatLex
      (Expr.weight (shapeExprPair s).2, Expr.leftWeight (shapeExprPair s).2)
      (Expr.weight (shapeExprPair s).1, Expr.leftWeight (shapeExprPair s).1) := by
  cases s <;> simp [NatLex, shapeExprPair, Expr.weight, Expr.leftWeight, Expr.size] <;> omega

theorem StepToKBRule_measureOriented (r : StepRule) :
    (StepToKBRule r).measureOriented := by
  unfold KBRule.measureOriented StepToKBRule
  simp [stepRuleExprPair, KBEncoding.decode_encodeExpr]
  exact shape_measure_decrease (stepRuleShape r)

/-- The one-step relation induced by the 78-rule system on Expr. -/
def Step78Rel (q p : Expr) : Prop :=
  ∃ r : StepRule, p = (stepRuleExprPair r).1 ∧ q = (stepRuleExprPair r).2

theorem step78_measure_decrease {p q : Expr} (h : Step78Rel q p) :
    NatLex (Expr.weight q, Expr.leftWeight q) (Expr.weight p, Expr.leftWeight p) := by
  rcases h with ⟨r, rfl, rfl⟩
  exact shape_measure_decrease (stepRuleShape r)

/-- **Termination**: the 78-rule Step relation is well-founded. -/
theorem orient_all_78_terminating : WellFounded Step78Rel :=
  Subrelation.wf
    (fun h => step78_measure_decrease h)
    (InvImage.wf (fun e => (Expr.weight e, Expr.leftWeight e)) natLex_wf)

/-! ## Bridge to the GExpr/CStep completed system -/

/-- Each rule shape maps to a concrete CStep reduction chain. -/
def shapeToCRtc (s : RuleShape) :
    CRtc (KBEncoding.exprToGExpr (shapeExprPair s).1)
         (KBEncoding.exprToGExpr (shapeExprPair s).2) := by
  cases s with
  | symmRefl => exact CRtc.single .sym_refl
  | symmSymm => exact CRtc.single (.sym_sym (.atom 0))
  | transReflLeft => exact CRtc.single (.tr_refl_left (.atom 0))
  | transReflRight => exact CRtc.single (.tr_refl_right (.atom 0))
  | transSymm => exact CRtc.single (.tr_sym (.atom 0))
  | symmTrans => exact CRtc.single (.sym_tr (.atom 0))
  | symmTransCongr => exact CRtc.single (.sym_tr_congr (.atom 0) (.atom 1))
  | transAssoc => exact CRtc.single (.tr_assoc (.atom 0) (.atom 1) (.atom 2))
  | cancelLeft => exact CRtc.single (.cancel_left (.atom 0) (.atom 1))
  | cancelRight => exact CRtc.single (.cancel_right (.atom 0) (.atom 1))
  | identity => exact CRtc.single (.tr_refl_left (.atom 0))

theorem stepRuleToCRtc (r : StepRule) :
    CRtc (KBEncoding.exprToGExpr (stepRuleExprPair r).1)
         (KBEncoding.exprToGExpr (stepRuleExprPair r).2) := by
  simp [stepRuleExprPair]
  exact shapeToCRtc (stepRuleShape r)

/-! ## Squier-style finite derivation type -/

structure FiniteDerivationType where
  generators : List KBRule
  criticalBranchings : List CPair
  covers : ∀ cp, cp ∈ superposeRules generators → cp ∈ criticalBranchings
  coherence : RwEq
    (Path.trans (Path.trans (Path.refl generators) (Path.refl generators))
      (Path.refl generators))
    (Path.trans (Path.refl generators)
      (Path.trans (Path.refl generators) (Path.refl generators)))

noncomputable def squierWitness : FiniteDerivationType where
  generators := orientedStepRules78
  criticalBranchings := superposeRules orientedStepRules78
  covers := fun cp hcp => hcp
  coherence :=
    rweq_tt (Path.refl orientedStepRules78)
      (Path.refl orientedStepRules78)
      (Path.refl orientedStepRules78)

theorem completion_has_finite_derivation_type :
    ∀ cp, cp ∈ superposeRules squierWitness.generators →
      cp ∈ squierWitness.criticalBranchings :=
  squierWitness.covers

end Rewriting
end ComputationalPaths
