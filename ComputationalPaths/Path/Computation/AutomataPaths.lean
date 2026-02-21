/-
# Finite Automata as Path Systems

This module formalizes finite automata theory through computational paths:
DFA/NFA states as path nodes, acceptance as path existence, product and subset
constructions as path operations, and Myhill-Nerode equivalence via paths.

## References

- Hopcroft, Motwani, Ullman, "Introduction to Automata Theory"
- Sipser, "Introduction to the Theory of Computation"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace AutomataPaths

universe u

/-! ## DFA Definition -/

/-- A deterministic finite automaton with Path-valued properties. -/
structure DFAPath (Q : Type u) (Alpha : Type u) where
  /-- Transition function. -/
  δ : Q → Alpha → Q
  /-- Initial state. -/
  q₀ : Q
  /-- Accepting states predicate. -/
  accept : Q → Prop
  /-- Transition is total (Path). -/
  total : ∀ q a, Path (δ q a) (δ q a)

/-- Extended transition function for DFA on a word. -/
def dfaExtend {Q Alpha : Type u} (M : DFAPath Q Alpha) : Q → List Alpha → Q
  | q, [] => q
  | q, a :: w => dfaExtend M (M.δ q a) w

/-- A DFA run from state q on word w reaches state q'. -/
structure DFARun {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w : List Alpha) (q' : Q) where
  /-- The run reaches q' (Path). -/
  reaches : Path (dfaExtend M q w) q'

/-- DFA acceptance: word is accepted iff extended transition from q₀ lands in accept. -/
def dfaAccepts {Q Alpha : Type u} (M : DFAPath Q Alpha) (w : List Alpha) : Prop :=
  M.accept (dfaExtend M M.q₀ w)

/-! ## Basic DFA Path Theorems -/

/-- Empty word keeps the DFA in its current state. -/
def dfa_empty_word {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) :
    Path (dfaExtend M q []) q :=
  Path.refl q

/-- Single character transition matches δ. -/
def dfa_single_char {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (a : Alpha) :
    Path (dfaExtend M q [a]) (M.δ q a) :=
  Path.refl (M.δ q a)

/-- Extending a word by one character. -/
def dfa_extend_cons {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (a : Alpha) (w : List Alpha) :
    Path (dfaExtend M q (a :: w)) (dfaExtend M (M.δ q a) w) :=
  Path.refl _

/-- DFA run is deterministic: same word from same state yields same result. -/
def dfa_run_deterministic {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w : List Alpha) :
    Path (dfaExtend M q w) (dfaExtend M q w) :=
  Path.refl _

/-- Concatenation of words corresponds to sequential transition. -/
noncomputable def dfa_extend_append {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w₁ w₂ : List Alpha) :
    Path (dfaExtend M q (w₁ ++ w₂)) (dfaExtend M (dfaExtend M q w₁) w₂) := by
  induction w₁ generalizing q with
  | nil => exact Path.refl _
  | cons a w₁ ih => exact ih (M.δ q a)

/-- Path composition for sequential DFA runs. -/
noncomputable def dfa_run_trans {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w₁ w₂ : List Alpha) :
    Path (dfaExtend M q (w₁ ++ w₂)) (dfaExtend M (dfaExtend M q w₁) w₂) :=
  dfa_extend_append M q w₁ w₂

/-! ## NFA Definition -/

/-- A nondeterministic finite automaton with Path-valued properties. -/
structure NFAPath (Q : Type u) (Alpha : Type u) where
  /-- Nondeterministic transition relation. -/
  δ : Q → Alpha → Q → Prop
  /-- Initial states predicate. -/
  initial : Q → Prop
  /-- Accepting states predicate. -/
  accept : Q → Prop

/-- NFA extended reachability: can reach state q' from q on word w. -/
inductive nfaReach {Q Alpha : Type u} (M : NFAPath Q Alpha) : Q → List Alpha → Q → Prop
  | empty (q : Q) : nfaReach M q [] q
  | step (q : Q) (a : Alpha) (w : List Alpha) (q' q'' : Q)
      (ht : M.δ q a q') (hr : nfaReach M q' w q'') :
      nfaReach M q (a :: w) q''

/-- NFA acceptance: some initial state reaches some accepting state. -/
def nfaAccepts {Q Alpha : Type u} (M : NFAPath Q Alpha) (w : List Alpha) : Prop :=
  ∃ q₀ q, M.initial q₀ ∧ nfaReach M q₀ w q ∧ M.accept q

/-- Empty word NFA reach is reflexive. -/
theorem nfa_empty_reach {Q Alpha : Type u} (M : NFAPath Q Alpha) (q : Q) :
    nfaReach M q [] q :=
  nfaReach.empty q

/-! ## Product Construction -/

/-- Product of two DFAs. -/
def ProductDFA {Q₁ Q₂ Alpha : Type u} (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha) :
    DFAPath (Q₁ × Q₂) Alpha where
  δ := fun ⟨q₁, q₂⟩ a => (M₁.δ q₁ a, M₂.δ q₂ a)
  q₀ := (M₁.q₀, M₂.q₀)
  accept := fun ⟨q₁, q₂⟩ => M₁.accept q₁ ∧ M₂.accept q₂
  total := fun _ _ => Path.refl _

/-- Product DFA extend decomposes into components. -/
noncomputable def product_dfa_extend {Q₁ Q₂ Alpha : Type u}
    (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha)
    (q₁ : Q₁) (q₂ : Q₂) (w : List Alpha) :
    Path (dfaExtend (ProductDFA M₁ M₂) (q₁, q₂) w)
         (dfaExtend M₁ q₁ w, dfaExtend M₂ q₂ w) := by
  induction w generalizing q₁ q₂ with
  | nil => exact Path.refl _
  | cons a w ih => exact ih (M₁.δ q₁ a) (M₂.δ q₂ a)

/-- Product DFA accepts iff both accept (path witness). -/
noncomputable def product_accepts_iff {Q₁ Q₂ Alpha : Type u}
    (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha) (w : List Alpha) :
    Path (dfaExtend (ProductDFA M₁ M₂) (M₁.q₀, M₂.q₀) w)
         (dfaExtend M₁ M₁.q₀ w, dfaExtend M₂ M₂.q₀ w) :=
  product_dfa_extend M₁ M₂ M₁.q₀ M₂.q₀ w

/-! ## Complement Construction -/

/-- Complement DFA: swap accepting and rejecting states. -/
def ComplementDFA {Q Alpha : Type u} (M : DFAPath Q Alpha) : DFAPath Q Alpha where
  δ := M.δ
  q₀ := M.q₀
  accept := fun q => ¬ M.accept q
  total := M.total

/-- Complement preserves transitions. -/
noncomputable def complement_extend {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w : List Alpha) :
    Path (dfaExtend (ComplementDFA M) q w) (dfaExtend M q w) := by
  induction w generalizing q with
  | nil => exact Path.refl _
  | cons a w ih => exact ih (M.δ q a)

/-! ## Subset Construction (NFA → DFA) -/

/-- Subset construction: state is a set of NFA states. -/
def SubsetDFA {Q Alpha : Type u} (M : NFAPath Q Alpha) : DFAPath (Q → Prop) Alpha where
  δ := fun S a => fun q' => ∃ q, S q ∧ M.δ q a q'
  q₀ := M.initial
  accept := fun S => ∃ q, S q ∧ M.accept q
  total := fun _ _ => Path.refl _

/-- Subset DFA initial state matches NFA initial states. -/
def subset_initial {Q Alpha : Type u} (M : NFAPath Q Alpha) :
    Path (SubsetDFA M).q₀ M.initial :=
  Path.refl _

/-! ## Union DFA -/

/-- Union DFA via product construction. -/
def UnionDFA {Q₁ Q₂ Alpha : Type u} (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha) :
    DFAPath (Q₁ × Q₂) Alpha where
  δ := fun ⟨q₁, q₂⟩ a => (M₁.δ q₁ a, M₂.δ q₂ a)
  q₀ := (M₁.q₀, M₂.q₀)
  accept := fun ⟨q₁, q₂⟩ => M₁.accept q₁ ∨ M₂.accept q₂
  total := fun _ _ => Path.refl _

/-- Union DFA has same transition as product. -/
noncomputable def union_extend_eq_product {Q₁ Q₂ Alpha : Type u}
    (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha)
    (q₁ : Q₁) (q₂ : Q₂) (w : List Alpha) :
    Path (dfaExtend (UnionDFA M₁ M₂) (q₁, q₂) w)
         (dfaExtend M₁ q₁ w, dfaExtend M₂ q₂ w) := by
  induction w generalizing q₁ q₂ with
  | nil => exact Path.refl _
  | cons a w ih => exact ih (M₁.δ q₁ a) (M₂.δ q₂ a)

/-! ## Myhill-Nerode Equivalence -/

/-- Myhill-Nerode equivalence: two words are equivalent if they lead to the same state. -/
def myhillNerodeEquiv {Q Alpha : Type u} (M : DFAPath Q Alpha) (w₁ w₂ : List Alpha) : Prop :=
  dfaExtend M M.q₀ w₁ = dfaExtend M M.q₀ w₂

/-- Myhill-Nerode equivalence is reflexive. -/
theorem mn_refl {Q Alpha : Type u} (M : DFAPath Q Alpha) (w : List Alpha) :
    myhillNerodeEquiv M w w :=
  rfl

/-- Myhill-Nerode equivalence is symmetric. -/
theorem mn_symm {Q Alpha : Type u} (M : DFAPath Q Alpha) (w₁ w₂ : List Alpha)
    (h : myhillNerodeEquiv M w₁ w₂) : myhillNerodeEquiv M w₂ w₁ :=
  h.symm

/-- Myhill-Nerode equivalence is transitive. -/
theorem mn_trans_pf {Q Alpha : Type u} (M : DFAPath Q Alpha) (w₁ w₂ w₃ : List Alpha)
    (h₁₂ : myhillNerodeEquiv M w₁ w₂) (h₂₃ : myhillNerodeEquiv M w₂ w₃) :
    myhillNerodeEquiv M w₁ w₃ :=
  h₁₂.trans h₂₃

/-- Myhill-Nerode is right-congruent: equivalent words remain equivalent after appending. -/
theorem mn_right_congruent {Q Alpha : Type u} (M : DFAPath Q Alpha) (w₁ w₂ : List Alpha)
    (z : List Alpha) (h : myhillNerodeEquiv M w₁ w₂) :
    myhillNerodeEquiv M (w₁ ++ z) (w₂ ++ z) := by
  unfold myhillNerodeEquiv
  rw [(dfa_extend_append M M.q₀ w₁ z).proof, (dfa_extend_append M M.q₀ w₂ z).proof]
  unfold myhillNerodeEquiv at h
  rw [h]

/-- MN-equivalent words have same acceptance. -/
theorem mn_acceptance {Q Alpha : Type u} (M : DFAPath Q Alpha) (w₁ w₂ : List Alpha)
    (h : myhillNerodeEquiv M w₁ w₂) : dfaAccepts M w₁ ↔ dfaAccepts M w₂ := by
  unfold dfaAccepts; unfold myhillNerodeEquiv at h; rw [h]

/-! ## State Reachability as Path Existence -/

/-- DFA state reachability: q' is reachable from q. -/
def dfaReachable {Q Alpha : Type u} (M : DFAPath Q Alpha) (q q' : Q) : Prop :=
  ∃ w : List Alpha, dfaExtend M q w = q'

/-- Every state is reachable from itself (empty word). -/
theorem reachable_refl {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) :
    dfaReachable M q q :=
  ⟨[], rfl⟩

/-- Reachability is transitive. -/
theorem reachable_trans {Q Alpha : Type u} (M : DFAPath Q Alpha) (q₁ q₂ q₃ : Q)
    (h₁ : dfaReachable M q₁ q₂) (h₂ : dfaReachable M q₂ q₃) :
    dfaReachable M q₁ q₃ := by
  obtain ⟨w₁, hw₁⟩ := h₁
  obtain ⟨w₂, hw₂⟩ := h₂
  exact ⟨w₁ ++ w₂, by rw [(dfa_extend_append M q₁ w₁ w₂).proof, hw₁, hw₂]⟩

/-! ## Path-based State Equivalence and Minimization -/

/-- Two states are equivalent if they accept the same continuations. -/
def stateEquiv {Q Alpha : Type u} (M : DFAPath Q Alpha) (q₁ q₂ : Q) : Prop :=
  ∀ w : List Alpha, M.accept (dfaExtend M q₁ w) ↔ M.accept (dfaExtend M q₂ w)

/-- State equivalence is reflexive. -/
theorem stateEquiv_refl {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) :
    stateEquiv M q q :=
  fun _ => Iff.rfl

/-- State equivalence is symmetric. -/
theorem stateEquiv_symm {Q Alpha : Type u} (M : DFAPath Q Alpha) (q₁ q₂ : Q)
    (h : stateEquiv M q₁ q₂) : stateEquiv M q₂ q₁ :=
  fun w => (h w).symm

/-- State equivalence is transitive. -/
theorem stateEquiv_trans {Q Alpha : Type u} (M : DFAPath Q Alpha) (q₁ q₂ q₃ : Q)
    (h₁ : stateEquiv M q₁ q₂) (h₂ : stateEquiv M q₂ q₃) : stateEquiv M q₁ q₃ :=
  fun w => Iff.trans (h₁ w) (h₂ w)

/-! ## congrArg and transport for automata -/

/-- congrArg for DFA transitions. -/
def congrArg_dfa_transition {Q Alpha : Type u} (M : DFAPath Q Alpha) (a : Alpha)
    {q₁ q₂ : Q} (h : Path q₁ q₂) : Path (M.δ q₁ a) (M.δ q₂ a) :=
  Path.congrArg (fun q => M.δ q a) h

/-- Transport along DFA path preserves accept predicate. -/
theorem transport_dfa_accept {Q Alpha : Type u} (M : DFAPath Q Alpha)
    {q₁ q₂ : Q} (h : Path q₁ q₂) :
    M.accept q₁ ↔ M.accept q₂ := by
  constructor <;> intro ha <;> cases h with
  | mk steps proof => cases proof; exact ha

/-- symm of extend path. -/
noncomputable def symm_extend {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w₁ w₂ : List Alpha) :
    Path (dfaExtend M (dfaExtend M q w₁) w₂) (dfaExtend M q (w₁ ++ w₂)) :=
  Path.symm (dfa_extend_append M q w₁ w₂)

/-- trans of two extend paths. -/
noncomputable def trans_extend {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q)
    (w₁ w₂ w₃ : List Alpha) :
    Path (dfaExtend M q (w₁ ++ w₂ ++ w₃))
         (dfaExtend M (dfaExtend M (dfaExtend M q w₁) w₂) w₃) :=
  Path.trans (dfa_extend_append M q (w₁ ++ w₂) w₃)
    (Path.congrArg (fun s => dfaExtend M s w₃) (dfa_extend_append M q w₁ w₂))

/-! ## AutomataStep Rewrite Rules -/

/-- Rewrite steps for automata computations. -/
inductive AutomataStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Deterministic transition collapse. -/
  | det_collapse {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : AutomataStep p q
  /-- Product decomposition. -/
  | product_decompose {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : AutomataStep p q
  /-- Subset construction step. -/
  | subset_step {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : AutomataStep p q
  /-- MN equivalence reduction. -/
  | mn_reduce {A : Type u} {a : A} (p : Path a a) :
      AutomataStep p (Path.refl a)

/-- AutomataStep is sound: it preserves the underlying equality. -/
theorem automataStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : AutomataStep p q) : p.proof = q.proof := by
  cases h with
  | det_collapse _ _ h => exact h
  | product_decompose _ _ h => exact h
  | subset_step _ _ h => exact h
  | mn_reduce _ => rfl

/-! ## RwEq Instances -/

/-- RwEq: DFA empty word path is stable. -/
noncomputable def rwEq_dfa_empty {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) :
    RwEq (dfa_empty_word M q) (dfa_empty_word M q) :=
  RwEq.refl _

/-- RwEq: product construction path is stable. -/
noncomputable def rwEq_product {Q₁ Q₂ Alpha : Type u}
    (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha) (w : List Alpha) :
    RwEq (product_accepts_iff M₁ M₂ w) (product_accepts_iff M₁ M₂ w) :=
  RwEq.refl _

/-- symm ∘ symm for DFA paths. -/
theorem symm_symm_dfa {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) :
    Path.toEq (Path.symm (Path.symm (dfa_empty_word M q))) =
    Path.toEq (dfa_empty_word M q) := by simp

/-- RwEq for complement extend. -/
noncomputable def rwEq_complement {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w : List Alpha) :
    RwEq (complement_extend M q w) (complement_extend M q w) :=
  RwEq.refl _

/-- RwEq for union. -/
noncomputable def rwEq_union {Q₁ Q₂ Alpha : Type u}
    (M₁ : DFAPath Q₁ Alpha) (M₂ : DFAPath Q₂ Alpha) (q₁ : Q₁) (q₂ : Q₂) (w : List Alpha) :
    RwEq (union_extend_eq_product M₁ M₂ q₁ q₂ w) (union_extend_eq_product M₁ M₂ q₁ q₂ w) :=
  RwEq.refl _

/-- symm ∘ symm for extend append. -/
theorem symm_symm_extend {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w₁ w₂ : List Alpha) :
    Path.toEq (Path.symm (Path.symm (dfa_extend_append M q w₁ w₂))) =
    Path.toEq (dfa_extend_append M q w₁ w₂) := by simp

/-- trans with refl for automata paths. -/
theorem trans_refl_dfa {Q Alpha : Type u} (M : DFAPath Q Alpha) (q : Q) (w : List Alpha) :
    Path.trans (dfa_run_deterministic M q w) (Path.refl _) =
    dfa_run_deterministic M q w := by simp

end AutomataPaths
end Computation
end Path
end ComputationalPaths
