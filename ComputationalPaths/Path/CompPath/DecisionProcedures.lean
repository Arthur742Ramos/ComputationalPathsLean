/-
# Decision Procedures for Path Equality

Formalizes decision procedures for path and word problems in rewriting systems:
decidability of path equality for confluent + terminating TRS, automata-theoretic
recognition of path languages, Dehn function bounds, and closure properties
of regular path sets.

## References

- Baader & Nipkow, "Term Rewriting and All That" (1998)
- Epstein et al., "Word Processing in Groups" (1992)
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.CompPath.DecisionProcedures

open ComputationalPaths.Path

universe u

/-! ## Word Problem for Confluent Terminating Systems -/

/-- Multi-step reduction. -/
inductive RStar {A : Type u} (step : A → A → Prop) : A → A → Prop where
  | refl : RStar step a a
  | cons : step a b → RStar step b c → RStar step a c

namespace RStar

theorem single {A : Type u} {step : A → A → Prop} {a b : A}
    (s : step a b) : RStar step a b := .cons s .refl

theorem append {A : Type u} {step : A → A → Prop} {a b c : A}
    (h1 : RStar step a b) (h2 : RStar step b c) : RStar step a c := by
  induction h1 with
  | refl => exact h2
  | cons s _ ih => exact .cons s (ih h2)

end RStar

def IsNF {A : Type u} (step : A → A → Prop) (a : A) : Prop := ∀ b, ¬step a b

def Confluent {A : Type u} (step : A → A → Prop) : Prop :=
  ∀ {a b c : A}, RStar step a b → RStar step a c →
    ∃ d, RStar step b d ∧ RStar step c d

def SN {A : Type u} (step : A → A → Prop) : Prop :=
  WellFounded (fun b a => step a b)

theorem sn_has_nf {A : Type u} {step : A → A → Prop} (hT : SN step) (a : A) :
    ∃ nf, RStar step a nf ∧ IsNF step nf := by
  induction a using hT.induction with
  | _ a ih =>
    by_cases h : ∃ b, step a b
    · obtain ⟨b, hab⟩ := h
      obtain ⟨nf, hnf, hnfnf⟩ := ih b hab
      exact ⟨nf, .cons hab hnf, hnfnf⟩
    · simp only [not_exists] at h
      exact ⟨a, .refl, h⟩

theorem nf_unique {A : Type u} {step : A → A → Prop}
    (hC : Confluent step) {a nf1 nf2 : A}
    (h1 : RStar step a nf1) (hn1 : IsNF step nf1)
    (h2 : RStar step a nf2) (hn2 : IsNF step nf2) : nf1 = nf2 := by
  obtain ⟨d, hd1, hd2⟩ := hC h1 h2
  cases hd1 with
  | refl =>
    cases hd2 with
    | refl => rfl
    | cons s _ => exact absurd s (hn2 _)
  | cons s _ => exact absurd s (hn1 _)

noncomputable def normalForm {A : Type u} {step : A → A → Prop}
    (hT : SN step) (a : A) : A :=
  (sn_has_nf hT a).choose

theorem normalForm_reduces {A : Type u} {step : A → A → Prop}
    (hT : SN step) (a : A) : RStar step a (normalForm hT a) :=
  (sn_has_nf hT a).choose_spec.1

theorem normalForm_is_nf {A : Type u} {step : A → A → Prop}
    (hT : SN step) (a : A) : IsNF step (normalForm hT a) :=
  (sn_has_nf hT a).choose_spec.2

/-- Key lemma: if a →* c and a has normalForm nf(a), then nf(a) = nf(c). -/
theorem nf_of_reduct {A : Type u} {step : A → A → Prop}
    (hT : SN step) (hC : Confluent step) {a c : A}
    (hac : RStar step a c) : normalForm hT a = normalForm hT c := by
  have ha := normalForm_reduces hT a
  have hc := normalForm_reduces hT c
  have hna := normalForm_is_nf hT a
  have hnc := normalForm_is_nf hT c
  -- a →* nf(a) and a →* c →* nf(c)
  exact nf_unique hC ha hna (RStar.append hac hc) hnc

/-- Two elements are joinable iff they have the same normal form. -/
theorem joinable_iff_nf_eq {A : Type u} {step : A → A → Prop}
    (hT : SN step) (hC : Confluent step) {a b : A} :
    (∃ c, RStar step a c ∧ RStar step b c) ↔
    normalForm hT a = normalForm hT b := by
  constructor
  · intro ⟨c, hac, hbc⟩
    rw [nf_of_reduct hT hC hac, nf_of_reduct hT hC hbc]
  · intro heq
    exact ⟨normalForm hT a, normalForm_reduces hT a, heq ▸ normalForm_reduces hT b⟩

noncomputable def word_problem_decidable {A : Type u} {step : A → A → Prop}
    (hT : SN step) (hC : Confluent step) [DecidableEq A]
    (a b : A) : Decidable (∃ c, RStar step a c ∧ RStar step b c) := by
  rw [joinable_iff_nf_eq hT hC]
  exact decEq _ _

/-! ## Path Words -/

/-- A path word over alphabet `Sym`. -/
abbrev PathWord (Sym : Type u) := List Sym

def PathWord.empty (Sym : Type u) : PathWord Sym := []

def PathWord.concat {Sym : Type u} (w1 w2 : PathWord Sym) : PathWord Sym :=
  w1 ++ w2

theorem pathword_concat_assoc {Sym : Type u} (w1 w2 w3 : PathWord Sym) :
    PathWord.concat (PathWord.concat w1 w2) w3 =
    PathWord.concat w1 (PathWord.concat w2 w3) :=
  List.append_assoc w1 w2 w3

theorem pathword_concat_empty_left {Sym : Type u} (w : PathWord Sym) :
    PathWord.concat (PathWord.empty Sym) w = w :=
  List.nil_append w

theorem pathword_concat_empty_right {Sym : Type u} (w : PathWord Sym) :
    PathWord.concat w (PathWord.empty Sym) = w :=
  List.append_nil w

theorem pathword_concat_len {Sym : Type u} (w1 w2 : PathWord Sym) :
    (PathWord.concat w1 w2).length = w1.length + w2.length := by
  simp [PathWord.concat, List.length_append]

/-! ## DFA for Path Recognition -/

/-- A Deterministic Finite Automaton. -/
structure DFA (Sym : Type u) where
  State : Type u
  start : State
  accept : State → Bool
  delta : State → Sym → State

namespace DFA

variable {Sym : Type u}

def run (M : DFA Sym) (w : PathWord Sym) : M.State :=
  w.foldl M.delta M.start

def accepts (M : DFA Sym) (w : PathWord Sym) : Bool :=
  M.accept (M.run w)

/-- A DFA accepts a word iff it ends in an accepting state (decidable). -/
theorem accepts_decidable (M : DFA Sym) (w : PathWord Sym) :
    M.accepts w = true ∨ M.accepts w = false := by
  cases M.accepts w <;> simp

theorem run_empty (M : DFA Sym) : M.run (PathWord.empty Sym) = M.start := rfl

theorem run_single (M : DFA Sym) (a : Sym) :
    M.run [a] = M.delta M.start a := rfl

theorem run_concat (M : DFA Sym) (w1 w2 : PathWord Sym) :
    M.run (PathWord.concat w1 w2) = w2.foldl M.delta (M.run w1) := by
  simp [run, PathWord.concat, List.foldl_append]

end DFA

/-! ## Regular Path Languages via DFA acceptance -/

/-- A language predicate on path words is regular if decided by a DFA. -/
def IsRegular {Sym : Type u} (L : PathWord Sym → Prop) : Prop :=
  ∃ M : DFA Sym, ∀ w, M.accepts w = true ↔ L w

/-- The always-false predicate is regular. -/
theorem empty_regular (Sym : Type u) : IsRegular (fun (_ : PathWord Sym) => False) := by
  refine ⟨⟨PUnit.{u+1}, PUnit.unit, fun _ => false, fun _ _ => PUnit.unit⟩, fun w => ?_⟩
  simp [DFA.accepts]

/-- The always-true predicate is regular. -/
theorem univ_regular (Sym : Type u) : IsRegular (fun (_ : PathWord Sym) => True) := by
  refine ⟨⟨PUnit.{u+1}, PUnit.unit, fun _ => true, fun _ _ => PUnit.unit⟩, fun w => ?_⟩
  simp [DFA.accepts]

/-- Complement of a regular language is regular. -/
theorem regular_complement {Sym : Type u} {L : PathWord Sym → Prop}
    (hL : IsRegular L) : IsRegular (fun w => ¬L w) := by
  obtain ⟨M, hM⟩ := hL
  refine ⟨⟨M.State, M.start, fun s => !M.accept s, M.delta⟩, fun w => ?_⟩
  simp only [DFA.accepts, DFA.run]
  constructor
  · intro h hLw
    have hmw := (hM w).mpr hLw
    -- hmw : M.accepts w = true, i.e., M.accept (foldl ...) = true
    -- h : (!M.accept (foldl ...)) = true, i.e., M.accept (foldl ...) = false
    simp [DFA.accepts, DFA.run] at hmw
    rw [hmw] at h
    simp at h
  · intro hLw
    have := mt (hM w).mp hLw
    simp only [Bool.not_eq_true, DFA.accepts, DFA.run] at this
    rw [this]
    rfl

/-! ## Dehn Function -/

structure DehnFunction where
  bound : Nat → Nat
  monotone : ∀ m n, m ≤ n → bound m ≤ bound n

def LinearDehn (C : Nat) : DehnFunction where
  bound := fun n => C * n
  monotone := fun _ _ h => Nat.mul_le_mul_left C h

def QuadraticDehn (C : Nat) : DehnFunction where
  bound := fun n => C * n * n
  monotone := fun _ _ h => Nat.mul_le_mul (Nat.mul_le_mul_left C h) h

theorem linear_dehn_bound (C n : Nat) :
    (LinearDehn C).bound n = C * n := rfl

theorem quadratic_dehn_bound (C n : Nat) :
    (QuadraticDehn C).bound n = C * n * n := rfl

def DehnFunction.comp (f g : DehnFunction) : DehnFunction where
  bound := fun n => f.bound (g.bound n)
  monotone := fun _ _ h => f.monotone _ _ (g.monotone _ _ h)

theorem dehn_comp_bound (f g : DehnFunction) (n : Nat) :
    (f.comp g).bound n = f.bound (g.bound n) := rfl

/-! ## Decidable Rewriting System -/

structure DecRWS (A : Type u) [DecidableEq A] where
  step : A → A → Prop
  terminating : SN step
  confluent : Confluent step

noncomputable def dec_rws_decidable {A : Type u} [DecidableEq A] (R : DecRWS A)
    (a b : A) : Decidable (∃ c, RStar R.step a c ∧ RStar R.step b c) :=
  word_problem_decidable R.terminating R.confluent a b

theorem dec_rws_equiv_refl {A : Type u} [DecidableEq A] (R : DecRWS A)
    (a : A) : ∃ c, RStar R.step a c ∧ RStar R.step a c :=
  ⟨a, .refl, .refl⟩

theorem dec_rws_equiv_symm {A : Type u} [DecidableEq A] (R : DecRWS A)
    {a b : A} (h : ∃ c, RStar R.step a c ∧ RStar R.step b c) :
    ∃ c, RStar R.step b c ∧ RStar R.step a c := by
  obtain ⟨c, hac, hbc⟩ := h; exact ⟨c, hbc, hac⟩

theorem dec_rws_equiv_trans {A : Type u} [DecidableEq A] (R : DecRWS A)
    {a b c : A}
    (h1 : ∃ d, RStar R.step a d ∧ RStar R.step b d)
    (h2 : ∃ d, RStar R.step b d ∧ RStar R.step c d) :
    ∃ d, RStar R.step a d ∧ RStar R.step c d := by
  obtain ⟨d1, had1, hbd1⟩ := h1
  obtain ⟨d2, hbd2, hcd2⟩ := h2
  obtain ⟨e, hd1e, hd2e⟩ := R.confluent hbd1 hbd2
  exact ⟨e, RStar.append had1 hd1e, RStar.append hcd2 hd2e⟩

/-! ## Connection to Computational Paths -/

def eqToPath {A : Type u} {a b : A} (h : a = b) : Path a b :=
  Path.mk [Step.mk _ _ h] h

/-- All proofs of `a = b` are equal (proof irrelevance). -/
theorem path_toEq_irrel {A : Type u} {a b : A} (p q : Path a b) :
    p.toEq = q.toEq := rfl

/-- Two paths with the same endpoints transport identically. -/
theorem path_transport_eq {A : Type u} {a b : A} {D : A → Type u}
    (p q : Path a b) (x : D a) :
    Path.transport p x = Path.transport q x := by
  cases p with | mk _ hp => cases q with | mk _ hq => cases hp; cases hq; rfl

theorem path_transport_refl {A : Type u} {a : A} {D : A → Type u}
    (x : D a) : Path.transport (Path.refl a) x = x := rfl

noncomputable instance path_endpoints_decidable {A : Type u} [DecidableEq A]
    (a b : A) : Decidable (a = b) := inferInstance

/-! ## Path Traces and Automata -/

def pathTrace {A : Type u} {a b : A} (p : Path a b) : List (Step A) := p.steps

theorem pathTrace_refl {A : Type u} (a : A) :
    pathTrace (Path.refl a) = [] := rfl

theorem pathTrace_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathTrace (Path.trans p q) = pathTrace p ++ pathTrace q := rfl

theorem pathTrace_symm {A : Type u} {a b : A} (p : Path a b) :
    pathTrace (Path.symm p) = (pathTrace p).reverse.map Step.symm := rfl

def pathTraceLen {A : Type u} {a b : A} (p : Path a b) : Nat :=
  (pathTrace p).length

theorem pathTraceLen_refl {A : Type u} (a : A) :
    pathTraceLen (Path.refl a) = 0 := rfl

theorem pathTraceLen_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathTraceLen (Path.trans p q) = pathTraceLen p + pathTraceLen q := by
  simp [pathTraceLen, pathTrace, List.length_append]

theorem pathTraceLen_symm {A : Type u} {a b : A} (p : Path a b) :
    pathTraceLen (Path.symm p) = pathTraceLen p := by
  simp [pathTraceLen, pathTrace, List.length_map, List.length_reverse]

end ComputationalPaths.Path.CompPath.DecisionProcedures
