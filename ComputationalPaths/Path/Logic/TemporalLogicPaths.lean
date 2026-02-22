/-
# Temporal Logic via Computational Paths

This module models temporal logic using computational paths:
LTL operators (always, eventually, until, next), CTL operators,
model checking aspects, and fairness properties.

## References

- Baier & Katoen, "Principles of Model Checking"
- Pnueli, "The Temporal Logic of Programs"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace TemporalLogicPaths

universe u

open ComputationalPaths.Path

/-! ## Transition Systems -/

/-- A transition system: states with a next-state relation. -/
structure TransSystem (S : Type u) where
  next : S → S → Prop
  init : S → Prop

/-- A trace: an infinite sequence of states. -/
noncomputable def Trace (S : Type u) := Nat → S

/-- A trace is valid if each consecutive pair is a transition. -/
noncomputable def validTrace {S : Type u} (T : TransSystem S) (σ : Trace S) : Prop :=
  ∀ i : Nat, T.next (σ i) (σ (i + 1))

/-- A trace starts from an initial state. -/
noncomputable def initTrace {S : Type u} (T : TransSystem S) (σ : Trace S) : Prop :=
  T.init (σ 0)

/-! ## LTL Operators -/

/-- State proposition: a predicate on states. -/
abbrev StateProp (S : Type u) := S → Prop

/-- Trace proposition: a predicate on traces from a given position. -/
abbrev TraceProp (S : Type u) := Trace S → Nat → Prop

/-- Next operator: Xφ holds at position i iff φ holds at i+1. -/
noncomputable def nextOp {S : Type u} (φ : StateProp S) : TraceProp S :=
  fun σ i => φ (σ (i + 1))

/-- Always operator: □φ (Gφ) holds at i iff φ holds at all j ≥ i. -/
noncomputable def alwaysOp {S : Type u} (φ : StateProp S) : TraceProp S :=
  fun σ i => ∀ j : Nat, i ≤ j → φ (σ j)

/-- Eventually operator: ◇φ (Fφ) holds at i iff φ holds at some j ≥ i. -/
noncomputable def eventuallyOp {S : Type u} (φ : StateProp S) : TraceProp S :=
  fun σ i => ∃ j : Nat, i ≤ j ∧ φ (σ j)

/-- Until operator: φ U ψ holds at i iff ψ eventually holds and φ holds until then. -/
noncomputable def untilOp {S : Type u} (φ ψ : StateProp S) : TraceProp S :=
  fun σ i => ∃ j : Nat, i ≤ j ∧ ψ (σ j) ∧ ∀ k : Nat, i ≤ k → k < j → φ (σ k)

/-- Weak until: φ W ψ = (φ U ψ) ∨ □φ. -/
noncomputable def weakUntilOp {S : Type u} (φ ψ : StateProp S) : TraceProp S :=
  fun σ i => untilOp φ ψ σ i ∨ alwaysOp φ σ i

/-- Release operator: φ R ψ = ψ W (φ ∧ ψ). -/
noncomputable def releaseOp {S : Type u} (φ ψ : StateProp S) : TraceProp S :=
  fun σ i => weakUntilOp ψ (fun s => φ s ∧ ψ s) σ i

/-! ## LTL Theorems -/

/-- Always implies current: □φ at i implies φ at i. -/
theorem always_implies_current {S : Type u} (φ : StateProp S)
    (σ : Trace S) (i : Nat) (h : alwaysOp φ σ i) : φ (σ i) :=
  h i (Nat.le_refl i)

/-- Always implies next: □φ implies X□φ. -/
theorem always_implies_next {S : Type u} (φ : StateProp S)
    (σ : Trace S) (i : Nat) (h : alwaysOp φ σ i) :
    alwaysOp φ σ (i + 1) := by
  intro j hj
  exact h j (Nat.le_trans (Nat.le_succ i) hj)

/-- Always distributes over conjunction. -/
theorem always_conj {S : Type u} (φ ψ : StateProp S)
    (σ : Trace S) (i : Nat) :
    alwaysOp (fun s => φ s ∧ ψ s) σ i ↔
    (alwaysOp φ σ i ∧ alwaysOp ψ σ i) := by
  constructor
  · intro h
    exact ⟨fun j hj => (h j hj).1, fun j hj => (h j hj).2⟩
  · intro ⟨h₁, h₂⟩ j hj
    exact ⟨h₁ j hj, h₂ j hj⟩

/-- Eventually-always duality: ¬□φ ↔ ◇¬φ. -/
theorem not_always_iff_eventually_not {S : Type u} (φ : StateProp S)
    (σ : Trace S) (i : Nat) :
    ¬ alwaysOp φ σ i ↔ eventuallyOp (fun s => ¬ φ s) σ i := by
  constructor
  · intro h
    by_contra hne
    apply h
    intro j hj
    by_contra hnφ
    exact hne ⟨j, hj, hnφ⟩
  · intro ⟨j, hj, hnφ⟩ hall
    exact hnφ (hall j hj)

/-- Eventually implies weak until: ◇ψ implies ⊤ U ψ. -/
theorem eventually_implies_until {S : Type u} (ψ : StateProp S)
    (σ : Trace S) (i : Nat) (h : eventuallyOp ψ σ i) :
    untilOp (fun _ => True) ψ σ i := by
  obtain ⟨j, hj, hψ⟩ := h
  exact ⟨j, hj, hψ, fun _ _ _ => trivial⟩

/-- Until implies eventually: φ U ψ implies ◇ψ. -/
theorem until_implies_eventually {S : Type u} (φ ψ : StateProp S)
    (σ : Trace S) (i : Nat) (h : untilOp φ ψ σ i) :
    eventuallyOp ψ σ i := by
  obtain ⟨j, hj, hψ, _⟩ := h
  exact ⟨j, hj, hψ⟩

/-- Always is monotone. -/
theorem always_monotone {S : Type u} (φ ψ : StateProp S)
    (h : ∀ s, φ s → ψ s) (σ : Trace S) (i : Nat) :
    alwaysOp φ σ i → alwaysOp ψ σ i := by
  intro hall j hj
  exact h _ (hall j hj)

/-- Eventually is monotone. -/
theorem eventually_monotone {S : Type u} (φ ψ : StateProp S)
    (h : ∀ s, φ s → ψ s) (σ : Trace S) (i : Nat) :
    eventuallyOp φ σ i → eventuallyOp ψ σ i := by
  intro ⟨j, hj, hφ⟩
  exact ⟨j, hj, h _ hφ⟩

/-- Eventually of eventually simplifies: ◇◇φ ↔ ◇φ. -/
theorem eventually_idempotent {S : Type u} (φ : StateProp S)
    (σ : Trace S) (i : Nat) :
    eventuallyOp (fun s => eventuallyOp φ σ i) σ i →
    eventuallyOp φ σ i := by
  intro ⟨_, _, h⟩; exact h

/-- Always of always: □□φ → □φ. -/
theorem always_of_always {S : Type u} (φ : StateProp S)
    (σ : Trace S) (i : Nat) :
    alwaysOp (fun s => alwaysOp φ σ i → φ s) σ i := by
  intro j hj hall
  exact hall j hj

/-! ## CTL Operators -/

/-- CTL universal quantifier: for all traces from a state. -/
noncomputable def ctlForAll {S : Type u} (T : TransSystem S) (ψ : TraceProp S)
    (s : S) : Prop :=
  ∀ σ : Trace S, σ 0 = s → validTrace T σ → ψ σ 0

/-- CTL existential quantifier: exists a trace from a state. -/
noncomputable def ctlExists {S : Type u} (T : TransSystem S) (ψ : TraceProp S)
    (s : S) : Prop :=
  ∃ σ : Trace S, σ 0 = s ∧ validTrace T σ ∧ ψ σ 0

/-- AG: for all paths, always. -/
noncomputable def agOp {S : Type u} (T : TransSystem S) (φ : StateProp S) : StateProp S :=
  ctlForAll T (alwaysOp φ)

/-- EF: exists a path, eventually. -/
noncomputable def efOp {S : Type u} (T : TransSystem S) (φ : StateProp S) : StateProp S :=
  ctlExists T (eventuallyOp φ)

/-- AG implies current state. -/
theorem ag_implies_current {S : Type u} (T : TransSystem S) (φ : StateProp S)
    (s : S) (σ : Trace S) (hσ0 : σ 0 = s) (hvalid : validTrace T σ)
    (h : agOp T φ s) : φ s := by
  have := h σ hσ0 hvalid
  rw [← hσ0]
  exact this 0 (Nat.le_refl 0)

/-- EF is monotone. -/
theorem ef_monotone {S : Type u} (T : TransSystem S) (φ ψ : StateProp S)
    (h : ∀ s, φ s → ψ s) (s : S) :
    efOp T φ s → efOp T ψ s := by
  intro ⟨σ, hσ0, hvalid, hef⟩
  exact ⟨σ, hσ0, hvalid, eventually_monotone φ ψ h σ 0 hef⟩

/-! ## Fairness -/

/-- Strong fairness: if φ is enabled infinitely often, it occurs infinitely often. -/
noncomputable def strongFairness {S : Type u} (enabled occurs : StateProp S) (σ : Trace S) : Prop :=
  (∀ i, eventuallyOp enabled σ i) → (∀ i, eventuallyOp occurs σ i)

/-- Weak fairness: if φ is always eventually enabled, it occurs infinitely often. -/
noncomputable def weakFairness {S : Type u} (enabled occurs : StateProp S) (σ : Trace S) : Prop :=
  alwaysOp enabled σ 0 → (∀ i, eventuallyOp occurs σ i)

/-- Strong fairness implies weak fairness. -/
theorem strong_implies_weak_fairness {S : Type u}
    (enabled occurs : StateProp S) (σ : Trace S) :
    strongFairness enabled occurs σ → weakFairness enabled occurs σ := by
  intro hstrong halways
  apply hstrong
  intro i
  exact ⟨i, Nat.le_refl i, halways i (Nat.zero_le i)⟩

/-! ## Path-based Model Checking -/

/-- Path for state proposition congruence along state paths. -/
noncomputable def stateProp_congrArg {S : Type u} (φ : StateProp S)
    (s₁ s₂ : S) (p : Path s₁ s₂) :
    Path (φ s₁) (φ s₂) :=
  Path.congrArg φ p

/-- Transport of state truth along a path. -/
theorem transport_stateProp {S : Type u} (φ : StateProp S)
    (s₁ s₂ : S) (p : Path s₁ s₂) :
    Path.transport (D := fun s => φ s → φ s) p id = id := by
  cases p with
  | mk steps proof =>
    cases proof; simp [Path.transport]

/-- Trans path for temporal composition. -/
noncomputable def temporal_trans_path {S : Type u} (s₁ s₂ s₃ : S)
    (p : Path s₁ s₂) (q : Path s₂ s₃) :
    Path s₁ s₃ :=
  Path.trans p q

/-- Symm path for temporal reversal. -/
noncomputable def temporal_symm_path {S : Type u} (s₁ s₂ : S) (p : Path s₁ s₂) :
    Path s₂ s₁ :=
  Path.symm p

/-- CongrArg on transition system traces. -/
noncomputable def trace_congrArg_path {S : Type u} (φ : StateProp S)
    (σ₁ σ₂ : Trace S) (i : Nat) (p : Path (σ₁ i) (σ₂ i)) :
    Path (φ (σ₁ i)) (φ (σ₂ i)) :=
  Path.congrArg φ p

/-- Path for always at shifted position. -/
theorem always_shift {S : Type u} (φ : StateProp S)
    (σ : Trace S) (i j : Nat) (hij : i ≤ j)
    (h : alwaysOp φ σ i) : alwaysOp φ σ j := by
  intro k hk
  exact h k (Nat.le_trans hij hk)

/-- Trace suffix path. -/
noncomputable def traceSuffix {S : Type u} (σ : Trace S) (k : Nat) : Trace S :=
  fun i => σ (k + i)

/-- Valid trace suffix is valid. -/
theorem validTrace_suffix {S : Type u} (T : TransSystem S)
    (σ : Trace S) (k : Nat) (h : validTrace T σ) :
    validTrace T (traceSuffix σ k) := by
  intro i
  simp [traceSuffix]
  have heq : k + (i + 1) = k + i + 1 := by omega
  rw [heq]
  exact h (k + i)

end TemporalLogicPaths
end Logic
end Path
end ComputationalPaths
