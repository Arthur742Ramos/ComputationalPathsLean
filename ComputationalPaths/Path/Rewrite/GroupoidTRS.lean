/-
# Termination of the core groupoid rewrite system (LND_EQ-TRS)

This module proves that the core groupoid fragment of the computational
paths rewrite system terminates. The TRS operates on expressions built
from `atom`, `refl`, `symm`, `trans`, closed under congruence.

## Termination measure

Lexicographic pair `(weight, leftWeight)`:

* `weight`: polynomial interpretation with `w(symm e) = 2·w(e) + 1` and
  `w(trans e₁ e₂) = w(e₁) + w(e₂) + 2`. Rules 1–7 strictly decrease it.

* `leftWeight`: `lw(trans e₁ e₂) = lw(e₁) + lw(e₂) + size(e₁)`.
  Rule 8 (trans_assoc) preserves weight but strictly decreases leftWeight.

Key lemma: `step_weight_eq_imp_size_eq` — if a step preserves weight, it
also preserves size, ensuring leftWeight decreases through congruences.
-/

namespace ComputationalPaths.Path.Rewrite.GroupoidTRS

inductive Expr where
  | atom (n : Nat) : Expr
  | refl : Expr
  | symm (e : Expr) : Expr
  | trans (e₁ e₂ : Expr) : Expr
  deriving DecidableEq, Repr

namespace Expr

/-! ## Measures -/

@[simp] noncomputable def size : Expr → Nat
  | atom _ => 1
  | refl => 1
  | symm e => e.size + 1
  | trans e₁ e₂ => e₁.size + e₂.size + 1

theorem size_pos (e : Expr) : 0 < e.size := by cases e <;> simp <;> omega

@[simp] noncomputable def weight : Expr → Nat
  | atom _ => 4
  | refl => 4
  | symm e => 2 * e.weight + 1
  | trans e₁ e₂ => e₁.weight + e₂.weight + 2

theorem weight_ge_four (e : Expr) : 4 ≤ e.weight := by
  induction e <;> simp_all <;> omega

@[simp] noncomputable def leftWeight : Expr → Nat
  | atom _ => 0
  | refl => 0
  | symm e => e.leftWeight
  | trans e₁ e₂ => e₁.leftWeight + e₂.leftWeight + e₁.size

/-! ## Rewrite relation -/

inductive Step : Expr → Expr → Prop where
  | symm_refl : Step (.symm .refl) .refl
  | symm_symm (p) : Step (.symm (.symm p)) p
  | trans_refl_left (p) : Step (.trans .refl p) p
  | trans_refl_right (p) : Step (.trans p .refl) p
  | trans_symm (p) : Step (.trans p (.symm p)) .refl
  | symm_trans (p) : Step (.trans (.symm p) p) .refl
  | symm_trans_congr (p q) : Step (.symm (.trans p q)) (.trans (.symm q) (.symm p))
  | trans_assoc (p q r) : Step (.trans (.trans p q) r) (.trans p (.trans q r))
  | symm_congr {p q} : Step p q → Step (.symm p) (.symm q)
  | trans_congr_left {p q} (r) : Step p q → Step (.trans p r) (.trans q r)
  | trans_congr_right (p) {q r} : Step q r → Step (.trans p q) (.trans p r)

/-! ## Weight-preservation implies size-preservation -/

theorem step_weight_eq_imp_size_eq {p q : Expr} (h : Step p q)
    (hw : q.weight = p.weight) : q.size = p.size := by
  induction h with
  | symm_refl => simp at hw
  | symm_symm p => simp at hw; have := weight_ge_four p; omega
  | trans_refl_left _ => simp at hw; omega
  | trans_refl_right _ => simp at hw; omega
  | trans_symm p => simp at hw; have := weight_ge_four p; omega
  | symm_trans p => simp at hw; have := weight_ge_four p; omega
  | symm_trans_congr _ _ => simp at hw; omega
  | trans_assoc _ _ _ => simp; omega
  | symm_congr _ ih =>
    simp at hw ⊢; exact ih (by omega)
  | trans_congr_left _ _ ih =>
    simp at hw ⊢; exact ih (by omega)
  | trans_congr_right _ _ ih =>
    simp at hw ⊢; exact ih (by omega)

/-! ## Main lemma: lexicographic decrease -/

theorem step_lex_decrease {p q : Expr} (h : Step p q) :
    q.weight < p.weight ∨ (q.weight = p.weight ∧ q.leftWeight < p.leftWeight) := by
  induction h with
  | symm_refl => left; simp
  | symm_symm p => left; simp; have := weight_ge_four p; omega
  | trans_refl_left _ => left; simp; omega
  | trans_refl_right _ => left; simp; omega
  | trans_symm p => left; simp; have := weight_ge_four p; omega
  | symm_trans p => left; simp; have := weight_ge_four p; omega
  | symm_trans_congr _ _ => left; simp; omega
  | trans_assoc p _ _ =>
    right; constructor
    · simp; omega
    · simp; have := size_pos p; omega
  | symm_congr _ ih =>
    rcases ih with hw | ⟨hw, hl⟩
    · left; simp; omega
    · right; exact ⟨by simp; omega, by simp; omega⟩
  | trans_congr_left r h ih =>
    rcases ih with hw | ⟨hw, hl⟩
    · left; simp; omega
    · right
      have hsz := step_weight_eq_imp_size_eq h hw
      exact ⟨by simp; omega, by simp; omega⟩
  | trans_congr_right p h ih =>
    rcases ih with hw | ⟨hw, hl⟩
    · left; simp; omega
    · right; exact ⟨by simp; omega, by simp; omega⟩

/-! ## Well-foundedness machinery -/

private noncomputable def NatLex : Nat × Nat → Nat × Nat → Prop :=
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
      · cases heq; exact ihl l' hl

private theorem natLex_wf : WellFounded NatLex :=
  ⟨fun ⟨w, l⟩ => natLex_acc w l⟩

noncomputable def termMeasure (e : Expr) : Nat × Nat := (e.weight, e.leftWeight)

theorem step_measure_lt {p q : Expr} (h : Step p q) :
    NatLex (termMeasure q) (termMeasure p) :=
  step_lex_decrease h

/-! ## Main Theorem -/

/-- **The core groupoid TRS is terminating.**

The step relation is well-founded, proved via the lexicographic measure
`(weight, leftWeight)`. Every step strictly decreases this measure.

This replaces the `Terminating := True` axiom in `ConfluenceProof.lean`
with genuine mathematical content. -/
theorem termination : WellFounded (fun q p : Expr => Step p q) :=
  Subrelation.wf (fun h => step_measure_lt h) (InvImage.wf termMeasure natLex_wf)

theorem acc_step (e : Expr) : Acc (fun q p => Step p q) e :=
  termination.apply e

/-- **No bidirectional steps**: For any expressions p and q, we cannot have
    both `Step p q` and `Step q p`.

    This follows directly from termination: every step strictly decreases
    the lexicographic measure `(weight, leftWeight)`. Having both directions
    would require the measure to both decrease and increase, which is impossible.

    This theorem is crucial for proving that "mixed polarity" cases in
    derivation normal forms are unreachable. -/
theorem no_bidirectional_step {p q : Expr} :
    ¬(Step p q ∧ Step q p) := by
  intro ⟨s₁, s₂⟩
  have h₁ := step_lex_decrease s₁
  have h₂ := step_lex_decrease s₂
  -- h₁ : q.weight < p.weight ∨ (q.weight = p.weight ∧ q.leftWeight < p.leftWeight)
  -- h₂ : p.weight < q.weight ∨ (p.weight = q.weight ∧ p.leftWeight < q.leftWeight)
  -- These form a lexicographic contradiction
  rcases h₁ with hlt₁ | ⟨heq₁, hlt₁'⟩
  · rcases h₂ with hlt₂ | ⟨heq₂, hlt₂'⟩
    · exact Nat.lt_asymm hlt₁ hlt₂
    · exact Nat.ne_of_lt hlt₁ heq₂.symm
  · rcases h₂ with hlt₂ | ⟨heq₂, hlt₂'⟩
    · exact Nat.ne_of_lt hlt₂ heq₁.symm
    · exact Nat.lt_asymm hlt₁' hlt₂'

end Expr
end ComputationalPaths.Path.Rewrite.GroupoidTRS
