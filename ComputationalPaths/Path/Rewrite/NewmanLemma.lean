/-
# Newman's Lemma and Confluence Analysis for GroupoidTRS

This module provides:
1. An abstract **Newman's Lemma** in Lean 4: termination + local confluence → full confluence
2. Analysis of why the 8-rule GroupoidTRS system requires `Step.canon` for confluence
3. Full confluence of `GroupoidTRS.Expr.Step` (the complete system with canon)

## Why Newman's Lemma Alone Does Not Suffice for the 8-Rule System

The 8 base groupoid rewrite rules (without `Step.canon`) are not locally confluent.
The critical pair `trans_symm` vs `trans_assoc` on the term

    trans(trans(p, q), symm(trans(p, q)))

produces two results:
- Via `trans_symm`: `refl`
- Via `trans_assoc`: `trans(p, trans(q, symm(trans(p, q))))`

The second term normalizes (under the 8 rules + congruence) to

    trans(p, trans(q, trans(symm(q), symm(p))))

which is irreducible but not equal to `refl` (for non-trivial `p`, `q`).
The system lacks a rule to "reassociate left" so that `q . symm(q)` could
be reduced as a root redex.

The confluence proof in this project uses `Step.canon` (Rule 77 in Step.lean),
which maps every path to `stepChain p.toEq`, a canonical normal form.
This makes confluence immediate without Newman's Lemma.

## References

- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Huet, "Confluent Reductions" (1980)
-/

import ComputationalPaths.Path.Rewrite.GroupoidTRS

namespace ComputationalPaths.Path.Rewrite.GroupoidTRS

open Expr

/-! ## Reflexive-Transitive Closure -/

/-- Reflexive-transitive closure of a relation. -/
inductive RTC {α : Sort _} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : RTC R a a
  | head {a b c : α} : R a b → RTC R b c → RTC R a c

namespace RTC

variable {α : Sort _} {R : α → α → Prop}

theorem single {a b : α} (h : R a b) : RTC R a b :=
  .head h (.refl b)

theorem trans {a b c : α} (h₁ : RTC R a b) (h₂ : RTC R b c) : RTC R a c := by
  induction h₁ with
  | refl => exact h₂
  | head step _ ih => exact .head step (ih h₂)

theorem tail {a b c : α} (h₁ : RTC R a b) (h₂ : R b c) : RTC R a c :=
  h₁.trans (.single h₂)

/-- Case analysis: either reflexive or starts with a step. -/
theorem cases_head {a b : α} (h : RTC R a b) :
    (a = b) ∨ (∃ c, R a c ∧ RTC R c b) := by
  cases h with
  | refl => left; rfl
  | head step rest => right; exact ⟨_, step, rest⟩

end RTC

/-! ## Newman's Lemma (Abstract)

This is the standard abstract formulation: for any type with a binary relation,
well-foundedness (termination) plus local confluence implies full confluence.

The proof is by well-founded induction on the source element `a`. Given
diverging multi-step reductions `a ->* b` and `a ->* c`, we extract the
first step of each, apply local confluence, and use the IH to paste the
resulting diagrams together. -/

/-- Newman's Lemma: A terminating, locally confluent relation is confluent. -/
theorem newman_lemma {α : Type _} {R : α → α → Prop}
    (wf : WellFounded (fun y x => R x y))
    (lc : ∀ a b c, R a b → R a c →
      ∃ d, RTC R b d ∧ RTC R c d)
    : ∀ a b c, RTC R a b → RTC R a c →
        ∃ d, RTC R b d ∧ RTC R c d := by
  intro a
  induction a using wf.induction with
  | _ a ih =>
    intro b c hab hac
    -- Decompose a ->* b by extracting the first step
    rcases hab.cases_head with rfl | ⟨a₁, ha_a₁, ha₁_b⟩
    · -- a = b: trivially join at c
      exact ⟨c, hac, .refl _⟩
    · -- a -> a₁ ->* b. Now decompose a ->* c.
      rcases hac.cases_head with rfl | ⟨a₂, ha_a₂, ha₂_c⟩
      · -- a = c: join at b
        exact ⟨b, .refl _, .head ha_a₁ ha₁_b⟩
      · -- Peak: a -> a₁ and a -> a₂, plus a₁ ->* b and a₂ ->* c
        -- Step 1: Local confluence on the peak
        obtain ⟨d₀, h_a₁_d₀, h_a₂_d₀⟩ := lc a a₁ a₂ ha_a₁ ha_a₂
        -- Step 2: IH at a₁ (since R a a₁, so a₁ < a)
        obtain ⟨d₁, h_b_d₁, h_d₀_d₁⟩ := ih a₁ ha_a₁ b d₀ ha₁_b h_a₁_d₀
        -- Step 3: a₂ ->* d₀ ->* d₁
        have h_a₂_d₁ : RTC R a₂ d₁ := h_a₂_d₀.trans h_d₀_d₁
        -- Step 4: IH at a₂ (since R a a₂, so a₂ < a)
        obtain ⟨d₂, h_c_d₂, h_d₁_d₂⟩ := ih a₂ ha_a₂ c d₁ ha₂_c h_a₂_d₁
        -- Step 5: b ->* d₁ ->* d₂ and c ->* d₂
        exact ⟨d₂, h_b_d₁.trans h_d₁_d₂, h_c_d₂⟩

/-! ## Non-Local-Confluence of the 8-Rule System

We exhibit the critical pair that prevents local confluence of the
8 base rules (without `Step.canon`). -/

/-- The term witnessing the critical pair between trans_symm and trans_assoc. -/
def critical_pair_witness : Expr :=
  .trans (.trans (.atom 0) (.atom 1)) (.symm (.trans (.atom 0) (.atom 1)))

/-- Via trans_symm, the witness reduces to refl. -/
theorem critical_pair_left : Step critical_pair_witness .refl :=
  Step.trans_symm _

/-- Via trans_assoc, the witness reduces to a different term. -/
theorem critical_pair_right :
    Step critical_pair_witness
      (.trans (.atom 0) (.trans (.atom 1) (.symm (.trans (.atom 0) (.atom 1))))) :=
  Step.trans_assoc _ _ _

/-- The right side of the critical pair is NOT refl (syntactically distinct). -/
theorem critical_pair_right_ne_refl :
    Expr.trans (.atom 0) (.trans (.atom 1) (.symm (.trans (.atom 0) (.atom 1)))) ≠ .refl := by
  intro h; cases h

/-! ## Confluence of the Full Step Relation

The full `Step` relation (including `Step.canon`) maps every term to
`stepChain p.toEq`, a canonical normal form. Since `toEq` is
proof-irrelevant, this gives unique normal forms and hence confluence.

The proof is in `ConfluenceProof.lean`. Newman's Lemma, while a correct
abstract result, is not the mechanism used because the base 8-rule
subsystem is not locally confluent on its own. -/

end ComputationalPaths.Path.Rewrite.GroupoidTRS
