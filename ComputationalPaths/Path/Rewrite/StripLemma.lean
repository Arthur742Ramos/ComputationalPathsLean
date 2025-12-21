/-
# Strip Lemma for Computational Paths TRS

This module provides an alternative proof approach for the strip lemma.

## The Strip Lemma

Given:
- `Step p q` (single-step reduction)
- `Rw p r` (multi-step reduction)

We want to show there exists `s` such that:
- `Rw q s`
- `Rw r s`

## Analysis

The standard proof uses Newman's lemma which requires:
1. Local confluence (assumed via `ConfluenceProof.HasLocalConfluence`)
2. Termination (we have this via RPO in Termination.lean)

The challenge in formalizing is that `Rw` is Prop-valued, so we cannot
directly extract derivation lengths for well-founded recursion.

The `step_strip_prop` assumption (typeclass) in ConfluenceProof.lean is justified by
the metatheoretic argument that:
- All critical pairs join (established by explicit proofs)
- The TRS terminates (established by RPO)
- Therefore by Newman's lemma, confluence holds

This module explores what can be proven constructively.
-/

import ComputationalPaths.Path.Rewrite.ConfluenceProof

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace StripLemma

open ConfluenceProof Confluence

universe u

variable {A : Type u} {a b : A}

/-! ## Constructive Partial Results

We can prove some special cases of the strip lemma without the full axiom.
-/

/-- Strip lemma for the base case: Step joins with Rw.refl. -/
theorem step_strip_refl {p q : Path a b}
    (hstep : Step p q) :
    ∃ s : Path a b, Rw q s ∧ Rw p s :=
  ⟨q, Rw.refl q, rw_of_step hstep⟩

/-- Strip lemma when multi-step has length 1: diamond property. -/
theorem step_strip_single [HasLocalConfluence.{u}] {p q r : Path a b}
    (hstep_pq : Step p q) (hstep_pr : Step p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s := by
  let j := local_confluence hstep_pq hstep_pr
  exact ⟨j.meet, j.left, j.right⟩

/-- Strip lemma when multi-step has length 2. -/
theorem step_strip_two [HasLocalConfluence.{u}] [HasStepStrip.{u}] {p q r' r : Path a b}
    (hstep : Step p q) (h1 : Step p r') (h2 : Step r' r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s := by
  -- First join hstep with h1
  let j1 := local_confluence hstep h1
  -- j1.meet joins q and r', j1.left : Rw q j1.meet, j1.right : Rw r' j1.meet
  -- Now join h2 : Step r' r with j1.right : Rw r' j1.meet
  -- step_strip_prop h2 j1.right gives ∃ s, Rw r s ∧ Rw j1.meet s
  have ⟨s, hrs, hms⟩ := step_strip_prop h2 j1.right
  exact ⟨s, rw_trans j1.left hms, hrs⟩

/-! ## Sized Rewrite Relation

To prove the strip lemma constructively, we define a sized version of Rw
that carries the derivation length. This allows well-founded induction.
-/

/-- Sized multi-step rewrite relation. RwN p q n means p rewrites to q in exactly n steps. -/
inductive RwN {A : Type u} {a b : A} : Path a b → Path a b → Nat → Prop
  | refl (p : Path a b) : RwN p p 0
  | tail {p q r : Path a b} {n : Nat} : RwN p q n → Step q r → RwN p r (n + 1)

namespace RwN

variable {A : Type u} {a b : A}

/-- RwN implies Rw. -/
theorem toRw {p q : Path a b} {n : Nat} (h : RwN p q n) : Rw p q := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih step

/-- Rw can be represented as RwN for some length. -/
theorem ofRw {p q : Path a b} (h : Rw p q) : ∃ n, RwN p q n := by
  induction h with
  | refl => exact ⟨0, RwN.refl _⟩
  | tail _ step ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, RwN.tail hn step⟩

/-- RwN is transitive (with length addition). -/
theorem trans {p q r : Path a b} {m n : Nat}
    (h1 : RwN p q m) (h2 : RwN q r n) : RwN p r (m + n) := by
  induction h2 with
  | refl => rw [Nat.add_zero]; exact h1
  | tail h2' step ih =>
    rw [Nat.add_succ]
    exact RwN.tail ih step

/-- Single step as RwN. -/
theorem ofStep {p q : Path a b} (h : Step p q) : RwN p q 1 :=
  RwN.tail (RwN.refl p) h

end RwN

/-! ## Constructive Strip Lemma via Sized Induction -/

/-- Join data for sized rewrites. -/
structure JoinN {A : Type u} {a b : A} (p q : Path a b) where
  meet : Path a b
  leftLen : Nat
  rightLen : Nat
  left : RwN p meet leftLen
  right : RwN q meet rightLen

/-! ## Well-Founded Approach

To prove step_strip_prop from local_confluence, we need well-founded recursion
on the sum of derivation lengths. The key insight from Newman's lemma is that
when we apply local_confluence to join two steps, the resulting derivations
have total length strictly less than the original.

For a single step vs n-step derivation:
- Base case (n=0): trivial, the step itself is the witness
- Inductive case: Apply local_confluence to the first step of the multi-step
  derivation, then recursively join the remaining steps.

The measure decreases because:
- We reduce the multi-step derivation by 1 (n → n-1)
- Local confluence produces derivations whose sum is bounded
-/

section

variable [HasStepStrip.{u}]

/-- Helper: join a single step with RwN using well-founded recursion.

This is the core of Newman's strip lemma. Given:
- `Step r' r` (single step)
- `RwN r' s' n` (n-step derivation)

We produce a common descendant with derivations from both r and s'.

The proof uses strong induction on n. -/
theorem join_step_rwN {r' r s' : Path a b} {n : Nat}
    (hstep : Step r' r) (hrw : RwN r' s' n) :
    ∃ s m₁ m₂, RwN r s m₁ ∧ RwN s' s m₂ := by
  induction n using Nat.strongRecOn generalizing r' r s' with
  | ind n ih =>
    match n, hrw with
    | 0, RwN.refl _ =>
      -- RwN with 0 steps means s' = r'
      exact ⟨r, 0, 1, RwN.refl r, RwN.ofStep hstep⟩
    | n' + 1, RwN.tail h_r's'' step_s''s' =>
      -- h_r's'' : RwN r' s'' n', step_s''s' : Step s'' s'
      -- By IH on n': join Step r' r with RwN r' s'' n'
      have h_lt : n' < n' + 1 := Nat.lt_succ_self n'
      obtain ⟨s''', m₁, m₂, h_r_s''', h_s''_s'''⟩ := ih n' h_lt hstep h_r's''
      -- h_r_s''' : RwN r s''' m₁
      -- h_s''_s''' : RwN s'' s''' m₂
      -- Now we need to join Step s'' s' with RwN s'' s''' m₂
      --
      -- This is where Newman's lemma requires the nested strip argument.
      -- We need to join step_s''s' with h_s''_s''' (a multi-step derivation).
      --
      -- The fully constructive proof would use:
      -- 1. If m₂ = 0: trivially extend by step_s''s'
      -- 2. If m₂ = 1: use local_confluence (diamond property)
      -- 3. If m₂ > 1: recursively join, using the termination argument that
      --    the sum of derivation lengths decreases.
      --
      -- For now, use the step_strip_prop axiom which is justified by Newman's lemma.
      have ⟨final, h_l, h_r⟩ := step_strip_prop step_s''s' (RwN.toRw h_s''_s''')
      obtain ⟨k₁, hk₁⟩ := RwN.ofRw h_l
      obtain ⟨k₂, hk₂⟩ := RwN.ofRw h_r
      exact ⟨final, m₁ + k₂, k₁, RwN.trans h_r_s''' hk₂, hk₁⟩

/-- The key lemma: join Step with RwN by induction on the length.

This is the constructive version of step_strip_prop.
Note: The current proof uses step_strip_prop in a nested case; a fully
constructive proof would require more sophisticated termination argument. -/
theorem step_strip_sized {p q r : Path a b} {n : Nat}
    (hstep : Step p q) (hmulti : RwN p r n) :
    ∃ s m₁ m₂, RwN q s m₁ ∧ RwN r s m₂ := by
  induction n generalizing p q r with
  | zero =>
    cases hmulti with
    | refl =>
      exact ⟨q, 0, 1, RwN.refl q, RwN.ofStep hstep⟩
  | succ n ih =>
    cases hmulti with
    | tail h step_r'r =>
      -- h : RwN p r' n, step_r'r : Step r' r
      obtain ⟨s', m₁', m₂', hqs', hr's'⟩ := ih hstep h
      -- Join Step r' r with RwN r' s'
      obtain ⟨s, m₁'', m₂'', hrs, hs's⟩ := join_step_rwN step_r'r hr's'
      -- Chain: RwN q s' and RwN s' s gives RwN q s
      exact ⟨s, m₁' + m₂'', m₁'', RwN.trans hqs' hs's, hrs⟩

/-- Verify the existing axiom still works. -/
theorem strip_lemma_via_axiom {p q r : Path a b}
    (hstep : Step p q) (hmulti : Rw p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  step_strip_prop hstep hmulti

end

/-! ## Summary: Axiom Justification Analysis

### Current Axiom Status

The confluence proof uses two axioms:

1. **`local_confluence`**: For `Step p q` and `Step p r`, produces `Join q r`.
   - **Why needed**: `Step` is Prop-valued, so `Step.casesOn` only eliminates into `Prop`.
     We need to produce a `Type`-valued `Join`, which requires a Type-level eliminator.
   - **Justification**: All critical pairs have explicit join proofs in `ConfluenceProof.lean`.

2. **`step_strip_prop`**: For `Step p q` and `Rw p r`, produces `∃ s, Rw q s ∧ Rw r s`.
   - **Why needed**: The nested recursion in `join_step_rwN` produces derivations whose
     lengths may increase, preventing simple structural induction.
   - **Justification**: Follows from `local_confluence` + termination by Newman's lemma.

### Theoretical Path to Fully Constructive Proof

To eliminate `step_strip_prop` axiom, the proof would need:

1. **Define a well-founded measure**: The sum of reduction lengths from source to
   current positions, bounded by the termination argument.

2. **Show local_confluence decreases measure**: When joining two steps, the new
   derivations have smaller total "reduction potential" than the original.

3. **Use `WellFounded.fix`**: Define `step_strip_prop` as a recursive function that
   terminates by the well-founded measure.

This is theoretically sound but technically complex in Lean 4 because:
- We'd need to connect `Termination.lean`'s RPO ordering to derivation lengths
- The measure must be constructively computable, not just existential
- Dependent type issues arise when tracking intermediate paths

### Alternative: Make Step Type-Valued

If `Step` were defined as `→ Type` instead of `→ Prop`, then:
- We could case-split on Step proofs to produce Type-valued results
- `local_confluence` could become a theorem via exhaustive case analysis
- But this would require 76² = 5776 cases and change the proof irrelevance properties

### Conclusion

The current axiom-based approach is:
- **Sound**: Justified by explicit critical pair proofs and termination
- **Practical**: Avoids massive case analysis or complex well-founded recursion
- **Transparent**: The axioms are clearly documented with their justifications

The axioms represent "computed" results that are metatheoretically valid but expensive
to fully formalize in Lean's type theory.

### Note on Other Axioms (Wedge SVK, Circle encode-decode)

Similar analysis applies to encode-decode axioms for HITs like Circle, Wedge, etc.:

1. **Circle encode axioms** (`HasCircleLoopDecode`): Define the winding number function.
   - Needed because we must analyze loop structure to extract integer windings.
   - Justified by the standard encode-decode argument for S¹.

2. **Wedge SVK encode/decode data** (`WedgeSVKInstances.HasWedgeSVKEncodeData`):
   - Needed because we must decompose wedge loops into left/right pieces.
   - Justified by the Seifert-Van Kampen theorem (wedge case).
   - Kept as an explicit typeclass assumption; an opt-in kernel-axiom instance is
     provided by `ComputationalPaths.Path.HIT.WedgeSVKAxiom`.

To prove these constructively would require:
- A "flattening lemma" relating Ω(Pushout) to Pushout(Ω(...))
- Or detailed structural analysis of path spaces in HITs
- Both are complex and beyond typical HIT axiomatizations

The current approach of using well-justified axioms is standard practice for
formalizing HoTT-style results in proof assistants.
-/

end StripLemma
end Rewrite
end Path
end ComputationalPaths
