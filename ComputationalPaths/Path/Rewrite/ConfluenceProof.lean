/-
# Confluence Proof for Computational Paths TRS

This module proves `HasJoinOfRw` from Prop-level local confluence. We assume
`HasLocalConfluenceProp` (single-step peaks can be closed by multi-step
rewrites), derive the strip lemma and confluence for `Rw`, and extract
Type-valued join witnesses with `Classical.choose`.

## Status: COMPLETE (with Prop-level local confluence + termination assumptions)

The assumptions are:

1. **`local_confluence_prop`**: For any `Step p q` and `Step p r`, there exists
   `s` with `Rw q s` and `Rw r s`.
2. **`termination_prop`**: The one-step rewrite relation is terminating
   (well-founded on the non-empty transitive closure).

This stays Prop-level because `Step` is Prop-valued and exhaustive case analysis
into `Type` would require a large explicit enumeration of rule pairs.

## Key Achievements

1. **Critical pair infrastructure**: Explicit join witnesses for key path algebra
   overlaps, including inverse-related ones.

2. **Commutation lemmas**: Steps at disjoint positions commute
   (`commute_trans_left_right`, `join_lift_trans_left/right`, `join_lift_symm`).

3. **Identity context technique**: Inverse critical pairs close using
   `context_tt_cancel_left` specialized to the identity context via `congrArg_id`.

4. **Confluence proof**: `confluence_prop` proves confluence in `Prop` and
   `confluence_of_local` extracts `Join` witnesses via `Classical.choose`.

## Main Results

- `confluence_prop`: Prop-level confluence (induction using the strip lemma)
- `confluence_of_local`: Type-level Join construction
- `instHasJoinOfRw`: Instance of `HasJoinOfRw` for downstream use
-/

import ComputationalPaths.Path.Rewrite.Confluence
import ComputationalPaths.Path.Rewrite.ConfluenceConstructive

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceProof

open LNDEQ ConfluenceConstructive

universe u

variable {A : Type u}

/-! ## Helper Lemmas -/

/-- Identity context for use with context-based rules. -/
@[simp] def idContext (A : Type u) : Context A A := ⟨id⟩

/-- `Context.map idContext p = p` (specialization of congrArg_id). -/
@[simp] theorem map_idContext {a b : A} (p : Path a b) :
    Context.map (idContext A) p = p :=
  congrArg_id p

/-- `congrArg id p = p` for any path. -/
@[simp] theorem congrArg_id' {a b : A} (p : Path a b) :
    congrArg id p = p :=
  congrArg_id p

/-- Step that re-associates a cancellation pattern.
    `p · (symm(p) · q) → (p · symm(p)) · q`
    This is `context_tt_cancel_left` specialized to the identity context. -/
def step_cancel_left_reassoc {a b c : A} (p : Path a b) (q : Path a c) :
    Step (Path.trans p (Path.trans (Path.symm p) q))
         (Path.trans (Path.trans p (Path.symm p)) q) := by
  have ctx_step := Step.context_tt_cancel_left (idContext A) p q
  simp only [idContext, Context.map] at ctx_step
  -- congrArg id p = p
  rw [congrArg_id', congrArg_id', congrArg_id'] at ctx_step
  exact ctx_step

/-- Step that re-associates a symmetric cancellation pattern.
    `symm(p) · (p · q) → (symm(p) · p) · q`  -/
def step_cancel_right_reassoc {a b c : A} (p : Path a b) (q : Path b c) :
    Step (Path.trans (Path.symm p) (Path.trans p q))
         (Path.trans (Path.trans (Path.symm p) p) q) := by
  -- Use context_tt_cancel_left with symm(p) in place of p
  have ctx_step := Step.context_tt_cancel_left (idContext A) (Path.symm p) q
  simp only [idContext, Context.map] at ctx_step
  rw [congrArg_id', congrArg_id', congrArg_id', Path.symm_symm] at ctx_step
  exact ctx_step

/-! ## Commutation Lemmas for Non-overlapping Steps

When two steps apply to disjoint subterms, they commute. We capture this via
specific commutation lemmas for congruence rules. -/

/-! ### Rw congruence helpers

We reuse the standard congruence lemmas from `Rw.lean`, except for the
symmetry congruence which we define there as `rw_symm_congr`. -/

/-- Steps at left and right positions of a trans commute. -/
def commute_trans_left_right {a b c : A} {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : Step p₁ p₂) (hq : Step q₁ q₂) :
    Confluence.Join
      (Path.trans p₂ q₁)  -- applied left step
      (Path.trans p₁ q₂)  -- applied right step
  :=
  { meet := Path.trans p₂ q₂
  , left := Rw.tail (Rw.refl _) (Step.trans_congr_right p₂ hq)
  , right := Rw.tail (Rw.refl _) (Step.trans_congr_left q₂ hp) }

/-- Two steps on the left component of trans: lift the join. -/
def join_lift_trans_left {a b c : A} {p₁ p₂ : Path a b} (r : Path b c)
    (hj : Confluence.Join p₁ p₂) :
    Confluence.Join (Path.trans p₁ r) (Path.trans p₂ r) :=
  { meet := Path.trans hj.meet r
  , left := rw_trans_congr_left r hj.left
  , right := rw_trans_congr_left r hj.right }

/-- Two steps on the right component of trans: lift the join. -/
def join_lift_trans_right {a b c : A} (p : Path a b) {q₁ q₂ : Path b c}
    (hj : Confluence.Join q₁ q₂) :
    Confluence.Join (Path.trans p q₁) (Path.trans p q₂) :=
  { meet := Path.trans p hj.meet
  , left := rw_trans_congr_right p hj.left
  , right := rw_trans_congr_right p hj.right }

/-- Lift a join through symm_congr. -/
def join_lift_symm {a b : A} {p q : Path a b} (hj : Confluence.Join p q) :
    Confluence.Join (Path.symm p) (Path.symm q) :=
  { meet := Path.symm hj.meet
  , left := rw_symm_congr hj.left
  , right := rw_symm_congr hj.right }

/-- Direct join construction when both steps result in the same path. -/
@[simp] def join_eq {a b : A} {p q : Path a b} (h : Path p q) :
    Confluence.Join p q :=
  { meet := p
  , left := Rw.refl p
  , right := rw_of_eq h.toEq.symm }

/-- Join from definitional equality. -/
@[simp] def join_rfl {a b : A} (p : Path a b) :
    Confluence.Join p p :=
  { meet := p
  , left := Rw.refl p
  , right := Rw.refl p }

/-- Extend a join by applying additional steps. -/
@[simp] def join_extend_left {a b : A} {p q r : Path a b} {_s : Path a b}
    (j : Confluence.Join p q) (hs : Rw r j.meet) (hp : Path r p) :
    Confluence.Join p q :=
  { meet := j.meet
  , left := hp.toEq ▸ hs
  , right := j.right }

/-- Build a join when one side already reduces to the other's target. -/
@[simp] def join_of_rw_to_same {a b : A} {p q : Path a b} {_r : Path a b} {s : Path a b}
    (hq : Rw p s) (hr : Rw q s) :
    Confluence.Join p q :=
  { meet := s
  , left := hq
  , right := hr }

/-! ## Basic Critical Pairs: Associativity vs Units -/

section AssocUnits

variable {a b c d : A}

/-- Critical pair: `trans_assoc` vs `trans_refl_right`
    Source: `((p · q) · refl)`
    Via assoc: `p · (q · refl)`
    Via rrr on outer: `p · q`
    Join: Both reach `p · q` (the second via `trans_refl_right` on inner). -/
def local_confluence_tt_rrr (p : Path a b) (q : Path b c) :
    Confluence.Join
      (Path.trans p (Path.trans q (Path.refl c)))  -- via trans_assoc
      (Path.trans p q)  -- via trans_refl_right
  :=
  { meet := Path.trans p q
  , left := Rw.tail (Rw.refl _) (Step.trans_congr_right p (Step.trans_refl_right q))
  , right := Rw.refl _ }

/-- Critical pair: `trans_assoc` vs `trans_refl_left`
    Source: `((refl · q) · r)`
    Via assoc: `refl · (q · r)`
    Via lrr on inner: `q · r`
    Join: Both reach `q · r`. -/
def local_confluence_tt_lrr (q : Path a b) (r : Path b c) :
    Confluence.Join
      (Path.trans (Path.refl a) (Path.trans q r))  -- via trans_assoc
      (Path.trans q r)  -- via trans_refl_left
  := by
  exact {
    meet := Path.trans q r
    left := Rw.tail (Rw.refl _) (Step.trans_refl_left _)
    right := Rw.refl _
  }

/-- Critical pair: Nested associativity
    Source: `(((p · q) · r) · s)`
    Two ways to apply trans_assoc. -/
def local_confluence_tt_tt (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Confluence.Join
      (Path.trans (Path.trans p (Path.trans q r)) s)  -- inner assoc first: (p · (q · r)) · s
      (Path.trans (Path.trans p q) (Path.trans r s))  -- outer assoc first: (p · q) · (r · s)
  :=
  -- Both can reach `p · (q · (r · s))` via further assoc steps
  { meet := Path.trans p (Path.trans q (Path.trans r s))
  , left := Rw.tail
      (Rw.tail (Rw.refl _) (Step.trans_assoc p (Path.trans q r) s))
      (Step.trans_congr_right p (Step.trans_assoc q r s))
  , right := Rw.tail (Rw.refl _) (Step.trans_assoc p q (Path.trans r s))
  }

end AssocUnits

/-! ## Critical Pairs: Symmetry Rules -/

section Symmetry

variable {a b c : A}

/-- Critical pair: `symm_symm` vs `symm_refl`
    Source: `symm(symm(refl))`
    Via symm_symm: `refl`
    Via symm applied to symm_refl: `symm(refl)` → need to then apply symm_refl
    Join: Both reach `refl`. -/
def local_confluence_ss_sr (a : A) :
    Confluence.Join
      (Path.refl a)  -- via symm_symm
      (Path.symm (Path.refl a))  -- via symm_congr of symm_refl
  := by
  exact {
    meet := Path.refl a
    left := Rw.refl _
    right := Rw.tail (Rw.refl _) (Step.symm_refl a)
  }

/-- Critical pair: `symm_trans_congr` vs `symm_symm`
    Source: `symm(symm(q) · symm(p))`
    Via symm_trans_congr: `symm(symm(p)) · symm(symm(q))`
    The other direction applies symm_symm to the whole thing after recognizing
    it as `symm(symm(p · q))` if we had gotten there via symm_trans_congr first.

    Actually, let's reconsider. If we have `symm(p · q)`:
    - Via symm_trans_congr: `symm(q) · symm(p)`
    Then applying symm_symm doesn't directly apply.

    The critical pair is when we have nested symms.
    Source: `symm(symm(p · q))`
    Via symm_symm: `p · q`
    Via symm_congr of symm_trans_congr: `symm(symm(q) · symm(p))`
    Join: The second needs `symm_trans_congr` then `symm_symm` twice.
-/
def local_confluence_ss_stss (p : Path a b) (q : Path b c) :
    Confluence.Join
      (Path.trans p q)  -- via symm_symm
      (Path.symm (Path.trans (Path.symm q) (Path.symm p)))  -- via symm_congr ∘ symm_trans_congr
  :=
  -- The second side needs: symm_trans_congr then symm_symm twice
  -- symm(symm(q) · symm(p)) → symm(symm(p)) · symm(symm(q)) → p · symm(symm(q)) → p · q
  { meet := Path.trans p q
  , left := Rw.refl _
  , right := Rw.tail
      (Rw.tail
        (Rw.tail (Rw.refl _) (Step.symm_trans_congr (Path.symm q) (Path.symm p)))
        (Step.trans_congr_left (Path.symm (Path.symm q)) (Step.symm_symm p)))
      (Step.trans_congr_right p (Step.symm_symm q))
  }

end Symmetry

/-! ## Critical Pairs: Inverse Laws -/

section Inverses

variable {a b c : A}

/-- Critical pair: `trans_assoc` vs `trans_symm`
    Source: `((p · symm(p)) · q)`
    Via assoc: `p · (symm(p) · q)`
    Via trans_symm on inner: `refl · q`
    Join: Both reach `q`.
    Path for left: `p · (symm(p) · q)` → `(p · symm(p)) · q` → `refl · q` → `q`
    Path for right: `refl · q` → `q` -/
def local_confluence_tt_ts (p : Path a b) (q : Path a c) :
    Confluence.Join
      (Path.trans p (Path.trans (Path.symm p) q))  -- via trans_assoc
      (Path.trans (Path.refl a) q)  -- via trans_symm then still have outer trans
  :=
  { meet := q
  , left := Rw.tail
      (Rw.tail
        (Rw.tail (Rw.refl _) (step_cancel_left_reassoc p q))
        (Step.trans_congr_left q (Step.trans_symm p)))
      (Step.trans_refl_left q)
  , right := Rw.tail (Rw.refl _) (Step.trans_refl_left q)
  }

/-- Critical pair: `trans_assoc` vs `symm_trans`
    Source: `((symm(p) · p) · q)`
    Via assoc: `symm(p) · (p · q)`
    Via symm_trans on inner: `refl · q`
    Join: Both reach `q`.
    Path for left: `symm(p) · (p · q)` → `(symm(p) · p) · q` → `refl · q` → `q`
    Path for right: `refl · q` → `q` -/
def local_confluence_tt_st (p : Path a b) (q : Path b c) :
    Confluence.Join
      (Path.trans (Path.symm p) (Path.trans p q))  -- via trans_assoc
      (Path.trans (Path.refl b) q)  -- via symm_trans on inner, keeping outer trans
  :=
  { meet := q
  , left := Rw.tail
      (Rw.tail
        (Rw.tail (Rw.refl _) (step_cancel_right_reassoc p q))
        (Step.trans_congr_left q (Step.symm_trans p)))
      (Step.trans_refl_left q)
  , right := Rw.tail (Rw.refl _) (Step.trans_refl_left q)
  }

end Inverses

/-! ## Local Confluence (Prop-Level Assumption)

Local confluence for our TRS is justified by critical pair analysis. We have
explicit join witnesses for key path algebra overlaps above. Because `Step` is
Prop-valued, exhaustive case analysis into `Type` is not directly possible.

We therefore assume Prop-level local confluence via `HasLocalConfluenceProp`.
The intended justification is:
1. The critical pair proofs above (tt_rrr, tt_lrr, tt_tt, ss_sr, ss_stss, tt_ts, tt_st)
2. Commutation of non-overlapping steps (commute_trans_left_right)
3. Lifting lemmas for congruence (join_lift_trans_left/right, join_lift_symm)
-/

/-! ## Full Confluence from Local Confluence

We use a Prop-level Newman's lemma (termination + local confluence → confluence).
`Classical.choose` is only used to produce `Type`-level join witnesses for
downstream convenience.
-/
/-- Transitivity for Rw (append two derivations). -/
def rw_append {a b : A} {p q r : Path a b} (h1 : Rw p q) (h2 : Rw q r) : Rw p r := by
  induction h2 with
  | refl => exact h1
  | tail _ step ih => exact Rw.tail ih step

/-- Diamond lemma: Given Step p q and Step p r, there exists s with Rw q s and
    Rw r s. This follows directly from Prop-level local confluence. -/
theorem diamond_prop [ConfluenceConstructive.HasLocalConfluenceProp.{u}] {a b : A}
    {p q r : Path a b} (hq : Step p q) (hr : Step p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  ConfluenceConstructive.local_confluence_prop hq hr

/-! ## Termination and Newman's lemma (Prop-level) -/

/-- Non-empty transitive closure of `Step`. -/
inductive RwPlus {A : Type u} {a b : A} : Path a b → Path a b → Prop
  | single {p q : Path a b} : Step p q → RwPlus p q
  | tail {p q r : Path a b} : RwPlus p q → Step q r → RwPlus p r

theorem rw_of_plus {a b : A} {p q : Path a b} (h : RwPlus p q) : Rw p q := by
  induction h with
  | single hstep => exact rw_of_step hstep
  | tail hplus hstep ih => exact Rw.tail ih hstep

theorem rw_plus_trans {a b : A} {p q r : Path a b}
    (h1 : RwPlus p q) (h2 : Rw q r) : RwPlus p r := by
  induction h2 with
  | refl => exact h1
  | tail _ step ih => exact RwPlus.tail ih step

theorem rw_uncons {a b : A} {p q : Path a b} (h : Rw p q) :
    Nonempty (Path p q) ∨ ∃ r, Step p r ∧ Rw r q := by
  induction h with
  | refl => exact Or.inl ⟨Path.refl _⟩
  | tail h step ih =>
    cases ih with
    | inl hpeq =>
        rcases hpeq with ⟨hpath⟩
        refine Or.inr ?_
        refine ⟨_, ?_, Rw.refl _⟩
        cases hpath.toEq
        exact step
    | inr hdata =>
        rcases hdata with ⟨r, hstep, hrq⟩
        refine Or.inr ⟨r, hstep, ?_⟩
        exact Rw.tail hrq step

/-- Termination: well-foundedness of the reverse `RwPlus` relation. -/
def Terminating {A : Type u} {a b : A} : Prop :=
  WellFounded (fun p q => RwPlus (A := A) (a := a) (b := b) q p)

class HasTerminationProp.{v} : Prop where
  termination_prop : ∀ {A : Type v} {a b : A}, Terminating (A := A) (a := a) (b := b)

theorem termination_prop [HasTerminationProp.{u}] {a b : A} :
    Terminating (A := A) (a := a) (b := b) :=
  HasTerminationProp.termination_prop

section

variable [HasTerminationProp.{u}] [ConfluenceConstructive.HasLocalConfluenceProp.{u}]

theorem confluence_prop {a b : A} {p q r : Path a b}
    (hq : Rw p q) (hr : Rw p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s := by
  classical
  revert q r hq hr
  induction p using (termination_prop (A := A) (a := a) (b := b)).induction with
  | h p ih =>
    intro q r hq hr
    cases rw_uncons hq with
    | inl hq_eq =>
        rcases hq_eq with ⟨hq_path⟩
        refine ⟨r, ?_, Rw.refl r⟩
        cases hq_path.toEq
        simpa using hr
    | inr hq_data =>
        rcases hq_data with ⟨p1, hp1, hq_rest⟩
        cases rw_uncons hr with
        | inl hr_eq =>
            rcases hr_eq with ⟨hr_path⟩
            refine ⟨q, Rw.refl q, ?_⟩
            cases hr_path.toEq
            simpa using hq
        | inr hr_data =>
            rcases hr_data with ⟨p2, hp2, hr_rest⟩
            obtain ⟨s, hp1s, hp2s⟩ := local_confluence_prop hp1 hp2
            obtain ⟨s1, hq_s1, hs_s1⟩ := ih p1 (RwPlus.single hp1) hq_rest hp1s
            obtain ⟨s2, hr_s2, hs_s2⟩ := ih p2 (RwPlus.single hp2) hr_rest hp2s
            have hplus_ps : RwPlus (A := A) (a := a) (b := b) p s :=
              rw_plus_trans (RwPlus.single hp1) hp1s
            obtain ⟨t, hs1t, hs2t⟩ := ih s hplus_ps hs_s1 hs_s2
            exact ⟨t, rw_append hq_s1 hs1t, rw_append hr_s2 hs2t⟩

/-- Strip lemma (Prop version): a single step joins with a multi-step. -/
theorem strip_lemma_prop {a b : A} {p q r : Path a b}
    (hstep : Step p q) (hmulti : Rw p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  confluence_prop (hq := rw_of_step hstep) (hr := hmulti)
/-- **Confluence of LND_EQ-TRS**: For any two multi-step rewrites from the same
    source, there exists a common descendant.

    This follows from Prop-level local confluence. The implementation extracts
    a Type-valued witness from the Prop-level existence proof using
    `Classical.choose`. -/
noncomputable def confluence_of_local {a b : A} {p q r : Path a b}
    (hq : Rw p q) (hr : Rw p r) :
    Confluence.Join q r :=
  have h := confluence_prop hq hr
  let s := Classical.choose h
  let ⟨hqs, hrs⟩ := Classical.choose_spec h
  { meet := s, left := hqs, right := hrs }

/-- The main result: instantiate HasJoinOfRw. -/
noncomputable instance instHasJoinOfRw : Confluence.HasJoinOfRw.{u} where
  join_of_rw := fun hq hr => confluence_of_local hq hr

end

end ConfluenceProof
end Rewrite
end Path
end ComputationalPaths












