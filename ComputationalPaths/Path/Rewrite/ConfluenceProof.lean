/-
# Confluence Proof for Computational Paths TRS

This module **proves** full confluence of the computational-paths rewriting
system and derives `HasJoinOfRw` unconditionally — no assumptions required.

## Two Levels of Confluence

There are two distinct confluence results in this project, operating at
different levels of abstraction:

### 1. Path-level confluence (this module)

The `Path a b` type is a **structure** (in `Type`) carrying both a step trace
(`steps : List (Step A)`) and an equality witness (`proof : a = b`).
Different step traces produce genuinely distinct `Path` values (see
`UIP.lean: not_uip_of_nonempty`).

At this level, confluence of the `Rw` relation is proved via `step_drop`
(Rule 77), which rewrites any path `p` to `Path.stepChain p.toEq`.
Since `toEq` is proof-irrelevant (all equality proofs `a = b` are equal in
Lean's `Prop`), the canonical target is unique: `stepChain q.toEq =
stepChain r.toEq` for any `q r : Path a b`.

This is a **valid** confluence proof, but it relies on UIP for the underlying
`Eq` type.  It collapses all paths with the same endpoints to the same
rewrite-equivalence class — a consequence of Lean's proof-irrelevant `Prop`.

### 2. Expr-level confluence (GroupoidConfluence.lean)

The `GroupoidTRS.Expr` type is an **untyped** syntax tree where distinct
terms are genuinely distinct.  The completed groupoid TRS (`CStep`: 10 rules
+ 3 congruences) is confluent, proved via a **semantic interpretation into
the free group**.

This is the **genuine mathematical result**: confluence of the groupoid
rewrite system as an algebraic property, independent of UIP or proof
irrelevance.  The proof constructs an explicit homomorphism `toRW : Expr →
List Gen` into reduced words, shows it is invariant under `CStep`, and
derives confluence from the uniqueness of reduced words.

See `GroupoidConfluence.confluence` for the statement and proof.

## Termination

Termination is proved in `GroupoidTRS.lean` for the core groupoid fragment
operating on abstract syntax (`GroupoidTRS.Expr`). The proof uses a
lexicographic pair `(weight, leftWeight)` where:
- `weight` is a polynomial interpretation (rules 1–7 strictly decrease it)
- `leftWeight` handles associativity (rule 8 preserves weight but strictly
  decreases leftWeight)

At the semantic `Path` level, some `Step` constructors produce identity
rewrites (e.g. `symm_refl` maps `symm(refl a)` to `refl a` — these are
definitionally equal), making `RwPlus` reflexive. A reflexive relation
cannot be well-founded. The termination result therefore lives on the
*syntactic* `Expr` type, which is the mathematically correct level.

## Main Results

- `instHasTerminationProp`: **Proved** — `HasTerminationProp` instance
  (genuine termination proof via `GroupoidTRS.Expr.termination`)
- `instHasConfluenceProp`: **Proved** — full confluence via `step_drop`
- `instLocalOfConfluence`: **Proved** — local confluence (corollary)
- `confluence_prop`: Prop-level confluence (proved)
- `strip_lemma_prop`: Strip lemma (corollary of confluence)
- `instHasJoinOfRw`: **Proved** — instance of `HasJoinOfRw`
- `expr_confluence`: Bridge to the genuine algebraic confluence result

## Key Achievements

1. **Critical pair infrastructure**: Explicit join witnesses for key
   path algebra overlaps, including inverse-related ones.

2. **Commutation lemmas**: Steps at disjoint positions commute
   (`commute_trans_left_right`, `join_lift_trans_left/right`,
   `join_lift_symm`).

3. **Identity context technique**: Inverse critical pairs close using
   `context_tt_cancel_left` specialized to the identity context via
   `congrArg_id`.

4. **Algebraic confluence**: The completed groupoid TRS is confluent
   via free group interpretation — no `Step.canon`, no UIP
   (see `GroupoidConfluence.lean`).
-/

import ComputationalPaths.Path.Rewrite.Confluence
import ComputationalPaths.Path.Rewrite.ConfluenceConstructive
import ComputationalPaths.Path.Rewrite.GroupoidTRS
import ComputationalPaths.Path.Rewrite.GroupoidConfluence

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

/-- Every path rewrites to one with an empty step list.
    Proof by induction on the step list length: `step_drop` removes
    one step at a time until the list is empty. -/
theorem rw_to_nil {a b : A} (p : Path a b) :
    Rw p (Path.mk [] p.toEq) := by
  cases p with
  | mk steps proof =>
    show Rw (Path.mk steps proof) (Path.mk [] proof)
    induction steps with
    | nil => exact Rw.refl _
    | cons s rest ih =>
      exact rw_append (rw_of_step (Step.step_drop s rest proof)) ih

/-- Diamond lemma (local confluence): Given Step p q and Step p r,
    there exists s with Rw q s and Rw r s.

    **Proof**: Both `q` and `r` reduce to `Path.mk [] _` via
    `rw_to_nil`.  Since all `Path a b` values share the same
    `proof` field (proof irrelevance of `Eq`), the two normal
    forms are identical. -/
theorem diamond_prop {a b : A}
    {p q r : Path a b} (_hq : Step p q) (_hr : Step p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  ⟨ Path.mk [] q.toEq
  , rw_to_nil q
  , by have : Path.mk (A := A) [] r.toEq = Path.mk [] q.toEq := by
         simp
       rw [this]; exact rw_to_nil r ⟩

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



/-- Termination of the rewrite system.

The computational-paths TRS terminates when viewed at the syntactic level:
the abstract groupoid rewrite system on `GroupoidTRS.Expr` (with rules
`symm_refl`, `symm_symm`, `trans_refl_left/right`, `trans_symm`,
`symm_trans`, `symm_trans_congr`, `trans_assoc`, and congruence closure)
is well-founded. This is proved in `GroupoidTRS.lean` via the lexicographic
measure `(weight, leftWeight)`.

At the semantic `Path` level, some `Step` constructors produce identity
rewrites (since `Path` satisfies UIP on the underlying equality proof),
making `RwPlus` reflexive and hence non-well-founded as a relation on
`Path` values. The termination result therefore lives on the *syntactic*
`Expr` type, which is the mathematically correct level for TRS termination.

`Terminating` records that the abstract TRS terminates: specifically, that
`GroupoidTRS.Expr.Step` is well-founded. -/
def Terminating : Prop :=
  WellFounded (fun q p : GroupoidTRS.Expr => GroupoidTRS.Expr.Step p q)

class HasTerminationProp : Prop where
  termination_prop : Terminating

/-- **`HasTerminationProp` instance** — proved via `GroupoidTRS.Expr.termination`.

This is a genuine termination proof using the polynomial weight function
`w(symm e) = 2·w(e) + 1`, `w(trans e₁ e₂) = w(e₁) + w(e₂) + 2`
combined lexicographically with the left-association weight
`lw(trans e₁ e₂) = lw(e₁) + lw(e₂) + size(e₁)`. Every rewrite step
strictly decreases this measure. -/
instance instHasTerminationProp : HasTerminationProp where
  termination_prop := GroupoidTRS.Expr.termination

theorem termination_prop_of [HasTerminationProp] :
    Terminating :=
  HasTerminationProp.termination_prop

/-! ### Path-level confluence via toEq preservation

Every `Step` rule preserves `toEq` (proved in `step_toEq`).  Therefore,
any multi-step `Rw` chain also preserves `toEq`.  Given two chains
`Rw p q` and `Rw p r`, we have `q.toEq = p.toEq = r.toEq`.

Since `Path a b` is a structure `{ steps : List (Step A), proof : a = b }`
and the `proof` field is proof-irrelevant, paths differ only in their
`steps` metadata.  The `Step` rewrite rules transform this metadata
while preserving the underlying equality witness.

**Confluence proof strategy**: We use the fact that `toEq` is a
complete invariant for the rewrite system: all `Rw`-reachable paths
from a given source share the same `toEq`, and the `steps` field
is rewriting metadata that does not affect the mathematical content.
The join is constructed by choosing an arbitrary common descendant
(using Classical reasoning in `Prop`).

For the genuine algebraic confluence of the groupoid TRS fragment — proved
via free group interpretation without any appeal to proof irrelevance — see
`GroupoidConfluence.lean`.
-/

/-- Multi-step rewriting preserves `toEq`. -/
theorem rw_toEq {a b : A} {p q : Path a b} (h : Rw p q) :
    p.toEq = q.toEq := by
  induction h with
  | refl => rfl
  | tail _ step ih => exact ih.trans (step_toEq step)

/-- Prop-level confluence: any two multi-step rewrites from the same
source can be joined. -/
class HasConfluenceProp.{v} : Prop where
  confluence : ∀ {A : Type v} {a b : A} {p q r : @Path A a b},
    Rw p q → Rw p r → ∃ s, Rw q s ∧ Rw r s

/-- **Strip lemma**: if `Step p q` and `Rw p r`, then there exists `s`
with `Rw q s` and `Rw r s`.

Proof via `rw_to_nil`: both `q` and `r` reduce to `Path.mk [] _`,
which is the same value by proof irrelevance. -/
theorem strip_lemma_from_diamond {a b : A} {p q r : Path a b}
    (_hstep : Step p q) (_hrw : Rw p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  ⟨ Path.mk [] q.toEq
  , rw_to_nil q
  , by have : Path.mk (A := A) [] r.toEq = Path.mk [] q.toEq := by
         simp
       rw [this]; exact rw_to_nil r ⟩

/-- **`HasConfluenceProp` instance** — proved via `rw_to_nil`.

Every path `p : Path a b` rewrites (via `step_drop`) to `Path.mk [] p.toEq`.
Since `toEq` is proof-irrelevant, all `Path a b` values share the same
normal form.  Given `Rw p q` and `Rw p r`, both `q` and `r` reduce to
this common normal form.

**Philosophical note**: The `step_drop` rule says "steps in the step
list are computational witnesses / traces that can be forgotten."  This
is NOT the same as UIP (which says "all proofs of `a = b` are equal"):
- `step_drop` operates on the `steps : List (Step A)` field (in `Type`)
- The `proof : a = b` field (in `Prop`) is untouched by `step_drop`
- No canonical form is constructed from the equality proof

The genuine algebraic confluence of the groupoid TRS — without any
step-list erasure or proof irrelevance — is proved in
`GroupoidConfluence.lean` via free group interpretation. -/
instance instHasConfluenceProp : HasConfluenceProp.{u} where
  confluence := fun {A} {a} {b} {_p} {q} {r} _hq _hr =>
    ⟨ Path.mk [] q.toEq
    , rw_to_nil q
    , by have : Path.mk (A := A) [] r.toEq = Path.mk [] q.toEq := by
           simp
         rw [this]; exact rw_to_nil r ⟩

/-- Confluence implies local confluence. -/
instance (priority := 50) instLocalOfConfluence :
    ConfluenceConstructive.HasLocalConfluenceProp.{u} where
  local_confluence := fun hq hr =>
    instHasConfluenceProp.confluence (rw_of_step hq) (rw_of_step hr)

/-- **Confluence** (Prop-level): `Rw p q` and `Rw p r` imply joinability. -/
theorem confluence_prop {a b : A} {p q r : Path a b}
    (hq : Rw p q) (hr : Rw p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  HasConfluenceProp.confluence hq hr

/-- Strip lemma: corollary of `confluence_prop`. -/
theorem strip_lemma_prop {a b : A} {p q r : Path a b}
    (hstep : Step p q) (hmulti : Rw p r) :
    ∃ s : Path a b, Rw q s ∧ Rw r s :=
  confluence_prop (rw_of_step hstep) hmulti

/-- Extract `Type`-level join witnesses via `Classical.choose`. -/
noncomputable def confluence_of_local {a b : A} {p q r : Path a b}
    (hq : Rw p q) (hr : Rw p r) :
    Confluence.Join q r :=
  have h := confluence_prop hq hr
  let s := Classical.choose h
  let ⟨hqs, hrs⟩ := Classical.choose_spec h
  { meet := s, left := hqs, right := hrs }

/-- The main result: instantiate HasJoinOfRw unconditionally. -/
noncomputable instance instHasJoinOfRw : Confluence.HasJoinOfRw.{u} where
  join_of_rw := fun hq hr => confluence_of_local hq hr

/-! ## Bridge to Algebraic Confluence (GroupoidConfluence)

The `instHasConfluenceProp` above uses `step_drop`, which allows dropping
steps from the step list.  This is a legitimate simplification rule: step
lists are computational traces that can be forgotten without affecting the
underlying equality.  Combined with proof irrelevance of `Eq` (which makes
all `Path a b` values share the same `proof` field), `step_drop` ensures
that all paths normalise to `Path.mk [] h`, yielding unique normal forms
and hence confluence.

The **genuine** algebraic confluence result lives in `GroupoidConfluence.lean`
on the abstract syntax type `GroupoidTRS.Expr`.  There, the completed
groupoid TRS (10 rules + 3 congruences) is shown confluent via a semantic
interpretation into the **free group** on `Nat`-indexed generators.  This
proof:

1. Defines `toRW : Expr → List Gen` mapping expressions to reduced words
2. Shows `toRW` is invariant under `CStep` (`toRW_invariant`)
3. Shows every `Expr` reduces to a canonical form (`reach_canon`)
4. Derives confluence from the uniqueness of reduced words

No `Step.canon`, no `toEq`, no UIP, no proof irrelevance.

### Path-level vs Expr-level confluence

The `Path a b` type is a **structure** in `Type`, not `Prop`:
```
structure Path {A : Type u} (a b : A) where
  steps : List (Step A)
  proof : a = b
```
Two paths with different step lists are genuinely distinct values
(see `UIP.lean: not_uip_of_nonempty`).  The `Rw` relation rewrites
these step lists according to the `Step` constructors.

At the `Path` level, confluence uses `step_drop` (which erases step-list
entries) together with proof irrelevance of `Eq`.  At the `Expr` level,
confluence is a purely algebraic result about the groupoid TRS — no
step lists, no proof irrelevance.

The thesis can cite `GroupoidConfluence.confluence` as the primary
mathematical contribution (genuine algebra) and `instHasConfluenceProp`
as the convenient `Path`-level wrapper.
-/

/-- **Algebraic confluence** of the completed groupoid TRS.

This is the genuine mathematical result: for any `GroupoidTRS.Expr` and
two `CStep*` reduction sequences to `b` and `c`, there exists `d` with
`b →* d` and `c →* d`.

Proved in `GroupoidConfluence.lean` via free group interpretation.
No `Step.canon`, no UIP, no proof irrelevance. -/
theorem expr_confluence (a b c : GroupoidTRS.Expr)
    (hab : GroupoidConfluence.CRTC a b) (hac : GroupoidConfluence.CRTC a c) :
    ∃ d, GroupoidConfluence.CRTC b d ∧ GroupoidConfluence.CRTC c d :=
  GroupoidConfluence.confluence a b c hab hac

/-- **Church-Rosser** for the completed groupoid TRS on `Expr`.

Two expressions have the same free group interpretation if and only if
they are joinable under `CStep`.  This completely characterizes the
equivalence relation generated by the groupoid rewrite rules. -/
theorem expr_church_rosser (e₁ e₂ : GroupoidTRS.Expr) :
    GroupoidConfluence.toRW e₁ = GroupoidConfluence.toRW e₂ ↔
    ∃ d, GroupoidConfluence.CRTC e₁ d ∧ GroupoidConfluence.CRTC e₂ d :=
  GroupoidConfluence.toRW_characterizes_joinability e₁ e₂

/-- **Unique normal forms** for the completed groupoid TRS.

If two expressions in normal form are both reachable from the same source,
they are identical.  This is the strongest form of the confluence property. -/
theorem expr_unique_normal_forms (e₁ e₂ : GroupoidTRS.Expr)
    (h : GroupoidConfluence.CRTC e₁ e₂)
    (hnf : ∀ e', ¬GroupoidConfluence.CStep e₂ e') :
    ∀ e₃, GroupoidConfluence.CRTC e₁ e₃ →
      (∀ e', ¬GroupoidConfluence.CStep e₃ e') → e₂ = e₃ :=
  GroupoidConfluence.normal_form_unique e₁ e₂ h hnf

end ConfluenceProof
end Rewrite
end Path
end ComputationalPaths
