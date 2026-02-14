/-
# Constructive Confluence via Prop-Level Proofs

This module packages the Prop-level local confluence interface used by the
rewrite system and supplies supporting lemmas. The concrete instance is
provided in `ConfluenceProof.lean` via `Step.canon` and full confluence.

For the genuine algebraic confluence result (without `Step.canon` or UIP),
see `GroupoidConfluence.lean`, which proves confluence of the completed
groupoid TRS on abstract `Expr` syntax via free group interpretation.

## Strategy

1. **Prop-level local confluence**: Provide `HasLocalConfluenceProp` and
   `local_confluence_prop` as a reusable interface.

2. **Helper lemmas**: Lift Prop-level joins through the congruence rules.

## Key Results

- `HasLocalConfluenceProp` and `local_confluence_prop`
- Prop-level lifting lemmas for `trans`/`symm`

## Instance

The concrete instance `instLocalOfConfluence` is in `ConfluenceProof.lean`,
derived from the proved `instHasConfluenceProp`.
-/

import ComputationalPaths.Path.Rewrite.Confluence

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceConstructive

open Confluence

universe u

variable {A : Type u} {a b : A}

/-! ## Prop-Level Local Confluence

The key insight is that we can prove local confluence at the Prop level
by leveraging the existing critical pair proofs. Since all genuine critical
pairs have explicit join witnesses in ConfluenceProof.lean, and non-overlapping
cases trivially commute, the result follows.

The proof interface keeps local confluence abstract while the critical
pair joins in ConfluenceProof.lean provide the intended justification.
-/

/-- Helper: convert existing Type-valued Join to Prop existence. -/
theorem join_to_prop {p q : Path a b} (j : Confluence.Join p q) :
    ∃ s, Rw p s ∧ Rw q s :=
  ⟨j.meet, j.left, j.right⟩

/-- Helper: lift join through trans_congr_left. -/
theorem join_lift_trans_left_prop {a b c : A} {p q : Path a b} (r : Path b c)
    (h : ∃ s, Rw p s ∧ Rw q s) :
    ∃ s, Rw (trans p r) s ∧ Rw (trans q r) s := by
  obtain ⟨s, hp, hq⟩ := h
  exact ⟨trans s r, rw_trans_congr_left r hp, rw_trans_congr_left r hq⟩

/-- Helper: lift join through trans_congr_right. -/
theorem join_lift_trans_right_prop {a b c : A} (p : Path a b) {q r : Path b c}  
    (h : ∃ s, Rw q s ∧ Rw r s) :
    ∃ s, Rw (trans p q) s ∧ Rw (trans p r) s := by
  obtain ⟨s, hq, hr⟩ := h
  exact ⟨trans p s, rw_trans_congr_right p hq, rw_trans_congr_right p hr⟩       

/-- Helper: lift join through symm_congr. -/
theorem join_lift_symm_prop {a b : A} {p q : Path a b}
    (h : ∃ s, Rw p s ∧ Rw q s) :
    ∃ s, Rw (symm p) s ∧ Rw (symm q) s := by
  obtain ⟨s, hp, hq⟩ := h
  exact ⟨symm s, rw_symm_congr hp, rw_symm_congr hq⟩

/-! ## Local Confluence Typeclass Interface

The local confluence property (diamond property) states that for any two
single-step rewrites from the same source, the results can be joined.

This is established metatheoretically by:
1. Critical pair analysis (all genuine overlaps have explicit joins in ConfluenceProof.lean)
2. Commutation of non-overlapping steps
3. Trivial join for identical steps

The property is packaged as a typeclass assumption. Provide a local instance
in downstream code if you want a global default.
-/

/-- **Local Confluence Prop** (typeclass interface).

For any two single-step rewrites from the same source path, there exists
a common descendant reachable by multi-step rewrites from both results.

**Instance**: `ConfluenceProof.instLocalOfConfluence` provides a concrete
instance, derived from the proved full confluence (`instHasConfluenceProp`)
which uses `Step.canon` to join via the canonical normal form.

**Algebraic alternative**: For the UIP-free local confluence result on
abstract `Expr` syntax, see `GroupoidConfluence.local_confluence`. -/
class HasLocalConfluenceProp.{v} : Prop where
  local_confluence : ∀ {A : Type v} {a b : A} {p q r : Path a b}
    (_hq : Step p q) (_hr : Step p r), ∃ s, Rw q s ∧ Rw r s

/-- Local confluence at the Prop level, given the typeclass assumption. -/
theorem local_confluence_prop [h : HasLocalConfluenceProp.{u}] {A : Type u} {a b : A} {p q r : Path a b}
    (hq : Step p q) (hr : Step p r) : ∃ s, Rw q s ∧ Rw r s :=
  h.local_confluence hq hr

end ConfluenceConstructive
end Rewrite
end Path
end ComputationalPaths
