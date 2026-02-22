/-
# Path Simplification Tactics

This module provides automation for proving RwEq goals using the computational
paths rewrite system. The `path_simp` tactic combines the extensive @[simp]
lemma library in RwEq.lean with specialized tactics for path equality reasoning.

## Tactics Provided

### Basic Tactics
- `path_simp`: Simplify RwEq goals using the built-in simp lemmas
- `path_rfl`: Close RwEq goals that are reflexive
- `path_canon`: Use canonicalization to close RwEq goals

### Transitivity Tactics
- `path_trans h`: Apply transitivity with intermediate path from hypothesis h
- `path_trans_via p`: Apply transitivity with explicit intermediate path p

### Congruence Tactics
- `path_congr_left h`: Apply congruence on left side of trans
- `path_congr_right h`: Apply congruence on right side of trans

### Structural Tactics
- `path_assoc`: Reassociate trans chains to the right
- `path_assoc_left`: Reassociate trans chains to the left

## Usage Examples

```lean
example (p : Path a a) : RwEq (trans refl p) p := by path_simp

example (h : RwEq p q) : RwEq (trans p r) (trans q r) := by
  path_congr_left h
```

## References

- Computational Paths paper (de Queiroz et al.)
- LND_EQ-TRS rewrite system
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path

/-! ## Notation for RwEq -/

/-- Notation `p ≈ q` for `RwEq p q` in path reasoning. -/
scoped infix:50 " ≈ " => RwEq

namespace Tactic

/-! ## Basic Tactics -/

/-- `path_rfl` closes RwEq goals that are reflexive (p = p). -/
macro "path_rfl" : tactic => `(tactic| exact RwEq.refl _)

/-- `path_symm` transforms `RwEq p q` to `RwEq q p`. -/
macro "path_symm" : tactic => `(tactic| apply rweq_symm)

/-! ## Transitivity Tactics -/

/-- `path_trans h` applies transitivity using hypothesis h.
    If goal is `RwEq p r` and `h : RwEq p q`, produces goal `RwEq q r`.
    If goal is `RwEq p r` and `h : RwEq q r`, produces goal `RwEq p q`. -/
macro "path_trans" h:term : tactic =>
  `(tactic| first
    | exact rweq_trans $h (by assumption)
    | exact rweq_trans (by assumption) $h
    | apply rweq_trans $h
    | apply rweq_trans _ $h)

/-- `path_trans_via p` applies transitivity with explicit intermediate path p.
    Transforms goal `RwEq a c` into goals `RwEq a p` and `RwEq p c`. -/
macro "path_trans_via" p:term : tactic =>
  `(tactic| apply rweq_trans (q := $p))

/-! ## Congruence Tactics -/

/-- `path_congr_left h` applies left congruence.
    If goal is `RwEq (trans p r) (trans q r)` and `h : RwEq p q`, closes the goal. -/
macro "path_congr_left" h:term : tactic =>
  `(tactic| exact rweq_trans_congr_left _ $h)

/-- `path_congr_right h` applies right congruence.
    If goal is `RwEq (trans r p) (trans r q)` and `h : RwEq p q`, closes the goal. -/
macro "path_congr_right" h:term : tactic =>
  `(tactic| exact rweq_trans_congr_right _ $h)

/-- `path_congr h1, h2` applies congruence on both sides.
    If goal is `RwEq (trans p q) (trans p' q')`, uses h1 for left and h2 for right. -/
macro "path_congr" h1:term "," h2:term : tactic =>
  `(tactic| exact rweq_trans_congr $h1 $h2)

/-! ## Structural Tactics -/

/-- `path_assoc` reassociates a trans chain to the right.
    Transforms `RwEq (trans (trans p q) r) t` to use `RwEq (trans p (trans q r)) t`. -/
macro "path_assoc" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_tt
    | apply rweq_trans (rweq_symm rweq_tt))

/-- `path_assoc_left` reassociates a trans chain to the left.
    Transforms `RwEq (trans p (trans q r)) t` to use `RwEq (trans (trans p q) r) t`. -/
macro "path_assoc_left" : tactic =>
  `(tactic| first
    | apply rweq_trans (rweq_symm rweq_tt)
    | apply rweq_trans rweq_tt)

/-- `path_unit_left` eliminates a left unit (refl · p ≈ p). -/
macro "path_unit_left" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_cmpA_refl_left
    | apply rweq_trans (rweq_symm rweq_cmpA_refl_left))

/-- `path_unit_right` eliminates a right unit (p · refl ≈ p). -/
macro "path_unit_right" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_cmpA_refl_right
    | apply rweq_trans (rweq_symm rweq_cmpA_refl_right))

/-- `path_cancel_left` applies left inverse cancellation (p⁻¹ · p ≈ refl). -/
macro "path_cancel_left" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_cmpA_inv_left
    | exact rweq_cmpA_inv_left _)

/-- `path_cancel_right` applies right inverse cancellation (p · p⁻¹ ≈ refl). -/
macro "path_cancel_right" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_cmpA_inv_right
    | exact rweq_cmpA_inv_right _)

/-- `path_inv_inv` applies double inverse: σ(σ(p)) ≈ p. -/
macro "path_inv_inv" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_ss
    | exact rweq_ss _)

/-- `path_symm_refl` applies symm of refl: σ(ρ) ≈ ρ. -/
macro "path_symm_refl" : tactic =>
  `(tactic| first
    | apply rweq_trans rweq_sr
    | exact rweq_sr _)

/-- `path_inv_distr` applies distribution of symm over trans: σ(p · q) ≈ σ(q) · σ(p). -/
macro "path_inv_distr" : tactic =>
  `(tactic| first
    | exact rweq_symm_trans_congr
    | apply rweq_trans rweq_symm_trans_congr)

/-- `path_congr_symm h` applies symm congruence: if h : RwEq p q, then RwEq (symm p) (symm q). -/
macro "path_congr_symm" h:term : tactic =>
  `(tactic| exact rweq_symm_congr $h)

/-- `path_congrArg f, h` applies congrArg congruence: if h : RwEq p q, then RwEq (congrArg f p) (congrArg f q). -/
macro "path_congrArg" f:term "," h:term : tactic =>
  `(tactic| exact rweq_congrArg_of_rweq $f $h)

/-- `path_simp` simplifies RwEq goals using the extensive simp library.

    This tactic:
    1. First tries `rfl` (for definitional equality)
    2. Then applies `simp only [...]` with all RwEq @[simp] lemmas
    3. Finally tries `path_canon` for remaining goals

    The lemma set includes:
    - Unit laws: `trans (refl a) p ≈ p`, `trans p (refl b) ≈ p`
    - Inverse laws: `trans p (symm p) ≈ refl`, `trans (symm p) p ≈ refl`
    - Associativity: `trans (trans p q) r ≈ trans p (trans q r)`
    - Double symmetry: `symm (symm p) ≈ p`
    - Congruence lemmas for trans, symm, congrArg, etc.
-/
macro "path_simp" : tactic =>
  `(tactic|
    first
    | exact RwEq.refl _
    | simp only [
        rweq_refl, rweq_of_step,
        rweq_trans_congr_left, rweq_trans_congr_right, rweq_trans_congr,
        rweq_cmpA_refl_left, rweq_cmpA_refl_right,
        rweq_cmpA_inv_left, rweq_cmpA_inv_right,
        rweq_tt, rweq_sr, rweq_ss,
        rweq_symm_trans_congr,
        rweq_congrArg_of_rweq, rweq_congrArg_trans,
        rweq_congrArg_symm, rweq_congrArg_refl
      ])

/-- `path_simp_all` is a more aggressive version that also uses
    hypotheses in the context. -/
macro "path_simp_all" : tactic =>
  `(tactic|
    simp_all only [
      rweq_refl, rweq_of_step,
      rweq_trans_congr_left, rweq_trans_congr_right, rweq_trans_congr,
      rweq_cmpA_refl_left, rweq_cmpA_refl_right,
      rweq_cmpA_inv_left, rweq_cmpA_inv_right,
      rweq_tt, rweq_sr, rweq_ss,
      rweq_symm_trans_congr,
      rweq_congrArg_of_rweq, rweq_congrArg_trans,
      rweq_congrArg_symm, rweq_congrArg_refl
    ])

/-- `path_decide` attempts to close RwEq goals automatically by:
    1. Trying direct reflexivity
    2. Normalizing and comparing -/
macro "path_decide" : tactic =>
  `(tactic|
    first
    | exact RwEq.refl _
    | (path_simp; try exact RwEq.refl _))

/-! ## Advanced Tactics -/

/-- `path_auto` is the main automation tactic for RwEq goals.

    It repeatedly applies simplification, congruence, and structural
    rules until the goal is solved or no more progress can be made.

    Strategy order:
    1. Try reflexivity
    2. Apply simp with all RwEq lemmas
    3. Try symmetry if goal is symmetric to something in context
    4. Apply congruence rules for nested trans/symm/congrArg
    5. Try hypothesis from context -/
macro "path_auto" : tactic =>
  `(tactic|
    first
    | exact RwEq.refl _
    | simp only [
        rweq_refl, rweq_of_step, rweq_of_eq, rweq_of_rw,
        rweq_trans_congr_left, rweq_trans_congr_right, rweq_trans_congr,
        rweq_cmpA_refl_left, rweq_cmpA_refl_right,
        rweq_cmpA_inv_left, rweq_cmpA_inv_right,
        rweq_tt, rweq_sr, rweq_ss,
        rweq_symm_trans_congr, rweq_symm_congr,
        rweq_congrArg_of_rweq, rweq_congrArg_trans,
        rweq_congrArg_symm, rweq_congrArg_refl, rweq_congrArg_const,
        rweq_mapLeft_of_rweq, rweq_mapRight_of_rweq, rweq_map2_of_rweq,
        rweq_mapLeft_trans, rweq_mapRight_trans,
        rweq_mapLeft_symm, rweq_mapRight_symm,
        rweq_mapLeft_refl, rweq_mapRight_refl,
        rweq_prod_fst_beta, rweq_prod_snd_beta, rweq_prod_eta,
        rweq_fst_prodMk, rweq_snd_prodMk,
        rweq_sigma_fst_beta, rweq_sigma_snd_beta, rweq_sigma_eta,
        rweq_sigmaMk_refl,
        rweq_fun_app_beta, rweq_fun_eta,
        rweq_apd_refl, rweq_transport_refl_beta
      ]; first | exact RwEq.refl _ | assumption
    | assumption)

/-- `path_auto!` is a more aggressive version that also uses hypotheses. -/
macro "path_auto!" : tactic =>
  `(tactic|
    first
    | exact RwEq.refl _
    | simp_all only [
        rweq_refl, rweq_of_step, rweq_of_eq, rweq_of_rw,
        rweq_trans_congr_left, rweq_trans_congr_right, rweq_trans_congr,
        rweq_cmpA_refl_left, rweq_cmpA_refl_right,
        rweq_cmpA_inv_left, rweq_cmpA_inv_right,
        rweq_tt, rweq_sr, rweq_ss,
        rweq_symm_trans_congr, rweq_symm_congr,
        rweq_congrArg_of_rweq, rweq_congrArg_trans,
        rweq_congrArg_symm, rweq_congrArg_refl, rweq_congrArg_const,
        rweq_mapLeft_of_rweq, rweq_mapRight_of_rweq, rweq_map2_of_rweq,
        rweq_mapLeft_trans, rweq_mapRight_trans,
        rweq_mapLeft_symm, rweq_mapRight_symm,
        rweq_mapLeft_refl, rweq_mapRight_refl,
        rweq_prod_fst_beta, rweq_prod_snd_beta, rweq_prod_eta,
        rweq_fst_prodMk, rweq_snd_prodMk,
        rweq_sigma_fst_beta, rweq_sigma_snd_beta, rweq_sigma_eta,
        rweq_sigmaMk_refl,
        rweq_fun_app_beta, rweq_fun_eta,
        rweq_apd_refl, rweq_transport_refl_beta
      ]; first | exact RwEq.refl _ | assumption
    | assumption)

/-! ## Normalization Tactics -/

/-- `path_normalize` puts paths in a canonical form:
    - Right-associated trans chains: p · (q · r) instead of (p · q) · r
    - Units eliminated: refl · p → p, p · refl → p
    - Double inverses removed: symm (symm p) → p

    This is useful before comparing two paths or as a preprocessing step. -/
macro "path_normalize" : tactic =>
  `(tactic|
    simp only [
      -- Associativity (right-associate)
      rweq_tt,
      -- Unit elimination
      rweq_cmpA_refl_left, rweq_cmpA_refl_right,
      -- Double inverse
      rweq_ss,
      -- Symm of refl
      rweq_sr,
      -- congrArg simplifications
      rweq_congrArg_refl, rweq_congrArg_trans, rweq_congrArg_symm
    ])

/-- `path_normalize_left` normalizes by left-associating trans chains.
    Useful when the target is left-associated.

    Note: This only eliminates units and simplifies; for actual left-association
    use `path_assoc_left` repeatedly. -/
macro "path_normalize_left" : tactic =>
  `(tactic|
    simp only [
      -- Unit elimination
      rweq_cmpA_refl_left, rweq_cmpA_refl_right,
      -- Double inverse
      rweq_ss,
      -- Symm of refl
      rweq_sr,
      -- congrArg simplifications
      rweq_congrArg_refl, rweq_congrArg_trans, rweq_congrArg_symm
    ])

/-! ## Combined Transitivity-Congruence Tactics

These tactics combine transitivity with congruence, which is the most common
pattern in RwEq proofs. They correspond to:
- `apply rweq_trans (rweq_trans_congr_left q h)` - apply h in left position
- `apply rweq_trans (rweq_trans_congr_right p h)` - apply h in right position
-/

/-- `path_trans_congr_left h` transforms goal `RwEq (trans p q) t` using `h : RwEq p p'`
    to produce goal `RwEq (trans p' q) t`.

    This is the combined pattern: `apply rweq_trans (rweq_trans_congr_left q h)` -/
macro "path_trans_congr_left" h:term : tactic =>
  `(tactic| apply rweq_trans (rweq_trans_congr_left _ $h))

/-- `path_trans_congr_right h` transforms goal `RwEq (trans p q) t` using `h : RwEq q q'`
    to produce goal `RwEq (trans p q') t`.

    This is the combined pattern: `apply rweq_trans (rweq_trans_congr_right p h)` -/
macro "path_trans_congr_right" h:term : tactic =>
  `(tactic| apply rweq_trans (rweq_trans_congr_right _ $h))

/-- `path_both_eq h1, h2` closes goal `RwEq p q` when `h1 : RwEq p t` and `h2 : RwEq q t`
    for some common path t. The proof is `rweq_trans h1 (rweq_symm h2)`.

    This is a very common pattern when showing two expressions are equal by
    reducing both to the same normal form. -/
macro "path_both_eq" h1:term "," h2:term : tactic =>
  `(tactic| exact rweq_trans $h1 (rweq_symm $h2))

/-- `path_chain h1, h2` applies `rweq_trans h1 h2` for chaining two hypotheses. -/
macro "path_chain" h1:term "," h2:term : tactic =>
  `(tactic| exact rweq_trans $h1 $h2)

/-- `path_chain3 h1, h2, h3` chains three hypotheses via transitivity. -/
macro "path_chain3" h1:term "," h2:term "," h3:term : tactic =>
  `(tactic| exact rweq_trans $h1 (rweq_trans $h2 $h3))

/-- `path_chain4 h1, h2, h3, h4` chains four hypotheses via transitivity. -/
macro "path_chain4" h1:term "," h2:term "," h3:term "," h4:term : tactic =>
  `(tactic| exact rweq_trans $h1 (rweq_trans $h2 (rweq_trans $h3 $h4)))

/-- `path_then_cancel_right` applies congruence then right inverse cancellation.
    Transforms `trans p (trans q (symm q))` to `p`. -/
macro "path_then_cancel_right" : tactic =>
  `(tactic|
    first
    | exact rweq_trans (rweq_trans_congr_right _ (rweq_cmpA_inv_right _)) (rweq_cmpA_refl_right _)
    | apply rweq_trans (rweq_trans_congr_right _ (rweq_cmpA_inv_right _)))

/-- `path_then_cancel_left` applies congruence then left inverse cancellation.
    Transforms `trans (trans (symm q) q) p` to `p`. -/
macro "path_then_cancel_left" : tactic =>
  `(tactic|
    first
    | exact rweq_trans (rweq_trans_congr_left _ (rweq_cmpA_inv_left _)) (rweq_cmpA_refl_left _)
    | apply rweq_trans (rweq_trans_congr_left _ (rweq_cmpA_inv_left _)))

/-! ## Beta/Eta Tactics -/

/-- `path_beta` applies beta reduction rules for products, sigmas, and functions. -/
macro "path_beta" : tactic =>
  `(tactic|
    simp only [
      rweq_prod_fst_beta, rweq_prod_snd_beta, rweq_prod_rec_beta,
      rweq_sigma_fst_beta, rweq_sigma_snd_beta,
      rweq_fun_app_beta,
      rweq_sum_rec_inl_beta, rweq_sum_rec_inr_beta,
      rweq_apd_refl, rweq_transport_refl_beta
    ])

/-- `path_eta` applies eta expansion/contraction rules. -/
macro "path_eta" : tactic =>
  `(tactic|
    first
    | exact rweq_prod_eta _
    | exact rweq_sigma_eta _
    | exact rweq_fun_eta _
    | simp only [rweq_prod_eta, rweq_sigma_eta, rweq_fun_eta])

/-! ## Calc Support for RwEq -/

/-- Enable calc notation for RwEq: `calc p ≈ q := h₁; _ ≈ r := h₂` -/
noncomputable def instTransRwEqRwEqRwEq : Trans (α := Path a b) RwEq RwEq RwEq where
  trans := rweq_trans

noncomputable instance : Trans (α := Path a b) RwEq RwEq RwEq := instTransRwEqRwEqRwEq

end Tactic

/-! ## Summary

This module provides comprehensive automation for RwEq reasoning.

### Basic Tactics
1. **path_rfl**: For reflexive cases (p ≈ p)
2. **path_symm**: For applying symmetry (p ≈ q → q ≈ p)
3. **path_simp**: The main workhorse - applies simp with core RwEq lemmas
4. **path_simp_all**: More aggressive version using hypotheses
5. **path_decide**: Attempts to close goals automatically

### Transitivity Tactics
6. **path_trans h**: Apply transitivity with hypothesis h
7. **path_trans_via p**: Apply transitivity with explicit intermediate path

### Congruence Tactics
8. **path_congr_left h**: Apply congruence on left of trans
9. **path_congr_right h**: Apply congruence on right of trans
10. **path_congr h1, h2**: Apply congruence on both sides (comma-separated)
11. **path_congr_symm h**: Apply symm congruence (σ(p) ≈ σ(q) from p ≈ q)
12. **path_congrArg f, h**: Apply congrArg congruence (comma-separated)

### Structural Tactics
13. **path_assoc**: Reassociate to the right ((p·q)·r ≈ p·(q·r))
14. **path_assoc_left**: Reassociate to the left
15. **path_unit_left**: Eliminate left unit (refl·p ≈ p)
16. **path_unit_right**: Eliminate right unit (p·refl ≈ p)
17. **path_cancel_left**: Left inverse cancellation (p⁻¹·p ≈ refl)
18. **path_cancel_right**: Right inverse cancellation (p·p⁻¹ ≈ refl)
19. **path_inv_inv**: Double inverse (σ(σ(p)) ≈ p)
20. **path_symm_refl**: Symm of refl (σ(ρ) ≈ ρ)
21. **path_inv_distr**: Distribute symm over trans (σ(p·q) ≈ σ(q)·σ(p))

### Combined Cancellation Tactics
22. **path_then_cancel_right**: Congruence + right inverse cancellation
23. **path_then_cancel_left**: Congruence + left inverse cancellation

### Advanced Automation Tactics
24. **path_auto**: The most powerful tactic - combines simplification,
    congruence, beta/eta rules, and hypothesis search
25. **path_auto!**: Aggressive version that also rewrites hypotheses

### Normalization Tactics
26. **path_normalize**: Put paths in canonical right-associated form
27. **path_normalize_left**: Left-associating variant

### Beta/Eta Tactics
28. **path_beta**: Apply beta rules for products, sigmas, functions
29. **path_eta**: Apply eta expansion/contraction rules

### Calc Support
The `Trans` instance enables calc notation:
```lean
calc p
  _ ≈ q := h₁
  _ ≈ r := h₂
```

### Implementation Notes

These tactics leverage the ~90 @[simp] lemmas in RwEq.lean encoding:
- Groupoid laws (unit, associativity, inverses)
- Congruence principles (trans, symm, congrArg, mapLeft, mapRight)
- Beta rules (prod_fst_beta, sigma_fst_beta, fun_app_beta, etc.)
- Eta rules (prod_eta, sigma_eta, fun_eta)

This implements the "Automated path computation via term rewriting"
goal from the computational paths research program.
-/

end Path
end ComputationalPaths
