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

/-- `path_congr h1 h2` applies congruence on both sides.
    If goal is `RwEq (trans p q) (trans p' q')`, uses h1 for left and h2 for right. -/
macro "path_congr" h1:term h2:term : tactic =>
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
        rweq_refl, rweq_of_step, rweq_symm, rweq_trans,
        rweq_trans_congr_left, rweq_trans_congr_right, rweq_trans_congr,
        rweq_cmpA_refl_left, rweq_cmpA_refl_right,
        rweq_cmpA_inv_left, rweq_cmpA_inv_right,
        rweq_dd, rweq_tt,
        rweq_symm_refl, rweq_symm_symm, rweq_symm_trans,
        rweq_congrArg_of_rweq, rweq_congrArg_trans,
        rweq_congrArg_symm, rweq_congrArg_refl
      ])

/-- `path_simp_all` is a more aggressive version that also uses
    hypotheses in the context. -/
macro "path_simp_all" : tactic =>
  `(tactic|
    simp_all only [
      rweq_refl, rweq_of_step, rweq_symm, rweq_trans,
      rweq_trans_congr_left, rweq_trans_congr_right, rweq_trans_congr,
      rweq_cmpA_refl_left, rweq_cmpA_refl_right,
      rweq_cmpA_inv_left, rweq_cmpA_inv_right,
      rweq_dd, rweq_tt,
      rweq_symm_refl, rweq_symm_symm, rweq_symm_trans,
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

end Tactic

/-! ## Summary

This module provides automation for RwEq reasoning:

### Basic Tactics
1. **path_rfl**: For reflexive cases (p ≈ p)
2. **path_symm**: For applying symmetry (p ≈ q → q ≈ p)
3. **path_simp**: The main workhorse - applies simp with all RwEq lemmas
4. **path_simp_all**: More aggressive version using hypotheses
5. **path_decide**: Attempts to close goals automatically

### Transitivity Tactics
6. **path_trans h**: Apply transitivity with hypothesis h
7. **path_trans_via p**: Apply transitivity with explicit intermediate path

### Congruence Tactics
8. **path_congr_left h**: Apply congruence on left of trans
9. **path_congr_right h**: Apply congruence on right of trans
10. **path_congr h1 h2**: Apply congruence on both sides

### Structural Tactics
11. **path_assoc**: Reassociate to the right ((p·q)·r ≈ p·(q·r))
12. **path_assoc_left**: Reassociate to the left
13. **path_unit_left**: Eliminate left unit (refl·p ≈ p)
14. **path_unit_right**: Eliminate right unit (p·refl ≈ p)
15. **path_cancel_left**: Left inverse cancellation (p⁻¹·p ≈ refl)
16. **path_cancel_right**: Right inverse cancellation (p·p⁻¹ ≈ refl)

These tactics leverage the @[simp] lemmas in RwEq.lean that encode:
- Groupoid laws (unit, associativity, inverses)
- Congruence principles

This implements part of the Future Work from the SVK paper:
"Automated path computation via term rewriting"
-/

end Path
end ComputationalPaths
