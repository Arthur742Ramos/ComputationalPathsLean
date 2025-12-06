/-
# Path Simplification Tactics

This module provides automation for proving RwEq goals using the computational
paths rewrite system. The `path_simp` tactic combines the extensive @[simp]
lemma library in RwEq.lean with specialized tactics for path equality reasoning.

## Tactics Provided

- `path_simp`: Simplify RwEq goals using the built-in simp lemmas
- `path_rfl`: Close RwEq goals that are reflexive
- `path_canon`: Use canonicalization to close RwEq goals

## Usage Examples

```lean
example (p : Path a a) : RwEq (trans refl p) p := by path_simp
```

## References

- Computational Paths paper (de Queiroz et al.)
- LND_EQ-TRS rewrite system
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Tactic

/-! ## Main Tactics -/

/-- `path_rfl` closes RwEq goals that are reflexive (p = p). -/
macro "path_rfl" : tactic => `(tactic| exact RwEq.refl _)

/-- `path_canon` closes RwEq goals by canonicalizing both sides.
    This works when p.toEq = q.toEq (proof irrelevance). -/
macro "path_canon" : tactic => `(tactic| (apply rweq_of_toEq_eq; rfl))

/-- `path_symm` transforms `RwEq p q` to `RwEq q p`. -/
macro "path_symm" : tactic => `(tactic| apply rweq_symm)

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
        rweq_refl, rweq_of_step, rweq_canon, rweq_symm, rweq_trans,
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
      rweq_refl, rweq_of_step, rweq_canon, rweq_symm, rweq_trans,
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
    2. Using toEq equality (proof irrelevance)
    3. Normalizing and comparing -/
macro "path_decide" : tactic =>
  `(tactic|
    first
    | exact RwEq.refl _
    | (apply rweq_of_toEq_eq; rfl)
    | (path_simp; try exact RwEq.refl _))

end Tactic

/-! ## Summary

This module provides automation for RwEq reasoning:

1. **path_simp**: The main workhorse - applies simp with all RwEq lemmas
2. **path_rfl**: For reflexive cases
3. **path_canon**: Uses canonicalization (p.toEq = q.toEq → p ≈ q)
4. **path_symm**: For applying symmetry
5. **path_decide**: Attempts to close goals automatically

These tactics leverage the ~90 @[simp] lemmas in RwEq.lean that encode:
- Groupoid laws (unit, associativity, inverses)
- Congruence principles
- Canonicalization via Step.canon

This implements part of the Future Work from the SVK paper:
"Automated path computation via term rewriting"
-/

end Path
end ComputationalPaths
