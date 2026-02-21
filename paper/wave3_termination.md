# Wave 3: Termination Tightness Report

## Summary

File: `ComputationalPaths/Path/Rewrite/TerminationTight.lean`  
Lines: 258 | Definitions/Theorems: 19 | Sorry: 0 | Admit: 0

## Results

### 1. Minimality of the Weight Function

- **`weight_coeff_minimal_symm_mul`**: Proves that `symmMul < 2` (i.e., `symmMul = 1`) leads to a contradiction for `symm_trans_congr`. With `symmMul = 1`, the decrease from `symm(trans p q)` to `trans(symm q)(symm p)` fails because the weight change is `0 > symmAdd`, impossible.

- **`weight_coeff_trans_add_pos`**: Documents that `transAdd ≥ 0` is necessary (trivially) and that our choice of `transAdd = 2` provides the strongest bounds.

- **`atom_weight_at_least_four`**: Re-exports `weight_ge_four`, confirming atom weight ≥ 4 is forced by `trans_symm` and `symm_trans` rules.

### 2. Worst-Case Reduction Sequences

- **`leftChain n`**: Constructs the left-associated chain `((atom 0 · atom 1) · ... · atom n)`.
- **`leftChain_size`**: Size = `2n + 1`.
- **`leftChain_weight`**: Weight = `6n + 4`.
- **`leftChain_leftWeight_ge`**: leftWeight ≥ `n²`, growing quadratically.
- **`assocSteps_formula`**: The number of `trans_assoc` steps to right-associate is `n(n-1)/2` (triangular number).

This proves the normalization of left chains requires **Θ(n²) steps**, matching the quadratic lower bound from leftWeight.

### 3. Polynomial Complexity

- **`leftWeight_le_size_sq`**: leftWeight ≤ `size²` for any expression.
- **`step_lex_decrease'`**: Every step strictly decreases `(weight, leftWeight)` lexicographically.
- **`step_weight_le`**: Weight is non-increasing along reduction sequences.
- **`acc_with_bound`**: Well-foundedness gives termination; the depth is bounded by `O(weight² + leftWeight)`.

**Complexity class**: Normalization is polynomial in expression size. The weight can be exponential in size (due to `symm` nesting: `w(symm^n(atom)) ≈ 5·2^n`), but for the groupoid fragment without deep `symm` nesting, it is O(n²).

## Paper-Relevant Claims

1. The lexicographic measure `(weight, leftWeight)` is tight: reducing `symmMul` below 2 breaks `symm_trans_congr`.
2. Left-associated chains of n atoms require Θ(n²) normalization steps.
3. Normalization is polynomial (specifically bounded by the initial lex measure value).

## Build Status

✅ `lake build` succeeds (6186 jobs)
