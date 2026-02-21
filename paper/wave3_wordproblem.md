# Wave 3: Word Problem Decidability Report

## Summary

File: `ComputationalPaths/Path/Rewrite/WordProblem.lean`  
Lines: 118 | Definitions/Theorems: 11 | Sorry: 0 | Admit: 0

## Results

### 1. Decision Procedure

- **`decideExprRwEq`**: A computable `Bool`-valued function that decides `ExprRwEq` by comparing reduced word representations (`toRW`).

### 2. Correctness

- **`decideExprRwEq_spec`**: `decideExprRwEq e₁ e₂ = true ↔ ExprRwEq e₁ e₂`
  - Soundness: if procedure says yes → expressions are equivalent
  - Completeness: if equivalent → procedure says yes

- **`exprRwEq_decidable`**: `Decidable` instance for `ExprRwEq e₁ e₂`

### 3. Canonical Forms

- **`canon_eq_iff_exprRwEq`**: `canon e₁ = canon e₂ ↔ ExprRwEq e₁ e₂`
- **`canon_canon`**: Canonical form is idempotent: `canon(canon(e)) = canon(e)`

### 4. Separation Theorem

- **`exprRwEq_separation`**: If `toRW e₁ ≠ toRW e₂` then `¬ ExprRwEq e₁ e₂`
- **`atom_zero_ne_one`**: Concrete example: `atom 0` and `atom 1` are not equivalent
- **`atom_ne_refl`**: Concrete example: `atom 0` and `refl` are not equivalent

### 5. Algebraic Properties

- **`decideExprRwEq_symm'`**: Decision procedure respects symmetry
- **`exprRwEq_trans'`**: ExprRwEq is transitive
- **`exprRwEqSetoid`**: Full Setoid instance

### 6. Complexity Discussion

The decision procedure runs in O(n₁ + n₂) time:
- `toRW` traverses each expression once (O(n) with amortized O(n) for reduced word operations)
- Comparison of reduced words is O(min(k,l))

### 7. Full System: Undecidability Conjecture

For the full LNDEQ system with dependent types:
- **Conjecture**: Word problem is Σ₁⁰-complete
- **Evidence**: System can encode System F (Wells' undecidability result)

## Paper-Relevant Claims

1. The groupoid fragment word problem is **decidable in linear time**.
2. The decision procedure is **formally verified** sound and complete.
3. Concrete separation examples show the procedure correctly rejects non-equivalent terms.
4. The `Setoid` and `Decidable` instances make the quotient `Expr/ExprRwEq` a first-class Lean type.

## Build Status

✅ `lake build` succeeds
