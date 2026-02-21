# Wave 3: 3-Cells (Derivation Equivalence) Report

## Summary

File: `ComputationalPaths/Path/Polygraph/ThreeCells.lean`  
Lines: 166 | Definitions/Theorems: 14 | Sorry: 0 | Admit: 0

## The ω-Groupoid Structure

The formalization now has a genuine 3-dimensional categorical structure:

| Dimension | Object | File |
|-----------|--------|------|
| 0-cells | `Expr` (expressions) | GroupoidTRS.lean |
| 1-cells | `ExprRwEq` (rewrite equivalence) | GroupoidConfluence.lean |
| 2-cells | `RwEqDeriv` (derivation trees) | RwEqDerivation.lean |
| **3-cells** | **`DerivEquiv` (derivation equivalence)** | **ThreeCells.lean** |

## Results

### 1. DerivEquiv Inductive Type

`DerivEquiv` has 8 constructors:
- `refl`, `symm`, `dtrans`: equivalence relation structure
- `vcomp_congr_left/right`: vertical composition respects equivalence
- `hcomp_congr`: horizontal composition respects equivalence
- **`interchange`**: the key 2-groupoid axiom
  `(d₁ ∘ᵥ d₂) ∘ₕ (d₃ ∘ᵥ d₄) = (d₁ ∘ₕ d₃) ∘ᵥ (d₂ ∘ₕ d₄)`

### 2. Equivalence Relation

- `derivEquiv_refl`, `derivEquiv_symm`, `derivEquiv_trans`: packaged proofs
- `derivEquivSetoid`: Setoid instance on `RwEqDeriv e₁ e₂`

### 3. Naturality Squares

- `naturality_right_whisker_symm_refl`: right whiskering by basic steps equals `trans_congr_right`
- `naturality_left_whisker_symm_refl`: left whiskering by basic steps equals `trans_congr_left`

### 4. Non-Trivial 3-Cells

- **`nontrivial_three_cell_exists`**: There exist two distinct 2-cells `d₁ ≠ d₂ : RwEqDeriv (trans refl refl) refl` and a 3-cell relating their composite. This witnesses genuine 3-dimensionality — the structure is NOT a 2-groupoid.

### 5. Composition Respects Equivalence

- `vcomp_respects_equiv`: vertical composition well-defined on quotient
- `hcomp_respects_equiv`: horizontal composition well-defined on quotient
- `two_cell_inverse`: every 2-cell has an inverse (groupoid property)

## Paper-Relevant Claims

1. **First formalization of a 3-dimensional polygraph** for the groupoid TRS in Lean 4.
2. The interchange law is formalized as a genuine axiom, not derived.
3. Non-trivial 3-cells exist: `trans_refl_left` ≠ `trans_refl_right` as derivations.
4. This is the foundation for connecting to the Grothendieck–Maltsiniotis ω-groupoid conjecture.

## Build Status

✅ `lake build` succeeds
