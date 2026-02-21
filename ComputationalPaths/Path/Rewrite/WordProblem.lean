/-
# Word Problem Decidability for the Groupoid Fragment

The word problem for the groupoid rewriting system on `Expr` is decidable:
given two expressions `e₁ e₂ : Expr`, we can decide whether they are
rewrite-equivalent (`ExprRwEq e₁ e₂`).

## Strategy

The groupoid fragment is the free group on atoms. Two expressions are
equivalent iff their reduced word representations (`toRW`) are equal.
Since `toRW` is computable and reduced words have `DecidableEq`,
this gives a decision procedure.

## Main Results

1. `decideExprRwEq`: a decision procedure for `ExprRwEq`
2. `decideExprRwEq_spec`: soundness and completeness  
3. `exprRwEq_decidable`: `Decidable` instance
4. `exprRwEq_separation`: distinct normal forms → not equivalent

## References

- Magnus, Karrass & Solitar, "Combinatorial Group Theory"
-/

import ComputationalPaths.Path.Rewrite.GroupoidConfluence

namespace ComputationalPaths.Path.Rewrite.GroupoidConfluence

open GroupoidTRS

/-! ## The Decision Procedure -/

/-- Decision procedure for `ExprRwEq`: normalize both to reduced words. -/
def decideExprRwEq (e₁ e₂ : Expr) : Bool :=
  toRW e₁ == toRW e₂

/-- The decision procedure is sound and complete. -/
theorem decideExprRwEq_spec (e₁ e₂ : Expr) :
    decideExprRwEq e₁ e₂ = true ↔ ExprRwEq e₁ e₂ := by
  simp only [decideExprRwEq, beq_iff_eq]
  exact toRW_eq_iff_exprRwEq e₁ e₂

/-- `ExprRwEq` is decidable. -/
instance exprRwEq_decidable (e₁ e₂ : Expr) : Decidable (ExprRwEq e₁ e₂) := by
  rw [← toRW_eq_iff_exprRwEq]
  exact toRW_eq_decidable e₁ e₂

/-! ## Canonical form and uniqueness -/

/-- Two expressions have the same canonical form iff they are `ExprRwEq`. -/
theorem canon_eq_iff_exprRwEq (e₁ e₂ : Expr) :
    canon e₁ = canon e₂ ↔ ExprRwEq e₁ e₂ := by
  rw [← toRW_eq_iff_exprRwEq, ← canon_eq_iff_toRW_eq]

/-- Canonical forms are idempotent. -/
theorem canon_canon (e : Expr) : canon (canon e) = canon e := by
  -- canon e = rwToExpr (toRW e)
  -- canon (canon e) = rwToExpr (toRW (canon e))
  -- toRW (canon e) = toRW e  (by toRW_invariant_rtc and reach_canon)
  simp only [canon]
  congr 1
  exact (toRW_invariant_rtc (reach_canon e)).symm

/-! ## Separation theorem -/

/-- If two expressions have different reduced words, they are NOT equivalent.
    This is the separation half of the word problem. -/
theorem exprRwEq_separation (e₁ e₂ : Expr)
    (h : toRW e₁ ≠ toRW e₂) : ¬ ExprRwEq e₁ e₂ := by
  intro heq
  exact h (toRW_eq_of_exprRwEq heq)

/-- Concrete separation example: `atom 0` and `atom 1` are not equivalent. -/
theorem atom_zero_ne_one : ¬ ExprRwEq (.atom 0) (.atom 1) := by
  apply exprRwEq_separation
  simp [toRW]

/-- Concrete separation: `atom 0` and `refl` are not equivalent. -/
theorem atom_ne_refl : ¬ ExprRwEq (.atom 0) .refl := by
  apply exprRwEq_separation
  simp [toRW]

/-! ## Additional Word Problem Properties -/

/-- The word problem respects symmetry (via ExprRwEq). -/
theorem decideExprRwEq_symm' (e₁ e₂ : Expr)
    (h : decideExprRwEq e₁ e₂ = true) : decideExprRwEq e₂ e₁ = true := by
  rw [decideExprRwEq_spec] at h ⊢
  exact ExprRwEq.symm h

/-- Transitivity: if e₁ ~ e₂ and e₂ ~ e₃, then e₁ ~ e₃. -/
theorem exprRwEq_trans' {e₁ e₂ e₃ : Expr}
    (h₁ : ExprRwEq e₁ e₂) (h₂ : ExprRwEq e₂ e₃) :
    ExprRwEq e₁ e₃ :=
  ExprRwEq.trans h₁ h₂

/-- `ExprRwEq` is an equivalence relation (packaged as Setoid). -/
instance exprRwEqSetoid : Setoid Expr where
  r := ExprRwEq
  iseqv := ⟨ExprRwEq.refl, fun h => ExprRwEq.symm h, fun h₁ h₂ => ExprRwEq.trans h₁ h₂⟩

/-! ## The Full System: Undecidability Discussion

For the **full** computational paths system including β-reduction,
η-expansion, and dependent type formers, the word problem is expected
to be undecidable:

1. The system can encode System F (polymorphic λ-calculus)
2. Typechecking in System F is undecidable (Wells, 1999)  
3. The word problem for βη-equality subsumes typechecking

**Conjecture**: The word problem for the full LNDEQ system
extended with dependent types is Σ₁⁰-complete.
-/

end ComputationalPaths.Path.Rewrite.GroupoidConfluence
