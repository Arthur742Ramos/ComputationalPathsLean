/-
# Decision procedures for path normalization

This module packages decidability facts and complexity bounds for the
LND_EQ-TRS rewrite system. We record how canonical normalization makes
path equality decidable, quantify the complexity decrease in the core
PathExpr fragment, and connect the path-algebra word problem to π₁.

## Key Results

- `normalize_eq_of_toEq`: normal forms of parallel paths coincide
- `normalize_decidable`: decidability of normal form equality
- `rweq_decidable`: classical decidability of rewrite equality
- `expr_step_complexity_lt`: each PathExpr step lowers complexity (vacuous)
- `expr_terminating`: PathExpr rewriting is terminating
- `ExprWordProblem`: word problem for path expressions
- `expr_wordProblem_sound`: word problem implies path rewrite equality
- `piOne_eq_of_rweq`: rewrite-equivalent loops have equal π₁ classes
- `piOne_eq_of_expr_wordProblem`: expression word problem lifts to π₁

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- Newman, "On theories with a combinatorial definition of equivalence"
- Licata & Shulman, "Calculating the Fundamental Group of the Circle"
-/

import ComputationalPaths.Path.HigherPathInduction
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Normalization
import ComputationalPaths.Path.Rewrite.PathExpr
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Rewrite

universe u

/-! ## Normalization and decidability -/

variable {A : Type u} {a b : A}

/-- Normalization collapses to the canonical `ofEq` witness, so normal forms agree. -/
@[simp] theorem normalize_eq_of_toEq (p q : Path a b) :
    normalize (A := A) (a := a) (b := b) p =
      normalize (A := A) (a := a) (b := b) q := by
  simp [normalize]

/-- Equality of normal forms is decidable (in fact, always true). -/
def normalize_decidable (p q : Path a b) :
    Decidable (normalize (A := A) (a := a) (b := b) p =
      normalize (A := A) (a := a) (b := b) q) := by
  exact isTrue (normalize_eq_of_toEq (A := A) (a := a) (b := b) p q)

/-- Rewrite equality is classically decidable. -/
noncomputable def rweq_decidable (p q : Path a b) : Decidable (RwEqProp p q) := by
  classical
  exact inferInstance

/-! ## Complexity bounds for PathExpr normalization -/

/-- Every PathExpr step strictly lowers the complexity measure.
    (Vacuously true: `PathExpr.Step` has no constructors.) -/
theorem expr_step_complexity_lt
    {p q : PathExpr A a b} (h : PathExpr.Step p q) :
    PathExpr.complexity q < PathExpr.complexity p :=
  nomatch h

/-- The core PathExpr rewrite system is terminating (well-founded).
    (Immediate: `PathExpr.Step` is empty.) -/
theorem expr_terminating :
    WellFounded (fun q p : PathExpr A a b => PathExpr.Step p q) :=
  ⟨fun x => ⟨x, fun _ h => nomatch h⟩⟩

/-! ## Word problems and rewrite equality -/

/-- Word problem for path expressions: do two expressions rewrite to a common term? -/
def ExprWordProblem {A : Type u} {a b : A}
    (p q : PathExpr A a b) : Prop :=
  ∃ r, PathExpr.Rw p r ∧ PathExpr.Rw q r

/-- The expression word problem is classically decidable. -/
noncomputable def expr_wordProblem_decidable {A : Type u} {a b : A}
    {p q : PathExpr A a b} :
    Decidable (ExprWordProblem p q) := by
  classical
  exact inferInstance

/-- Joinable expressions are equal (since Step is empty). -/
private theorem expr_wordProblem_eq {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : ExprWordProblem p q) :
    p = q := by
  obtain ⟨r, hp, hq⟩ := h
  have h1 := PathExpr.rw_eq_source hp
  have h2 := PathExpr.rw_eq_source hq
  exact h1.symm.trans h2

/-- Joinable expressions yield rewrite equality after evaluation. -/
noncomputable def expr_wordProblem_sound {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : ExprWordProblem p q) :
    RwEq (PathExpr.eval p) (PathExpr.eval q) := by
  rw [expr_wordProblem_eq h]

/-! ## Word problem for groups via π₁ -/

/-- Rewrite-equivalent loops represent the same π₁ element. -/
noncomputable def piOne_eq_of_rweq {A : Type u} {a : A} {p q : LoopSpace A a}
    (h : RwEq p q) :
    PiOne.ofLoop (A := A) (a := a) p =
      PiOne.ofLoop (A := A) (a := a) q := by
  exact Quot.sound h

/-- The expression word problem for loops lifts to equality in π₁. -/
theorem piOne_eq_of_expr_wordProblem {A : Type u} {a : A}
    {p q : PathExpr A a a}
    (h : ExprWordProblem p q) :
    PiOne.ofLoop (A := A) (a := a) (PathExpr.eval p) =
      PiOne.ofLoop (A := A) (a := a) (PathExpr.eval q) :=
  piOne_eq_of_rweq (expr_wordProblem_sound h)

end Rewrite
end Path
end ComputationalPaths
