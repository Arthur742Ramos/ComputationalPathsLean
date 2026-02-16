/-
# Confluence transfer for PathExpr

This module lifts PathExpr confluence results to Path-level joins by evaluating
expression rewrites back into computational paths. It provides the core
`eval_join_of_rw` combinator along with derived structural lemmas, congruence
properties, and interactions with the `normalize` function.

## Key Results

- `eval_join_of_rw`: lift PathExpr confluence to Path-level join
- `eval_join_of_steps`: lift single-step confluence to Path-level join
- `eval_join_of_refl`: trivial join for reflexive chains
- `eval_join_symm`: swap components of Path-level join
- `eval_join_rweq`: two chain targets are RwEq
- `eval_preserves_rw`: rewriting preserves evaluation
- `eval_join_normalize_agree`: joined paths have the same normal form
- Various eval identity lemmas for PathExpr constructors

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Rewrite.PathExpr
import ComputationalPaths.Path.Rewrite.ExprConfluence
import ComputationalPaths.Path.Rewrite.Confluence
import ComputationalPaths.Path.Rewrite.Normalization
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace PathExpr

open Confluence

universe u

/-! ## Core lift combinator -/

/-- Lift a PathExpr `Join` to a `Confluence.Join` at the Path level.

In the minimal core every `Rw` chain is trivial (source = target), so
we can produce the Path-level join by using the expression-level equality. -/
noncomputable def eval_join_of_expr_join
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (J : PathExpr.Join (A := A) (a := a) (b := b) p q) :
    Confluence.Join (A := A) (a := a) (b := b) (eval p) (eval q) := by
  have hpq : p = q := PathExpr.join_eq J
  cases hpq
  exact Confluence.join_refl (eval p)

/-- Lift PathExpr confluence to a Path-level join via evaluation. -/
noncomputable def eval_join_of_rw [HasJoinOfRwExpr.{u}]
    {A : Type u} {a b : A}
    {p q r : PathExpr A a b}
    (hq : Rw p q) (hr : Rw p r) :
    Confluence.Join (A := A) (a := a) (b := b) (eval q) (eval r) := by
  have J := HasJoinOfRwExpr.join_of_rw (A := A) (a := a) (b := b) hq hr
  exact eval_join_of_expr_join J

/-- Lift single-step PathExpr confluence to a Path-level join. -/
noncomputable def eval_join_of_steps [HasJoinOfRwExpr.{u}]
    {A : Type u} {a b : A}
    {p q r : PathExpr A a b}
    (hq : Step p q) (hr : Step p r) :
    Confluence.Join (A := A) (a := a) (b := b) (eval q) (eval r) :=
  eval_join_of_rw (A := A) (a := a) (b := b)
    (hq := rw_of_step hq) (hr := rw_of_step hr)

/-! ## Trivial join -/

/-- Reflexive chains produce a reflexive join. -/
def eval_join_of_refl
    {A : Type u} {a b : A}
    (p : PathExpr A a b) :
    Confluence.Join (A := A) (a := a) (b := b) (eval p) (eval p) :=
  Confluence.join_refl (eval p)

/-! ## Symmetry -/

/-- The Path-level join is symmetric. -/
def eval_join_symm
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    Confluence.Join (A := A) (a := a) (b := b) q p :=
  { meet := J.meet, left := J.right, right := J.left }

/-! ## Join implies RwEq -/

/-- Two paths that are joined are RwEq. -/
def eval_join_rweq
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    RwEq p q :=
  J.rweq

/-! ## Join implies propositional equality -/

/-- Joined paths witness the same propositional equality. -/
theorem eval_join_toEq
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    p.toEq = q.toEq :=
  rweq_toEq J.rweq

/-! ## Eval preservation under rewriting -/

/-- Rewriting (in the trivial core) preserves the eval. -/
theorem eval_preserves_rw
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) :
    eval p = eval q := by
  have : p = q := rw_eq_source h
  rw [this]

/-- Path witness for eval preservation under rewriting. -/
def eval_preserves_rw_path
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) :
    Path (eval p) (eval q) := by
  have : p = q := rw_eq_source h
  cases this
  exact Path.refl (eval p)

/-! ## Normalization interactions -/

/-- Normal forms agree for expressions related by Rw. -/
theorem eval_rw_normalize_agree
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) :
    ComputationalPaths.Path.normalize (eval p) = ComputationalPaths.Path.normalize (eval q) := by
  have : p = q := rw_eq_source h
  rw [this]

/-- Path witness that normalized evaluations agree. -/
def eval_rw_normalize_path
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) :
    Path (ComputationalPaths.Path.normalize (eval p)) (ComputationalPaths.Path.normalize (eval q)) := by
  have : p = q := rw_eq_source h
  cases this
  exact Path.refl _

/-- Joined paths have the same normal form. -/
theorem eval_join_normalize_agree
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    ComputationalPaths.Path.normalize p = ComputationalPaths.Path.normalize q :=
  normalize_of_rweq J.rweq

/-- Path witness for normal form agreement. -/
def eval_join_normalize_path
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    Path (ComputationalPaths.Path.normalize p) (ComputationalPaths.Path.normalize q) :=
  Path.stepChain (eval_join_normalize_agree J)

/-! ## Quotient compatibility -/

/-- Joined paths descend to the same quotient class. -/
theorem eval_join_quot_eq
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    (Quot.mk _ p : PathRwQuot A a b) = Quot.mk _ q :=
  J.quot_eq

/-! ## PathExpr eval identities -/

/-- Eval of refl expression is Path.refl. -/
theorem eval_refl_eq (A : Type u) (a : A) :
    eval (PathExpr.refl a) = Path.refl a := by
  simp [eval]

/-- Eval of atom expression is the wrapped path. -/
theorem eval_atom_eq {A : Type u} {a b : A} (p : Path a b) :
    eval (PathExpr.atom p) = p := by
  simp [eval]

/-- Eval of symm expression. -/
theorem eval_symm_eq {A : Type u} {a b : A}
    (p : PathExpr A a b) :
    eval (PathExpr.symm p) = Path.symm (eval p) := by
  simp [eval]

/-- Eval of trans expression. -/
theorem eval_trans_eq {A : Type u} {a b c : A}
    (p : PathExpr A a b)
    (q : PathExpr A b c) :
    eval (PathExpr.trans p q) = Path.trans (eval p) (eval q) := by
  simp [eval]

/-! ## Complexity agrees with size -/

/-- Complexity is defined as size. -/
theorem complexity_eq_size {A : Type u} {a b : A}
    (p : PathExpr A a b) :
    complexity p = size p := rfl

/-! ## Eval toEq preservation -/

/-- Rewriting preserves the propositional equality under eval. -/
theorem eval_rw_toEq
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Rw p q) :
    (eval p).toEq = (eval q).toEq := by
  have : p = q := rw_eq_source h
  rw [this]

/-- Steps preserve the propositional equality under eval. -/
theorem eval_step_toEq
    {A : Type u} {a b : A}
    {p q : PathExpr A a b}
    (h : Step p q) :
    (eval p).toEq = (eval q).toEq := by
  cases h

/-! ## Summary

This module provides the core transfer from PathExpr-level confluence to
Path-level joins, along with interactions with normalization, quotients,
and the basic eval identities.
-/

end PathExpr
end Rewrite
end Path
end ComputationalPaths
