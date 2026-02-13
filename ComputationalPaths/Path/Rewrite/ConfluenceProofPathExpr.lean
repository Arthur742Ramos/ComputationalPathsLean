/-
# Confluence for PathExpr rewrites (evaluated)

This module packages the PathExpr confluence proof to produce Path-level join
witnesses after evaluation. It extends the raw `eval_join_of_rw` interface with
derived lemmas about symmetry, determinism, and interactions with normalization.

## Key Results

- `confluence_eval`: join at the Path level from PathExpr rewrites
- `confluence_eval_of_steps`: join from single steps
- `confluence_eval_refl`: reflexive chains yield reflexive joins
- `confluence_eval_symm`: symmetry of evaluated joins
- `eval_rw_preserves_toEq`: all rewriting preserves propositional equality
- `eval_rw_path_witness`: Path witness that rewriting preserves identity
- `eval_deterministic`: any two rewrite chains from the same source agree

## References

- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
- Bezem et al., "Machine Checked Confluence"
-/

import ComputationalPaths.Path.Rewrite.PathExprConfluence

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceProofPathExpr

universe u

/-! ## Core confluence evaluation -/

/-- Join at the Path level from two PathExpr rewrite chains. -/
def confluence_eval
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : PathExpr.Rw p q) (hr : PathExpr.Rw p r) :
    Confluence.Join (A := A) (a := a) (b := b) (PathExpr.eval q) (PathExpr.eval r) := by
  have hpq : p = q := (PathExpr.rw_eq_source hq).symm
  have hpr : p = r := (PathExpr.rw_eq_source hr).symm
  have hqr : q = r := hpq.symm.trans hpr
  cases hqr
  exact Confluence.join_refl (PathExpr.eval q)

/-- Join at the Path level from two single-step PathExpr rewrites. -/
def confluence_eval_of_steps
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : PathExpr.Step p q) (_hr : PathExpr.Step p r) :
    Confluence.Join (A := A) (a := a) (b := b) (PathExpr.eval q) (PathExpr.eval r) := by
  cases hq

/-! ## Reflexive chains -/

/-- A reflexive rewrite chain produces a reflexive join. -/
def confluence_eval_refl
    {A : Type u} {a b : A}
    (p : PathExpr (A := A) (a := a) (b := b)) :
    Confluence.Join (A := A) (a := a) (b := b) (PathExpr.eval p) (PathExpr.eval p) :=
  Confluence.join_refl (PathExpr.eval p)

/-! ## Symmetry of evaluated joins -/

/-- Evaluated join data can be swapped. -/
def confluence_eval_symm
    {A : Type u} {a b : A}
    {p q : Path a b}
    (J : Confluence.Join (A := A) (a := a) (b := b) p q) :
    Confluence.Join (A := A) (a := a) (b := b) q p :=
  { meet := J.meet, left := J.right, right := J.left }

/-! ## Rewriting preserves propositional equality -/

/-- Every PathExpr Rw chain preserves the propositional equality witness. -/
theorem eval_rw_preserves_toEq
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Rw p q) :
    (PathExpr.eval p).toEq = (PathExpr.eval q).toEq := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  rw [this]

/-- Path witness that eval is invariant under rewriting. -/
def eval_rw_path_witness
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Rw p q) :
    Path (PathExpr.eval p) (PathExpr.eval q) := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  cases this
  exact Path.refl (PathExpr.eval p)

/-! ## Determinism of rewriting -/

/-- Any two rewrite chains from the same source produce equal evaluations. -/
theorem eval_deterministic
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : PathExpr.Rw p q) (hr : PathExpr.Rw p r) :
    PathExpr.eval q = PathExpr.eval r := by
  have hq' : q = p := PathExpr.rw_eq_source hq
  have hr' : r = p := PathExpr.rw_eq_source hr
  rw [hq', hr']

/-- Path witness for determinism. -/
def eval_deterministic_path
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : PathExpr.Rw p q) (hr : PathExpr.Rw p r) :
    Path (PathExpr.eval q) (PathExpr.eval r) :=
  Path.ofEq (eval_deterministic hq hr)

/-! ## Step determinism -/

/-- Any two single steps from the same source produce the same result. -/
theorem step_deterministic
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : PathExpr.Step p q) (_hr : PathExpr.Step p r) :
    q = r := by
  cases hq

/-- Eval of a step target equals eval of the source. -/
theorem eval_step_eq
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Step p q) :
    PathExpr.eval q = PathExpr.eval p := by
  cases h

/-! ## Interactions with PathExpr constructors -/

/-- Rewriting the body of a symm preserves eval. -/
theorem eval_symm_rw
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Rw p q) :
    Path.symm (PathExpr.eval p) = Path.symm (PathExpr.eval q) := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  rw [this]

/-- Path witness for symm of rewritten expression. -/
def eval_symm_rw_path
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Rw p q) :
    Path (Path.symm (PathExpr.eval p)) (Path.symm (PathExpr.eval q)) := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  cases this
  exact Path.refl (Path.symm (PathExpr.eval p))

/-- Rewriting on the left component of a trans preserves eval. -/
theorem eval_trans_rw_left
    {A : Type u} {a b c : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (r : PathExpr (A := A) (a := b) (b := c))
    (h : PathExpr.Rw p q) :
    Path.trans (PathExpr.eval p) (PathExpr.eval r) =
      Path.trans (PathExpr.eval q) (PathExpr.eval r) := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  rw [this]

/-- Rewriting on the right component of a trans preserves eval. -/
theorem eval_trans_rw_right
    {A : Type u} {a b c : A}
    (p : PathExpr (A := A) (a := a) (b := b))
    {q r : PathExpr (A := A) (a := b) (b := c)}
    (h : PathExpr.Rw q r) :
    Path.trans (PathExpr.eval p) (PathExpr.eval q) =
      Path.trans (PathExpr.eval p) (PathExpr.eval r) := by
  have : q = r := (PathExpr.rw_eq_source h).symm
  rw [this]

/-- Path witness for left rewriting in trans. -/
def eval_trans_rw_left_path
    {A : Type u} {a b c : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (r : PathExpr (A := A) (a := b) (b := c))
    (h : PathExpr.Rw p q) :
    Path (Path.trans (PathExpr.eval p) (PathExpr.eval r))
         (Path.trans (PathExpr.eval q) (PathExpr.eval r)) :=
  Path.ofEq (eval_trans_rw_left r h)

/-- Path witness for right rewriting in trans. -/
def eval_trans_rw_right_path
    {A : Type u} {a b c : A}
    (p : PathExpr (A := A) (a := a) (b := b))
    {q r : PathExpr (A := A) (a := b) (b := c)}
    (h : PathExpr.Rw q r) :
    Path (Path.trans (PathExpr.eval p) (PathExpr.eval q))
         (Path.trans (PathExpr.eval p) (PathExpr.eval r)) :=
  Path.ofEq (eval_trans_rw_right p h)

/-! ## Normal form agreement -/

/-- Rewriting preserves normalization of eval. -/
theorem eval_rw_normalize_eq
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Rw p q) :
    normalize (PathExpr.eval p) = normalize (PathExpr.eval q) := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  rw [this]

/-- Path witness for normal form agreement. -/
def eval_rw_normalize_path
    {A : Type u} {a b : A}
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : PathExpr.Rw p q) :
    Path (normalize (PathExpr.eval p)) (normalize (PathExpr.eval q)) := by
  have : p = q := (PathExpr.rw_eq_source h).symm
  cases this
  exact Path.refl _

/-! ## Summary -/

/-!
This module provides the evaluated confluence interface for PathExpr rewrites:
1. `confluence_eval` / `confluence_eval_of_steps`: basic join production
2. `confluence_eval_refl` / `confluence_eval_symm`: structural combinators
3. `eval_deterministic`: all rewrite chains from the same source agree
4. `eval_rw_path_witness`: Path-level evidence of evaluation invariance
5. `eval_symm_rw_path` / `eval_trans_rw_*`: interactions with constructors
-/

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ConfluenceProofPathExpr
end Rewrite
end Path
end ComputationalPaths
