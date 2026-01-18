/-
# Confluence transfer for PathExpr

This module lifts PathExpr confluence results to Path-level joins by evaluating
expression rewrites back into computational paths.
-/

import ComputationalPaths.Path.Rewrite.PathExpr
import ComputationalPaths.Path.Rewrite.ExprConfluence
import ComputationalPaths.Path.Rewrite.Confluence

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace PathExpr

open Confluence

universe u

noncomputable def eval_join_of_rw [HasJoinOfRwExpr.{u}]
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Rw p q) (hr : Rw p r) :
    Confluence.Join (A := A) (a := a) (b := b) (eval q) (eval r) := by
  classical
  obtain ⟨s, hq_s, hr_s⟩ :=
    (HasJoinOfRwExpr.join_of_rw (A := A) (a := a) (b := b) hq hr)
  exact { meet := s, left := hq_s, right := hr_s }

noncomputable def eval_join_of_steps [HasJoinOfRwExpr.{u}]
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Step p q) (hr : Step p r) :
    Confluence.Join (A := A) (a := a) (b := b) (eval q) (eval r) :=
  eval_join_of_rw (A := A) (a := a) (b := b)
    (hq := rw_of_step hq) (hr := rw_of_step hr)

end PathExpr
end Rewrite
end Path
end ComputationalPaths
