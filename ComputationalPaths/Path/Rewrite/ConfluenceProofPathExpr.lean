/-
# Confluence for PathExpr rewrites (evaluated)

This module packages the PathExpr confluence proof to produce Path-level join
witnesses after evaluation.
-/

import ComputationalPaths.Path.Rewrite.PathExprConfluence

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceProofPathExpr

open PathExpr

universe u

theorem confluence_eval
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Rw p q) (hr : Rw p r) :
    Confluence.Join (A := A) (a := a) (b := b) (eval q) (eval r) :=
  eval_join_of_rw (A := A) (a := a) (b := b) hq hr

theorem confluence_eval_of_steps
    {A : Type u} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Step p q) (hr : Step p r) :
    Confluence.Join (A := A) (a := a) (b := b) (eval q) (eval r) :=
  eval_join_of_steps (A := A) (a := a) (b := b) hq hr

end ConfluenceProofPathExpr
end Rewrite
end Path
end ComputationalPaths
