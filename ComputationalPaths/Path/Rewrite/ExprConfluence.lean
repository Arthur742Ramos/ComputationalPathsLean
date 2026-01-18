/-
# Confluence witnesses for PathExpr rewrites

This module packages the PathExpr confluence result into a reusable interface.
-/

import ComputationalPaths.Path.Rewrite.PathExpr

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace PathExpr

universe u

/-- Join data for two PathExpr rewrites. -/
class HasJoinOfRwExpr.{v} : Prop where
  join_of_rw {A : Type v} {a b : A}
      {p q r : PathExpr (A := A) (a := a) (b := b)}
      (hq : Rw p q) (hr : Rw p r) :
      Join (A := A) (a := a) (b := b) q r

noncomputable instance instHasJoinOfRwExpr : HasJoinOfRwExpr.{u} where
  join_of_rw := fun hq hr => confluence_of_local (A := _) (a := _) (b := _) hq hr

end PathExpr
end Rewrite
end Path
end ComputationalPaths
