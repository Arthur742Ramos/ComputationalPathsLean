/-
# Rewriting system on computational paths

This module captures the fragment of the `rw`-rewrite system from the paper
concerned with symmetry and transitivity.  We provide the basic rewrite steps
and the reflexive/transitive closure `Rw`, together with its symmetric
reflexive/transitive closure `RwEq`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.LNDEQ
import ComputationalPaths.Path.Rewrite.Termination
import ComputationalPaths.Path.Rewrite.Confluence
import ComputationalPaths.Path.Rewrite.ConfluenceProof
import ComputationalPaths.Path.Rewrite.ConfluenceTerminationDerived
import ComputationalPaths.Path.Rewrite.Normalization
import ComputationalPaths.Path.Rewrite.NormalizationDerived
import ComputationalPaths.Path.Rewrite.PathNormalizationDecision
import ComputationalPaths.Path.Rewrite.PathExpr
import ComputationalPaths.Path.Rewrite.HigherRewriting
import ComputationalPaths.Path.Rewrite.ExprConfluence
import ComputationalPaths.Path.Rewrite.PathExprConfluence
import ComputationalPaths.Path.Rewrite.ConfluenceProofPathExpr

/-!
  This file serves as an umbrella import for the modular rewrite system.
-/
