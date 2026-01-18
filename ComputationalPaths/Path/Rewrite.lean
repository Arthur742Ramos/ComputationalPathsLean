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
import ComputationalPaths.Path.Rewrite.PathExpr

/-!
  This file serves as an umbrella import for the modular rewrite system.
-/

