/-
# Computational Paths infrastructure

This umbrella module gathers the submodules that formalise the notion of
computational paths, the rewrite system that relates them, and the higher
groupoid structure provided by identity types.
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
import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.Bicategory
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Homotopy.HoTT
import ComputationalPaths.Path.HIT.Torus
import ComputationalPaths.Path.HIT.Cylinder
import ComputationalPaths.Path.HIT.MobiusBand
import ComputationalPaths.Path.HIT.KleinBottle
import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.OmegaGroupoid
