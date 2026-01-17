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
import ComputationalPaths.Path.Rewrite.ConfluenceProof
import ComputationalPaths.Path.Rewrite.ConfluenceConstructive
import ComputationalPaths.Path.Rewrite.PathTactic
import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.GroupoidDerived
import ComputationalPaths.Path.PathAlgebraDerived
import ComputationalPaths.Path.ProductSigmaDerived
import ComputationalPaths.Path.TransportDerived
import ComputationalPaths.Path.StepDerived
import ComputationalPaths.Path.CoherenceDerived
import ComputationalPaths.Path.BiContextDerived
import ComputationalPaths.Path.LoopDerived
import ComputationalPaths.Path.Bicategory
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.LoopIteration
import ComputationalPaths.Path.Homotopy.IntArith
import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.HigherInducedMaps
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup
import ComputationalPaths.Path.Homotopy.HigherProductHomotopy
import ComputationalPaths.Path.Homotopy.LieGroups
import ComputationalPaths.Path.Homotopy.Hurewicz
import ComputationalPaths.Path.Homotopy.Sets
import ComputationalPaths.Path.Homotopy.Reflexivity
import ComputationalPaths.Path.Homotopy.IdentityType
import ComputationalPaths.Path.Homotopy.Coproduct
import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.CircleStep
import ComputationalPaths.Path.Homotopy.HoTT
import ComputationalPaths.Path.HIT.Torus
import ComputationalPaths.Path.HIT.TorusStep
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.HIT.FigureEight
import ComputationalPaths.Path.HIT.BouquetN
import ComputationalPaths.Path.HIT.Sphere
-- removed legacy assumption-heavy modules (Mobius/Lens/Hopf/Pi2/Pi3/CP/James/Freudenthal/Cellular)
import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.OmegaGroupoid.Derived
import ComputationalPaths.Path.OmegaGroupoid.StepToCanonical
import ComputationalPaths.Path.Algebra.Abelianization

