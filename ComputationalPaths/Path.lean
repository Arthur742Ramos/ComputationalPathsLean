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
import ComputationalPaths.Path.Rewrite.PathTactic
import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.Bicategory
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.LoopIteration
import ComputationalPaths.Path.Homotopy.IntArith
import ComputationalPaths.Path.Homotopy.HigherHomotopy
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.Fibration
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.EilenbergMacLane
import ComputationalPaths.Path.Homotopy.FreudenthalSuspension
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup
import ComputationalPaths.Path.Homotopy.HigherProductHomotopy
import ComputationalPaths.Path.Homotopy.LieGroups
import ComputationalPaths.Path.Homotopy.Hurewicz
import ComputationalPaths.Path.Homotopy.CoveringClassification
import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.CircleStep
import ComputationalPaths.Path.Homotopy.HoTT
import ComputationalPaths.Path.HIT.Torus
import ComputationalPaths.Path.HIT.Cylinder
import ComputationalPaths.Path.HIT.MobiusBand
import ComputationalPaths.Path.HIT.KleinBottle
import ComputationalPaths.Path.HIT.KleinBottleSVK
import ComputationalPaths.Path.HIT.ProjectivePlane
import ComputationalPaths.Path.HIT.ProjectivePlaneSVK
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths
import ComputationalPaths.Path.HIT.PushoutPathsInstances
import ComputationalPaths.Path.HIT.FigureEight
import ComputationalPaths.Path.HIT.BouquetN
import ComputationalPaths.Path.HIT.Sphere
import ComputationalPaths.Path.HIT.HopfFibration
import ComputationalPaths.Path.HIT.Pi2Sphere
import ComputationalPaths.Path.HIT.Pi3Sphere
import ComputationalPaths.Path.HIT.Pi4S3
import ComputationalPaths.Path.HIT.QuaternionicHopf
import ComputationalPaths.Path.HIT.OrientableSurface
import ComputationalPaths.Path.HIT.TorusGenus1
import ComputationalPaths.Path.OmegaGroupoid
