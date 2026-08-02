import ComputationalPaths.Path.Topology.TopologicalCompPathGroupoidLaws
import ComputationalPaths.Path.Homotopy.PresentedGeometricAdapter

/-!
# Continuous total paths for presented computational path spaces

The presented SVK edge type is combinatorial, so its natural parameter-space
topology is discrete.  With that topology, the existing presented geometric
step system becomes a `ContinuousGeometricStepSystem`, and every recursively
realized presented raw path becomes a point of the total endpoint-varying
space constructed by the topology modules.

This is the bridge from the general phases to the paper's actual nerve
realization.  No new ambient-space hypothesis is introduced: the ambient
space remains the canonical topological realization of the presentation.
-/

namespace ComputationalPaths
namespace Path
namespace Presented
namespace Realization
namespace GeometricAdapter

open GeometricTopology
open scoped Topology

universe u v

variable {G : Graph.{u, v}} (P : Presentation G)

/-- Combinatorial presented edges carry the discrete step topology. -/
noncomputable instance edgeStepDiscreteTopology :
    TopologicalSpace (EdgeStep G) :=
  ⊥

noncomputable instance edgeStepDiscreteTopologyClass :
    DiscreteTopology (EdgeStep G) :=
  ⟨rfl⟩

/-- The presented edge system with its discrete parameter topology. -/
noncomputable def continuousPresentedStepSystem :
    ContinuousGeometricStepSystem
      (topologicalRealization P) (EdgeStep G) where
  toGeometricStepSystem := presentedStepSystem P
  continuous_src := continuous_of_discreteTopology
  continuous_tgt := continuous_of_discreteTopology
  continuous_realize := continuous_of_discreteTopology

/-- Every presented raw path is a point of the total computational-path
space, not just of an endpoint-indexed fibre. -/
noncomputable def rawPathToTotal
    {x y : G.Point} (p : RawPath G x y) :
    TotalOpenGeometricCompPath
      (topologicalRealization P) (EdgeStep G)
      (continuousPresentedStepSystem P) :=
  ⟨_, _, by
    simpa [continuousPresentedStepSystem] using
      (rawPathToGeometric P p)⟩

theorem rawPathToTotal_geometric (p : RawPath G x y) :
    (rawPathToTotal P p).geometricPath =
      (rawPathToGeometric P p).geometric := by
  rfl

theorem rawPathToTotal_fundamentalArrow (p : RawPath G x y) :
    TotalOpenGeometricCompPath.fundamentalArrow
        (continuousPresentedStepSystem P) (rawPathToTotal P p) =
      geometricArrow P p := by
  rfl

/-! ## Specialized certificates -/

noncomputable def continuousPresentedEvaluationCertificate :
    TotalOpenGeometricCompPath.TopologicalCompPathEvaluationCertificate
      (continuousPresentedStepSystem P) :=
  TotalOpenGeometricCompPath.topologicalCompPathEvaluationCertificate
    (continuousPresentedStepSystem P)

noncomputable def continuousPresentedFundamentalGroupoidCertificate :
    TotalOpenGeometricCompPath.TopologicalCompPathFundamentalGroupoidCertificate
      (continuousPresentedStepSystem P) :=
  TotalOpenGeometricCompPath.topologicalCompPathFundamentalGroupoidCertificate
    (continuousPresentedStepSystem P)

/-- The presented SVK realization carries the complete unconditional
quotient-compatible topological groupoid laws. -/
noncomputable def continuousPresentedTopologicalGroupoidCertificate :
    TotalOpenGeometricCompPath.UnconditionalTopologicalGroupoidCertificate
      (continuousPresentedStepSystem P) :=
  TotalOpenGeometricCompPath.unconditionalTopologicalGroupoidCertificate
    (continuousPresentedStepSystem P)

/-! Keep an explicit multi-step computational witness in the presented layer. -/
noncomputable def presentedTraceLoopCertificate (p : RawPath G x y) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (rawPathToTotal P p).trace)
      (GeometricTrace.traceLength (rawPathToTotal P p).trace) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl
      (GeometricTrace.traceLength (rawPathToTotal P p).trace))
    (ComputationalPaths.Path.refl
      (GeometricTrace.traceLength (rawPathToTotal P p).trace))

end GeometricAdapter
end Realization
end Presented
end Path
end ComputationalPaths
