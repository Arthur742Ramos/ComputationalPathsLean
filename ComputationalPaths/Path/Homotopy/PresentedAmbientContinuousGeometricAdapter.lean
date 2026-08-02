import ComputationalPaths.Path.Homotopy.PresentedAmbientGeometricAdapter
import ComputationalPaths.Path.Homotopy.PresentedContinuousGeometricAdapter

/-!
# Continuous total paths in an ambient realization

When a presented realization is transported along an explicit homotopy
equivalence to an ambient topological space, the transported edge system is
also a continuous geometric step system: the combinatorial edge parameter is
discrete, and all endpoint/realization maps are therefore continuous.

This file exposes the transported raw paths in the total path carrier and
keeps their fundamental-groupoid arrows identified with the ambient adapter's
existing comparison map.
-/

namespace ComputationalPaths
namespace Path
namespace Presented
namespace Realization
namespace AmbientAdapter

open GeometricTopology
open scoped ContinuousMap Topology

universe u v

variable {G : Graph.{u, v}} (P : Presentation G)

/-- The transported presented edge system with the discrete edge topology. -/
noncomputable def continuousAmbientStepSystem
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    ContinuousGeometricStepSystem X
      (GeometricAdapter.EdgeStep G) where
  toGeometricStepSystem := ambientStepSystem P h
  continuous_src := continuous_of_discreteTopology
  continuous_tgt := continuous_of_discreteTopology
  continuous_realize := continuous_of_discreteTopology

/-- A raw presented path as a point of the transported total path space. -/
noncomputable def rawPathToAmbientTotal
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    {x y : G.Point} (p : RawPath G x y) :
    TotalOpenGeometricCompPath X
      (GeometricAdapter.EdgeStep G)
      (continuousAmbientStepSystem P h) :=
  ⟨_, _, by
    simpa [continuousAmbientStepSystem] using
      (rawPathToAmbientGeometric P h p)⟩

theorem rawPathToAmbientTotal_geometric
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    (p : RawPath G x y) :
    (rawPathToAmbientTotal P h p).geometricPath =
      (rawPathToAmbientGeometric P h p).geometric := by
  rfl

theorem rawPathToAmbientTotal_fundamentalArrow
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    (p : RawPath G x y) :
    TotalOpenGeometricCompPath.fundamentalArrow
        (continuousAmbientStepSystem P h) (rawPathToAmbientTotal P h p) =
      ambientGeometricArrow P h p := by
  rfl

/-! ## Specialized ambient certificates -/

noncomputable def continuousAmbientEvaluationCertificate
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    TotalOpenGeometricCompPath.TopologicalCompPathEvaluationCertificate
      (continuousAmbientStepSystem P h) :=
  TotalOpenGeometricCompPath.topologicalCompPathEvaluationCertificate
    (continuousAmbientStepSystem P h)

noncomputable def continuousAmbientFundamentalGroupoidCertificate
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    TotalOpenGeometricCompPath.TopologicalCompPathFundamentalGroupoidCertificate
      (continuousAmbientStepSystem P h) :=
  TotalOpenGeometricCompPath.topologicalCompPathFundamentalGroupoidCertificate
    (continuousAmbientStepSystem P h)

/-- Transporting the presentation through an ambient homotopy equivalence
preserves the complete unconditional quotient-compatible topological groupoid
certificate. -/
noncomputable def continuousAmbientTopologicalGroupoidCertificate
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X) :
    TotalOpenGeometricCompPath.UnconditionalTopologicalGroupoidCertificate
      (continuousAmbientStepSystem P h) :=
  TotalOpenGeometricCompPath.unconditionalTopologicalGroupoidCertificate
    (continuousAmbientStepSystem P h)

/-! Keep a multi-step computational witness in the ambient layer. -/
noncomputable def ambientTraceLoopCertificate
    {X : TopCat.{max u v}}
    (h : topologicalRealization P ≃ₕ X)
    (p : RawPath G x y) :
    ComputationalPaths.Path
      (GeometricTrace.traceLength (rawPathToAmbientTotal P h p).trace)
      (GeometricTrace.traceLength (rawPathToAmbientTotal P h p).trace) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl
      (GeometricTrace.traceLength (rawPathToAmbientTotal P h p).trace))
    (ComputationalPaths.Path.refl
      (GeometricTrace.traceLength (rawPathToAmbientTotal P h p).trace))

end AmbientAdapter
end Realization
end Presented
end Path
end ComputationalPaths
