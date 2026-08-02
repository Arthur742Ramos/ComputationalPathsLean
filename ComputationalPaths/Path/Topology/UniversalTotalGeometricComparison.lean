import ComputationalPaths.Path.Topology.TopologicalCompPathEvaluation

/-!
# Universality of the total geometric computational-path space

For the maximal continuous step system, every ordinary Mathlib interval path
is represented by a single computational step.  This file proves both
endpointwise coverage and continuity of that single-step section into the
total carrier.

Thus the total construction is a genuine enlargement of the raw equality
space: it contains all continuous paths between arbitrary endpoints while
retaining explicit trace data.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped ContinuousMap Topology

universe u

namespace UniversalTotalGeometricComparison

variable {A : Type u} [TopologicalSpace A]

abbrev UniversalStep := ContinuousPathStep A
noncomputable abbrev UniversalSystem := continuousPathStepSystem A
noncomputable abbrev UniversalTotal :=
  TotalOpenGeometricCompPath A (ContinuousPathStep A) (continuousPathStepSystem A)

/-- The universal single-step section from the ordinary path space. -/
noncomputable def sectionMap {a b : A} (γ : _root_.Path a b) :
    UniversalTotal (A := A) :=
  ⟨γ 0, γ 1, continuousPathStep γ.toContinuousMap⟩

theorem section_geometric {a b : A} (γ : _root_.Path a b) :
    (sectionMap γ).geometricPath.cast γ.source.symm γ.target.symm = γ := by
  ext t
  rfl

theorem section_trace_realize {a b : A} (γ : _root_.Path a b) :
    (GeometricTrace.realize (sectionMap γ).trace).cast
      γ.source.symm γ.target.symm = γ := by
  ext t
  rfl

theorem continuous_section {a b : A} :
    Continuous (sectionMap : _root_.Path a b → UniversalTotal (A := A)) := by
  apply continuous_induced_rng.mpr
  unfold sectionMap
  change Continuous (fun γ : _root_.Path a b =>
    (γ 0, (γ 1, (1, (γ.toContinuousMap, γ.toContinuousMap)))))
  exact (continuous_eval_const (F := _root_.Path a b) (X := A) (0 : unitInterval)).prodMk <|
    (continuous_eval_const (F := _root_.Path a b) (X := A) (1 : unitInterval)).prodMk <|
      continuous_const.prodMk
        (continuous_induced_dom.prodMk continuous_induced_dom)

theorem endpointwise_realization_surjective {a b : A} :
    Function.Surjective
      (fun p : {q : UniversalTotal (A := A) // q.src = a ∧ q.tgt = b} =>
        p.1.geometricPath.cast p.2.1.symm p.2.2.symm) := by
  intro γ
  refine ⟨⟨sectionMap γ, γ.source, γ.target⟩, ?_⟩
  exact section_geometric γ

/-! ## A compact universality certificate -/

structure Certificate where
  section_continuous {a b : A} :
    Continuous (sectionMap : _root_.Path a b → UniversalTotal (A := A))
  section_realizes {a b : A} (γ : _root_.Path a b) :
    (sectionMap γ).geometricPath.cast γ.source.symm γ.target.symm = γ
  section_trace_realizes {a b : A} (γ : _root_.Path a b) :
    (GeometricTrace.realize (sectionMap γ).trace).cast
      γ.source.symm γ.target.symm = γ
  endpointwise_coverage {a b : A} :
    Function.Surjective
      (fun p : {q : UniversalTotal (A := A) // q.src = a ∧ q.tgt = b} =>
        p.1.geometricPath.cast p.2.1.symm p.2.2.symm)

noncomputable def certificate : Certificate (A := A) where
  section_continuous := continuous_section
  section_realizes := section_geometric
  section_trace_realizes := section_trace_realize
  endpointwise_coverage := endpointwise_realization_surjective

/-! Keep an explicit multi-step computational witness in the universal layer. -/
noncomputable def universalLoopCertificate {a b : A}
    (_γ : _root_.Path a b) : ComputationalPaths.Path a a :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl a)
    (ComputationalPaths.Path.refl a)

end UniversalTotalGeometricComparison
end GeometricTopology
end Path
end ComputationalPaths
