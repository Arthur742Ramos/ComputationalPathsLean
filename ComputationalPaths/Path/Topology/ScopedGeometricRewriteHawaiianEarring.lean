import ComputationalPaths.Path.Topology.ScopedGeometricRewriteComparison

/-!
# Hawaiian-earring product obstruction

This module formalizes the transfer argument used for the Hawaiian-earring
example in the manuscript.  The external theorem that the quotient map from
the Hawaiian-earring loop space has a non-quotient square, and that quotient
multiplication is discontinuous, is supplied as input data.  The Lean theorem
proved here is the semantic deduction: a homeomorphic comparison transfers
that obstruction to the ordinary pair map and to the final/ordinary topology
criterion.

The external Hawaiian-earring theorem is not reproved here.  This keeps the
artifact honest about its formalization boundary while checking the complete
quotient-topology argument that connects the external result to the scoped
presentation construction.
-/

namespace ComputationalPaths
namespace Path
namespace GeometricTopology

open scoped Topology

universe u v w

/-- A quotient-map obstruction transported through a continuous representative
map and a homeomorphic comparison of the quotient targets. -/
structure QuotientObstructionTransfer
    (source : Type u) (target : Type v)
    (externalSource : Type w) (externalTarget : Type w)
    [TopologicalSpace source] [TopologicalSpace target]
    [TopologicalSpace externalSource] [TopologicalSpace externalTarget] where
  quotientMap : source → target
  externalQuotientMap : externalSource → externalTarget
  representativeMap : source → externalSource
  comparison : target ≃ₜ externalTarget
  representative_continuous : Continuous representativeMap
  external_quotient_continuous : Continuous externalQuotientMap
  comparison_commutes :
    comparison ∘ quotientMap = externalQuotientMap ∘ representativeMap
  external_pair_not_quotient :
    ¬ Topology.IsQuotientMap externalQuotientMap

namespace QuotientObstructionTransfer

variable {source : Type u} {target : Type v}
  {externalSource : Type w} {externalTarget : Type w}
  [TopologicalSpace source] [TopologicalSpace target]
  [TopologicalSpace externalSource] [TopologicalSpace externalTarget]
  (C : QuotientObstructionTransfer source target externalSource externalTarget)

/-- If the transported map were quotient, then the external map would be
quotient as well. -/
theorem external_isQuotientMap_of_source_isQuotientMap
    (hsource : Topology.IsQuotientMap C.quotientMap) :
    Topology.IsQuotientMap C.externalQuotientMap := by
  have hcomparison :
      Topology.IsQuotientMap (C.comparison ∘ C.quotientMap) :=
    C.comparison.isQuotientMap.comp hsource
  have hcomposite :
      Topology.IsQuotientMap (C.externalQuotientMap ∘ C.representativeMap) := by
    rw [← C.comparison_commutes]
    exact hcomparison
  exact Topology.IsQuotientMap.of_comp
    C.representative_continuous C.external_quotient_continuous hcomposite

/-- The external non-quotient result forces failure of quotientness on the
source-side map. -/
theorem not_isQuotientMap_quotientMap :
    ¬ Topology.IsQuotientMap C.quotientMap := by
  intro hsource
  exact C.external_pair_not_quotient
    (C.external_isQuotientMap_of_source_isQuotientMap hsource)

end QuotientObstructionTransfer

/-- A multiplication comparison packages the second part of the obstruction:
the two quotient arrow spaces are homeomorphic and their multiplications
commute with that homeomorphism. -/
structure MultiplicationComparison
    (sourceArrow : Type u) (externalArrow : Type v)
    [TopologicalSpace sourceArrow] [TopologicalSpace externalArrow] where
  sourceMultiplication : sourceArrow × sourceArrow → sourceArrow
  externalMultiplication : externalArrow × externalArrow → externalArrow
  comparison : sourceArrow ≃ₜ externalArrow
  multiplication_commutes :
    comparison ∘ sourceMultiplication =
      externalMultiplication ∘ (Homeomorph.prodCongr comparison comparison)

namespace MultiplicationComparison

variable {sourceArrow : Type u} {externalArrow : Type v}
  [TopologicalSpace sourceArrow] [TopologicalSpace externalArrow]
  (C : MultiplicationComparison sourceArrow externalArrow)

/-- Continuity of source multiplication would imply continuity of external
multiplication. -/
theorem external_continuous_of_source_continuous
    (hsource : Continuous C.sourceMultiplication) :
    Continuous C.externalMultiplication := by
  have hcomp : Continuous
      (C.externalMultiplication ∘
        (Homeomorph.prodCongr C.comparison C.comparison)) := by
    rw [← C.multiplication_commutes]
    exact C.comparison.continuous.comp hsource
  exact (Homeomorph.prodCongr C.comparison C.comparison).isQuotientMap.continuous_iff.2
    hcomp

/-- Discontinuous external multiplication transfers back to the source. -/
theorem not_source_continuous_of_not_external_continuous
    (hexternal : ¬ Continuous C.externalMultiplication) :
    ¬ Continuous C.sourceMultiplication := by
  intro hsource
  exact hexternal (C.external_continuous_of_source_continuous hsource)

end MultiplicationComparison

/-- The complete Lean-checkable interface for the Hawaiian-earring transfer.
The fields named external facts are the imported classical facts; the two
conclusions below are proved by the artifact. -/
structure HawaiianEarringObstructionCertificate
    (source : Type u) (target : Type v)
    (externalSource : Type w) (externalTarget : Type w)
    (sourceArrow : Type u) (externalArrow : Type v)
    [TopologicalSpace source] [TopologicalSpace target]
    [TopologicalSpace externalSource] [TopologicalSpace externalTarget]
    [TopologicalSpace sourceArrow] [TopologicalSpace externalArrow] where
  quotientTransfer :
    QuotientObstructionTransfer source target externalSource externalTarget
  multiplicationTransfer : MultiplicationComparison sourceArrow externalArrow
  external_multiplication_not_continuous :
    ¬ Continuous multiplicationTransfer.externalMultiplication

namespace HawaiianEarringObstructionCertificate

variable {source : Type u} {target : Type v}
  {externalSource : Type w} {externalTarget : Type w}
  {sourceArrow : Type u} {externalArrow : Type v}
  [TopologicalSpace source] [TopologicalSpace target]
  [TopologicalSpace externalSource] [TopologicalSpace externalTarget]
  [TopologicalSpace sourceArrow] [TopologicalSpace externalArrow]
  (C : HawaiianEarringObstructionCertificate
    source target externalSource externalTarget sourceArrow externalArrow)

/-- The ordinary pair map in the scoped presentation is not quotient. -/
theorem ordinary_pair_map_not_quotient :
    ¬ Topology.IsQuotientMap C.quotientTransfer.quotientMap :=
  C.quotientTransfer.not_isQuotientMap_quotientMap

/-- Ordinary-pullback compatibility is impossible when its raw pair map is
the source map carried by the certificate. -/
theorem ordinary_pullback_compatibility_fails
    (compatibility : Prop)
    (compatibility_implies_quotient :
      compatibility →
        Topology.IsQuotientMap C.quotientTransfer.quotientMap) :
    ¬ compatibility := by
  intro hcompat
  exact C.ordinary_pair_map_not_quotient
    (compatibility_implies_quotient hcompat)

/-- The ordinary multiplication on the source quotient is discontinuous. -/
theorem source_multiplication_not_continuous :
    ¬ Continuous C.multiplicationTransfer.sourceMultiplication :=
  C.multiplicationTransfer.not_source_continuous_of_not_external_continuous
    C.external_multiplication_not_continuous

end HawaiianEarringObstructionCertificate

namespace ScopedGeometricRewrite

variable {A : Type u} [TopologicalSpace A]
  {Step : Type v} [TopologicalSpace Step]
  {S : ContinuousGeometricStepSystem A Step}
  (P : ScopedGeometricRewritePresentation S)

/-- A Fabel-style external obstruction rules out ordinary-pullback
compatibility for the scoped presentation when its source map is the raw
ordinary-pair map. -/
theorem not_productQuotientCompatibility_of_transfer
    {externalSource : Type w} {externalTarget : Type w}
    [TopologicalSpace externalSource] [TopologicalSpace externalTarget]
    (C : QuotientObstructionTransfer
      (ScopedComposableRaw (S := S)) (ScopedComposablePair P)
      externalSource externalTarget)
    (hmap : C.quotientMap = scopedOrdinaryPairMap P) :
    ¬ ProductQuotientCompatibility P := by
  intro hcompat
  have hquotient :
      Topology.IsQuotientMap C.quotientMap := by
    rw [hmap]
    exact
      (scopedProductCompatibility_iff_raw_pair_map_quotient P).1 hcompat
  exact C.not_isQuotientMap_quotientMap hquotient

/-- The same transferred obstruction separates the final and ordinary
topologies on the composable-pair arrow space. -/
theorem not_final_topology_agreement_of_transfer
    {externalSource : Type w} {externalTarget : Type w}
    [TopologicalSpace externalSource] [TopologicalSpace externalTarget]
    (C : QuotientObstructionTransfer
      (ScopedComposableRaw (S := S)) (ScopedComposablePair P)
      externalSource externalTarget)
    (hmap : C.quotientMap = scopedOrdinaryPairMap P) :
    ¬ (inferInstance : TopologicalSpace (ScopedComposableClass P)) =
        TopologicalSpace.induced (scopedPairToOrdinary P)
          (inferInstance : TopologicalSpace (ScopedComposablePair P)) := by
  intro htop
  exact not_productQuotientCompatibility_of_transfer P C hmap
    ((scopedProductCompatibility_iff_final_topology_agreement P).2 htop)

end ScopedGeometricRewrite

/-- A small explicit computational-path witness retained in this module's
certificate layer. -/
noncomputable def hawaiianEarringTransferPath (n : Nat) :
    ComputationalPaths.Path (n + n) (n + n) :=
  ComputationalPaths.Path.trans
    (ComputationalPaths.Path.refl (n + n))
    (ComputationalPaths.Path.refl (n + n))

/-- The corresponding unit rewrite is a genuine RwEq step. -/
noncomputable def hawaiianEarringTransferRwEq (n : Nat) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl (n + n))
        (ComputationalPaths.Path.refl (n + n)))
      (ComputationalPaths.Path.refl (n + n)) :=
  ComputationalPaths.Path.RwEq.step
    (ComputationalPaths.Path.Step.trans_refl_right
      (ComputationalPaths.Path.refl (n + n)))

end GeometricTopology
end Path
end ComputationalPaths
