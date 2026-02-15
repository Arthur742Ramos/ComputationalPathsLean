/-!
# Advanced Spectral Sequences via Computational Paths

This module packages advanced spectral-sequence-flavored bookkeeping in the
computational paths style: Serre, Eilenberg-Moore, Bockstein,
Adams-Novikov, chromatic filtrations, and multiplicative structures.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace SpectralSequencesAdv

universe u

structure BigradedTerm where
  filtration : Nat
  totalDegree : Nat

structure SerreSS where
  baseFiltration : Nat
  fiberFiltration : Nat
  differentialLength : Nat
  edgeMapRank : Nat

structure EilenbergMooreSS where
  cotorDegree : Nat
  barLength : Nat
  extensionRank : Nat

structure BocksteinSS where
  torsionExponent : Nat
  connectingRank : Nat
  exactCoupleLength : Nat

structure AdamsNovikovSS where
  prime : Nat
  height : Nat
  stem : Nat
  filtration : Nat

structure ChromaticSS where
  layer : Nat
  monochromaticWeight : Nat
  convergenceBound : Nat

structure MultiplicativeSS where
  leftDegree : Nat
  rightDegree : Nat
  unitDegree : Nat

def serreE2Total (S : SerreSS) : Nat :=
  S.baseFiltration + S.fiberFiltration

def serreEInfinityTotal (S : SerreSS) : Nat :=
  serreE2Total S + S.differentialLength

def serreFiltrationGap (S : SerreSS) : Nat :=
  S.fiberFiltration - S.baseFiltration

def serreHasEdgeMap (S : SerreSS) : Bool :=
  S.edgeMapRank > 0

def serreDifferentialTarget (S : SerreSS) : Nat :=
  S.baseFiltration + S.differentialLength

def eilenbergMooreE2Degree (E : EilenbergMooreSS) : Nat :=
  E.cotorDegree + E.barLength

def eilenbergMooreLength (E : EilenbergMooreSS) : Nat :=
  E.barLength + E.extensionRank

def eilenbergMooreConverges (E : EilenbergMooreSS) : Bool :=
  E.extensionRank <= eilenbergMooreLength E

def bocksteinPrimaryStage (B : BocksteinSS) : Nat :=
  B.torsionExponent + 1

def bocksteinSecondaryStage (B : BocksteinSS) : Nat :=
  bocksteinPrimaryStage B + B.connectingRank

def bocksteinTertiaryStage (B : BocksteinSS) : Nat :=
  bocksteinSecondaryStage B + B.exactCoupleLength

def adamsNovikovStem (A : AdamsNovikovSS) : Nat :=
  A.stem + A.height

def adamsNovikovFiltration (A : AdamsNovikovSS) : Nat :=
  A.filtration + A.prime

def adamsNovikovHeightWeight (A : AdamsNovikovSS) : Nat :=
  A.height * A.prime

def chromaticLayerWeight (C : ChromaticSS) : Nat :=
  C.layer + C.monochromaticWeight

def chromaticTotalWeight (C : ChromaticSS) : Nat :=
  chromaticLayerWeight C + C.convergenceBound

def chromaticBounded (C : ChromaticSS) : Bool :=
  C.layer <= chromaticTotalWeight C

def multiplicativeProductDegree (M : MultiplicativeSS) : Nat :=
  M.leftDegree + M.rightDegree

def multiplicativeUnitDegree (M : MultiplicativeSS) : Nat :=
  M.unitDegree

def multiplicativeLeibnizShift (M : MultiplicativeSS) : Nat :=
  multiplicativeProductDegree M + M.unitDegree

def spectralDegreeShift (r p q : Nat) : Nat :=
  p + q + r

def spectralConvergenceIndex (r p q : Nat) : Nat :=
  spectralDegreeShift r p q + r

def spectralPageWeight (t : BigradedTerm) : Nat :=
  t.filtration + t.totalDegree

def serreDifferentialStep (S : SerreSS) : Nat :=
  serreDifferentialTarget S + S.fiberFiltration

def eilenbergMooreDifferentialStep (E : EilenbergMooreSS) : Nat :=
  eilenbergMooreE2Degree E + E.extensionRank

def spectralThreeStep {alpha : Type u} {a b c d : alpha}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans (Path.trans p q) r

def spectralLoopFold {alpha : Type u} {a b : alpha} (p : Path a b) : Path a a :=
  Path.trans p (Path.symm p)

theorem serre_e2_total_refl (S : SerreSS) :
    Path (serreE2Total S) (serreE2Total S) := by
  sorry

theorem serre_einfinity_total_refl (S : SerreSS) :
    Path (serreEInfinityTotal S) (serreEInfinityTotal S) := by
  sorry

theorem serre_filtration_gap_refl (S : SerreSS) :
    Path (serreFiltrationGap S) (serreFiltrationGap S) := by
  sorry

theorem serre_has_edge_map_refl (S : SerreSS) :
    Path (serreHasEdgeMap S) (serreHasEdgeMap S) := by
  sorry

theorem serre_differential_target_refl (S : SerreSS) :
    Path (serreDifferentialTarget S) (serreDifferentialTarget S) := by
  sorry

theorem eilenberg_moore_e2_refl (E : EilenbergMooreSS) :
    Path (eilenbergMooreE2Degree E) (eilenbergMooreE2Degree E) := by
  sorry

theorem eilenberg_moore_length_refl (E : EilenbergMooreSS) :
    Path (eilenbergMooreLength E) (eilenbergMooreLength E) := by
  sorry

theorem eilenberg_moore_converges_refl (E : EilenbergMooreSS) :
    Path (eilenbergMooreConverges E) (eilenbergMooreConverges E) := by
  sorry

theorem bockstein_primary_refl (B : BocksteinSS) :
    Path (bocksteinPrimaryStage B) (bocksteinPrimaryStage B) := by
  sorry

theorem bockstein_secondary_refl (B : BocksteinSS) :
    Path (bocksteinSecondaryStage B) (bocksteinSecondaryStage B) := by
  sorry

theorem bockstein_tertiary_refl (B : BocksteinSS) :
    Path (bocksteinTertiaryStage B) (bocksteinTertiaryStage B) := by
  sorry

theorem adams_novikov_stem_refl (A : AdamsNovikovSS) :
    Path (adamsNovikovStem A) (adamsNovikovStem A) := by
  sorry

theorem adams_novikov_filtration_refl (A : AdamsNovikovSS) :
    Path (adamsNovikovFiltration A) (adamsNovikovFiltration A) := by
  sorry

theorem adams_novikov_height_weight_refl (A : AdamsNovikovSS) :
    Path (adamsNovikovHeightWeight A) (adamsNovikovHeightWeight A) := by
  sorry

theorem chromatic_layer_weight_refl (C : ChromaticSS) :
    Path (chromaticLayerWeight C) (chromaticLayerWeight C) := by
  sorry

theorem chromatic_total_weight_refl (C : ChromaticSS) :
    Path (chromaticTotalWeight C) (chromaticTotalWeight C) := by
  sorry

theorem chromatic_bounded_refl (C : ChromaticSS) :
    Path (chromaticBounded C) (chromaticBounded C) := by
  sorry

theorem multiplicative_product_degree_refl (M : MultiplicativeSS) :
    Path (multiplicativeProductDegree M) (multiplicativeProductDegree M) := by
  sorry

theorem multiplicative_unit_degree_refl (M : MultiplicativeSS) :
    Path (multiplicativeUnitDegree M) (multiplicativeUnitDegree M) := by
  sorry

theorem multiplicative_leibniz_shift_refl (M : MultiplicativeSS) :
    Path (multiplicativeLeibnizShift M) (multiplicativeLeibnizShift M) := by
  sorry

theorem spectral_convergence_index_refl (r p q : Nat) :
    Path (spectralConvergenceIndex r p q) (spectralConvergenceIndex r p q) := by
  sorry

theorem spectral_page_weight_refl (t : BigradedTerm) :
    Path (spectralPageWeight t) (spectralPageWeight t) := by
  sorry

theorem spectral_three_step_refl {alpha : Type u} {a b c d : alpha}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path (spectralThreeStep p q r) (spectralThreeStep p q r) := by
  sorry

theorem spectral_loop_fold_refl {alpha : Type u} {a b : alpha} (p : Path a b) :
    Path (spectralLoopFold p) (spectralLoopFold p) := by
  sorry

end SpectralSequencesAdv
end Topology
end Path
end ComputationalPaths
