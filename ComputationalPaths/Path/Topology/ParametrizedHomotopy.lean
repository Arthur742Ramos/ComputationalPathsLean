/-!
# Parametrized Homotopy via Computational Paths

This module records parametrized-space bookkeeping in computational paths:
fiberwise homotopy, ex-spaces, fiberwise suspension, parametrized spectra,
and twisted cohomology structures.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace ParametrizedHomotopy

universe u

structure BaseSpace where
  points : Nat
  chosenPoint : Nat

structure ParamSpace where
  base : BaseSpace
  totalPoints : Nat
  fiberRank : Nat
  sectionRank : Nat

structure FiberwiseMap where
  source : ParamSpace
  target : ParamSpace
  mapRank : Nat
  preservesSection : Bool

structure ExSpace where
  carrier : ParamSpace
  exRank : Nat
  zeroSectionRank : Nat

structure FiberwiseSuspension where
  source : ParamSpace
  suspensionDegree : Nat
  reducedRank : Nat

structure ParamSpectrum where
  base : BaseSpace
  stageCount : Nat
  connectiveBound : Nat
  twistWeight : Nat

structure TwistedCohomology where
  spectrum : ParamSpectrum
  twistDegree : Nat
  classRank : Nat
  differentialDegree : Nat

def basePoint (B : BaseSpace) : Nat :=
  B.chosenPoint

def totalPointCount (P : ParamSpace) : Nat :=
  P.totalPoints

def projectionFiberRank (P : ParamSpace) : Nat :=
  P.fiberRank

def sectionPointRank (P : ParamSpace) : Nat :=
  P.sectionRank

def fiberwiseComposeRank (f g : FiberwiseMap) : Nat :=
  f.mapRank + g.mapRank

def fiberwiseIdRank (P : ParamSpace) : Nat :=
  P.fiberRank + P.sectionRank

def exSpaceFiberRank (E : ExSpace) : Nat :=
  E.carrier.fiberRank + E.exRank

def exSpaceSectionValue (E : ExSpace) : Nat :=
  E.carrier.sectionRank + E.zeroSectionRank

def fiberwiseSuspensionDegree (S : FiberwiseSuspension) : Nat :=
  S.suspensionDegree + S.reducedRank

def fiberwiseSuspensionLevel (S : FiberwiseSuspension) : Nat :=
  S.source.fiberRank + S.suspensionDegree

def parametrizedSpectrumShift (S : ParamSpectrum) : Nat :=
  S.stageCount + S.connectiveBound

def parametrizedSpectrumConnective (S : ParamSpectrum) : Bool :=
  S.connectiveBound <= parametrizedSpectrumShift S

def twistDegreeShift (T : TwistedCohomology) : Nat :=
  T.twistDegree + T.differentialDegree

def twistWeight (T : TwistedCohomology) : Nat :=
  T.spectrum.twistWeight + T.classRank

def twistedCohomologyClass (T : TwistedCohomology) : Nat :=
  T.classRank + T.twistDegree

def twistedCupLength (T : TwistedCohomology) : Nat :=
  T.classRank + T.spectrum.stageCount

def parametrizedLoopDepth (P : ParamSpace) : Nat :=
  P.fiberRank + P.base.points

def parametrizedPathLength (P : ParamSpace) : Nat :=
  P.totalPoints + P.base.chosenPoint

def fiberTransportIndex (P : ParamSpace) : Nat :=
  parametrizedLoopDepth P + P.sectionRank

def exFibrationStage (E : ExSpace) : Nat :=
  E.exRank + E.carrier.base.points

def fiberwiseStableRange (S : ParamSpectrum) : Nat :=
  S.stageCount + S.twistWeight

def fiberwiseDescentIndex (S : ParamSpectrum) : Nat :=
  S.connectiveBound + S.twistWeight

def twistedDifferentialDegree (T : TwistedCohomology) : Nat :=
  T.differentialDegree + T.twistDegree

def twistedTotalWeight (T : TwistedCohomology) : Nat :=
  twistWeight T + twistedDifferentialDegree T

def fiberwiseThreeStep {alpha : Type u} {a b c d : alpha}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans (Path.trans p q) r

def fiberwiseRoundTrip {alpha : Type u} {a b : alpha} (p : Path a b) : Path a a :=
  Path.trans p (Path.symm p)

theorem base_point_refl (B : BaseSpace) :
    Path (basePoint B) (basePoint B) := by
  sorry

theorem total_point_count_refl (P : ParamSpace) :
    Path (totalPointCount P) (totalPointCount P) := by
  sorry

theorem projection_fiber_rank_refl (P : ParamSpace) :
    Path (projectionFiberRank P) (projectionFiberRank P) := by
  sorry

theorem section_point_rank_refl (P : ParamSpace) :
    Path (sectionPointRank P) (sectionPointRank P) := by
  sorry

theorem fiberwise_compose_rank_refl (f g : FiberwiseMap) :
    Path (fiberwiseComposeRank f g) (fiberwiseComposeRank f g) := by
  sorry

theorem fiberwise_id_rank_refl (P : ParamSpace) :
    Path (fiberwiseIdRank P) (fiberwiseIdRank P) := by
  sorry

theorem ex_space_fiber_rank_refl (E : ExSpace) :
    Path (exSpaceFiberRank E) (exSpaceFiberRank E) := by
  sorry

theorem ex_space_section_value_refl (E : ExSpace) :
    Path (exSpaceSectionValue E) (exSpaceSectionValue E) := by
  sorry

theorem fiberwise_suspension_degree_refl (S : FiberwiseSuspension) :
    Path (fiberwiseSuspensionDegree S) (fiberwiseSuspensionDegree S) := by
  sorry

theorem fiberwise_suspension_level_refl (S : FiberwiseSuspension) :
    Path (fiberwiseSuspensionLevel S) (fiberwiseSuspensionLevel S) := by
  sorry

theorem parametrized_spectrum_shift_refl (S : ParamSpectrum) :
    Path (parametrizedSpectrumShift S) (parametrizedSpectrumShift S) := by
  sorry

theorem parametrized_spectrum_connective_refl (S : ParamSpectrum) :
    Path (parametrizedSpectrumConnective S) (parametrizedSpectrumConnective S) := by
  sorry

theorem twist_degree_shift_refl (T : TwistedCohomology) :
    Path (twistDegreeShift T) (twistDegreeShift T) := by
  sorry

theorem twist_weight_refl (T : TwistedCohomology) :
    Path (twistWeight T) (twistWeight T) := by
  sorry

theorem twisted_cohomology_class_refl (T : TwistedCohomology) :
    Path (twistedCohomologyClass T) (twistedCohomologyClass T) := by
  sorry

theorem twisted_cup_length_refl (T : TwistedCohomology) :
    Path (twistedCupLength T) (twistedCupLength T) := by
  sorry

theorem fiber_transport_index_refl (P : ParamSpace) :
    Path (fiberTransportIndex P) (fiberTransportIndex P) := by
  sorry

theorem fiberwise_stable_range_refl (S : ParamSpectrum) :
    Path (fiberwiseStableRange S) (fiberwiseStableRange S) := by
  sorry

theorem twisted_total_weight_refl (T : TwistedCohomology) :
    Path (twistedTotalWeight T) (twistedTotalWeight T) := by
  sorry

theorem fiberwise_three_step_refl {alpha : Type u} {a b c d : alpha}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path (fiberwiseThreeStep p q r) (fiberwiseThreeStep p q r) := by
  sorry

theorem fiberwise_round_trip_refl {alpha : Type u} {a b : alpha} (p : Path a b) :
    Path (fiberwiseRoundTrip p) (fiberwiseRoundTrip p) := by
  sorry



/-! ## Computational path expansion: fiberwise rewriting -/

def fiberwiseRewriteStep (x y : ParamSpace) (h : x = y) : Step ParamSpace :=
  Step.mk x y h

def fiberwisePathWitness (x y : ParamSpace) (h : x = y) : Path x y :=
  Path.stepChain h

def fiberwiseRewrite {x y : ParamSpace} (p q : Path x y) : Prop :=
  ∃ r : Path y y, q = Path.trans p r

def fiberwiseRewriteConfluent : Prop :=
  ∀ {x y : ParamSpace} (p q₁ q₂ : Path x y),
    fiberwiseRewrite p q₁ →
    fiberwiseRewrite p q₂ →
    ∃ q₃ : Path x y, fiberwiseRewrite q₁ q₃ ∧ fiberwiseRewrite q₂ q₃

theorem fiberwiseRewrite_refl {x y : ParamSpace} (p : Path x y) :
    fiberwiseRewrite p (Path.trans p (Path.refl y)) := by
  exact ⟨Path.refl y, rfl⟩

theorem fiberwiseRewrite_confluence : fiberwiseRewriteConfluent := by
  sorry

theorem fiberwiseRewrite_coherence {x y z w : ParamSpace}
    (p : Path x y) (q : Path y z) (r : Path z w) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simpa using Path.trans_assoc p q r

end ParametrizedHomotopy
end Topology
end Path
end ComputationalPaths
