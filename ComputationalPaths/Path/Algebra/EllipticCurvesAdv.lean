import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace EllipticCurvesAdv

structure EllipticCurveData where
  conductor : Nat
  discriminant : Int
  jInvariantHeight : Nat
  torsionOrder : Nat

structure MordellWeilData where
  curve : EllipticCurveData
  rankValue : Nat
  regulatorValue : Nat

structure TateShafarevichData where
  curve : EllipticCurveData
  analyticOrderGuess : Nat
  finiteFlag : Bool

structure SelmerGroupData where
  curve : EllipticCurveData
  prime : Nat
  dimensionValue : Nat

structure BSDData where
  curve : EllipticCurveData
  leadingCoefficientHeight : Nat
  predictedRank : Nat

structure ModularParametrizationData where
  curve : EllipticCurveData
  modularDegreeValue : Nat
  level : Nat

structure HeegnerPointData where
  curve : EllipticCurveData
  heightValue : Nat
  discriminantParameter : Int

structure GrossZagierData where
  heegner : HeegnerPointData
  derivativeOrderValue : Nat
  normalizedHeightValue : Nat

def ellipticConductor (E : EllipticCurveData) : Nat :=
  E.conductor

def ellipticDiscriminantAbs (E : EllipticCurveData) : Nat :=
  E.discriminant.natAbs

def mordellWeilRank (M : MordellWeilData) : Nat :=
  M.rankValue

def mordellWeilRegulator (M : MordellWeilData) : Nat :=
  M.regulatorValue

def tateShafarevichOrderGuess (T : TateShafarevichData) : Nat :=
  T.analyticOrderGuess

def tateShafarevichFinite (T : TateShafarevichData) : Prop :=
  T.finiteFlag = true

def selmerDimension (S : SelmerGroupData) : Nat :=
  S.dimensionValue

def selmerUpperBoundOnRank (S : SelmerGroupData) : Nat :=
  S.dimensionValue

def bsdPredictedRank (B : BSDData) : Nat :=
  B.predictedRank

def bsdLeadingCoefficientHeight (B : BSDData) : Nat :=
  B.leadingCoefficientHeight

def modularDegree (M : ModularParametrizationData) : Nat :=
  M.modularDegreeValue

def modularLevel (M : ModularParametrizationData) : Nat :=
  M.level

def heegnerHeight (H : HeegnerPointData) : Nat :=
  H.heightValue

def heegnerDiscriminantAbs (H : HeegnerPointData) : Nat :=
  H.discriminantParameter.natAbs

def grossZagierDerivativeOrder (G : GrossZagierData) : Nat :=
  G.derivativeOrderValue

def grossZagierNormalizedHeight (G : GrossZagierData) : Nat :=
  G.normalizedHeightValue

def analyticRankCandidate (E : EllipticCurveData) : Nat :=
  E.jInvariantHeight % 7

def algebraicRankCandidate (M : MordellWeilData) : Nat :=
  M.rankValue

def bsdDefect (B : BSDData) (M : MordellWeilData) : Nat :=
  B.predictedRank + M.rankValue

def heegnerPointNonTorsionCandidate (H : HeegnerPointData) : Prop :=
  0 < H.heightValue

def selmerToShaGap (S : SelmerGroupData) (T : TateShafarevichData) : Nat :=
  S.dimensionValue + T.analyticOrderGuess

def ellipticPathWitness (E : EllipticCurveData) : Path E E :=
  Path.refl E

def bsdPathWitness (B : BSDData) : Path (bsdPredictedRank B) (bsdPredictedRank B) :=
  Path.refl _

def grossZagierPathWitness (G : GrossZagierData) : Path (grossZagierNormalizedHeight G) (grossZagierNormalizedHeight G) :=
  Path.refl _

theorem conductor_positive_shift (E : EllipticCurveData) :
    0 < ellipticConductor E + 1 := by
  sorry

theorem discriminant_abs_nonnegative (E : EllipticCurveData) :
    0 <= ellipticDiscriminantAbs E := by
  sorry

theorem mordellWeilRank_nonnegative (M : MordellWeilData) :
    0 <= mordellWeilRank M := by
  sorry

theorem mordellWeilRegulator_nonnegative (M : MordellWeilData) :
    0 <= mordellWeilRegulator M := by
  sorry

theorem sha_order_guess_positive_shift (T : TateShafarevichData) :
    0 < tateShafarevichOrderGuess T + 1 := by
  sorry

theorem selmer_dimension_nonnegative (S : SelmerGroupData) :
    0 <= selmerDimension S := by
  sorry

theorem selmer_upper_bound_reflexive (S : SelmerGroupData) :
    mordellWeilRank { curve := S.curve, rankValue := selmerUpperBoundOnRank S, regulatorValue := 0 } <=
      selmerUpperBoundOnRank S := by
  sorry

theorem bsd_predicted_rank_nonnegative (B : BSDData) :
    0 <= bsdPredictedRank B := by
  sorry

theorem bsd_leading_coefficient_nonnegative (B : BSDData) :
    0 <= bsdLeadingCoefficientHeight B := by
  sorry

theorem modular_degree_positive_shift (M : ModularParametrizationData) :
    0 < modularDegree M + 1 := by
  sorry

theorem modular_level_positive_shift (M : ModularParametrizationData) :
    0 < modularLevel M + 1 := by
  sorry

theorem heegner_height_nonnegative (H : HeegnerPointData) :
    0 <= heegnerHeight H := by
  sorry

theorem heegner_discriminant_abs_nonnegative (H : HeegnerPointData) :
    0 <= heegnerDiscriminantAbs H := by
  sorry

theorem grossZagier_derivative_order_nonnegative (G : GrossZagierData) :
    0 <= grossZagierDerivativeOrder G := by
  sorry

theorem grossZagier_height_nonnegative (G : GrossZagierData) :
    0 <= grossZagierNormalizedHeight G := by
  sorry

theorem analytic_rank_candidate_bound (E : EllipticCurveData) :
    analyticRankCandidate E < 7 := by
  sorry

theorem bsd_defect_nonnegative (B : BSDData) (M : MordellWeilData) :
    0 <= bsdDefect B M := by
  sorry

theorem selmer_sha_gap_nonnegative (S : SelmerGroupData) (T : TateShafarevichData) :
    0 <= selmerToShaGap S T := by
  sorry

theorem ellipticPathWitness_refl (E : EllipticCurveData) :
    ellipticPathWitness E = Path.refl E := by
  sorry

theorem bsdPathWitness_refl (B : BSDData) :
    bsdPathWitness B = Path.refl (bsdPredictedRank B) := by
  sorry

theorem grossZagierPathWitness_refl (G : GrossZagierData) :
    grossZagierPathWitness G = Path.refl (grossZagierNormalizedHeight G) := by
  sorry

theorem bsd_rank_consistency_candidate (B : BSDData) (M : MordellWeilData) :
    bsdPredictedRank B <= bsdDefect B M := by
  sorry

end EllipticCurvesAdv
end Algebra
end Path
end ComputationalPaths
