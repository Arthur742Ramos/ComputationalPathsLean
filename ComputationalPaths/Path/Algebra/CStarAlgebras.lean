import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CStarAlgebras

universe u

structure CStarAlgebra where
  carrier : Type u
  norm : carrier → Nat
  star : carrier → carrier
  mul : carrier → carrier → carrier
  add : carrier → carrier → carrier
  zero : carrier
  one : carrier

structure GNSDatum (A : CStarAlgebra.{u}) where
  cyclicVector : A.carrier
  cyclicWeight : Nat
  repWeight : Nat

structure AFDatum where
  stageCount : Nat
  bratteliEdges : Nat → Nat

structure CuntzDatum where
  generatorCount : Nat
  relationDefect : Nat

structure KirchbergPhillipsDatum where
  kirchbergPart : Nat
  phillipsPart : Nat

structure ElliottInvariant where
  k0Rank : Nat
  k1Rank : Nat
  traceRank : Nat

structure JiangSuDatum where
  scale : Nat
  absorption : Nat

def cstarPathCompose {X : Type u} {a b c : X}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def starTwice (A : CStarAlgebra.{u}) (a : A.carrier) : A.carrier :=
  A.star (A.star a)

def starNorm (A : CStarAlgebra.{u}) (a : A.carrier) : Nat :=
  A.norm (A.star a)

def gnsCyclicNorm (A : CStarAlgebra.{u}) (G : GNSDatum A) : Nat :=
  A.norm G.cyclicVector + G.cyclicWeight

def gnsRepresentationWeight (A : CStarAlgebra.{u}) (G : GNSDatum A) : Nat :=
  G.repWeight + A.norm G.cyclicVector

def gelfandTransformWeight (A : CStarAlgebra.{u}) (a : A.carrier) : Nat :=
  A.norm a + A.norm (A.star a)

def gelfandNaimarkRank (A : CStarAlgebra.{u}) : Nat :=
  A.norm A.one + A.norm A.zero

def afStageWeight (F : AFDatum) : Nat :=
  F.stageCount

def afBratteliDepth (F : AFDatum) : Nat :=
  F.bratteliEdges F.stageCount

def cuntzGeneratorWeight (O : CuntzDatum) : Nat :=
  O.generatorCount

def cuntzRelationDefect (O : CuntzDatum) : Nat :=
  O.relationDefect

def kirchbergPartWeight (K : KirchbergPhillipsDatum) : Nat :=
  K.kirchbergPart

def phillipsPartWeight (K : KirchbergPhillipsDatum) : Nat :=
  K.phillipsPart

def kirchbergPhillipsCode (K : KirchbergPhillipsDatum) : Nat :=
  kirchbergPartWeight K + phillipsPartWeight K

def elliottK0Part (E : ElliottInvariant) : Nat :=
  E.k0Rank

def elliottK1Part (E : ElliottInvariant) : Nat :=
  E.k1Rank

def elliottTracePart (E : ElliottInvariant) : Nat :=
  E.traceRank

def jiangSuScale (J : JiangSuDatum) : Nat :=
  J.scale

def jiangSuAbsorptionScore (J : JiangSuDatum) : Nat :=
  J.absorption

def nuclearDimensionBound (A : CStarAlgebra.{u}) : Nat :=
  A.norm A.one

def exactnessWitness (A : CStarAlgebra.{u}) : Nat :=
  A.norm A.zero

def quasidiagonalityWitness (A : CStarAlgebra.{u}) : Nat :=
  A.norm A.one + A.norm A.one

def stableRankEstimate (A : CStarAlgebra.{u}) : Nat :=
  A.norm A.one + 1

def realRankEstimate (A : CStarAlgebra.{u}) : Nat :=
  A.norm A.zero + 1

def classificationComplexity (A : CStarAlgebra.{u}) (K : KirchbergPhillipsDatum)
    (E : ElliottInvariant) (J : JiangSuDatum) : Nat :=
  kirchbergPhillipsCode K + elliottK0Part E + elliottK1Part E +
    elliottTracePart E + jiangSuAbsorptionScore J + nuclearDimensionBound A

theorem cstarPathCompose_refl {X : Type u} (a : X) :
    cstarPathCompose (Path.refl a) (Path.refl a) =
      Path.trans (Path.refl a) (Path.refl a) := by
  sorry

theorem starTwice_def (A : CStarAlgebra.{u}) (a : A.carrier) :
    starTwice A a = A.star (A.star a) := by
  sorry

theorem starNorm_def (A : CStarAlgebra.{u}) (a : A.carrier) :
    starNorm A a = A.norm (A.star a) := by
  sorry

theorem gnsCyclicNorm_def (A : CStarAlgebra.{u}) (G : GNSDatum A) :
    gnsCyclicNorm A G = A.norm G.cyclicVector + G.cyclicWeight := by
  sorry

theorem gnsRepresentationWeight_def (A : CStarAlgebra.{u}) (G : GNSDatum A) :
    gnsRepresentationWeight A G = G.repWeight + A.norm G.cyclicVector := by
  sorry

theorem gelfandTransformWeight_def (A : CStarAlgebra.{u}) (a : A.carrier) :
    gelfandTransformWeight A a = A.norm a + A.norm (A.star a) := by
  sorry

theorem gelfandNaimarkRank_def (A : CStarAlgebra.{u}) :
    gelfandNaimarkRank A = A.norm A.one + A.norm A.zero := by
  sorry

theorem afStageWeight_def (F : AFDatum) :
    afStageWeight F = F.stageCount := by
  sorry

theorem afBratteliDepth_def (F : AFDatum) :
    afBratteliDepth F = F.bratteliEdges F.stageCount := by
  sorry

theorem cuntzGeneratorWeight_def (O : CuntzDatum) :
    cuntzGeneratorWeight O = O.generatorCount := by
  sorry

theorem cuntzRelationDefect_def (O : CuntzDatum) :
    cuntzRelationDefect O = O.relationDefect := by
  sorry

theorem kirchbergPartWeight_def (K : KirchbergPhillipsDatum) :
    kirchbergPartWeight K = K.kirchbergPart := by
  sorry

theorem phillipsPartWeight_def (K : KirchbergPhillipsDatum) :
    phillipsPartWeight K = K.phillipsPart := by
  sorry

theorem kirchbergPhillipsCode_def (K : KirchbergPhillipsDatum) :
    kirchbergPhillipsCode K = kirchbergPartWeight K + phillipsPartWeight K := by
  sorry

theorem elliottK0Part_def (E : ElliottInvariant) :
    elliottK0Part E = E.k0Rank := by
  sorry

theorem elliottK1Part_def (E : ElliottInvariant) :
    elliottK1Part E = E.k1Rank := by
  sorry

theorem elliottTracePart_def (E : ElliottInvariant) :
    elliottTracePart E = E.traceRank := by
  sorry

theorem jiangSuScale_def (J : JiangSuDatum) :
    jiangSuScale J = J.scale := by
  sorry

theorem jiangSuAbsorptionScore_def (J : JiangSuDatum) :
    jiangSuAbsorptionScore J = J.absorption := by
  sorry

theorem nuclearDimensionBound_def (A : CStarAlgebra.{u}) :
    nuclearDimensionBound A = A.norm A.one := by
  sorry

theorem exactnessWitness_def (A : CStarAlgebra.{u}) :
    exactnessWitness A = A.norm A.zero := by
  sorry

theorem classificationComplexity_def (A : CStarAlgebra.{u}) (K : KirchbergPhillipsDatum)
    (E : ElliottInvariant) (J : JiangSuDatum) :
    classificationComplexity A K E J =
      kirchbergPhillipsCode K + elliottK0Part E + elliottK1Part E +
        elliottTracePart E + jiangSuAbsorptionScore J + nuclearDimensionBound A := by
  sorry

end CStarAlgebras
end Algebra
end Path
end ComputationalPaths
