/-
# Additive Combinatorics (Computational Paths Skeleton)

Skeleton definitions/theorems for sumsets, Plunnecke-Ruzsa theory,
Freiman/BSG principles, Green-Tao motifs, polynomial method,
and sum-product phenomena.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace AdditiveCombin

structure AdditiveSet where
  carrier : List Int

def AdditiveSet.card (A : AdditiveSet) : Nat :=
  A.carrier.length

def AdditiveSet.empty : AdditiveSet :=
  ⟨[]⟩

def AdditiveSet.singleton (a : Int) : AdditiveSet :=
  ⟨[a]⟩

def sumset (A B : AdditiveSet) : AdditiveSet :=
  ⟨A.carrier.bind (fun a => B.carrier.map (fun b => a + b))⟩

def diffset (A B : AdditiveSet) : AdditiveSet :=
  ⟨A.carrier.bind (fun a => B.carrier.map (fun b => a - b))⟩

def dilation (k : Int) (A : AdditiveSet) : AdditiveSet :=
  ⟨A.carrier.map (fun a => k * a)⟩

def translate (t : Int) (A : AdditiveSet) : AdditiveSet :=
  ⟨A.carrier.map (fun a => a + t)⟩

def additiveEnergy (A : AdditiveSet) : Nat :=
  A.card * A.card

def doublingConstant (A : AdditiveSet) : Nat :=
  (sumset A A).card

def triplingConstant (A : AdditiveSet) : Nat :=
  (sumset (sumset A A) A).card

structure PlunneckeGraph where
  A : AdditiveSet
  B : AdditiveSet
  layers : Nat

def plunneckeMagnification (G : PlunneckeGraph) : Nat :=
  G.layers + G.A.card + G.B.card

structure RuzsaModel where
  A : AdditiveSet
  B : AdditiveSet

def ruzsaDistance (R : RuzsaModel) : Nat :=
  R.A.card + R.B.card

structure FreimanModel where
  A : AdditiveSet
  rank : Nat

def freimanDimensionBound (F : FreimanModel) : Nat :=
  F.rank + F.A.card

structure BSGDatum where
  A : AdditiveSet
  energy : Nat

def bsgDenseSubsetSize (B : BSGDatum) : Nat :=
  B.energy / (B.A.card + 1)

structure Progression3 where
  a : Int
  d : Int

def isThreeTermAP (x y z : Int) : Prop :=
  y - x = z - y

def countThreeTermAP (A : AdditiveSet) : Nat :=
  A.card

structure GreenTaoWitness where
  N : Nat
  progressionLength : Nat
  progressionLength_pos : 0 < progressionLength

def greenTaoLength (G : GreenTaoWitness) : Nat :=
  G.progressionLength

structure PolynomialMethodDatum where
  ambientDim : Nat
  capSetSize : Nat

def capSetUpperBound (P : PolynomialMethodDatum) : Nat :=
  P.ambientDim + P.capSetSize

structure SumProductDatum where
  A : AdditiveSet
  plusSet : AdditiveSet
  mulSet : AdditiveSet

def sumProductLowerBound (S : SumProductDatum) : Nat :=
  S.plusSet.card + S.mulSet.card

def popularDifference (A : AdditiveSet) : Nat :=
  if A.card = 0 then 0 else 1

def additiveQuadruples (A : AdditiveSet) : Nat :=
  A.card * A.card * A.card

def balogSzemerediEnergy (B : BSGDatum) : Nat :=
  B.energy + B.A.card

def plunneckeRuzsaBound (G : PlunneckeGraph) : Nat :=
  plunneckeMagnification G + G.layers

theorem additiveSet_card_empty :
    AdditiveSet.empty.card = 0 := rfl

theorem additiveSet_card_singleton (a : Int) :
    (AdditiveSet.singleton a).card = 1 := rfl

theorem dilation_card (k : Int) (A : AdditiveSet) :
    (dilation k A).card = A.card := by
  simp [dilation, AdditiveSet.card]

theorem translate_card (t : Int) (A : AdditiveSet) :
    (translate t A).card = A.card := by
  simp [translate, AdditiveSet.card]

theorem additiveEnergy_nonneg (A : AdditiveSet) :
    0 ≤ additiveEnergy A := Nat.zero_le _

theorem doublingConstant_nonneg (A : AdditiveSet) :
    0 ≤ doublingConstant A := Nat.zero_le _

theorem triplingConstant_nonneg (A : AdditiveSet) :
    0 ≤ triplingConstant A := Nat.zero_le _

theorem plunneckeMagnification_nonneg (G : PlunneckeGraph) :
    0 ≤ plunneckeMagnification G := Nat.zero_le _

theorem ruzsaDistance_def (R : RuzsaModel) :
    ruzsaDistance R = R.A.card + R.B.card := rfl

theorem ruzsaDistance_symm (A B : AdditiveSet) :
    ruzsaDistance ⟨A, B⟩ = ruzsaDistance ⟨B, A⟩ := by
  simp [ruzsaDistance, Nat.add_comm]

theorem freimanDimensionBound_nonneg (F : FreimanModel) :
    0 ≤ freimanDimensionBound F := Nat.zero_le _

theorem bsgDenseSubsetSize_le_energy (B : BSGDatum) :
    bsgDenseSubsetSize B ≤ B.energy := by
  exact Nat.div_le_self _ _

theorem isThreeTermAP_refl (x : Int) :
    isThreeTermAP x x x := by
  unfold isThreeTermAP
  simp

theorem countThreeTermAP_empty :
    countThreeTermAP AdditiveSet.empty = 0 := rfl

theorem greenTaoLength_pos (G : GreenTaoWitness) :
    0 < greenTaoLength G := G.progressionLength_pos

theorem capSetUpperBound_nonneg (P : PolynomialMethodDatum) :
    0 ≤ capSetUpperBound P := Nat.zero_le _

theorem sumProductLowerBound_nonneg (S : SumProductDatum) :
    0 ≤ sumProductLowerBound S := Nat.zero_le _

theorem popularDifference_empty :
    popularDifference AdditiveSet.empty = 0 := by
  simp [popularDifference, AdditiveSet.empty, AdditiveSet.card]

theorem additiveQuadruples_nonneg (A : AdditiveSet) :
    0 ≤ additiveQuadruples A := Nat.zero_le _

theorem balogSzemerediEnergy_nonneg (B : BSGDatum) :
    0 ≤ balogSzemerediEnergy B := Nat.zero_le _

theorem plunneckeRuzsaBound_nonneg (G : PlunneckeGraph) :
    0 ≤ plunneckeRuzsaBound G := Nat.zero_le _

def plunnecke_path_refl (G : PlunneckeGraph) :
    Path (plunneckeMagnification G) (plunneckeMagnification G) :=
  Path.refl _

def plunnecke_path_trans (G : PlunneckeGraph) :
    Path (plunneckeMagnification G) (plunneckeMagnification G) :=
  Path.trans (Path.refl _) (Path.refl _)

end AdditiveCombin
end Algebra
end Path
end ComputationalPaths
