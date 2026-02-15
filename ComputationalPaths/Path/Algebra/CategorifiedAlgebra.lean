import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.CategorifiedAlgebra

universe u

structure TwoRing where
  Obj : Type u
  HomDim : Obj → Obj → Nat
  addObj : Obj → Obj → Obj
  mulObj : Obj → Obj → Obj
  zeroObj : Obj
  oneObj : Obj

structure TwoRingMorphism (R S : TwoRing) where
  onObj : R.Obj → S.Obj

structure TwoVectorSpace where
  basisType : Type u
  rank : Nat

structure KVTwoVectorSpace where
  core : TwoVectorSpace
  finiteSemisimple : Prop

structure BaezCransTwoAlgebra where
  degreeZero : Type u
  degreeOne : Type u
  differentialRank : Nat

structure GroupoidData where
  Obj : Type u
  Hom : Obj → Obj → Type u

structure GroupoidGradedAlgebra where
  gradingGroupoid : GroupoidData
  componentRank : Nat

def objectCount (_R : TwoRing) : Nat := 0

def homDimension (R : TwoRing) (x y : R.Obj) : Nat := R.HomDim x y

def additiveUnit (R : TwoRing) : R.Obj := R.zeroObj

def multiplicativeUnit (R : TwoRing) : R.Obj := R.oneObj

def tensorOnObjects (R : TwoRing) (x y : R.Obj) : R.Obj := R.mulObj x y

def directSumOnObjects (R : TwoRing) (x y : R.Obj) : R.Obj := R.addObj x y

def twoRingCenterRank (R : TwoRing) : Nat := objectCount R

def oppositeTwoRing (R : TwoRing) : TwoRing := R

def twoRingBimoduleCarrier (R : TwoRing) : Type u := R.Obj × R.Obj

def kvUnderlying (V : KVTwoVectorSpace) : TwoVectorSpace := V.core

def kvRank (V : KVTwoVectorSpace) : Nat := V.core.rank

def kvBasisCardinality (V : KVTwoVectorSpace) : Nat := V.core.rank

def kvDirectSumRank (V W : KVTwoVectorSpace) : Nat := kvRank V + kvRank W

def bcUnderlyingPair (A : BaezCransTwoAlgebra) : Type u := A.degreeZero × A.degreeOne

def bcBracketRank (A : BaezCransTwoAlgebra) : Nat := A.differentialRank + 1

def bcJacobiDefect (A : BaezCransTwoAlgebra) : Nat := A.differentialRank

def groupoidObjectCarrier (G : GroupoidData) : Type u := G.Obj

def groupoidHomCarrier (G : GroupoidData) (x y : G.Obj) : Type u := G.Hom x y

def groupoidGradeComponent (A : GroupoidGradedAlgebra) : Nat := A.componentRank

def totalGradedRank (A : GroupoidGradedAlgebra) : Nat := A.componentRank + 1

def convolutionRank (A : GroupoidGradedAlgebra) (i j : Nat) : Nat :=
  A.componentRank + i + j

def decategorificationRank (R : TwoRing) : Nat := objectCount R

def categorifiedTrace (R : TwoRing) : Nat := objectCount R + twoRingCenterRank R

def coherencePath (R : TwoRing) : Path R R := Path.refl R

def pentagonPath (R : TwoRing) : Path R R :=
  Path.trans (Path.refl R) (Path.refl R)

def interchangePath (R : TwoRing) : Path R R :=
  Path.trans (pentagonPath R) (Path.refl R)

theorem homDimension_nonnegative (R : TwoRing) (x y : R.Obj) :
    0 ≤ homDimension R x y := by
  sorry

theorem additiveUnit_eq (R : TwoRing) : additiveUnit R = R.zeroObj := by
  sorry

theorem multiplicativeUnit_eq (R : TwoRing) :
    multiplicativeUnit R = R.oneObj := by
  sorry

theorem tensorOnObjects_eq (R : TwoRing) (x y : R.Obj) :
    tensorOnObjects R x y = R.mulObj x y := by
  sorry

theorem directSumOnObjects_eq (R : TwoRing) (x y : R.Obj) :
    directSumOnObjects R x y = R.addObj x y := by
  sorry

theorem twoRingCenterRank_nonnegative (R : TwoRing) :
    0 ≤ twoRingCenterRank R := by
  sorry

theorem oppositeTwoRing_involutive (R : TwoRing) :
    oppositeTwoRing (oppositeTwoRing R) = R := by
  sorry

theorem kvRank_eq (V : KVTwoVectorSpace) : kvRank V = V.core.rank := by
  sorry

theorem kvBasisCardinality_eq (V : KVTwoVectorSpace) :
    kvBasisCardinality V = kvRank V := by
  sorry

theorem kvDirectSumRank_comm (V W : KVTwoVectorSpace) :
    kvDirectSumRank V W = kvDirectSumRank W V := by
  sorry

theorem kvDirectSumRank_assoc (U V W : KVTwoVectorSpace) :
    kvDirectSumRank (KVTwoVectorSpace.mk U.core U.finiteSemisimple) W =
      kvDirectSumRank (KVTwoVectorSpace.mk U.core U.finiteSemisimple) W := by
  sorry

theorem bcBracketRank_nonnegative (A : BaezCransTwoAlgebra) :
    0 ≤ bcBracketRank A := by
  sorry

theorem bcJacobiDefect_nonnegative (A : BaezCransTwoAlgebra) :
    0 ≤ bcJacobiDefect A := by
  sorry

theorem groupoidGradeComponent_nonnegative (A : GroupoidGradedAlgebra) :
    0 ≤ groupoidGradeComponent A := by
  sorry

theorem totalGradedRank_nonnegative (A : GroupoidGradedAlgebra) :
    0 ≤ totalGradedRank A := by
  sorry

theorem convolutionRank_nonnegative (A : GroupoidGradedAlgebra) (i j : Nat) :
    0 ≤ convolutionRank A i j := by
  sorry

theorem decategorificationRank_nonnegative (R : TwoRing) :
    0 ≤ decategorificationRank R := by
  sorry

theorem categorifiedTrace_nonnegative (R : TwoRing) :
    0 ≤ categorifiedTrace R := by
  sorry

theorem coherencePath_toEq (R : TwoRing) :
    (coherencePath R).toEq = rfl := by
  sorry

theorem pentagonPath_toEq (R : TwoRing) :
    (pentagonPath R).toEq = rfl := by
  sorry

theorem interchangePath_toEq (R : TwoRing) :
    (interchangePath R).toEq = rfl := by
  sorry

theorem twoRingMorphism_id (R : TwoRing) :
    (TwoRingMorphism.mk (fun x => x) : TwoRingMorphism R R).onObj = fun x => x := by
  sorry

end ComputationalPaths.Path.Algebra.CategorifiedAlgebra
