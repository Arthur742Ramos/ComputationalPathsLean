import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace OperatorSpaces

universe u

structure OperatorSpace where
  matrixNorm : Nat → Nat
  baseDim : Nat
  exactConst : Nat
  localReflexivity : Nat

structure CompletelyBoundedMap where
  cbNorm : Nat
  cpNorm : Nat
  distance : Nat

structure OperatorSystem where
  unitSize : Nat
  boundarySize : Nat
  envelopeSize : Nat

structure HaagerupDatum where
  leftNorm : Nat
  rightNorm : Nat

def operatorSpacePathCompose {X : Type u} {a b c : X}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def matrixNormAt (X : OperatorSpace) (n : Nat) : Nat :=
  X.matrixNorm n

def completeBoundedNorm (T : CompletelyBoundedMap) : Nat :=
  T.cbNorm

def ruanLeftBound (H : HaagerupDatum) : Nat :=
  H.leftNorm

def ruanRightBound (H : HaagerupDatum) : Nat :=
  H.rightNorm

def haagerupTensorNorm (H : HaagerupDatum) : Nat :=
  H.leftNorm + H.rightNorm

def minTensorNorm (X : OperatorSpace) : Nat :=
  X.baseDim

def maxTensorNorm (X : OperatorSpace) : Nat :=
  X.baseDim + X.exactConst

def pisierShlyakhtenkoWeight (X : OperatorSpace) : Nat :=
  X.localReflexivity + X.exactConst

def operatorSystemUnit (S : OperatorSystem) : Nat :=
  S.unitSize

def arvesonBoundaryScore (S : OperatorSystem) : Nat :=
  S.boundarySize

def injectiveEnvelopeSize (S : OperatorSystem) : Nat :=
  S.envelopeSize

def cbDistance (T : CompletelyBoundedMap) : Nat :=
  T.distance

def exactOperatorSpaceConstant (X : OperatorSpace) : Nat :=
  X.exactConst

def localReflexivityScore (X : OperatorSpace) : Nat :=
  X.localReflexivity

def completelyPositiveNorm (T : CompletelyBoundedMap) : Nat :=
  T.cpNorm

def dualOperatorSpaceWeight (X : OperatorSpace) : Nat :=
  X.baseDim + matrixNormAt X 1

def rowSpaceDimension (X : OperatorSpace) : Nat :=
  X.baseDim + 1

def columnSpaceDimension (X : OperatorSpace) : Nat :=
  X.baseDim + 1

def interpolationParameter (X : OperatorSpace) : Nat :=
  rowSpaceDimension X + columnSpaceDimension X

theorem operatorSpacePathCompose_refl {X : Type u} (a : X) :
    operatorSpacePathCompose (Path.refl a) (Path.refl a) =
      Path.trans (Path.refl a) (Path.refl a) := by
  sorry

theorem matrixNormAt_def (X : OperatorSpace) (n : Nat) :
    matrixNormAt X n = X.matrixNorm n := by
  sorry

theorem completeBoundedNorm_def (T : CompletelyBoundedMap) :
    completeBoundedNorm T = T.cbNorm := by
  sorry

theorem ruanLeftBound_def (H : HaagerupDatum) :
    ruanLeftBound H = H.leftNorm := by
  sorry

theorem ruanRightBound_def (H : HaagerupDatum) :
    ruanRightBound H = H.rightNorm := by
  sorry

theorem haagerupTensorNorm_def (H : HaagerupDatum) :
    haagerupTensorNorm H = H.leftNorm + H.rightNorm := by
  sorry

theorem minTensorNorm_def (X : OperatorSpace) :
    minTensorNorm X = X.baseDim := by
  sorry

theorem maxTensorNorm_def (X : OperatorSpace) :
    maxTensorNorm X = X.baseDim + X.exactConst := by
  sorry

theorem pisierShlyakhtenkoWeight_def (X : OperatorSpace) :
    pisierShlyakhtenkoWeight X = X.localReflexivity + X.exactConst := by
  sorry

theorem operatorSystemUnit_def (S : OperatorSystem) :
    operatorSystemUnit S = S.unitSize := by
  sorry

theorem arvesonBoundaryScore_def (S : OperatorSystem) :
    arvesonBoundaryScore S = S.boundarySize := by
  sorry

theorem injectiveEnvelopeSize_def (S : OperatorSystem) :
    injectiveEnvelopeSize S = S.envelopeSize := by
  sorry

theorem cbDistance_def (T : CompletelyBoundedMap) :
    cbDistance T = T.distance := by
  sorry

theorem exactOperatorSpaceConstant_def (X : OperatorSpace) :
    exactOperatorSpaceConstant X = X.exactConst := by
  sorry

theorem localReflexivityScore_def (X : OperatorSpace) :
    localReflexivityScore X = X.localReflexivity := by
  sorry

theorem completelyPositiveNorm_def (T : CompletelyBoundedMap) :
    completelyPositiveNorm T = T.cpNorm := by
  sorry

theorem dualOperatorSpaceWeight_def (X : OperatorSpace) :
    dualOperatorSpaceWeight X = X.baseDim + matrixNormAt X 1 := by
  sorry

theorem interpolationParameter_def (X : OperatorSpace) :
    interpolationParameter X = rowSpaceDimension X + columnSpaceDimension X := by
  sorry

end OperatorSpaces
end Algebra
end Path
end ComputationalPaths
