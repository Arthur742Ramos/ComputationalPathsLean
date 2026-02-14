import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace KKTheoryAdvanced

universe u

structure KKClass where
  degree : Nat
  support : Nat

structure UCTDatum where
  obstruction : Nat
  solved : Bool

structure BaumConnesDatum where
  assemblyWeight : Nat
  gammaWeight : Nat

structure DiracDualDiracDatum where
  diracWeight : Nat
  dualDiracWeight : Nat
  defect : Nat

structure EquivariantActionDatum where
  properDim : Nat
  groupRank : Nat
  descentRank : Nat

def kkPathCompose {X : Type u} {a b c : X}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def kasparovLeftWeight (x y : KKClass) : Nat :=
  x.degree + y.support

def kasparovRightWeight (x y : KKClass) : Nat :=
  y.degree + x.support

def kasparovProductWeight (x y : KKClass) : Nat :=
  x.degree + x.support + y.degree + y.support

def uctObstruction (U : UCTDatum) : Nat :=
  U.obstruction

def uctSolvedFlag (U : UCTDatum) : Bool :=
  U.solved

def assemblyMapWeight (B : BaumConnesDatum) : Nat :=
  B.assemblyWeight

def gammaElementWeight (B : BaumConnesDatum) : Nat :=
  B.gammaWeight

def diracElementWeight (D : DiracDualDiracDatum) : Nat :=
  D.diracWeight

def dualDiracElementWeight (D : DiracDualDiracDatum) : Nat :=
  D.dualDiracWeight

def diracDualDiracDefect (D : DiracDualDiracDatum) : Nat :=
  D.defect

def properActionDimension (E : EquivariantActionDatum) : Nat :=
  E.properDim

def equivariantKKWeight (E : EquivariantActionDatum) : Nat :=
  E.groupRank + E.descentRank

def baumConnesGap (B : BaumConnesDatum) : Nat :=
  B.assemblyWeight + B.gammaWeight

def descentWeight (E : EquivariantActionDatum) : Nat :=
  E.descentRank

def greenJulgWeight (E : EquivariantActionDatum) : Nat :=
  E.groupRank + E.properDim

def bottElementWeight (x : KKClass) : Nat :=
  x.degree + x.degree

def exteriorProductWeight (x y : KKClass) : Nat :=
  x.support + y.support

def moritaInvarianceWeight (x : KKClass) : Nat :=
  x.degree + x.support

def sixTermBoundaryWeight (x : KKClass) : Nat :=
  x.degree + 1

def coarseAssemblyWeight (B : BaumConnesDatum) (E : EquivariantActionDatum) : Nat :=
  assemblyMapWeight B + properActionDimension E

def localizationWeight (U : UCTDatum) (B : BaumConnesDatum) : Nat :=
  uctObstruction U + gammaElementWeight B

theorem kkPathCompose_refl {X : Type u} (a : X) :
    kkPathCompose (Path.refl a) (Path.refl a) =
      Path.trans (Path.refl a) (Path.refl a) := by
  sorry

theorem kasparovLeftWeight_def (x y : KKClass) :
    kasparovLeftWeight x y = x.degree + y.support := by
  sorry

theorem kasparovRightWeight_def (x y : KKClass) :
    kasparovRightWeight x y = y.degree + x.support := by
  sorry

theorem kasparovProductWeight_def (x y : KKClass) :
    kasparovProductWeight x y = x.degree + x.support + y.degree + y.support := by
  sorry

theorem uctObstruction_def (U : UCTDatum) :
    uctObstruction U = U.obstruction := by
  sorry

theorem uctSolvedFlag_def (U : UCTDatum) :
    uctSolvedFlag U = U.solved := by
  sorry

theorem assemblyMapWeight_def (B : BaumConnesDatum) :
    assemblyMapWeight B = B.assemblyWeight := by
  sorry

theorem gammaElementWeight_def (B : BaumConnesDatum) :
    gammaElementWeight B = B.gammaWeight := by
  sorry

theorem diracElementWeight_def (D : DiracDualDiracDatum) :
    diracElementWeight D = D.diracWeight := by
  sorry

theorem dualDiracElementWeight_def (D : DiracDualDiracDatum) :
    dualDiracElementWeight D = D.dualDiracWeight := by
  sorry

theorem diracDualDiracDefect_def (D : DiracDualDiracDatum) :
    diracDualDiracDefect D = D.defect := by
  sorry

theorem properActionDimension_def (E : EquivariantActionDatum) :
    properActionDimension E = E.properDim := by
  sorry

theorem equivariantKKWeight_def (E : EquivariantActionDatum) :
    equivariantKKWeight E = E.groupRank + E.descentRank := by
  sorry

theorem baumConnesGap_def (B : BaumConnesDatum) :
    baumConnesGap B = B.assemblyWeight + B.gammaWeight := by
  sorry

theorem descentWeight_def (E : EquivariantActionDatum) :
    descentWeight E = E.descentRank := by
  sorry

theorem greenJulgWeight_def (E : EquivariantActionDatum) :
    greenJulgWeight E = E.groupRank + E.properDim := by
  sorry

theorem bottElementWeight_def (x : KKClass) :
    bottElementWeight x = x.degree + x.degree := by
  sorry

theorem exteriorProductWeight_def (x y : KKClass) :
    exteriorProductWeight x y = x.support + y.support := by
  sorry

theorem moritaInvarianceWeight_def (x : KKClass) :
    moritaInvarianceWeight x = x.degree + x.support := by
  sorry

theorem localizationWeight_def (U : UCTDatum) (B : BaumConnesDatum) :
    localizationWeight U B = uctObstruction U + gammaElementWeight B := by
  sorry

end KKTheoryAdvanced
end Algebra
end Path
end ComputationalPaths
