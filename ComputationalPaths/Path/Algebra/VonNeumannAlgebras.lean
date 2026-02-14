import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace VonNeumannAlgebras

universe u

inductive FactorKind where
  | typeI
  | typeII
  | typeIII
deriving DecidableEq, Repr

structure VonNeumannAlgebra where
  carrier : Type u
  traceVal : carrier → Nat
  centerDim : Nat
  projectionCount : Nat
  kind : FactorKind

structure TomitaTakesakiDatum where
  modularOperator : Nat
  modularConjugation : Nat
  tomitaOperator : Nat
  flowParameter : Nat

structure ConnesDatum where
  tInvariant : Nat
  sInvariant : Nat
  injectiveClass : Nat

structure FreeProbabilityDatum where
  moment2 : Nat
  semicircularVar : Nat

structure SubfactorDatum where
  jonesIndex : Nat
  depth : Nat
  basicLevel : Nat

def vonPathCompose {X : Type u} {a b c : X}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

def predualDimension (M : VonNeumannAlgebra.{u}) : Nat :=
  M.centerDim + M.projectionCount

def projectionLatticeHeight (M : VonNeumannAlgebra.{u}) : Nat :=
  M.projectionCount

def centralSupport (M : VonNeumannAlgebra.{u}) : Nat :=
  M.centerDim

def typeCode (M : VonNeumannAlgebra.{u}) : Nat :=
  match M.kind with
  | FactorKind.typeI => 1
  | FactorKind.typeII => 2
  | FactorKind.typeIII => 3

def typeIWeight (M : VonNeumannAlgebra.{u}) : Nat :=
  match M.kind with
  | FactorKind.typeI => M.centerDim
  | _ => 0

def typeIIWeight (M : VonNeumannAlgebra.{u}) : Nat :=
  match M.kind with
  | FactorKind.typeII => M.projectionCount
  | _ => 0

def typeIIIWeight (M : VonNeumannAlgebra.{u}) : Nat :=
  match M.kind with
  | FactorKind.typeIII => M.centerDim + M.projectionCount
  | _ => 0

def modularOperatorWeight (T : TomitaTakesakiDatum) : Nat :=
  T.modularOperator

def modularConjugationWeight (T : TomitaTakesakiDatum) : Nat :=
  T.modularConjugation

def tomitaOperatorWeight (T : TomitaTakesakiDatum) : Nat :=
  T.tomitaOperator

def takesakiFlowWeight (T : TomitaTakesakiDatum) : Nat :=
  T.flowParameter

def connesTInvariant (C : ConnesDatum) : Nat :=
  C.tInvariant

def connesSInvariant (C : ConnesDatum) : Nat :=
  C.sInvariant

def connesInjectiveClass (C : ConnesDatum) : Nat :=
  C.injectiveClass

def injectiveFactorScore (C : ConnesDatum) : Nat :=
  C.injectiveClass + C.tInvariant

def freeProbabilityMoment (F : FreeProbabilityDatum) : Nat :=
  F.moment2

def semicircularVariance (F : FreeProbabilityDatum) : Nat :=
  F.semicircularVar

def jonesIndexValue (S : SubfactorDatum) : Nat :=
  S.jonesIndex

def subfactorDepth (S : SubfactorDatum) : Nat :=
  S.depth

def basicConstructionLevel (S : SubfactorDatum) : Nat :=
  S.basicLevel

def hyperfiniteApproximation (M : VonNeumannAlgebra.{u}) : Nat :=
  M.centerDim + M.projectionCount + typeCode M

def crossedProductWeight (M : VonNeumannAlgebra.{u}) (T : TomitaTakesakiDatum) : Nat :=
  predualDimension M + takesakiFlowWeight T

def bicentralizerSize (M : VonNeumannAlgebra.{u}) (C : ConnesDatum) : Nat :=
  centralSupport M + connesSInvariant C

def fullFactorIndicator (M : VonNeumannAlgebra.{u}) (C : ConnesDatum) : Nat :=
  typeCode M + connesTInvariant C + connesInjectiveClass C

theorem vonPathCompose_refl {X : Type u} (a : X) :
    vonPathCompose (Path.refl a) (Path.refl a) =
      Path.trans (Path.refl a) (Path.refl a) := by
  sorry

theorem predualDimension_def (M : VonNeumannAlgebra.{u}) :
    predualDimension M = M.centerDim + M.projectionCount := by
  sorry

theorem projectionLatticeHeight_def (M : VonNeumannAlgebra.{u}) :
    projectionLatticeHeight M = M.projectionCount := by
  sorry

theorem centralSupport_def (M : VonNeumannAlgebra.{u}) :
    centralSupport M = M.centerDim := by
  sorry

theorem typeCode_typeI (M : VonNeumannAlgebra.{u}) (h : M.kind = FactorKind.typeI) :
    typeCode M = 1 := by
  sorry

theorem typeCode_typeII (M : VonNeumannAlgebra.{u}) (h : M.kind = FactorKind.typeII) :
    typeCode M = 2 := by
  sorry

theorem typeCode_typeIII (M : VonNeumannAlgebra.{u}) (h : M.kind = FactorKind.typeIII) :
    typeCode M = 3 := by
  sorry

theorem typeIWeight_def (M : VonNeumannAlgebra.{u}) :
    typeIWeight M =
      match M.kind with
      | FactorKind.typeI => M.centerDim
      | _ => 0 := by
  sorry

theorem typeIIWeight_def (M : VonNeumannAlgebra.{u}) :
    typeIIWeight M =
      match M.kind with
      | FactorKind.typeII => M.projectionCount
      | _ => 0 := by
  sorry

theorem typeIIIWeight_def (M : VonNeumannAlgebra.{u}) :
    typeIIIWeight M =
      match M.kind with
      | FactorKind.typeIII => M.centerDim + M.projectionCount
      | _ => 0 := by
  sorry

theorem modularOperatorWeight_def (T : TomitaTakesakiDatum) :
    modularOperatorWeight T = T.modularOperator := by
  sorry

theorem modularConjugationWeight_def (T : TomitaTakesakiDatum) :
    modularConjugationWeight T = T.modularConjugation := by
  sorry

theorem tomitaOperatorWeight_def (T : TomitaTakesakiDatum) :
    tomitaOperatorWeight T = T.tomitaOperator := by
  sorry

theorem takesakiFlowWeight_def (T : TomitaTakesakiDatum) :
    takesakiFlowWeight T = T.flowParameter := by
  sorry

theorem connesTInvariant_def (C : ConnesDatum) :
    connesTInvariant C = C.tInvariant := by
  sorry

theorem connesSInvariant_def (C : ConnesDatum) :
    connesSInvariant C = C.sInvariant := by
  sorry

theorem connesInjectiveClass_def (C : ConnesDatum) :
    connesInjectiveClass C = C.injectiveClass := by
  sorry

theorem injectiveFactorScore_def (C : ConnesDatum) :
    injectiveFactorScore C = C.injectiveClass + C.tInvariant := by
  sorry

theorem freeProbabilityMoment_def (F : FreeProbabilityDatum) :
    freeProbabilityMoment F = F.moment2 := by
  sorry

theorem semicircularVariance_def (F : FreeProbabilityDatum) :
    semicircularVariance F = F.semicircularVar := by
  sorry

theorem jonesIndexValue_def (S : SubfactorDatum) :
    jonesIndexValue S = S.jonesIndex := by
  sorry

theorem fullFactorIndicator_def (M : VonNeumannAlgebra.{u}) (C : ConnesDatum) :
    fullFactorIndicator M C = typeCode M + connesTInvariant C + connesInjectiveClass C := by
  sorry

end VonNeumannAlgebras
end Algebra
end Path
end ComputationalPaths
