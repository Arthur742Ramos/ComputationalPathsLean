import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.HigherTopos

universe u

structure InfinityTopos where
  Obj : Type u
  SheafObj : Type u
  hasColimits : Prop

structure DescentDatum (X : InfinityTopos) where
  cover : Type u
  glue : cover → X.Obj

structure GiraudAxioms where
  finiteLimits : Prop
  disjointCoproducts : Prop
  universalColimits : Prop
  effectiveEquivalenceRelations : Prop

structure HypercompleteTopos where
  base : InfinityTopos
  hyperdescent : Prop

structure NTopos where
  truncationLevel : Nat
  underlying : InfinityTopos

structure ShapeTheory where
  base : InfinityTopos
  shapeObj : Type u

structure EtaleHomotopyType where
  base : InfinityTopos
  proSpace : Type u

structure ProfiniteShape where
  source : ShapeTheory
  profiniteObj : Type u

def objectType (X : InfinityTopos) : Type u := X.Obj

def sheafType (X : InfinityTopos) : Type u := X.SheafObj

def hasColimitsProp (X : InfinityTopos) : Prop := X.hasColimits

def descentCover {X : InfinityTopos} (D : DescentDatum X) : Type u := D.cover

def descentGluing {X : InfinityTopos} (D : DescentDatum X) : D.cover → X.Obj := D.glue

def constantDescent (X : InfinityTopos) (x0 : X.Obj) : DescentDatum X :=
  { cover := PUnit, glue := fun _ => x0 }

def localToGlobal (_X : InfinityTopos) : Prop := True

def stackCondition (_X : InfinityTopos) : Prop := True

def giraudHolds (A : GiraudAxioms) : Prop :=
  A.finiteLimits ∧ A.disjointCoproducts ∧ A.universalColimits ∧
    A.effectiveEquivalenceRelations

def toposSatisfiesGiraud (_X : InfinityTopos) (A : GiraudAxioms) : Prop := giraudHolds A

def hypercompletionOf (X : InfinityTopos) : HypercompleteTopos :=
  { base := X, hyperdescent := True }

def isHypercomplete (H : HypercompleteTopos) : Prop := H.hyperdescent

def hypercompletionUnderlying (H : HypercompleteTopos) : InfinityTopos := H.base

def nToposLevel (N : NTopos) : Nat := N.truncationLevel

def nToposBase (N : NTopos) : InfinityTopos := N.underlying

def shapeObject (S : ShapeTheory) : Type u := S.shapeObj

def shapePi0 (_S : ShapeTheory) : Nat := 0

def etaleShapeObject (E : EtaleHomotopyType) : Type u := E.proSpace

def etaleFundamentalGroup (_E : EtaleHomotopyType) : Nat := 0

def profiniteCompletion (S : ShapeTheory) : ProfiniteShape :=
  { source := S, profiniteObj := PUnit }

def profiniteShapeObject (P : ProfiniteShape) : Type u := P.profiniteObj

def profiniteShapeMap (P : ProfiniteShape) : Type u := P.source.shapeObj

def postnikovStage (_X : InfinityTopos) (n : Nat) : Nat := n

def hyperdescentTowerLength (_H : HypercompleteTopos) : Nat := 0

def boundedCohomologicalDim (_X : InfinityTopos) : Nat := 0

def descentIdentityPath (X : InfinityTopos) : Path X X :=
  Path.trans (Path.refl X) (Path.refl X)

def hypercompleteIdentityPath (H : HypercompleteTopos) : Path H H := Path.refl H

def profiniteComparisonPath (P : ProfiniteShape) : Path P P :=
  Path.trans (Path.refl P) (Path.refl P)

theorem objectType_eq (X : InfinityTopos) : objectType X = X.Obj := by
  sorry

theorem sheafType_eq (X : InfinityTopos) : sheafType X = X.SheafObj := by
  sorry

theorem hasColimitsProp_iff (X : InfinityTopos) :
    hasColimitsProp X ↔ X.hasColimits := by
  sorry

theorem descentCover_eq {X : InfinityTopos} (D : DescentDatum X) :
    descentCover D = D.cover := by
  sorry

theorem descentGluing_eq {X : InfinityTopos} (D : DescentDatum X) :
    descentGluing D = D.glue := by
  sorry

theorem localToGlobal_true (X : InfinityTopos) : localToGlobal X := by
  sorry

theorem stackCondition_true (X : InfinityTopos) : stackCondition X := by
  sorry

theorem giraudHolds_proj_finite (A : GiraudAxioms) :
    giraudHolds A → A.finiteLimits := by
  sorry

theorem giraudHolds_proj_disjoint (A : GiraudAxioms) :
    giraudHolds A → A.disjointCoproducts := by
  sorry

theorem giraudHolds_proj_universal (A : GiraudAxioms) :
    giraudHolds A → A.universalColimits := by
  sorry

theorem giraudHolds_proj_effective (A : GiraudAxioms) :
    giraudHolds A → A.effectiveEquivalenceRelations := by
  sorry

theorem toposSatisfiesGiraud_of_data (X : InfinityTopos) (A : GiraudAxioms) :
    giraudHolds A → toposSatisfiesGiraud X A := by
  sorry

theorem hypercompletionUnderlying_eq (H : HypercompleteTopos) :
    hypercompletionUnderlying H = H.base := by
  sorry

theorem isHypercomplete_of_hyperdescent (H : HypercompleteTopos) :
    H.hyperdescent → isHypercomplete H := by
  sorry

theorem nToposLevel_eq (N : NTopos) : nToposLevel N = N.truncationLevel := by
  sorry

theorem nToposBase_eq (N : NTopos) : nToposBase N = N.underlying := by
  sorry

theorem shapeObject_eq (S : ShapeTheory) : shapeObject S = S.shapeObj := by
  sorry

theorem etaleShapeObject_eq (E : EtaleHomotopyType) :
    etaleShapeObject E = E.proSpace := by
  sorry

theorem etaleFundamentalGroup_nonnegative (E : EtaleHomotopyType) :
    0 ≤ etaleFundamentalGroup E := by
  sorry

theorem profiniteCompletion_source (S : ShapeTheory) :
    (profiniteCompletion S).source = S := by
  sorry

theorem profiniteShapeObject_eq (P : ProfiniteShape) :
    profiniteShapeObject P = P.profiniteObj := by
  sorry

theorem profiniteShapeMap_eq (P : ProfiniteShape) :
    profiniteShapeMap P = P.source.shapeObj := by
  sorry

theorem postnikovStage_zero (X : InfinityTopos) :
    postnikovStage X 0 = 0 := by
  sorry

theorem hyperdescentTowerLength_nonnegative (H : HypercompleteTopos) :
    0 ≤ hyperdescentTowerLength H := by
  sorry

theorem boundedCohomologicalDim_nonnegative (X : InfinityTopos) :
    0 ≤ boundedCohomologicalDim X := by
  sorry

theorem descentIdentityPath_toEq (X : InfinityTopos) :
    (descentIdentityPath X).toEq = rfl := by
  sorry

theorem hypercompleteIdentityPath_toEq (H : HypercompleteTopos) :
    (hypercompleteIdentityPath H).toEq = rfl := by
  sorry

theorem profiniteComparisonPath_toEq (P : ProfiniteShape) :
    (profiniteComparisonPath P).toEq = rfl := by
  sorry

theorem profiniteCompletion_idempotent (S : ShapeTheory) :
    profiniteCompletion S = profiniteCompletion S := by
  sorry

end ComputationalPaths.Path.Algebra.HigherTopos
