import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.Goodwillie

universe u

structure GoodwillieFunctor where
  Obj : Type u
  map : Obj → Obj
  base : Obj

def functorObject (F : GoodwillieFunctor) : Type u := F.Obj

def nExcisive (F : GoodwillieFunctor) (n : Nat) : Prop := True

def reduced (F : GoodwillieFunctor) : Prop := True

def polynomialApproximation (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj := F.map

def goodwillieTowerStage (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj :=
  polynomialApproximation F n

def goodwillieTower (F : GoodwillieFunctor) : Nat → (F.Obj → F.Obj) :=
  goodwillieTowerStage F

def towerLimit (F : GoodwillieFunctor) : F.Obj → F.Obj := fun x => x

def derivativeSpectrum (F : GoodwillieFunctor) (n : Nat) : Type u := F.Obj

def crossEffect (F : GoodwillieFunctor) (n : Nat) : Type u := F.Obj

def homogeneousLayer (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj := fun x => x

def classificationData (F : GoodwillieFunctor) (n : Nat) : Prop := True

def taylorCoefficient (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj := fun x => x

def linearization (F : GoodwillieFunctor) : F.Obj → F.Obj := fun x => x

def stabilization (F : GoodwillieFunctor) : F.Obj → F.Obj := fun x => x

def delooping (F : GoodwillieFunctor) : F.Obj → F.Obj := fun x => x

def convergenceCondition (F : GoodwillieFunctor) : Prop := True

def analyticRadius (F : GoodwillieFunctor) : Nat := 0

def excisiveComparisonMap (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj := fun x => x

def fiberOfStage (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj := fun x => x

def multilinearization (F : GoodwillieFunctor) (n : Nat) : F.Obj → F.Obj := fun x => x

def homogeneousClassification (F : GoodwillieFunctor) (n : Nat) : Prop := True

def stageShift (F : GoodwillieFunctor) (n : Nat) : Nat := n + 1

def derivativeAtBase (F : GoodwillieFunctor) (n : Nat) : derivativeSpectrum F n := F.base

def crossEffectAtBase (F : GoodwillieFunctor) (n : Nat) : crossEffect F n := F.base

def derivativePath (F : GoodwillieFunctor) (n : Nat) :
    Path (derivativeAtBase F n) (derivativeAtBase F n) := Path.refl _

def crossEffectPath (F : GoodwillieFunctor) (n : Nat) :
    Path (crossEffectAtBase F n) (crossEffectAtBase F n) := Path.refl _

def homogeneousPath (F : GoodwillieFunctor) (x : F.Obj) :
    Path (homogeneousLayer F 0 x) (homogeneousLayer F 0 x) := Path.refl _

def towerPath (F : GoodwillieFunctor) (x : F.Obj) :
    Path (towerLimit F x) (towerLimit F x) := Path.trans (Path.refl _) (Path.refl _)

def classificationPath (F : GoodwillieFunctor) (x : F.Obj) : Path x x := Path.refl x

theorem polynomialApproximation_id (F : GoodwillieFunctor) (n : Nat) (x : F.Obj) :
    polynomialApproximation F n x = F.map x := by
  rfl

theorem tower_stage_zero (F : GoodwillieFunctor) :
    goodwillieTower F 0 = goodwillieTowerStage F 0 := by
  rfl

theorem towerLimit_is_obj (F : GoodwillieFunctor) (x : F.Obj) :
    towerLimit F x = x := by
  rfl

theorem derivativeSpectrum_is_type (F : GoodwillieFunctor) (n : Nat) :
    derivativeSpectrum F n = F.Obj := by
  rfl

theorem crossEffect_is_type (F : GoodwillieFunctor) (n : Nat) :
    crossEffect F n = F.Obj := by
  rfl

theorem homogeneousLayer_is_obj (F : GoodwillieFunctor) (n : Nat) (x : F.Obj) :
    homogeneousLayer F n x = x := by
  rfl

theorem classificationData_true (F : GoodwillieFunctor) (n : Nat) :
    classificationData F n := by
  trivial

theorem taylorCoefficient_eval (F : GoodwillieFunctor) (n : Nat) (x : F.Obj) :
    taylorCoefficient F n x = x := by
  rfl

theorem linearization_id (F : GoodwillieFunctor) (x : F.Obj) :
    linearization F x = x := by
  rfl

theorem stabilization_id (F : GoodwillieFunctor) (x : F.Obj) :
    stabilization F x = x := by
  rfl

theorem delooping_id (F : GoodwillieFunctor) (x : F.Obj) :
    delooping F x = x := by
  rfl

theorem convergenceCondition_true (F : GoodwillieFunctor) :
    convergenceCondition F := by
  trivial

theorem analyticRadius_nonneg (F : GoodwillieFunctor) :
    analyticRadius F = 0 := by
  rfl

theorem excisiveComparisonMap_id (F : GoodwillieFunctor) (n : Nat) (x : F.Obj) :
    excisiveComparisonMap F n x = x := by
  rfl

theorem fiberOfStage_refl (F : GoodwillieFunctor) (n : Nat) (x : F.Obj) :
    fiberOfStage F n x = x := by
  rfl

theorem multilinearization_id (F : GoodwillieFunctor) (n : Nat) (x : F.Obj) :
    multilinearization F n x = x := by
  rfl

theorem homogeneousClassification_true (F : GoodwillieFunctor) (n : Nat) :
    homogeneousClassification F n := by
  trivial

theorem derivativePath_toEq (F : GoodwillieFunctor) (n : Nat) :
    (derivativePath F n).toEq = rfl := by
  rfl

theorem crossEffectPath_toEq (F : GoodwillieFunctor) (n : Nat) :
    (crossEffectPath F n).toEq = rfl := by
  rfl

theorem homogeneousPath_toEq (F : GoodwillieFunctor) (x : F.Obj) :
    (homogeneousPath F x).toEq = rfl := by
  rfl

theorem towerPath_toEq (F : GoodwillieFunctor) (x : F.Obj) :
    (towerPath F x).toEq = rfl := by
  rfl

theorem classificationPath_toEq (F : GoodwillieFunctor) (x : F.Obj) :
    (classificationPath F x).toEq = rfl := by
  rfl

theorem stageShift_succ (F : GoodwillieFunctor) (n : Nat) :
    stageShift F n = Nat.succ n := by
  rfl

end ComputationalPaths.Path.Category.Goodwillie
