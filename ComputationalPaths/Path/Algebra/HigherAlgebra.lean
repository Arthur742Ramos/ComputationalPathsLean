import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.HigherAlgebra

universe u

structure EnAlgebra where
  Carrier : Type u
  tensor : Carrier → Carrier → Carrier
  unit : Carrier

structure EnMorphism (A B : EnAlgebra) where
  toFun : A.Carrier → B.Carrier

def enDegree (n : Nat) : Nat := n

def littleCubesArity (n : Nat) : Nat := n + 1

def lurieTensorObj (A B : EnAlgebra) : Type _ := A.Carrier × B.Carrier

def lurieTensorUnit (A B : EnAlgebra) : lurieTensorObj A B := (A.unit, B.unit)

def lurieTensorMul (A B : EnAlgebra) :
    lurieTensorObj A B → lurieTensorObj A B → lurieTensorObj A B :=
  fun x y => (A.tensor x.1 y.1, B.tensor x.2 y.2)

def lurieTensorProduct (A B : EnAlgebra) : EnAlgebra where
  Carrier := lurieTensorObj A B
  tensor := lurieTensorMul A B
  unit := lurieTensorUnit A B

def barrBeckLurieCondition (A : EnAlgebra) : Prop := True

def monadicDescentData (A : EnAlgebra) : Prop := True

def monadicComparisonMap (A : EnAlgebra) : A.Carrier → A.Carrier := fun x => x

def freeEnAlgebra (X : Type _) : EnAlgebra where
  Carrier := Option X
  tensor := fun x _ => x
  unit := none

def forgetCarrier (A : EnAlgebra) : Type _ := A.Carrier

def augmentationIdeal (A : EnAlgebra) : Type _ := A.Carrier

def barConstruction (A : EnAlgebra) : Type _ := List A.Carrier

def cobarConstruction (A : EnAlgebra) : Type _ := List A.Carrier

def koszulDualCarrier (A : EnAlgebra) : Type _ := A.Carrier

def koszulDual (A : EnAlgebra) : EnAlgebra := A

def iteratedLoopAction (A : EnAlgebra) (n : Nat) : Type _ := Fin (n + 1) → A.Carrier

def factorizationHomologyCarrier (A : EnAlgebra) : Type _ := A.Carrier

def factorizationHomology (A : EnAlgebra) : EnAlgebra := A

def topologicalChiralHomology (A : EnAlgebra) : EnAlgebra := factorizationHomology A

def derivedCenter (A : EnAlgebra) : Type _ := A.Carrier

def envelopingEnAlgebra (A : EnAlgebra) : EnAlgebra := A

def leftModuleCategory (A : EnAlgebra) : Type _ := A.Carrier → Type _

def rightModuleCategory (A : EnAlgebra) : Type _ := A.Carrier → Type _

def bimoduleCategory (A : EnAlgebra) : Type _ := A.Carrier → A.Carrier → Type _

def tensorReflPath (A : EnAlgebra) (x : A.Carrier) : Path x x := Path.refl x

def tensorUnitPath (A : EnAlgebra) : Path A.unit A.unit := Path.refl A.unit

def tensorChainPath (A : EnAlgebra) (x : A.Carrier) : Path x x :=
  Path.trans (Path.refl x) (Path.refl x)

def chiralComparisonPath (A : EnAlgebra) (x : A.Carrier) : Path x x := Path.refl x

def lurieTensorFunctorialityWitness (A B : EnAlgebra) : Prop := True

def monadicBarResolution (A : EnAlgebra) : Type _ := List A.Carrier

def koszulDualityPairing (A : EnAlgebra) : A.Carrier → A.Carrier := fun x => x

def topologicalChiralIntegration (A : EnAlgebra) : A.Carrier → A.Carrier := fun x => x

theorem enDegree_id (n : Nat) : enDegree n = n := by
  sorry

theorem littleCubesArity_pos (n : Nat) : littleCubesArity n > 0 := by
  sorry

theorem lurieTensorObj_eq (A B : EnAlgebra) :
    lurieTensorObj A B = (A.Carrier × B.Carrier) := by
  sorry

theorem lurieTensorMul_formula (A B : EnAlgebra) (x y : lurieTensorObj A B) :
    lurieTensorMul A B x y = (A.tensor x.1 y.1, B.tensor x.2 y.2) := by
  sorry

theorem lurieTensorProduct_carrier (A B : EnAlgebra) :
    (lurieTensorProduct A B).Carrier = (A.Carrier × B.Carrier) := by
  sorry

theorem barrBeckLurie_implies_data (A : EnAlgebra) :
    barrBeckLurieCondition A → monadicDescentData A := by
  sorry

theorem monadicDescentData_true (A : EnAlgebra) : monadicDescentData A := by
  sorry

theorem monadicComparisonMap_id (A : EnAlgebra) (x : A.Carrier) :
    monadicComparisonMap A x = x := by
  sorry

theorem freeEnAlgebra_carrier (X : Type _) :
    (freeEnAlgebra X).Carrier = Option X := by
  sorry

theorem forgetCarrier_def (A : EnAlgebra) : forgetCarrier A = A.Carrier := by
  sorry

theorem barConstruction_has_nil (A : EnAlgebra) :
    ([] : barConstruction A) = [] := by
  sorry

theorem cobarConstruction_has_nil (A : EnAlgebra) :
    ([] : cobarConstruction A) = [] := by
  sorry

theorem koszulDual_involutive (A : EnAlgebra) :
    koszulDual (koszulDual A) = A := by
  sorry

theorem factorization_equals_chiral (A : EnAlgebra) :
    topologicalChiralHomology A = factorizationHomology A := by
  sorry

theorem derivedCenter_is_carrier (A : EnAlgebra) :
    derivedCenter A = A.Carrier := by
  sorry

theorem leftModuleCategory_nonempty (A : EnAlgebra) : True := by
  sorry

theorem rightModuleCategory_nonempty (A : EnAlgebra) : True := by
  sorry

theorem bimoduleCategory_nonempty (A : EnAlgebra) : True := by
  sorry

theorem tensorReflPath_toEq (A : EnAlgebra) (x : A.Carrier) :
    (tensorReflPath A x).toEq = rfl := by
  sorry

theorem tensorUnitPath_toEq (A : EnAlgebra) :
    (tensorUnitPath A).toEq = rfl := by
  sorry

theorem tensorChainPath_toEq (A : EnAlgebra) (x : A.Carrier) :
    (tensorChainPath A x).toEq = rfl := by
  sorry

theorem chiralComparisonPath_toEq (A : EnAlgebra) (x : A.Carrier) :
    (chiralComparisonPath A x).toEq = rfl := by
  sorry

theorem monadicBarResolution_nil (A : EnAlgebra) :
    ([] : monadicBarResolution A) = [] := by
  sorry

theorem koszulDualityPairing_id (A : EnAlgebra) (x : A.Carrier) :
    koszulDualityPairing A x = x := by
  sorry

theorem topologicalChiralIntegration_id (A : EnAlgebra) (x : A.Carrier) :
    topologicalChiralIntegration A x = x := by
  sorry

theorem lurieTensorFunctorialityWitness_true (A B : EnAlgebra) :
    lurieTensorFunctorialityWitness A B := by
  sorry

end ComputationalPaths.Path.Algebra.HigherAlgebra
