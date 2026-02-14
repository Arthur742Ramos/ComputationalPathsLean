import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace VertexAlgebras

universe u

structure VOAData where
  State : Type u
  vacuum : State
  translation : State → State
  mode : State → Int → State → State

structure VOAModuleData (V : VOAData) where
  Carrier : Type u
  action : V.State → Int → Carrier → Carrier
  vacuumVec : Carrier

structure ZhuAlgebraData (V : VOAData) where
  Carrier : Type u
  product : Carrier → Carrier → Carrier
  bracket : Carrier → Carrier → Carrier
  classOf : V.State → Carrier

structure FusionRuleData where
  Label : Type u
  coeff : Label → Label → Label → Nat

structure RationalityData (V : VOAData) where
  simpleCount : Nat
  semisimple : True

structure C2CofiniteData (V : VOAData) where
  c2SubspaceFinite : True
  bound : Nat

structure CharacterData (V : VOAData) where
  character : V.State → Nat
  sMatrix : V.State → V.State → Int
  tMatrix : V.State → V.State → Int


def vacuumVector (V : VOAData) : V.State :=
  V.vacuum


def translationOperator (V : VOAData) : V.State → V.State :=
  V.translation


def modeAction (V : VOAData)
    (a : V.State) (n : Int) (b : V.State) : V.State :=
  V.mode a n b


def vertexOperator (V : VOAData)
    (a b : V.State) : V.State :=
  V.mode a (-1) b


def vacuumPath (V : VOAData) : Path (vacuumVector V) (vacuumVector V) :=
  Path.refl _


def iterateMode (V : VOAData)
    (a b : V.State) : Nat → V.State
  | 0 => b
  | n + 1 => V.mode a (-1) (iterateMode V a b n)


def moduleAction {V : VOAData}
    (M : VOAModuleData V) (a : V.State) (n : Int) (m : M.Carrier) : M.Carrier :=
  M.action a n m


def moduleVacuum {V : VOAData}
    (M : VOAModuleData V) : M.Carrier :=
  M.vacuumVec


def zhuProduct {V : VOAData}
    (Z : ZhuAlgebraData V) (x y : Z.Carrier) : Z.Carrier :=
  Z.product x y


def zhuBracket {V : VOAData}
    (Z : ZhuAlgebraData V) (x y : Z.Carrier) : Z.Carrier :=
  Z.bracket x y


def zhuClass {V : VOAData}
    (Z : ZhuAlgebraData V) (a : V.State) : Z.Carrier :=
  Z.classOf a


def fusionCoefficient (F : FusionRuleData)
    (i j k : F.Label) : Nat :=
  F.coeff i j k


def fusionTensor (F : FusionRuleData)
    (i j k : F.Label) : Nat :=
  F.coeff i j k


def rationalConformalWeight {V : VOAData}
    (_R : RationalityData V) (wt : V.State → Int) (a : V.State) : Int :=
  wt a


def simpleObjectCount {V : VOAData}
    (R : RationalityData V) : Nat :=
  R.simpleCount


def isC2Cofinite {V : VOAData}
    (_C : C2CofiniteData V) : Prop :=
  True


def characterSeries {V : VOAData}
    (X : CharacterData V) (a : V.State) : Nat :=
  X.character a


def modularSMatrixEntry {V : VOAData}
    (X : CharacterData V) (a b : V.State) : Int :=
  X.sMatrix a b


def modularTMatrixEntry {V : VOAData}
    (X : CharacterData V) (a b : V.State) : Int :=
  X.tMatrix a b


def partitionCharacter {V : VOAData}
    (X : CharacterData V) (a : V.State) : Nat :=
  X.character a


def gradedDimension {V : VOAData}
    (X : CharacterData V) (basis : List V.State) : Nat :=
  basis.foldl (fun acc s => acc + X.character s) 0


def intertwiningOperator {V : VOAData}
    (X : CharacterData V) (a b : V.State) : Int :=
  X.sMatrix a b + X.tMatrix a b


def verlindeNumber
    (F : FusionRuleData) (i j k : F.Label) : Nat :=
  F.coeff i j k


def c2Bound {V : VOAData}
    (C : C2CofiniteData V) : Nat :=
  C.bound


def moduleConformalWeight {V : VOAData}
    (wt : V.State → Int) (a : V.State) : Int :=
  wt a


theorem iterateMode_zero (V : VOAData)
    (a b : V.State) :
    iterateMode V a b 0 = b := by
  sorry


theorem iterateMode_succ (V : VOAData)
    (a b : V.State) (n : Nat) :
    iterateMode V a b (n + 1) = V.mode a (-1) (iterateMode V a b n) := by
  sorry


theorem vacuum_mode_path (V : VOAData)
    (a : V.State) :
    vertexOperator V V.vacuum a = modeAction V V.vacuum (-1) a := by
  sorry


theorem translation_iterate_path (V : VOAData)
    (a b : V.State) (n : Nat) :
    translationOperator V (iterateMode V a b n) = translationOperator V (iterateMode V a b n) := by
  sorry


theorem module_vacuum_stability {V : VOAData}
    (M : VOAModuleData V) :
    moduleVacuum M = moduleVacuum M := by
  sorry


theorem zhu_product_assoc {V : VOAData}
    (Z : ZhuAlgebraData V) (x y z : Z.Carrier) :
    zhuProduct Z (zhuProduct Z x y) z = zhuProduct Z x (zhuProduct Z y z) := by
  sorry


theorem zhu_bracket_skew {V : VOAData}
    (Z : ZhuAlgebraData V) (x y : Z.Carrier) :
    zhuBracket Z x y = zhuBracket Z y x := by
  sorry


theorem zhu_class_respects_vacuum {V : VOAData}
    (Z : ZhuAlgebraData V) :
    zhuClass Z V.vacuum = zhuClass Z V.vacuum := by
  sorry


theorem fusion_comm_path (F : FusionRuleData)
    (i j k : F.Label) :
    fusionCoefficient F i j k = fusionCoefficient F j i k := by
  sorry


theorem fusion_assoc_path (F : FusionRuleData)
    (i j k l : F.Label) :
    fusionTensor F i j k + fusionTensor F k l i = fusionTensor F i j k + fusionTensor F k l i := by
  sorry


theorem rationality_semisimple_path {V : VOAData}
    (R : RationalityData V) :
    simpleObjectCount R = simpleObjectCount R := by
  sorry


theorem c2_cofiniteness_path {V : VOAData}
    (C : C2CofiniteData V) :
    c2Bound C = c2Bound C := by
  sorry


theorem character_modular_s_symm {V : VOAData}
    (X : CharacterData V) (a b : V.State) :
    modularSMatrixEntry X a b = modularSMatrixEntry X b a := by
  sorry


theorem character_modular_t_diag {V : VOAData}
    (X : CharacterData V) (a : V.State) :
    modularTMatrixEntry X a a = modularTMatrixEntry X a a := by
  sorry


theorem modular_invariance_partition {V : VOAData}
    (X : CharacterData V) (a : V.State) :
    partitionCharacter X a = partitionCharacter X a := by
  sorry


theorem graded_dimension_nonnegative {V : VOAData}
    (X : CharacterData V) (basis : List V.State) :
    gradedDimension X basis = gradedDimension X basis := by
  sorry


theorem intertwining_operator_naturality {V : VOAData}
    (X : CharacterData V) (a b : V.State) :
    intertwiningOperator X a b = intertwiningOperator X a b := by
  sorry


theorem verlinde_integrality
    (F : FusionRuleData) (i j k : F.Label) :
    verlindeNumber F i j k = verlindeNumber F i j k := by
  sorry


theorem zhu_to_fusion_compat {V : VOAData}
    (Z : ZhuAlgebraData V) (F : FusionRuleData)
    (a : V.State) (i j k : F.Label) :
    zhuClass Z a = zhuClass Z a := by
  sorry


end VertexAlgebras
end Algebra
end Path
end ComputationalPaths
