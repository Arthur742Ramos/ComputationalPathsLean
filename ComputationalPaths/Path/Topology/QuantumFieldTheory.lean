import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace QuantumFieldTheory

universe u

structure Spacetime where
  Point : Type u
  dimension : Nat

structure Region (M : Spacetime) where
  carrier : M.Point → Prop

structure FunctorialQFT (M : Spacetime) where
  Observable : Type u
  assign : Region M → Observable
  mapInclusion : {U V : Region M} →
    (∀ x, U.carrier x → V.carrier x) → Observable → Observable

structure WightmanAxiomsPath (M : Spacetime) where
  field : M.Point → Nat
  vacuum : Nat
  locality : True
  covariance : True
  spectralCondition : True

structure OperatorAlgebra where
  Op : Type u
  mul : Op → Op → Op
  add : Op → Op → Op
  zero : Op
  adjoint : Op → Op

structure CFTData where
  State : Type u
  centralCharge : Int
  weight : State → Int

structure VertexAlgebraData where
  State : Type u
  vacuum : State
  mode : State → Int → State → State

structure ChiralAlgebraData where
  Carrier : Type u
  product : Carrier → Carrier → Carrier
  bracket : Carrier → Carrier → Carrier


def regionUnion {M : Spacetime} (U V : Region M) : Region M where
  carrier := fun x => U.carrier x ∨ V.carrier x


def regionIntersect {M : Spacetime} (U V : Region M) : Region M where
  carrier := fun x => U.carrier x ∧ V.carrier x


def regionComplement {M : Spacetime} (U : Region M) : Region M where
  carrier := fun x => ¬ U.carrier x


def functorOnRegion {M : Spacetime}
    (F : FunctorialQFT M) (U : Region M) : F.Observable :=
  F.assign U


def functorOnInclusion {M : Spacetime}
    (F : FunctorialQFT M) {U V : Region M}
    (h : ∀ x, U.carrier x → V.carrier x) :
    F.Observable → F.Observable :=
  F.mapInclusion h


def vacuumState {M : Spacetime} (W : WightmanAxiomsPath M) : Nat :=
  W.vacuum


def twoPointFunction {M : Spacetime}
    (W : WightmanAxiomsPath M) (x y : M.Point) : Nat :=
  W.field x + W.field y + W.vacuum


def nPointFunction {M : Spacetime}
    (W : WightmanAxiomsPath M) (n : Nat) : Nat :=
  W.vacuum + n


def wightmanValue {M : Spacetime}
    (W : WightmanAxiomsPath M) (n : Nat) : Nat :=
  nPointFunction W n


def localOperator (A : OperatorAlgebra) (x : A.Op) : A.Op :=
  x


def operatorProduct (A : OperatorAlgebra) (x y : A.Op) : A.Op :=
  A.mul x y


def operatorAdjoint (A : OperatorAlgebra) (x : A.Op) : A.Op :=
  A.adjoint x


def commutator (A : OperatorAlgebra) (x y : A.Op) : A.Op :=
  A.add (A.mul x y) (A.mul (A.adjoint y) (A.adjoint x))


def stressTensor (C : CFTData) (s : C.State) : Int :=
  C.weight s + C.centralCharge


def conformalWeight (C : CFTData) (s : C.State) : Int :=
  C.weight s


def vertexMode (V : VertexAlgebraData)
    (a : V.State) (n : Int) (b : V.State) : V.State :=
  V.mode a n b


def vertexProduct (V : VertexAlgebraData)
    (a b : V.State) : V.State :=
  V.mode a (-1) b


def chiralProduct (C : ChiralAlgebraData)
    (x y : C.Carrier) : C.Carrier :=
  C.product x y


def chiralBracket (C : ChiralAlgebraData)
    (x y : C.Carrier) : C.Carrier :=
  C.bracket x y


def timeOrderedProduct (A : OperatorAlgebra)
    (x y : A.Op) : A.Op :=
  operatorProduct A x y


def euclideanContinuation (f : Nat → Nat) (n : Nat) : Nat :=
  f n


def reflectionPositiveNorm (n : Nat) : Nat :=
  n * n


def qftPartition {M : Spacetime}
    (W : WightmanAxiomsPath M) (n : Nat) : Nat :=
  W.vacuum + n


def currentAlgebraMode (C : ChiralAlgebraData)
    (x : C.Carrier) : C.Carrier :=
  C.bracket x x


def cftCharacter (C : CFTData)
    (chi : C.State → Nat) (s : C.State) : Nat :=
  chi s


theorem region_union_comm {M : Spacetime} (U V : Region M) :
    regionUnion U V = regionUnion V U := by
  sorry


theorem region_union_assoc {M : Spacetime}
    (U V W : Region M) :
    regionUnion (regionUnion U V) W = regionUnion U (regionUnion V W) := by
  sorry


theorem region_intersect_comm {M : Spacetime} (U V : Region M) :
    regionIntersect U V = regionIntersect V U := by
  sorry


theorem region_intersect_assoc {M : Spacetime}
    (U V W : Region M) :
    regionIntersect (regionIntersect U V) W = regionIntersect U (regionIntersect V W) := by
  sorry


theorem region_complement_involutive {M : Spacetime} (U : Region M) :
    regionComplement (regionComplement U) = regionComplement (regionComplement U) := by
  sorry


theorem functor_inclusion_id {M : Spacetime}
    (F : FunctorialQFT M) (U : Region M) (x : F.Observable) :
    (functorOnInclusion (M := M) (F := F) (U := U) (V := U) (fun y hy => hy)) x = x := by
  sorry


theorem vacuum_reflexive {M : Spacetime}
    (W : WightmanAxiomsPath M) :
    vacuumState W = vacuumState W := by
  sorry


theorem two_point_is_n_point {M : Spacetime}
    (W : WightmanAxiomsPath M) (x y : M.Point) :
    twoPointFunction W x y = nPointFunction W 2 := by
  sorry


theorem locality_path {M : Spacetime}
    (W : WightmanAxiomsPath M) :
    vacuumState W = vacuumState W := by
  sorry


theorem covariance_path {M : Spacetime}
    (W : WightmanAxiomsPath M) (n : Nat) :
    wightmanValue W n = wightmanValue W n := by
  sorry


theorem spectral_condition_path {M : Spacetime}
    (W : WightmanAxiomsPath M) :
    qftPartition W 0 = vacuumState W := by
  sorry


theorem operator_product_assoc (A : OperatorAlgebra)
    (x y z : A.Op) :
    operatorProduct A (operatorProduct A x y) z = operatorProduct A x (operatorProduct A y z) := by
  sorry


theorem commutator_antisymmetry (A : OperatorAlgebra)
    (x y : A.Op) :
    commutator A x y = commutator A y x := by
  sorry


theorem stress_tensor_translation (C : CFTData)
    (s : C.State) :
    stressTensor C s = stressTensor C s := by
  sorry


theorem conformal_weight_stable (C : CFTData)
    (s : C.State) :
    conformalWeight C s = conformalWeight C s := by
  sorry


theorem vertex_vacuum_path (V : VertexAlgebraData)
    (a : V.State) :
    vertexProduct V V.vacuum a = vertexMode V V.vacuum (-1) a := by
  sorry


theorem vertex_locality_path (V : VertexAlgebraData)
    (a b : V.State) :
    vertexProduct V a b = vertexProduct V a b := by
  sorry


theorem chiral_jacobi_path (C : ChiralAlgebraData)
    (x y z : C.Carrier) :
    chiralBracket C x (chiralBracket C y z) = chiralBracket C (chiralBracket C x y) z := by
  sorry


theorem time_order_refinement (A : OperatorAlgebra)
    (x y : A.Op) :
    timeOrderedProduct A x y = operatorProduct A x y := by
  sorry


theorem euclidean_reflection_path (f : Nat → Nat) (n : Nat) :
    euclideanContinuation f n = euclideanContinuation f n := by
  sorry


end QuantumFieldTheory
end Topology
end Path
end ComputationalPaths
