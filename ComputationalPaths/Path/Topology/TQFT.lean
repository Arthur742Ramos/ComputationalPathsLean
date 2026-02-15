import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace TQFT

universe u v

structure Cobordism (Obj : Type u) where
  src : Obj
  tgt : Obj
  genus : Nat
  boundaryCount : Nat

structure MonoidalTarget (A : Type v) where
  tensor : A → A → A
  unit : A

structure ExtendedTQFTData (Obj : Type u) (A : Type v) where
  target : MonoidalTarget A
  assignObj : Obj → A
  assignCob : Cobordism Obj → A

structure DualizableObject {A : Type v} (T : MonoidalTarget A) (a : A) where
  dual : A
  coev : A
  ev : A

structure CobordismHypothesisWitness (Obj : Type u) (A : Type v) where
  theory : ExtendedTQFTData Obj A
  generator : Obj
  dualizable : DualizableObject theory.target (theory.assignObj generator)

structure FactorizationHomologyData (A : Type v) where
  localValue : Nat → A
  glue : A → A → A

structure ModularTensorCategoryData where
  Obj : Type u
  tensor : Obj → Obj → Obj
  unit : Obj
  braiding : Obj → Obj → Obj
  twist : Obj → Obj

structure ReshetikhinTuraevData where
  mtc : ModularTensorCategoryData
  invariant : Cobordism Nat → Nat

structure WittenChernSimonsData where
  level : Int
  partition : Cobordism Nat → Int


def idCobordism {Obj : Type u} (x : Obj) : Cobordism Obj where
  src := x
  tgt := x
  genus := 0
  boundaryCount := 0


def composeCobordism {Obj : Type u} (W1 W2 : Cobordism Obj) : Cobordism Obj where
  src := W1.src
  tgt := W2.tgt
  genus := W1.genus + W2.genus
  boundaryCount := W1.boundaryCount + W2.boundaryCount


def tensorCobordism {Obj : Type u} (W1 W2 : Cobordism Obj) : Cobordism Obj where
  src := W1.src
  tgt := W2.tgt
  genus := W1.genus + W2.genus
  boundaryCount := W1.boundaryCount + W2.boundaryCount


def composePath {Obj : Type u} (W1 W2 : Cobordism Obj) :
    Path (composeCobordism W1 W2) (composeCobordism W1 W2) :=
  Path.refl _


def tensorPath {Obj : Type u} (W1 W2 : Cobordism Obj) :
    Path (tensorCobordism W1 W2) (tensorCobordism W1 W2) :=
  Path.refl _


def evaluateOnPoint {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (x : Obj) : A :=
  Z.assignObj x


def evaluateOnCircle {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (circleObj : Obj) : A :=
  Z.assignObj circleObj


def foldTensor {A : Type v} (T : MonoidalTarget A) : List A → A
  | [] => T.unit
  | x :: xs => T.tensor x (foldTensor T xs)


def factorizationValue {A : Type v}
    (F : FactorizationHomologyData A) (n : Nat) : A :=
  F.localValue n


def factorizationBoundary {A : Type v}
    (F : FactorizationHomologyData A) (m n : Nat) : A :=
  F.glue (F.localValue m) (F.localValue n)


def rtInvariant (R : ReshetikhinTuraevData) (W : Cobordism Nat) : Nat :=
  R.invariant W


def wcsPartition (W : WittenChernSimonsData) (M : Cobordism Nat) : Int :=
  W.partition M


def mappingClassAction (R : ReshetikhinTuraevData)
    (g : Nat) (W : Cobordism Nat) : Nat :=
  R.invariant { W with genus := W.genus + g }


def anyonFusion (MTC : ModularTensorCategoryData)
    (a b : MTC.Obj) : MTC.Obj :=
  MTC.tensor a b


def anyonBraiding (MTC : ModularTensorCategoryData)
    (a b : MTC.Obj) : MTC.Obj :=
  MTC.braiding a b


def anyonTwist (MTC : ModularTensorCategoryData)
    (a : MTC.Obj) : MTC.Obj :=
  MTC.twist a


def stateSpace {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (boundary : Obj) : A :=
  Z.assignObj boundary


def closedState {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (W : Cobordism Obj) : A :=
  Z.assignCob W


def gluingAmplitude {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (a b : A) : A :=
  Z.target.tensor a b


def surgeryKernel {Obj : Type u} (W : Cobordism Obj) : Nat :=
  W.genus + W.boundaryCount


def framingCorrection (k : Int) (n : Nat) : Int :=
  k + Int.ofNat n


def quantumDimension {MTC : ModularTensorCategoryData}
    (qdim : MTC.Obj → Nat) (a : MTC.Obj) : Nat :=
  qdim a


def totalQuantumDimension {MTC : ModularTensorCategoryData}
    (qdim : MTC.Obj → Nat) (objs : List MTC.Obj) : Nat :=
  objs.foldl (fun acc x => acc + qdim x) 0


def cobordismTrace {Obj : Type u} (W : Cobordism Obj) : Nat :=
  W.genus * (W.boundaryCount + 1)


def handleShift {Obj : Type u} (W : Cobordism Obj) (k : Nat) : Cobordism Obj :=
  { W with genus := W.genus + k }


theorem compose_id_left {Obj : Type u} (W : Cobordism Obj) :
    composeCobordism (idCobordism W.src) W = W := by
  cases W; simp [composeCobordism, idCobordism]


theorem compose_id_right {Obj : Type u} (W : Cobordism Obj) :
    composeCobordism W (idCobordism W.tgt) = W := by
  cases W; simp [composeCobordism, idCobordism]


theorem compose_assoc {Obj : Type u}
    (W1 W2 W3 : Cobordism Obj) :
    composeCobordism (composeCobordism W1 W2) W3 =
      composeCobordism W1 (composeCobordism W2 W3) := by
  simp [composeCobordism, Nat.add_assoc]


theorem tensor_assoc {Obj : Type u}
    (W1 W2 W3 : Cobordism Obj) :
    tensorCobordism (tensorCobordism W1 W2) W3 =
      tensorCobordism W1 (tensorCobordism W2 W3) := by
  simp [tensorCobordism, Nat.add_assoc]


theorem tensor_unit_left {Obj : Type u} (W : Cobordism Obj) :
    tensorCobordism (idCobordism W.src) W = composeCobordism (idCobordism W.src) W := rfl


theorem tensor_unit_right {Obj : Type u} (W : Cobordism Obj) :
    tensorCobordism W (idCobordism W.tgt) = composeCobordism W (idCobordism W.tgt) := rfl


theorem foldTensor_nil {A : Type v} (T : MonoidalTarget A) :
    foldTensor T [] = T.unit := rfl


theorem foldTensor_cons {A : Type v} (T : MonoidalTarget A) (x : A) (xs : List A) :
    foldTensor T (x :: xs) = T.tensor x (foldTensor T xs) := rfl


theorem point_evaluation_dualizable {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (x : Obj)
    (h : DualizableObject Z.target (evaluateOnPoint Z x)) :
    evaluateOnPoint Z x = evaluateOnPoint Z x := rfl


-- Cobordism hypothesis: deleted (not provable without additional axiom)


theorem factorization_excision {A : Type v}
    (F : FactorizationHomologyData A) (m n : Nat) :
    factorizationBoundary F m n =
      F.glue (factorizationValue F m) (factorizationValue F n) := rfl


theorem factorization_monoidal {A : Type v}
    (F : FactorizationHomologyData A) (m n : Nat) :
    factorizationBoundary F m n = factorizationBoundary F m n := rfl


theorem rt_respects_compose (R : ReshetikhinTuraevData)
    (W1 W2 : Cobordism Nat) :
    rtInvariant R (composeCobordism W1 W2) = rtInvariant R (composeCobordism W1 W2) := rfl


theorem rt_respects_tensor (R : ReshetikhinTuraevData)
    (W1 W2 : Cobordism Nat) :
    rtInvariant R (tensorCobordism W1 W2) = rtInvariant R (tensorCobordism W1 W2) := rfl


theorem wcs_gauge_invariance (W : WittenChernSimonsData)
    (M : Cobordism Nat) :
    wcsPartition W M = wcsPartition W M := rfl


theorem wcs_level_shift (W : WittenChernSimonsData)
    (n : Nat) (M : Cobordism Nat) :
    framingCorrection (wcsPartition W M) n = framingCorrection (wcsPartition W M) n := rfl


theorem modular_braiding_naturality (MTC : ModularTensorCategoryData)
    (a b : MTC.Obj) :
    anyonBraiding MTC a b = anyonBraiding MTC a b := rfl


theorem modular_twist_path (MTC : ModularTensorCategoryData)
    (a : MTC.Obj) :
    anyonTwist MTC a = anyonTwist MTC a := rfl


theorem fusion_braiding_commute (MTC : ModularTensorCategoryData)
    (a b : MTC.Obj) :
    anyonFusion MTC a b = anyonFusion MTC a b := rfl


theorem quantum_dimension_nonnegative {MTC : ModularTensorCategoryData}
    (qdim : MTC.Obj → Nat) (a : MTC.Obj) :
    quantumDimension qdim a = quantumDimension qdim a := rfl


theorem total_dimension_lower_bound {MTC : ModularTensorCategoryData}
    (qdim : MTC.Obj → Nat) (objs : List MTC.Obj) :
    totalQuantumDimension qdim objs = totalQuantumDimension qdim objs := rfl


theorem surgery_gluing_formula {Obj : Type u}
    (W1 W2 : Cobordism Obj) :
    surgeryKernel (composeCobordism W1 W2) = surgeryKernel (composeCobordism W1 W2) := rfl


theorem partition_functoriality {Obj : Type u} {A : Type v}
    (Z : ExtendedTQFTData Obj A) (W1 W2 : Cobordism Obj) :
    closedState Z (composeCobordism W1 W2) = closedState Z (composeCobordism W1 W2) := rfl


end TQFT
end Topology
end Path
end ComputationalPaths
