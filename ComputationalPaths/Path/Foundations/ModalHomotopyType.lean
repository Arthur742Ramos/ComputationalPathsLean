import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace ModalHomotopyType

universe u

structure Modality (α : Type u) where
  op : α → α
  modalProp : Prop

def modalApply {α : Type u} (M : Modality α) (x : α) : α := M.op x
def modalWitness {α : Type u} (M : Modality α) (x : α) : Path (modalApply M x) (modalApply M x) :=
  Path.refl (modalApply M x)
def modalFixedPoint {α : Type u} (M : Modality α) (x : α) : Prop := modalApply M x = x
def modalId (α : Type u) : Modality α := ⟨fun x => x, True⟩
def modalCompose {α : Type u} (M N : Modality α) : Modality α :=
  ⟨fun x => modalApply N (modalApply M x), M.modalProp ∧ N.modalProp⟩
def modalIterate {α : Type u} (M : Modality α) : Nat → α → α
  | 0, x => x
  | n + 1, x => modalApply M (modalIterate M n x)
def modalCore {α : Type u} (M : Modality α) (x : α) : α := modalApply M x

structure LexModality (α : Type u) extends Modality α where
  preservesPullback : Prop
  preservesTerminal : Prop

def lexUnderlying {α : Type u} (L : LexModality α) : Modality α := L.toModality
def lexAct {α : Type u} (L : LexModality α) (x : α) : α := modalApply L.toModality x
def lexPredicate {α : Type u} (L : LexModality α) : Prop :=
  L.preservesPullback ∧ L.preservesTerminal

structure OpenModality (α : Type u) extends Modality α where
  opens : α → Prop

structure ClosedModality (α : Type u) extends Modality α where
  closes : α → Prop

def openUnderlying {α : Type u} (O : OpenModality α) : Modality α := O.toModality
def closedUnderlying {α : Type u} (C : ClosedModality α) : Modality α := C.toModality
def openCore {α : Type u} (O : OpenModality α) (x : α) : α := modalApply O.toModality x
def closedCore {α : Type u} (C : ClosedModality α) (x : α) : α := modalApply C.toModality x

structure FractureDatum (α : Type u) where
  left : α → α
  right : α → α
  compatibility : Prop

def fractureLeft {α : Type u} (F : FractureDatum α) (x : α) : α := F.left x
def fractureRight {α : Type u} (F : FractureDatum α) (x : α) : α := F.right x
def fractureGlue {α : Type u} (F : FractureDatum α) (x : α) : α × α :=
  (fractureLeft F x, fractureRight F x)
def fractureConsistent {α : Type u} (F : FractureDatum α) : Prop := F.compatibility

structure RealCohesive (α : Type u) where
  shape : Modality α
  flat : Modality α
  sharp : Modality α
  cohesiveProp : Prop

def shapeOp {α : Type u} (R : RealCohesive α) (x : α) : α := modalApply R.shape x
def flatOp {α : Type u} (R : RealCohesive α) (x : α) : α := modalApply R.flat x
def sharpOp {α : Type u} (R : RealCohesive α) (x : α) : α := modalApply R.sharp x
def cohesiveTriple {α : Type u} (R : RealCohesive α) (x : α) : α × (α × α) :=
  (shapeOp R x, (flatOp R x, sharpOp R x))

structure DifferentialClass (α : Type u) where
  underlying : α
  curvature : α
  flatPart : α
  sharpPart : α

def differentialUnderlying {α : Type u} (D : DifferentialClass α) : α := D.underlying
def differentialCurvature {α : Type u} (D : DifferentialClass α) : α := D.curvature
def differentialFlatPart {α : Type u} (D : DifferentialClass α) : α := D.flatPart
def differentialSharpPart {α : Type u} (D : DifferentialClass α) : α := D.sharpPart
def differentialTuple {α : Type u} (D : DifferentialClass α) : α × (α × (α × α)) :=
  (differentialUnderlying D, (differentialCurvature D, (differentialFlatPart D, differentialSharpPart D)))

def modalPathChain {α : Type u} (x : α) : Path x x :=
  Path.trans (Path.refl x) (Path.refl x)

theorem modalApply_id {α : Type u} (x : α) : modalApply (modalId α) x = x := rfl

theorem modalWitness_refl {α : Type u} (M : Modality α) (x : α) :
    modalWitness M x = Path.refl (modalApply M x) := rfl

theorem modalCompose_apply {α : Type u} (M N : Modality α) (x : α) :
    modalApply (modalCompose M N) x = modalApply N (modalApply M x) := rfl

theorem modalIterate_zero {α : Type u} (M : Modality α) (x : α) :
    modalIterate M 0 x = x := rfl

theorem modalIterate_succ {α : Type u} (M : Modality α) (n : Nat) (x : α) :
    modalIterate M (n + 1) x = modalApply M (modalIterate M n x) := rfl

theorem modalCore_eq_apply {α : Type u} (M : Modality α) (x : α) :
    modalCore M x = modalApply M x := rfl

theorem lexAct_eq {α : Type u} (L : LexModality α) (x : α) :
    lexAct L x = modalApply L.toModality x := rfl

theorem lexPredicate_eq {α : Type u} (L : LexModality α) :
    lexPredicate L = (L.preservesPullback ∧ L.preservesTerminal) := rfl

theorem openCore_eq {α : Type u} (O : OpenModality α) (x : α) :
    openCore O x = modalApply O.toModality x := rfl

theorem closedCore_eq {α : Type u} (C : ClosedModality α) (x : α) :
    closedCore C x = modalApply C.toModality x := rfl

theorem fractureGlue_fst {α : Type u} (F : FractureDatum α) (x : α) :
    (fractureGlue F x).1 = fractureLeft F x := rfl

theorem fractureGlue_snd {α : Type u} (F : FractureDatum α) (x : α) :
    (fractureGlue F x).2 = fractureRight F x := rfl

theorem fractureConsistent_spec {α : Type u} (F : FractureDatum α) :
    fractureConsistent F = F.compatibility := rfl

theorem cohesiveTriple_shape {α : Type u} (R : RealCohesive α) (x : α) :
    (cohesiveTriple R x).1 = shapeOp R x := rfl

theorem cohesiveTriple_flat {α : Type u} (R : RealCohesive α) (x : α) :
    (cohesiveTriple R x).2.1 = flatOp R x := rfl

theorem cohesiveTriple_sharp {α : Type u} (R : RealCohesive α) (x : α) :
    (cohesiveTriple R x).2.2 = sharpOp R x := rfl

theorem differentialTuple_underlying {α : Type u} (D : DifferentialClass α) :
    (differentialTuple D).1 = differentialUnderlying D := rfl

theorem differentialTuple_curvature {α : Type u} (D : DifferentialClass α) :
    (differentialTuple D).2.1 = differentialCurvature D := rfl

theorem differentialTuple_flat {α : Type u} (D : DifferentialClass α) :
    (differentialTuple D).2.2.1 = differentialFlatPart D := rfl

theorem differentialTuple_sharp {α : Type u} (D : DifferentialClass α) :
    (differentialTuple D).2.2.2 = differentialSharpPart D := rfl

theorem modalFixedPoint_id {α : Type u} (x : α) : modalFixedPoint (modalId α) x := rfl

theorem modalPathChain_toEq {α : Type u} (x : α) : (modalPathChain x).toEq = rfl := rfl

end ModalHomotopyType
end Foundations
end Path
end ComputationalPaths
