import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Foundations
namespace DirectedTypeTheory

universe u

structure DPath (α : Type u) where
  src : α
  tgt : α

def dpathRefl {α : Type u} (x : α) : DPath α := ⟨x, x⟩
def dpathRev {α : Type u} (p : DPath α) : DPath α := ⟨p.tgt, p.src⟩
def dpathComp {α : Type u} (p q : DPath α) : DPath α := ⟨p.src, q.tgt⟩
def dpathStart {α : Type u} (p : DPath α) : α := p.src
def dpathEnd {α : Type u} (p : DPath α) : α := p.tgt
def dpathBoundary {α : Type u} (p : DPath α) : α × α := (dpathStart p, dpathEnd p)
def dpathToPath {α : Type u} (x : α) : Path x x := Path.refl x
def directedIdentityPath {α : Type u} (x : α) : Path x x :=
  Path.trans (Path.refl x) (Path.refl x)

structure SemiSimplicialType (α : Type u) where
  obj : Nat → Type u
  edge : α → α → Type u

def semiObj0 {α : Type u} (S : SemiSimplicialType α) : Type u := S.obj 0
def semiObj1 {α : Type u} (S : SemiSimplicialType α) : Type u := S.obj 1
def semiEdge {α : Type u} (S : SemiSimplicialType α) (a b : α) : Type u := S.edge a b

structure SegalType (α : Type u) where
  hom : α → α → Type u
  comp : {a b c : α} → hom a b → hom b c → hom a c

def segalHom {α : Type u} (S : SegalType α) (a b : α) : Type u := S.hom a b
def segalComp {α : Type u} (S : SegalType α) {a b c : α}
    (f : S.hom a b) (g : S.hom b c) : S.hom a c := S.comp f g

structure RezkCompletion (α : Type u) where
  carrier : Type u
  embed : α → carrier
  complete : Prop

def rezkCarrier {α : Type u} (R : RezkCompletion α) : Type u := R.carrier
def rezkEmbed {α : Type u} (R : RezkCompletion α) : α → rezkCarrier R := R.embed
def rezkComplete {α : Type u} (R : RezkCompletion α) : Prop := R.complete

structure DirectedUnivalence (α : Type u) where
  code : α → α → Type u
  decode : {a b : α} → code a b → DPath α

def directedCode {α : Type u} (U : DirectedUnivalence α) (a b : α) : Type u := U.code a b
def directedDecode {α : Type u} (U : DirectedUnivalence α) {a b : α}
    (c : U.code a b) : DPath α := U.decode c

structure InfinityOneCategory (α : Type u) where
  hom : α → α → Type u
  id : (a : α) → hom a a
  comp : {a b c : α} → hom a b → hom b c → hom a c

def i1Hom {α : Type u} (C : InfinityOneCategory α) (a b : α) : Type u := C.hom a b
def i1Id {α : Type u} (C : InfinityOneCategory α) (a : α) : C.hom a a := C.id a
def i1Comp {α : Type u} (C : InfinityOneCategory α) {a b c : α}
    (f : C.hom a b) (g : C.hom b c) : C.hom a c := C.comp f g

theorem dpathRev_involutive {α : Type u} (p : DPath α) : dpathRev (dpathRev p) = p := by
  cases p
  rfl

theorem dpathStart_refl {α : Type u} (x : α) : dpathStart (dpathRefl x) = x := rfl

theorem dpathEnd_refl {α : Type u} (x : α) : dpathEnd (dpathRefl x) = x := rfl

theorem dpathStart_comp {α : Type u} (p q : DPath α) : dpathStart (dpathComp p q) = dpathStart p :=
  rfl

theorem dpathEnd_comp {α : Type u} (p q : DPath α) : dpathEnd (dpathComp p q) = dpathEnd q := rfl

theorem dpathBoundary_fst {α : Type u} (p : DPath α) : (dpathBoundary p).1 = dpathStart p := rfl

theorem dpathBoundary_snd {α : Type u} (p : DPath α) : (dpathBoundary p).2 = dpathEnd p := rfl

theorem dpathToPath_toEq {α : Type u} (x : α) : (dpathToPath x).toEq = rfl := rfl

theorem directedIdentityPath_toEq {α : Type u} (x : α) :
    (directedIdentityPath x).toEq = rfl := rfl

theorem semiObj0_eq {α : Type u} (S : SemiSimplicialType α) : semiObj0 S = S.obj 0 := rfl

theorem semiObj1_eq {α : Type u} (S : SemiSimplicialType α) : semiObj1 S = S.obj 1 := rfl

theorem semiEdge_eq {α : Type u} (S : SemiSimplicialType α) (a b : α) :
    semiEdge S a b = S.edge a b := rfl

theorem segalComp_def {α : Type u} (S : SegalType α) {a b c : α}
    (f : S.hom a b) (g : S.hom b c) :
    segalComp S f g = S.comp f g := rfl

theorem rezkComplete_eq {α : Type u} (R : RezkCompletion α) : rezkComplete R = R.complete := rfl

theorem directedCode_eq {α : Type u} (U : DirectedUnivalence α) (a b : α) :
    directedCode U a b = U.code a b := rfl

theorem directedDecode_eq {α : Type u} (U : DirectedUnivalence α) {a b : α}
    (c : U.code a b) : directedDecode U c = U.decode c := rfl

theorem i1Id_eq {α : Type u} (C : InfinityOneCategory α) (a : α) : i1Id C a = C.id a := rfl

theorem i1Comp_eq {α : Type u} (C : InfinityOneCategory α) {a b c : α}
    (f : C.hom a b) (g : C.hom b c) : i1Comp C f g = C.comp f g := rfl

end DirectedTypeTheory
end Foundations
end Path
end ComputationalPaths
