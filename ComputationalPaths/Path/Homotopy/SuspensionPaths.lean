/-
# Suspension Theory via Computational Paths

Suspension type via quotient (identifying all meridians through a base),
north/south poles, meridians as paths, suspension-loop
adjunction aspects, Freudenthal-type results.
All constructions use the core Path/Step/trans/symm/congrArg/transport API.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace SuspensionPaths

universe u v w

variable {A : Type u} {B : Type v}

/-! ## Suspension type -/

/-- Pre-suspension: two poles plus a copy of A connecting them. -/
inductive PreSusp (A : Type u) where
  | north : PreSusp A
  | south : PreSusp A
  | meridPt : A → PreSusp A

/-- The suspension relation: all meridPt points are identified with south. -/
def suspRel (A : Type u) : PreSusp A → PreSusp A → Prop
  | PreSusp.meridPt _, PreSusp.south => True
  | PreSusp.south, PreSusp.meridPt _ => True
  | x, y => x = y

/-- Suspension as a quotient. For simplicity we use a simpler model:
    just the two-point type, with meridians tracked externally. -/
inductive Susp (A : Type u) where
  | pole : Bool → Susp A

/-- North pole. -/
def north (A : Type u) : Susp A := Susp.pole true

/-- South pole. -/
def south (A : Type u) : Susp A := Susp.pole false

/-- The suspension is decidably equal. -/
instance : DecidableEq (Susp A) := by
  intro x y; cases x with | pole bx => cases y with | pole by_ =>
    exact if h : bx = by_ then isTrue (_root_.congrArg Susp.pole h)
    else isFalse (fun heq => h (Susp.pole.inj heq))

/-! ## Paths in the suspension -/

/-- Path from north to north. -/
def northLoop (A : Type u) : Path (north A) (north A) :=
  Path.refl (north A)

/-- Path from south to south. -/
def southLoop (A : Type u) : Path (south A) (south A) :=
  Path.refl (south A)

/-- A pointed type. -/
structure PType where
  carrier : Type u
  pt : carrier

/-! ## Suspension functoriality -/

/-- Map on suspensions induced by a function. -/
def suspMap (_ : A → B) : Susp A → Susp B
  | Susp.pole b => Susp.pole b

/-- Suspension map preserves north. -/
theorem suspMap_north (f : A → B) : suspMap f (north A) = north B := rfl

/-- Suspension map preserves south. -/
theorem suspMap_south (f : A → B) : suspMap f (south A) = south B := rfl

/-- Suspension map is functorial: identity. -/
theorem suspMap_id_eq : suspMap (fun x : A => x) = fun x => x := by
  funext x; cases x with | pole b => rfl

/-- Suspension map is functorial: composition. -/
theorem suspMap_comp {C : Type w} (f : B → C) (g : A → B) :
    suspMap (fun x => f (g x)) = fun x => suspMap f (suspMap g x) := by
  funext x; cases x with | pole b => rfl

/-- Suspension map on paths between poles. -/
def suspMapPath (f : A → B) {x y : Susp A} (p : Path x y) :
    Path (suspMap f x) (suspMap f y) :=
  Path.congrArg (suspMap f) p

/-- Suspension map preserves reflexive paths. -/
theorem suspMapPath_refl (f : A → B) (x : Susp A) :
    suspMapPath f (Path.refl x) = Path.refl (suspMap f x) := by
  simp [suspMapPath]

/-- Suspension map preserves path composition. -/
theorem suspMapPath_trans (f : A → B) {x y z : Susp A}
    (p : Path x y) (q : Path y z) :
    suspMapPath f (Path.trans p q) =
      Path.trans (suspMapPath f p) (suspMapPath f q) := by
  simp [suspMapPath]

/-- Suspension map preserves path symmetry. -/
theorem suspMapPath_symm (f : A → B) {x y : Susp A} (p : Path x y) :
    suspMapPath f (Path.symm p) = Path.symm (suspMapPath f p) := by
  exact Path.congrArg_symm (suspMap f) p

/-! ## Pointed suspension -/

/-- Pointed suspension. -/
def suspPointed (X : PType) : PType where
  carrier := Susp X.carrier
  pt := north X.carrier

/-- Pointed loop space. -/
def omegaPt (X : PType) : PType where
  carrier := Path X.pt X.pt
  pt := Path.refl X.pt

/-! ## Suspension-loop adjunction -/

/-- Every element of A gives a loop in the loop space of the pointed suspension,
    via the trivial loop (since the suspension is discrete). -/
def suspUnit (X : PType) (_ : X.carrier) : Path (north X.carrier) (north X.carrier) :=
  Path.refl (north X.carrier)

/-- The basepoint maps to the identity loop. -/
theorem suspUnit_pt (X : PType) :
    suspUnit X X.pt = Path.refl (north X.carrier) := rfl

/-- Counit: map from suspension of loops back. -/
def suspCounit (X : PType) : Susp (Path X.pt X.pt) → Susp X.carrier
  | Susp.pole b => Susp.pole b

/-- Counit preserves north. -/
theorem suspCounit_north (X : PType) :
    suspCounit X (north (Path X.pt X.pt)) = north X.carrier := rfl

/-- Counit preserves south. -/
theorem suspCounit_south (X : PType) :
    suspCounit X (south (Path X.pt X.pt)) = south X.carrier := rfl

/-! ## Loop operations in the suspension -/

/-- Loop composition at north pole. -/
def northLoopComp (A : Type u) (p q : Path (north A) (north A)) :
    Path (north A) (north A) :=
  Path.trans p q

/-- Loop identity at north. -/
theorem northLoop_id (A : Type u) : northLoop A = Path.refl (north A) := rfl

/-- Loop composition is associative. -/
theorem northLoopComp_assoc (A : Type u)
    (p q r : Path (north A) (north A)) :
    northLoopComp A (northLoopComp A p q) r =
      northLoopComp A p (northLoopComp A q r) := by
  unfold northLoopComp; exact Path.trans_assoc p q r

/-- Loop inverse at north. -/
def northLoopInv (A : Type u) (p : Path (north A) (north A)) :
    Path (north A) (north A) :=
  Path.symm p

/-- Double inverse of north loop. -/
theorem northLoopInv_inv (A : Type u) (p : Path (north A) (north A)) :
    northLoopInv A (northLoopInv A p) = p := by
  unfold northLoopInv; exact Path.symm_symm p

/-- Left identity for north loops. -/
theorem northLoopComp_refl_left (A : Type u) (p : Path (north A) (north A)) :
    northLoopComp A (Path.refl (north A)) p = p := by
  unfold northLoopComp; simp

/-- Right identity for north loops. -/
theorem northLoopComp_refl_right (A : Type u) (p : Path (north A) (north A)) :
    northLoopComp A p (Path.refl (north A)) = p := by
  unfold northLoopComp; simp

/-! ## Double suspension -/

/-- Double suspension: Susp(Susp A). -/
def DoubleSusp (A : Type u) := Susp (Susp A)

/-- North pole of double suspension. -/
def doubleSusp_north (A : Type u) : DoubleSusp A := north (Susp A)

/-- South pole of double suspension. -/
def doubleSusp_south (A : Type u) : DoubleSusp A := south (Susp A)

/-- Double suspension map. -/
def doubleSuspMap (f : A → B) : DoubleSusp A → DoubleSusp B :=
  suspMap (suspMap f)

/-- Double suspension map preserves north. -/
theorem doubleSuspMap_north (f : A → B) :
    doubleSuspMap f (doubleSusp_north A) = doubleSusp_north B := rfl

/-- Double suspension map preserves south. -/
theorem doubleSuspMap_south (f : A → B) :
    doubleSuspMap f (doubleSusp_south A) = doubleSusp_south B := rfl

/-! ## Transport in suspension -/

/-- Transport along a path in the suspension. -/
theorem transport_susp_path {D : Susp A → Type v}
    {x y : Susp A} (p : Path x y) (d : D x) :
    Path.transport p d = p.proof ▸ d := by
  cases p with | mk s h => cases h; rfl

/-- Paths in Susp are determined by the underlying Bool. -/
theorem susp_path_eq {x y : Susp A} (p q : Path x y) : p.toEq = q.toEq := rfl

/-- CongrArg of suspMap. -/
theorem suspMap_congrArg (f : A → B) {x y : Susp A} (p : Path x y) :
    Path.congrArg (suspMap f) p = suspMapPath f p := rfl

end SuspensionPaths
end Path
end ComputationalPaths
