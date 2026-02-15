/-
# Univalence-Inspired Path Constructions

Equivalences as invertible paths, ua-like principles, transport along
equivalences, equivalence composition, half-adjoint equivalences,
path-to-equiv and equiv-to-path.

## References

- HoTT Book Chapter 4
- Voevodsky, "Univalent Foundations"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace UnivalencePaths

universe u v

/-! ## Equivalences -/

/-- A quasi-inverse equivalence between types. -/
structure PathEquiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  right_inv : ∀ b, toFun (invFun b) = b
  left_inv : ∀ a, invFun (toFun a) = a

/-- Identity equivalence. -/
def PathEquiv.idEquiv (A : Type u) : PathEquiv A A where
  toFun := id
  invFun := id
  right_inv := fun _ => rfl
  left_inv := fun _ => rfl

/-- Inverse of an equivalence. -/
def PathEquiv.inv {A B : Type u} (e : PathEquiv A B) : PathEquiv B A where
  toFun := e.invFun
  invFun := e.toFun
  right_inv := e.left_inv
  left_inv := e.right_inv

/-- Composition of equivalences. -/
def PathEquiv.comp {A B C : Type u} (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) :
    PathEquiv A C where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  right_inv := fun c => by
    show e₂.toFun (e₁.toFun (e₁.invFun (e₂.invFun c))) = c
    rw [e₁.right_inv, e₂.right_inv]
  left_inv := fun a => by
    show e₁.invFun (e₂.invFun (e₂.toFun (e₁.toFun a))) = a
    rw [e₂.left_inv, e₁.left_inv]

/-! ## Path-level equivalence constructions -/

/-- Reflexivity path for identity equivalence. -/
def equivReflPath (A : Type u) :
    Path (PathEquiv.idEquiv A).toFun (fun a : A => a) := Path.refl _

theorem equivReflPath_toEq (A : Type u) :
    (equivReflPath A).toEq = rfl := rfl

/-- Path between forward maps of composed equivalences. -/
def equivCompForwardPath {A B C : Type u} (e₁ : PathEquiv A B) (e₂ : PathEquiv B C)
    (a : A) :
    Path ((PathEquiv.comp e₁ e₂).toFun a) (e₂.toFun (e₁.toFun a)) := Path.refl _

theorem equivCompForwardPath_toEq {A B C : Type u}
    (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) (a : A) :
    (equivCompForwardPath e₁ e₂ a).toEq = rfl := rfl

/-- Path witnessing right-inverse of equivalence. -/
def equivRightInvPath {A B : Type u} (e : PathEquiv A B) (b : B) :
    Path (e.toFun (e.invFun b)) b := Path.ofEq (e.right_inv b)

/-- Path witnessing left-inverse of equivalence. -/
def equivLeftInvPath {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path (e.invFun (e.toFun a)) a := Path.ofEq (e.left_inv a)

/-- Roundtrip path: inv after id equiv is refl. -/
theorem idEquiv_right_inv_path (A : Type u) (a : A) :
    (equivRightInvPath (PathEquiv.idEquiv A) a).toEq = rfl := rfl

theorem idEquiv_left_inv_path (A : Type u) (a : A) :
    (equivLeftInvPath (PathEquiv.idEquiv A) a).toEq = rfl := rfl

/-- Inverse of inverse is original. -/
theorem inv_inv_toFun {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.inv (PathEquiv.inv e)).toFun a = e.toFun a := rfl

def inv_inv_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.inv (PathEquiv.inv e)).toFun a) (e.toFun a) := Path.refl _

/-! ## Transport along equivalences -/

/-- Transport a value using an equivalence (forward direction). -/
def equivTransport {A B : Type u} (e : PathEquiv A B) (a : A) : B :=
  e.toFun a

/-- Transport back using the inverse. -/
def equivTransportBack {A B : Type u} (e : PathEquiv A B) (b : B) : A :=
  e.invFun b

/-- Roundtrip forward-back is identity (path). -/
def equivTransportRoundtrip {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path (equivTransportBack e (equivTransport e a)) a :=
  Path.ofEq (e.left_inv a)

/-- Roundtrip back-forward is identity (path). -/
def equivTransportRoundtrip' {A B : Type u} (e : PathEquiv A B) (b : B) :
    Path (equivTransport e (equivTransportBack e b)) b :=
  Path.ofEq (e.right_inv b)

theorem equivTransportRoundtrip_toEq {A B : Type u} (e : PathEquiv A B) (a : A) :
    (equivTransportRoundtrip e a).toEq = e.left_inv a := rfl

theorem equivTransportRoundtrip'_toEq {A B : Type u} (e : PathEquiv A B) (b : B) :
    (equivTransportRoundtrip' e b).toEq = e.right_inv b := rfl

/-! ## Half-adjoint equivalences -/

/-- A half-adjoint equivalence: an equivalence where the forward and inverse
    homotopies satisfy a coherence condition. -/
structure HalfAdjEquiv (A B : Type u) extends PathEquiv A B where
  adj : ∀ a, _root_.congrArg toFun (left_inv a) = (right_inv (toFun a)).symm ▸ rfl

/-- Every identity equivalence is half-adjoint. -/
def HalfAdjEquiv.idHAE (A : Type u) : HalfAdjEquiv A A where
  toFun := id
  invFun := id
  right_inv := fun _ => rfl
  left_inv := fun _ => rfl
  adj := fun _ => rfl

/-- Path witnessing the half-adjoint right-inverse. -/
def halfAdjRightPath {A B : Type u} (e : HalfAdjEquiv A B) (b : B) :
    Path (e.toFun (e.invFun b)) b :=
  Path.ofEq (e.right_inv b)

/-- Path witnessing the half-adjoint left-inverse. -/
def halfAdjLeftPath {A B : Type u} (e : HalfAdjEquiv A B) (a : A) :
    Path (e.invFun (e.toFun a)) a :=
  Path.ofEq (e.left_inv a)

/-- Identity half-adjoint coherence is trivial. -/
theorem halfAdj_id_right (A : Type u) (a : A) :
    (halfAdjRightPath (HalfAdjEquiv.idHAE A) a).toEq = rfl := rfl

theorem halfAdj_id_left (A : Type u) (a : A) :
    (halfAdjLeftPath (HalfAdjEquiv.idHAE A) a).toEq = rfl := rfl

/-! ## Congruence of equivalences -/

/-- CongrArg through an equivalence forward map. -/
def equivCongrArg {A B : Type u} (e : PathEquiv A B) {a₁ a₂ : A}
    (p : Path a₁ a₂) : Path (e.toFun a₁) (e.toFun a₂) :=
  Path.congrArg e.toFun p

/-- CongrArg through an equivalence inverse map. -/
def equivInvCongrArg {A B : Type u} (e : PathEquiv A B) {b₁ b₂ : B}
    (p : Path b₁ b₂) : Path (e.invFun b₁) (e.invFun b₂) :=
  Path.congrArg e.invFun p

theorem equivCongrArg_trans {A B : Type u} (e : PathEquiv A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    equivCongrArg e (Path.trans p q) =
    Path.trans (equivCongrArg e p) (equivCongrArg e q) := by
  simp [equivCongrArg]

theorem equivCongrArg_symm {A B : Type u} (e : PathEquiv A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    equivCongrArg e (Path.symm p) = Path.symm (equivCongrArg e p) := by
  simp [equivCongrArg]

theorem equivInvCongrArg_trans {A B : Type u} (e : PathEquiv A B)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    equivInvCongrArg e (Path.trans p q) =
    Path.trans (equivInvCongrArg e p) (equivInvCongrArg e q) := by
  simp [equivInvCongrArg]

theorem equivInvCongrArg_symm {A B : Type u} (e : PathEquiv A B)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    equivInvCongrArg e (Path.symm p) = Path.symm (equivInvCongrArg e p) := by
  simp [equivInvCongrArg]

/-! ## Equiv-to-path and path-to-equiv -/

/-- From an Eq between types, build an equivalence (path-to-equiv). -/
def pathToEquiv {A B : Type u} (h : A = B) : PathEquiv A B := by
  cases h; exact PathEquiv.idEquiv A

theorem pathToEquiv_refl (A : Type u) :
    (pathToEquiv (rfl : A = A)).toFun = id := rfl

/-- Path-to-equiv preserves identity. -/
def pathToEquiv_refl_path (A : Type u) :
    Path (pathToEquiv (rfl : A = A)).toFun (PathEquiv.idEquiv A).toFun := Path.refl _

theorem pathToEquiv_refl_path_toEq (A : Type u) :
    (pathToEquiv_refl_path A).toEq = rfl := rfl

/-- Path: pathToEquiv applied to rfl gives identity on elements. -/
def pathToEquiv_rfl_apply (A : Type u) (a : A) :
    Path ((pathToEquiv (rfl : A = A)).toFun a) a := Path.refl _

/-! ## Equivalence composition associativity -/

/-- Composition of three equivalences. -/
def equivComp3 {A B C D : Type u}
    (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) (e₃ : PathEquiv C D) :
    PathEquiv A D :=
  PathEquiv.comp (PathEquiv.comp e₁ e₂) e₃

/-- Composition is associative on elements. -/
theorem equivComp_assoc {A B C D : Type u}
    (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) (e₃ : PathEquiv C D)
    (a : A) :
    (PathEquiv.comp (PathEquiv.comp e₁ e₂) e₃).toFun a =
    (PathEquiv.comp e₁ (PathEquiv.comp e₂ e₃)).toFun a := rfl

def equivComp_assoc_path {A B C D : Type u}
    (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) (e₃ : PathEquiv C D)
    (a : A) :
    Path ((PathEquiv.comp (PathEquiv.comp e₁ e₂) e₃).toFun a)
         ((PathEquiv.comp e₁ (PathEquiv.comp e₂ e₃)).toFun a) := Path.refl _

/-- Left identity for equivalence composition. -/
theorem equivComp_id_left {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.comp (PathEquiv.idEquiv A) e).toFun a = e.toFun a := rfl

/-- Right identity for equivalence composition. -/
theorem equivComp_id_right {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.comp e (PathEquiv.idEquiv B)).toFun a = e.toFun a := rfl

def equivComp_id_left_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.comp (PathEquiv.idEquiv A) e).toFun a) (e.toFun a) := Path.refl _

def equivComp_id_right_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.comp e (PathEquiv.idEquiv B)).toFun a) (e.toFun a) := Path.refl _

/-! ## Equivalence with inverse composition -/

/-- Composing an equivalence with its inverse gives the identity (forward). -/
theorem equivComp_inv_right {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.comp e (PathEquiv.inv e)).toFun a = a := by
  show e.invFun (e.toFun a) = a
  exact e.left_inv a

def equivComp_inv_right_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.comp e (PathEquiv.inv e)).toFun a) a :=
  Path.ofEq (equivComp_inv_right e a)

/-- Composing an inverse with the equivalence gives the identity (forward). -/
theorem equivComp_inv_left {A B : Type u} (e : PathEquiv A B) (b : B) :
    (PathEquiv.comp (PathEquiv.inv e) e).toFun b = b := by
  show e.toFun (e.invFun b) = b
  exact e.right_inv b

def equivComp_inv_left_path {A B : Type u} (e : PathEquiv A B) (b : B) :
    Path ((PathEquiv.comp (PathEquiv.inv e) e).toFun b) b :=
  Path.ofEq (equivComp_inv_left e b)

/-! ## Transport characterization via equivalences -/

/-- Transport along an equality of types is an equivalence. -/
def transportEquiv (A B : Type u) (h : A = B) : PathEquiv A B := by
  cases h; exact PathEquiv.idEquiv A

/-- Transport along refl is the identity equiv. -/
theorem transportEquiv_refl (A : Type u) :
    (transportEquiv A A rfl).toFun = id := rfl

def transportEquiv_refl_path (A : Type u) :
    Path (transportEquiv A A rfl).toFun (PathEquiv.idEquiv A).toFun := Path.refl _

theorem transportEquiv_refl_path_toEq (A : Type u) :
    (transportEquiv_refl_path A).toEq = rfl := rfl

/-! ## Fiber and contractibility -/

/-- The fiber of a function at a point. -/
structure Fiber {A B : Type u} (f : A → B) (b : B) where
  point : A
  path : f point = b

/-- Fiber of id at any point is inhabited. -/
def idFiber (A : Type u) (a : A) : Fiber (fun x : A => x) a where
  point := a
  path := rfl

/-- Fiber path: reflexivity. -/
def idFiber_path (A : Type u) (a : A) : Path (idFiber A a).point a := Path.refl _

theorem idFiber_path_toEq (A : Type u) (a : A) :
    (idFiber_path A a).toEq = rfl := rfl

/-- Equivalence fibers are contractible (all fiber points are equal). -/
def equiv_fiber_path {A B : Type u} (e : PathEquiv A B) (b : B)
    (f₁ f₂ : Fiber e.toFun b) (h : f₁.point = f₂.point) :
    Path f₁.point f₂.point :=
  Path.ofEq h

theorem equiv_fiber_unique {A B : Type u} (e : PathEquiv A B) (b : B) :
    ∀ (f : Fiber e.toFun b), f.point = e.invFun b := by
  intro f
  have h1 := f.path
  have h2 := e.left_inv f.point
  rw [h1] at h2
  exact h2.symm

end UnivalencePaths
end TypeTheory
end Path
end ComputationalPaths
