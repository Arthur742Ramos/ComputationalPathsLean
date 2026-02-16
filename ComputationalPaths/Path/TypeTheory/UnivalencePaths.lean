/-
# Univalence-Inspired Path Constructions (Deepened)

Equivalences as invertible paths, ua-like principles, transport along
equivalences, equivalence composition, half-adjoint equivalences —
all witnesses built from `Path.refl`, `Path.trans`, `Path.symm`,
`Path.congrArg`, `Path.transport`. **Zero** `Path.ofEq`.

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

/-- A quasi-inverse equivalence between types, with Path witnesses. -/
structure PathEquiv (A B : Type u) where
  toFun : A → B
  invFun : B → A
  right_inv_path : ∀ b, Path (toFun (invFun b)) b
  left_inv_path : ∀ a, Path (invFun (toFun a)) a

/-- Identity equivalence. -/
def PathEquiv.idEquiv (A : Type u) : PathEquiv A A where
  toFun := id
  invFun := id
  right_inv_path _ := Path.refl _
  left_inv_path _ := Path.refl _

/-- Inverse of an equivalence. -/
def PathEquiv.inv {A B : Type u} (e : PathEquiv A B) : PathEquiv B A where
  toFun := e.invFun
  invFun := e.toFun
  right_inv_path := e.left_inv_path
  left_inv_path := e.right_inv_path

/-- Composition of equivalences. -/
def PathEquiv.comp {A B C : Type u} (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) :
    PathEquiv A C where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  right_inv_path c :=
    Path.trans
      (Path.congrArg e₂.toFun (e₁.right_inv_path (e₂.invFun c)))
      (e₂.right_inv_path c)
  left_inv_path a :=
    Path.trans
      (Path.congrArg e₁.invFun (e₂.left_inv_path (e₁.toFun a)))
      (e₁.left_inv_path a)

/-! ## Path-level equivalence constructions -/

/-- Reflexivity path for identity equivalence forward map. -/
def equivReflPath (A : Type u) :
    Path (PathEquiv.idEquiv A).toFun (fun a : A => a) := Path.refl _

theorem equivReflPath_toEq (A : Type u) :
    (equivReflPath A).toEq = rfl := rfl

/-- Composed equivalences agree on elements. -/
def equivCompForwardPath {A B C : Type u} (e₁ : PathEquiv A B) (e₂ : PathEquiv B C)
    (a : A) :
    Path ((PathEquiv.comp e₁ e₂).toFun a) (e₂.toFun (e₁.toFun a)) := Path.refl _

theorem equivCompForwardPath_toEq {A B C : Type u}
    (e₁ : PathEquiv A B) (e₂ : PathEquiv B C) (a : A) :
    (equivCompForwardPath e₁ e₂ a).toEq = rfl := rfl

/-- Right-inverse path from the equivalence structure. -/
def equivRightInvPath {A B : Type u} (e : PathEquiv A B) (b : B) :
    Path (e.toFun (e.invFun b)) b := e.right_inv_path b

/-- Left-inverse path from the equivalence structure. -/
def equivLeftInvPath {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path (e.invFun (e.toFun a)) a := e.left_inv_path a

/-- Id equiv roundtrip is refl. -/
theorem idEquiv_right_inv_path (A : Type u) (a : A) :
    (equivRightInvPath (PathEquiv.idEquiv A) a).toEq = rfl := rfl

theorem idEquiv_left_inv_path (A : Type u) (a : A) :
    (equivLeftInvPath (PathEquiv.idEquiv A) a).toEq = rfl := rfl

/-- Inverse of inverse is original (definitional). -/
theorem inv_inv_toFun {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.inv (PathEquiv.inv e)).toFun a = e.toFun a := rfl

def inv_inv_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.inv (PathEquiv.inv e)).toFun a) (e.toFun a) := Path.refl _

/-! ## Transport along equivalences -/

/-- Forward transport. -/
def equivTransport {A B : Type u} (e : PathEquiv A B) (a : A) : B :=
  e.toFun a

/-- Backward transport. -/
def equivTransportBack {A B : Type u} (e : PathEquiv A B) (b : B) : A :=
  e.invFun b

/-- Roundtrip forward-back: path from left inverse. -/
def equivTransportRoundtrip {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path (equivTransportBack e (equivTransport e a)) a :=
  e.left_inv_path a

/-- Roundtrip back-forward: path from right inverse. -/
def equivTransportRoundtrip' {A B : Type u} (e : PathEquiv A B) (b : B) :
    Path (equivTransport e (equivTransportBack e b)) b :=
  e.right_inv_path b

/-- Double roundtrip: forward, back, forward recovers forward. -/
def equivDoubleRoundtrip {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path (e.toFun (e.invFun (e.toFun a))) (e.toFun a) :=
  Path.congrArg e.toFun (e.left_inv_path a)

/-- Double roundtrip via right inverse. -/
def equivDoubleRoundtrip' {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path (e.toFun (e.invFun (e.toFun a))) (e.toFun a) :=
  e.right_inv_path (e.toFun a)

/-! ## Half-adjoint equivalences -/

/-- A half-adjoint equivalence: path-based coherence. -/
structure HalfAdjEquiv (A B : Type u) extends PathEquiv A B where
  adj : ∀ a, Path.congrArg toFun (left_inv_path a) = right_inv_path (toFun a)

/-- Every identity equivalence is half-adjoint. -/
def HalfAdjEquiv.idHAE (A : Type u) : HalfAdjEquiv A A where
  toFun := id
  invFun := id
  right_inv_path _ := Path.refl _
  left_inv_path _ := Path.refl _
  adj _ := rfl

/-- Half-adjoint right-inverse path. -/
def halfAdjRightPath {A B : Type u} (e : HalfAdjEquiv A B) (b : B) :
    Path (e.toFun (e.invFun b)) b :=
  e.right_inv_path b

/-- Half-adjoint left-inverse path. -/
def halfAdjLeftPath {A B : Type u} (e : HalfAdjEquiv A B) (a : A) :
    Path (e.invFun (e.toFun a)) a :=
  e.left_inv_path a

/-- Id HAE roundtrips are refl. -/
theorem halfAdj_id_right (A : Type u) (a : A) :
    (halfAdjRightPath (HalfAdjEquiv.idHAE A) a).toEq = rfl := rfl

theorem halfAdj_id_left (A : Type u) (a : A) :
    (halfAdjLeftPath (HalfAdjEquiv.idHAE A) a).toEq = rfl := rfl

/-! ## Congruence of equivalences -/

/-- CongrArg through forward map. -/
def equivCongrArg {A B : Type u} (e : PathEquiv A B) {a₁ a₂ : A}
    (p : Path a₁ a₂) : Path (e.toFun a₁) (e.toFun a₂) :=
  Path.congrArg e.toFun p

/-- CongrArg through inverse map. -/
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

/-- CongrArg of refl is refl. -/
theorem equivCongrArg_refl {A B : Type u} (e : PathEquiv A B) (a : A) :
    equivCongrArg e (Path.refl a) = Path.refl (e.toFun a) := by
  simp [equivCongrArg]

/-- Inverse congrArg of refl is refl. -/
theorem equivInvCongrArg_refl {A B : Type u} (e : PathEquiv A B) (b : B) :
    equivInvCongrArg e (Path.refl b) = Path.refl (e.invFun b) := by
  simp [equivInvCongrArg]

/-! ## Equiv-to-path and path-to-equiv -/

/-- From an Eq between types, build an equivalence via cast. -/
def pathToEquiv {A B : Type u} (h : A = B) : PathEquiv A B := by
  cases h; exact PathEquiv.idEquiv A

theorem pathToEquiv_refl (A : Type u) :
    (pathToEquiv (rfl : A = A)).toFun = id := rfl

def pathToEquiv_refl_path (A : Type u) :
    Path (pathToEquiv (rfl : A = A)).toFun (PathEquiv.idEquiv A).toFun := Path.refl _

theorem pathToEquiv_refl_path_toEq (A : Type u) :
    (pathToEquiv_refl_path A).toEq = rfl := rfl

def pathToEquiv_rfl_apply (A : Type u) (a : A) :
    Path ((pathToEquiv (rfl : A = A)).toFun a) a := Path.refl _

/-! ## Equivalence composition properties -/

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

/-- Left identity for equiv composition. -/
theorem equivComp_id_left {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.comp (PathEquiv.idEquiv A) e).toFun a = e.toFun a := rfl

theorem equivComp_id_right {A B : Type u} (e : PathEquiv A B) (a : A) :
    (PathEquiv.comp e (PathEquiv.idEquiv B)).toFun a = e.toFun a := rfl

def equivComp_id_left_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.comp (PathEquiv.idEquiv A) e).toFun a) (e.toFun a) := Path.refl _

def equivComp_id_right_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.comp e (PathEquiv.idEquiv B)).toFun a) (e.toFun a) := Path.refl _

/-! ## Equivalence with inverse composition -/

/-- e composed with e⁻¹ gives identity (via left inverse path). -/
def equivComp_inv_right_path {A B : Type u} (e : PathEquiv A B) (a : A) :
    Path ((PathEquiv.comp e (PathEquiv.inv e)).toFun a) a :=
  e.left_inv_path a

/-- e⁻¹ composed with e gives identity (via right inverse path). -/
def equivComp_inv_left_path {A B : Type u} (e : PathEquiv A B) (b : B) :
    Path ((PathEquiv.comp (PathEquiv.inv e) e).toFun b) b :=
  e.right_inv_path b

/-! ## Fiber and contractibility -/

/-- The fiber of a function at a point. -/
structure Fiber {A B : Type u} (f : A → B) (b : B) where
  point : A
  path : Path (f point) b

/-- Fiber of id at any point. -/
def idFiber (A : Type u) (a : A) : Fiber (fun x : A => x) a where
  point := a
  path := Path.refl _

/-- The fiber point for id is the point itself. -/
def idFiber_path (A : Type u) (a : A) : Path (idFiber A a).point a := Path.refl _

theorem idFiber_path_toEq (A : Type u) (a : A) :
    (idFiber_path A a).toEq = rfl := rfl

/-- Canonical fiber of an equivalence at b is (e⁻¹ b, right_inv). -/
def equivFiber {A B : Type u} (e : PathEquiv A B) (b : B) :
    Fiber e.toFun b where
  point := e.invFun b
  path := e.right_inv_path b

/-- Two fiber points related via congruence of the inverse. -/
def fiberPointPath {A B : Type u} (e : PathEquiv A B) {b₁ b₂ : B}
    (p : Path b₁ b₂) :
    Path (equivFiber e b₁).point (equivFiber e b₂).point :=
  Path.congrArg e.invFun p

/-! ## Transport characterization -/

/-- Transport along type equality via pathToEquiv. -/
def transportEquiv (A B : Type u) (h : A = B) : PathEquiv A B := by
  cases h; exact PathEquiv.idEquiv A

theorem transportEquiv_refl (A : Type u) :
    (transportEquiv A A rfl).toFun = id := rfl

def transportEquiv_refl_path (A : Type u) :
    Path (transportEquiv A A rfl).toFun (PathEquiv.idEquiv A).toFun := Path.refl _

theorem transportEquiv_refl_path_toEq (A : Type u) :
    (transportEquiv_refl_path A).toEq = rfl := rfl

end UnivalencePaths
end TypeTheory
end Path
end ComputationalPaths
