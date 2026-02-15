/-
# Equivalences via computational paths

This module develops the theory of equivalences using computational paths:
fibers, isEquiv, half-adjoint equivalences, bi-invertible maps, equivalence
composition, and basic univalence aspects.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace Equivalences

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Fibers -/

/-- The fiber (homotopy fiber) of `f` over `b`. -/
structure Fiber (f : A → B) (b : B) where
  point : A
  path : Path (f point) b

/-- Construct a fiber from a point and an equality. -/
def Fiber.ofEq (f : A → B) {a : A} {b : B} (h : f a = b) : Fiber f b :=
  ⟨a, Path.ofEq h⟩

/-- The canonical fiber element at `f a`. -/
def Fiber.canonical (f : A → B) (a : A) : Fiber f (f a) :=
  ⟨a, refl (f a)⟩

/-! ## Contractible types -/

/-- A type is contractible if it has a center and a path from center to every element. -/
structure IsContr (A : Type u) where
  center : A
  contr : (a : A) → Path center a

/-- A contractible type has a path between any two elements. -/
def isContr_path {h : IsContr A} (a b : A) : Path a b :=
  Path.trans (Path.symm (h.contr a)) (h.contr b)

/-- The unit type is contractible. -/
def unitContr : IsContr Unit where
  center := ()
  contr := fun () => refl ()

/-- PUnit is contractible. -/
def punitContr : IsContr PUnit where
  center := PUnit.unit
  contr := fun u => by cases u; exact refl PUnit.unit

/-! ## Equivalences (quasi-inverse style) -/

/-- A quasi-inverse for `f`. -/
structure QInv (f : A → B) where
  inv : B → A
  sect : (a : A) → Path (inv (f a)) a
  retr : (b : B) → Path (f (inv b)) b

/-- The identity has a quasi-inverse. -/
def idQInv : QInv (fun x : A => x) where
  inv := fun x => x
  sect := fun a => refl a
  retr := fun b => refl b

/-- An equivalence has a quasi-inverse going back. -/
def qinvInv {f : A → B} (e : QInv f) : QInv e.inv where
  inv := f
  sect := fun b => e.retr b
  retr := fun a => e.sect a

/-! ## Bi-invertible maps -/

/-- A left inverse for `f`. -/
structure HasLeftInverse (f : A → B) where
  linv : B → A
  sect : (a : A) → Path (linv (f a)) a

/-- A right inverse for `f`. -/
structure HasRightInverse (f : A → B) where
  rinv : B → A
  retr : (b : B) → Path (f (rinv b)) b

/-- A bi-invertible map has both a left and right inverse. -/
structure BiInv (f : A → B) where
  left : HasLeftInverse f
  right : HasRightInverse f

/-- A quasi-inverse yields a bi-invertible map. -/
def qinvToBiInv {f : A → B} (e : QInv f) : BiInv f where
  left := ⟨e.inv, e.sect⟩
  right := ⟨e.inv, e.retr⟩

/-- A bi-invertible map yields a quasi-inverse (using the left inverse). -/
def biInvToQInv {f : A → B} (e : BiInv f) : QInv f where
  inv := e.left.linv
  sect := e.left.sect
  retr := fun b =>
    -- Use: g(f(h(b))) = h(b) from sect, f(h(b)) = b from retr
    -- So f(g(b)) = b follows from: f(g(b)) = f(g(f(h(b)))) = f(h(b)) = b
    Path.ofEq (by
      have hsect := fun x => (e.left.sect x).proof
      have hretr := fun x => (e.right.retr x).proof
      -- g(f(x)) = x and f(h(x)) = x
      -- f(g(b)) = f(g(f(h(b)))) [by congrArg f (congrArg g (hretr b))⁻¹]
      --         = f(h(b))        [by congrArg f (hsect (h(b)))]
      --         = b              [by hretr b]
      calc f (e.left.linv b)
          = f (e.left.linv (f (e.right.rinv b))) := by rw [hretr b]
        _ = f (e.right.rinv b) := by rw [hsect]
        _ = b := hretr b)

/-! ## Half-adjoint equivalences -/

/-- A half-adjoint equivalence. -/
structure IsHAE (f : A → B) where
  inv : B → A
  sect : (a : A) → Path (inv (f a)) a
  retr : (b : B) → Path (f (inv b)) b
  coh : (a : A) →
    (congrArg f (sect a)).toEq = (retr (f a)).toEq

/-- Every quasi-inverse can be upgraded to a half-adjoint equivalence
(coherence holds by proof irrelevance). -/
def qinvToHAE {f : A → B} (e : QInv f) : IsHAE f where
  inv := e.inv
  sect := e.sect
  retr := e.retr
  coh := fun _ => Subsingleton.elim _ _

/-- A half-adjoint equivalence yields a quasi-inverse. -/
def haeToQInv {f : A → B} (e : IsHAE f) : QInv f where
  inv := e.inv
  sect := e.sect
  retr := e.retr

/-! ## Equivalence type -/

/-- An equivalence between types. -/
structure Equiv (A : Type u) (B : Type v) where
  toFun : A → B
  isEquiv : QInv toFun

notation:25 A " ≃ₚ " B => Equiv A B

/-- The identity equivalence. -/
def Equiv.refl (A : Type u) : A ≃ₚ A :=
  ⟨fun x => x, idQInv⟩

/-- Symmetry of equivalences. -/
def Equiv.symm (e : A ≃ₚ B) : B ≃ₚ A :=
  ⟨e.isEquiv.inv, qinvInv e.isEquiv⟩

/-- Composition of equivalences. -/
def Equiv.trans (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) : A ≃ₚ C where
  toFun := e₂.toFun ∘ e₁.toFun
  isEquiv :=
    { inv := e₁.isEquiv.inv ∘ e₂.isEquiv.inv
      sect := fun a =>
        Path.trans
          (congrArg e₁.isEquiv.inv (e₂.isEquiv.sect (e₁.toFun a)))
          (e₁.isEquiv.sect a)
      retr := fun c =>
        Path.trans
          (congrArg e₂.toFun (e₁.isEquiv.retr (e₂.isEquiv.inv c)))
          (e₂.isEquiv.retr c) }

/-! ## Equivalence properties -/

/-- Forward function of identity equivalence. -/
theorem equiv_refl_toFun (a : A) :
    (Equiv.refl A).toFun a = a := rfl

/-- Inverse of identity equivalence. -/
theorem equiv_refl_inv (a : A) :
    (Equiv.refl A).isEquiv.inv a = a := rfl

/-- Symmetry of refl is refl. -/
theorem equiv_symm_refl_toFun (a : A) :
    (Equiv.symm (Equiv.refl A)).toFun a = a := rfl

/-- Section of composed equivalence. -/
theorem equiv_trans_sect (e₁ : A ≃ₚ B) (e₂ : B ≃ₚ C) (a : A) :
    ((Equiv.trans e₁ e₂).isEquiv.sect a).toEq =
      (Path.trans
        (congrArg e₁.isEquiv.inv (e₂.isEquiv.sect (e₁.toFun a)))
        (e₁.isEquiv.sect a)).toEq := rfl

/-! ## Fiber properties -/

/-- The fiber of the identity is a singleton. -/
def fiberIdSingleton (a : A) : Fiber (fun x : A => x) a :=
  Fiber.canonical (fun x => x) a

/-- The fiber of a quasi-inverse over any point is inhabited. -/
def fiberEquivInhabited {f : A → B} (e : QInv f) (b : B) :
    Fiber f b :=
  ⟨e.inv b, e.retr b⟩

/-- Two fiber elements have paths in the base connected via the fiber. -/
def fiber_path {f : A → B} {b : B}
    (x y : Fiber f b) : Path (f x.point) (f y.point) :=
  Path.trans x.path (Path.symm y.path)

/-! ## Transport as equivalence -/

/-- Transport along a path is an equivalence. -/
def transportEquiv {D : A → Type v} {a b : A} (p : Path a b) :
    D a ≃ₚ D b where
  toFun := Path.transport p
  isEquiv :=
    { inv := Path.transport (Path.symm p)
      sect := fun x => Path.ofEq (Path.transport_symm_left p x)
      retr := fun y => Path.ofEq (Path.transport_symm_right p y) }

/-- Forward map of transportEquiv is transport. -/
theorem transportEquiv_toFun {D : A → Type v} {a b : A}
    (p : Path a b) (x : D a) :
    (transportEquiv p).toFun x = Path.transport p x := rfl

/-- Inverse of transportEquiv is transport along symm. -/
theorem transportEquiv_inv {D : A → Type v} {a b : A}
    (p : Path a b) (y : D b) :
    (transportEquiv p).isEquiv.inv y = Path.transport (Path.symm p) y := rfl

/-- Transport along refl is the identity. -/
theorem transportEquiv_refl {D : A → Type v} {a : A} (x : D a) :
    (transportEquiv (refl a) (D := D)).toFun x = x := by
  simp [transportEquiv, Path.transport]

/-! ## congrArg properties with equivalences -/

/-- congrArg of id on a path is the path itself. -/
theorem congrArg_id_equiv {a b : A} (p : Path a b) :
    congrArg (fun x => x) p = p :=
  Path.congrArg_id p

/-- Applying f then g to a path composes. -/
theorem congrArg_compose {f : A → B} {g : B → C}
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    congrArg (g ∘ f) p = congrArg g (congrArg f p) :=
  Path.congrArg_comp g f p

/-- congrArg preserves refl. -/
theorem congrArg_refl_eq {f : A → B} (a : A) :
    congrArg f (refl a) = refl (f a) := by simp

/-- congrArg preserves symm. -/
theorem congrArg_symm_eq {f : A → B} {a b : A} (p : Path a b) :
    congrArg f (Path.symm p) = Path.symm (congrArg f p) :=
  Path.congrArg_symm f p

/-- congrArg preserves trans. -/
theorem congrArg_trans_eq {f : A → B} {a b c : A}
    (p : Path a b) (q : Path b c) :
    congrArg f (Path.trans p q) = Path.trans (congrArg f p) (congrArg f q) :=
  Path.congrArg_trans f p q

/-- Equivalence from IsContr to Unit. -/
def contrToUnit (h : IsContr A) : A ≃ₚ Unit where
  toFun := fun _ => ()
  isEquiv :=
    { inv := fun _ => h.center
      sect := fun a => h.contr a
      retr := fun u => by cases u; exact refl () }

end Equivalences
end HoTT
end Path
end ComputationalPaths
