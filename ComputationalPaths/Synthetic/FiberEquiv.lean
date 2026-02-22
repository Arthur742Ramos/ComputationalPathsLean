/-
# Synthetic homotopy theory: fibers, equivalences, and contractibility

Develops the core HoTT notions (fiber, isEquiv, contractibility,
and n-types) using computational paths. Every coherence law is
witnessed by explicit `Path.Step` or `RwEq` rewriting.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Synthetic.HomotopyPaths

namespace ComputationalPaths
namespace Synthetic

open Path

universe u v

variable {A : Type u} {B : Type u}

/-! ## Fibers -/

/-- The homotopy fiber of `f` over `b`. -/
structure Fiber (f : A → B) (b : B) where
  point : A
  path  : Path (f point) b

noncomputable def fiber_comp {C : Type u} (f : A → B) (g : B → C) (c : C)
    (fib : Fiber (g ∘ f) c) : Fiber g c where
  point := f fib.point
  path  := fib.path

noncomputable def fiber_id (b : A) : Fiber (fun x : A => x) b where
  point := b
  path  := Path.refl b

theorem fiber_id_point (b : A) : (fiber_id b).point = b := rfl

noncomputable def fiber_const_of_path {b₀ b : B}
    (p : Path b₀ b) : Fiber (fun _ : A => b₀) b₀ → Fiber (fun _ : A => b₀) b₀ :=
  fun fib => fib

/-! ## Sections and retractions -/

structure HasSection (f : A → B) where
  sec : B → A
  inv : (b : B) → Path (f (sec b)) b

structure HasRetraction (f : A → B) where
  ret : B → A
  inv : (a : A) → Path (ret (f a)) a

/-! ## Quasi-inverse -/

structure QInv (f : A → B) where
  inv      : B → A
  rightInv : (b : B) → Path (f (inv b)) b
  leftInv  : (a : A) → Path (inv (f a)) a

noncomputable def qinv_to_section (f : A → B) (q : QInv f) : HasSection f where
  sec := q.inv
  inv := q.rightInv

noncomputable def qinv_to_retraction (f : A → B) (q : QInv f) : HasRetraction f where
  ret := q.inv
  inv := q.leftInv

/-- Identity has a quasi-inverse. -/
noncomputable def qinv_id : QInv (fun a : A => a) where
  inv      := fun a => a
  rightInv := fun a => Path.refl a
  leftInv  := fun a => Path.refl a

/-- QInv is symmetric. -/
noncomputable def qinv_symm (f : A → B) (q : QInv f) : QInv q.inv where
  inv      := f
  rightInv := q.leftInv
  leftInv  := q.rightInv

/-! ## Contractibility -/

structure IsContr (A : Type u) where
  center : A
  contr  : (a : A) → Path center a

noncomputable def unitContr : IsContr Unit where
  center := ()
  contr  := fun () => Path.refl ()

noncomputable def isContr_retract {r : B → A} {s : A → B}
    (h : (a : A) → Path (r (s a)) a)
    (c : IsContr B) : IsContr A where
  center := r c.center
  contr  := fun a => Path.trans (Path.congrArg r (c.contr (s a))) (h a)

/-- Contractible types have all elements path-equal to center. -/
noncomputable def isContr_path_to_center (c : IsContr A) (a b : A) : Path a b :=
  Path.trans (Path.symm (c.contr a)) (c.contr b)

/-- Path from center ∘ sym ∘ path to center reduces. -/
noncomputable def isContr_path_refl_rweq (c : IsContr A) (a : A) :
    RwEq (Path.trans (Path.symm (c.contr a)) (c.contr a)) (Path.refl a) :=
  rweq_of_step (Path.Step.symm_trans (c.contr a))

/-! ## IsEquiv (half-adjoint) -/

structure IsEquiv (f : A → B) where
  inv      : B → A
  rightInv : (b : B) → Path (f (inv b)) b
  leftInv  : (a : A) → Path (inv (f a)) a
  adj      : (a : A) → Path (Path.congrArg f (leftInv a)) (rightInv (f a))

structure Equiv' (A : Type u) (B : Type u) where
  toFun   : A → B
  isEquiv : IsEquiv toFun

noncomputable def idEquiv' : Equiv' A A where
  toFun   := fun a => a
  isEquiv := {
    inv      := fun a => a
    rightInv := fun a => Path.refl a
    leftInv  := fun a => Path.refl a
    adj      := fun a => Path.refl (Path.refl a)
  }

/-- Identity equivalence coherences. -/
theorem idEquiv'_rightInv (a : A) :
    (idEquiv' (A := A)).isEquiv.rightInv a = Path.refl a := rfl

theorem idEquiv'_leftInv (a : A) :
    (idEquiv' (A := A)).isEquiv.leftInv a = Path.refl a := rfl

theorem idEquiv'_inv (a : A) :
    (idEquiv' (A := A)).isEquiv.inv a = a := rfl

/-! ## n-Type structure -/

def IsProp (A : Type u) : Type u := (a b : A) → Path a b

def IsSet (A : Type u) : Type u := (a b : A) → (p q : Path a b) → Path p q

noncomputable def isContr_isProp (c : IsContr A) : IsProp A :=
  fun a b => Path.trans (Path.symm (c.contr a)) (c.contr b)

/-! ## Truncation levels -/

inductive TruncLevel
  | neg2 : TruncLevel
  | succ : TruncLevel → TruncLevel

/-- Level -1 = propositions. -/
abbrev TruncLevel.neg1 := TruncLevel.succ TruncLevel.neg2
/-- Level 0 = sets. -/
abbrev TruncLevel.zero := TruncLevel.succ TruncLevel.neg1

noncomputable def IsTrunc : TruncLevel → Type u → Type u
  | TruncLevel.neg2 => fun X => IsContr X
  | TruncLevel.succ n => fun X => (a b : X) → IsTrunc n (Path a b)

noncomputable def isContr_isTrunc_neg2 (c : IsContr A) : IsTrunc TruncLevel.neg2 A := c

/-! ## Pointed types and pointed maps -/

structure Pointed where
  carrier : Type u
  basepoint : carrier

structure PointedMap (X Y : Pointed) where
  toFun : X.carrier → Y.carrier
  preserves : Path (toFun X.basepoint) Y.basepoint

noncomputable def pointedMapId (X : Pointed) : PointedMap X X where
  toFun := fun x => x
  preserves := Path.refl X.basepoint

noncomputable def pointedMapComp {X Y Z : Pointed}
    (f : PointedMap X Y) (g : PointedMap Y Z) : PointedMap X Z where
  toFun := g.toFun ∘ f.toFun
  preserves := Path.trans (Path.congrArg g.toFun f.preserves) g.preserves

theorem pointedMapComp_assoc {X Y Z W : Pointed}
    (f : PointedMap X Y) (g : PointedMap Y Z) (h : PointedMap Z W) :
    (pointedMapComp (pointedMapComp f g) h).toFun =
    (pointedMapComp f (pointedMapComp g h)).toFun := rfl

theorem pointedMapComp_id_left {X Y : Pointed} (f : PointedMap X Y) :
    (pointedMapComp (pointedMapId X) f).toFun = f.toFun := rfl

theorem pointedMapComp_id_right {X Y : Pointed} (f : PointedMap X Y) :
    (pointedMapComp f (pointedMapId Y)).toFun = f.toFun := rfl

/-! ## Transport paths along functions -/

noncomputable def transport_fun (f : A → B) {a₁ a₂ : A}
    (p : Path a₁ a₂) : Path (f a₁) (f a₂) :=
  Path.congrArg f p

noncomputable def transport_fun_refl (f : A → B) (a : A) :
    Path (transport_fun f (Path.refl a)) (Path.refl (f a)) := by
  simp [transport_fun]; exact Path.refl _

noncomputable def transport_fun_trans (f : A → B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    Path (transport_fun f (Path.trans p q))
         (Path.trans (transport_fun f p) (transport_fun f q)) := by
  simp [transport_fun, Path.congrArg, Path.trans]
  exact Path.stepChain (by simp)

noncomputable def transport_fun_symm (f : A → B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (transport_fun f (Path.symm p))
         (Path.symm (transport_fun f p)) := by
  simp [transport_fun, Path.congrArg, Path.symm]
  exact Path.stepChain (by simp)

/-! ## Path-space characterization helpers -/

noncomputable def path_sigma_fst {C : A → Type u} {x y : Sigma C}
    (p : Path x y) : Path x.1 y.1 :=
  Path.congrArg Sigma.fst p

noncomputable def path_prod_fst {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) : Path a₁ a₂ :=
  Path.fst p

noncomputable def path_prod_snd {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) : Path b₁ b₂ :=
  Path.snd p

/-- Product path eta: mk(fst p, snd p) ▷ p. -/
noncomputable def path_prod_eta_rweq {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.prodMk (Path.fst p) (Path.snd p)) p :=
  RwEq.step (Path.Step.prod_eta p)

end Synthetic
end ComputationalPaths
