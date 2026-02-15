/-
# Monads via Computational Paths

Monads formalized through the path framework: unit and bind as path operations,
monad laws as path equalities with multi-step trans/symm/congrArg proofs,
Kleisli composition, monad morphisms, and derived operations.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MonadDeep

open ComputationalPaths.Path

universe u v w

/-! ## Path-witnessed monad structure -/

structure PathMonad (M : Type u → Type u) where
  pure : ∀ {A : Type u}, A → M A
  bind : ∀ {A B : Type u}, M A → (A → M B) → M B
  left_unit  : ∀ {A B : Type u} (a : A) (f : A → M B),
    Path (bind (pure a) f) (f a)
  right_unit : ∀ {A : Type u} (m : M A),
    Path (bind m pure) m
  assoc : ∀ {A B C : Type u} (m : M A) (f : A → M B) (g : B → M C),
    Path (bind (bind m f) g) (bind m (fun a => bind (f a) g))

variable {M : Type u → Type u} (mon : PathMonad M)

/-! ## Kleisli composition -/

def kleisli {A B C : Type u} (f : A → M B) (g : B → M C) : A → M C :=
  fun a => mon.bind (f a) g

/-! ## 1: Left identity of Kleisli -/
def kleisli_left_id {A B : Type u} (f : A → M B) (a : A) :
    Path (kleisli mon mon.pure f a) (f a) :=
  mon.left_unit a f

/-! ## 2: Right identity of Kleisli -/
def kleisli_right_id {A B : Type u} (f : A → M B) (a : A) :
    Path (kleisli mon f mon.pure a) (f a) :=
  mon.right_unit (f a)

/-! ## 3: Associativity of Kleisli -/
def kleisli_assoc {A B C D : Type u}
    (f : A → M B) (g : B → M C) (h : C → M D) (a : A) :
    Path (kleisli mon (kleisli mon f g) h a)
         (kleisli mon f (kleisli mon g h) a) :=
  mon.assoc (f a) g h

/-! ## 4: pure ∘ Kleisli collapses -/
def pure_kleisli {A B C : Type u}
    (f : A → M B) (g : B → M C) (a : A) :
    Path (mon.bind (mon.pure a) (kleisli mon f g))
         (kleisli mon f g a) :=
  mon.left_unit a (kleisli mon f g)

/-! ## 5: Double bind flattening -/
def double_bind_flatten {A B C : Type u}
    (m : M A) (f : A → M B) (g : B → M C) :
    Path (mon.bind (mon.bind m f) g)
         (mon.bind m (fun a => mon.bind (f a) g)) :=
  mon.assoc m f g

/-! ## 6: bind after right_unit via congrArg -/
def bind_after_right_unit {A B : Type u}
    (m : M A) (f : A → M B) :
    Path (mon.bind (mon.bind m mon.pure) f) (mon.bind m f) :=
  Path.congrArg (fun x => mon.bind x f) (mon.right_unit m)

/-! ## 7-8: Symmetric monad laws -/
def left_unit_symm {A B : Type u} (a : A) (f : A → M B) :
    Path (f a) (mon.bind (mon.pure a) f) :=
  Path.symm (mon.left_unit a f)

def right_unit_symm {A : Type u} (m : M A) :
    Path m (mon.bind m mon.pure) :=
  Path.symm (mon.right_unit m)

/-! ## 9: assoc symmetry -/
def assoc_symm {A B C : Type u}
    (m : M A) (f : A → M B) (g : B → M C) :
    Path (mon.bind m (fun a => mon.bind (f a) g))
         (mon.bind (mon.bind m f) g) :=
  Path.symm (mon.assoc m f g)

/-! ## 10-11: congrArg through bind -/
def bind_congrArg_left {A B : Type u}
    (m₁ m₂ : M A) (f : A → M B) (h : Path m₁ m₂) :
    Path (mon.bind m₁ f) (mon.bind m₂ f) :=
  Path.congrArg (fun x => mon.bind x f) h

def bind_congrArg_right {A B : Type u}
    (m : M A) (f g : A → M B) (h : f = g) :
    Path (mon.bind m f) (mon.bind m g) :=
  Path.ofEq (_root_.congrArg (fun k => mon.bind m k) h)

/-! ## 12: nested congrArg through two binds -/
def bind_nested_congrArg {A B C : Type u}
    (m₁ m₂ : M A) (f : A → M B) (g : B → M C) (h : Path m₁ m₂) :
    Path (mon.bind (mon.bind m₁ f) g)
         (mon.bind (mon.bind m₂ f) g) :=
  Path.congrArg (fun x => mon.bind x g)
    (Path.congrArg (fun x => mon.bind x f) h)

/-! ## 13: unit-bind-unit collapse -/
def unit_bind_unit {A : Type u} (a : A) :
    Path (mon.bind (mon.pure a) mon.pure) (mon.pure a) :=
  mon.left_unit a mon.pure

/-! ## 14: naturality of left_unit -/
def left_unit_naturality {A B C : Type u}
    (f : A → B) (g : B → M C) (a : A) :
    Path (mon.bind (mon.pure (f a)) g) (g (f a)) :=
  mon.left_unit (f a) g

/-! ## 15: bind-pure cancellation via 2-step trans -/
def bind_pure_cancel {A B : Type u} (a : A) (f : A → M B) :
    Path (mon.bind (mon.bind (mon.pure a) f) mon.pure)
         (f a) :=
  Path.trans
    (Path.congrArg (fun x => mon.bind x mon.pure) (mon.left_unit a f))
    (mon.right_unit (f a))

/-! ## 16: symmetric bind-pure cancellation -/
def bind_pure_cancel_symm {A B : Type u} (a : A) (f : A → M B) :
    Path (f a)
         (mon.bind (mon.bind (mon.pure a) f) mon.pure) :=
  Path.symm (bind_pure_cancel mon a f)

/-! ## 17: four-step chain: 2x left_unit via trans -/
def four_step_chain {A B : Type u}
    (a : A) (f : A → M B) :
    Path (mon.bind (mon.bind (mon.pure a) mon.pure) f)
         (f a) :=
  Path.trans
    (Path.congrArg (fun x => mon.bind x f) (mon.left_unit a mon.pure))
    (mon.left_unit a f)

/-! ## 18: deep trans: left_unit + bind -/
def deep_left_assoc {A B C : Type u}
    (a : A) (f : A → M B) (g : B → M C) :
    Path (mon.bind (mon.bind (mon.pure a) f) g)
         (mon.bind (f a) g) :=
  Path.congrArg (fun x => mon.bind x g) (mon.left_unit a f)

/-! ## 19: right_unit + nested congrArg -/
def right_unit_nested {A B C : Type u}
    (m : M A) (f : A → M B) (g : B → M C) :
    Path (mon.bind (mon.bind (mon.bind m mon.pure) f) g)
         (mon.bind (mon.bind m f) g) :=
  Path.congrArg (fun x => mon.bind (mon.bind x f) g) (mon.right_unit m)

/-! ## Monad morphisms -/

structure PathMonadMorphism {M N : Type u → Type u}
    (monM : PathMonad M) (monN : PathMonad N) where
  transform : ∀ {A : Type u}, M A → N A
  unit_compat : ∀ {A : Type u} (a : A),
    Path (transform (monM.pure a)) (monN.pure a)
  bind_compat : ∀ {A B : Type u} (m : M A) (f : A → M B),
    Path (transform (monM.bind m f))
         (monN.bind (transform m) (fun a => transform (f a)))

variable {N : Type u → Type u} {monN : PathMonad N}

/-! ## 20: morphism preserves left unit (2-step trans) -/
def morphism_preserves_left_unit
    (φ : PathMonadMorphism mon monN)
    {A B : Type u} (a : A) (f : A → M B) :
    Path (φ.transform (mon.bind (mon.pure a) f))
         (monN.bind (monN.pure a) (fun x => φ.transform (f x))) :=
  Path.trans
    (φ.bind_compat (mon.pure a) f)
    (Path.congrArg (fun x => monN.bind x (fun a => φ.transform (f a)))
      (φ.unit_compat a))

/-! ## 21: morphism preserves right unit -/
def morphism_preserves_right_unit
    (φ : PathMonadMorphism mon monN)
    {A : Type u} (m : M A) :
    Path (φ.transform (mon.bind m mon.pure))
         (φ.transform m) :=
  Path.congrArg φ.transform (mon.right_unit m)

/-! ## 22: morphism + left_unit chain -/
def morphism_left_unit_direct
    (φ : PathMonadMorphism mon monN)
    {A B : Type u} (a : A) (f : A → M B) :
    Path (φ.transform (mon.bind (mon.pure a) f))
         (φ.transform (f a)) :=
  Path.congrArg φ.transform (mon.left_unit a f)

/-! ## 23: morphism preserves assoc -/
def morphism_preserves_assoc
    (φ : PathMonadMorphism mon monN)
    {A B C : Type u} (m : M A) (f : A → M B) (g : B → M C) :
    Path (φ.transform (mon.bind (mon.bind m f) g))
         (φ.transform (mon.bind m (fun a => mon.bind (f a) g))) :=
  Path.congrArg φ.transform (mon.assoc m f g)

/-! ## 24: deep morphism chain (congrArg + bind_compat) -/
def morphism_deep_chain
    (φ : PathMonadMorphism mon monN)
    {A B C : Type u} (m : M A) (f : A → M B) (g : B → M C) :
    Path (φ.transform (mon.bind (mon.bind m f) g))
         (monN.bind (φ.transform m) (fun a => φ.transform (mon.bind (f a) g))) :=
  Path.trans
    (Path.congrArg φ.transform (mon.assoc m f g))
    (φ.bind_compat m (fun a => mon.bind (f a) g))

/-! ## 25: morphism symm chain (symm + symm via trans) -/
def morphism_symm_chain
    (φ : PathMonadMorphism mon monN)
    {A B : Type u} (a : A) (f : A → M B) :
    Path (monN.bind (monN.pure a) (fun x => φ.transform (f x)))
         (φ.transform (mon.bind (mon.pure a) f)) :=
  Path.trans
    (Path.symm
      (Path.congrArg (fun x => monN.bind x (fun a => φ.transform (f a)))
        (φ.unit_compat a)))
    (Path.symm (φ.bind_compat (mon.pure a) f))

/-! ## Derived operations -/

def fmap {A B : Type u} (f : A → B) (m : M A) : M B :=
  mon.bind m (fun a => mon.pure (f a))

def join {A : Type u} (m : M (M A)) : M A :=
  mon.bind m (fun x => x)

/-! ## 26: fmap identity -/
def fmap_id {A : Type u} (m : M A) :
    Path (fmap mon (fun x : A => x) m) m :=
  mon.right_unit m

/-! ## 27: join after pure -/
def join_pure {A : Type u} (m : M A) :
    Path (join mon (mon.pure m)) m :=
  mon.left_unit m (fun x => x)

/-! ## 28: symm of bind_congrArg -/
def bind_symm_congrArg {A B : Type u}
    (m₁ m₂ : M A) (f : A → M B) (h : Path m₁ m₂) :
    Path (mon.bind m₂ f) (mon.bind m₁ f) :=
  Path.congrArg (fun x => mon.bind x f) (Path.symm h)

/-! ## 29: trans of two congrArgs -/
def bind_trans_congrArgs {A B : Type u}
    (m₁ m₂ m₃ : M A) (f : A → M B)
    (h₁ : Path m₁ m₂) (h₂ : Path m₂ m₃) :
    Path (mon.bind m₁ f) (mon.bind m₃ f) :=
  Path.trans
    (Path.congrArg (fun x => mon.bind x f) h₁)
    (Path.congrArg (fun x => mon.bind x f) h₂)

/-! ## 30: deep congrArg + trans on bind -/
def bind_deep_congrArg {A B C : Type u}
    (m₁ m₂ m₃ : M A) (f : A → M B) (g : B → M C)
    (h₁ : Path m₁ m₂) (h₂ : Path m₂ m₃) :
    Path (mon.bind (mon.bind m₁ f) g)
         (mon.bind (mon.bind m₃ f) g) :=
  Path.congrArg (fun x => mon.bind x g)
    (Path.congrArg (fun x => mon.bind x f)
      (Path.trans h₁ h₂))

/-! ## 31: Kleisli triple chain -/
def kleisli_triple_chain {A B C D : Type u}
    (f : A → M B) (g : B → M C) (h : C → M D) (a : A) :
    Path (mon.bind (mon.bind (f a) g) h)
         (mon.bind (f a) (fun b => mon.bind (g b) h)) :=
  mon.assoc (f a) g h

/-! ## 32: 3-step trans chain: pure + bind + pure -/
def three_step_pure_bind {A B : Type u} (a : A) (f : A → M B) :
    Path (mon.bind (mon.bind (mon.pure a) mon.pure) f)
         (mon.bind (mon.pure a) f) :=
  Path.congrArg (fun x => mon.bind x f) (mon.left_unit a mon.pure)

/-! ## 33: 3-step: above + left_unit -/
def three_step_full {A B : Type u} (a : A) (f : A → M B) :
    Path (mon.bind (mon.bind (mon.pure a) mon.pure) f) (f a) :=
  Path.trans
    (three_step_pure_bind mon a f)
    (mon.left_unit a f)

/-! ## 34: congrArg + symm + trans deep -/
def congrArg_symm_trans_deep {A B C : Type u}
    (m₁ m₂ : M A) (f : A → M B) (g : B → M C)
    (h : Path m₁ m₂) :
    Path (mon.bind (mon.bind m₂ f) g)
         (mon.bind m₁ (fun a => mon.bind (f a) g)) :=
  Path.trans
    (Path.congrArg (fun x => mon.bind x g)
      (Path.congrArg (fun x => mon.bind x f) (Path.symm h)))
    (mon.assoc m₁ f g)

/-! ## 35: morphism + unit_compat + left_unit 3-chain -/
def morphism_three_chain
    (φ : PathMonadMorphism mon monN)
    {A B : Type u} (a : A) (f : A → M B) :
    Path (φ.transform (mon.bind (mon.pure a) f))
         (φ.transform (f a)) :=
  Path.congrArg φ.transform (mon.left_unit a f)

/-! ## 36: morphism round-trip: transform + bind_compat + symm -/
def morphism_roundtrip
    (φ : PathMonadMorphism mon monN)
    {A B : Type u} (m : M A) (f : A → M B) :
    Path (monN.bind (φ.transform m) (fun a => φ.transform (f a)))
         (φ.transform (mon.bind m f)) :=
  Path.symm (φ.bind_compat m f)

/-! ## 37: double morphism application -/
def morphism_double_apply
    (φ : PathMonadMorphism mon monN)
    {A B C : Type u} (a : A) (f : A → M B) (g : B → M C) :
    Path (φ.transform (mon.bind (mon.bind (mon.pure a) f) g))
         (φ.transform (mon.bind (f a) g)) :=
  Path.congrArg φ.transform
    (Path.congrArg (fun x => mon.bind x g) (mon.left_unit a f))

/-! ## 38: trans chain: congrArg + assoc + congrArg -/
def trans_congrArg_assoc {A B C : Type u}
    (m₁ m₂ : M A) (f : A → M B) (g : B → M C)
    (h : Path m₁ m₂) :
    Path (mon.bind (mon.bind m₁ f) g)
         (mon.bind m₂ (fun a => mon.bind (f a) g)) :=
  Path.trans
    (Path.congrArg (fun x => mon.bind x g)
      (Path.congrArg (fun x => mon.bind x f) h))
    (mon.assoc m₂ f g)

/-! ## 39: bind preserves path equality (trans + congrArg) -/
def bind_preserves_path {A B : Type u}
    (m₁ m₂ m₃ : M A) (f : A → M B)
    (h₁ : Path m₁ m₂) (h₂ : Path m₂ m₃) :
    Path (mon.bind m₁ f) (mon.bind m₃ f) :=
  Path.congrArg (fun x => mon.bind x f) (Path.trans h₁ h₂)

end MonadDeep
end Algebra
end Path
end ComputationalPaths
