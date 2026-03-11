/-
# LoopSpace

Public loop-space interface via computational paths.

This wrapper keeps the previous loop-space shim imports available while
surfacing representative constructions and theorems from `LoopSpaceDeep`.
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.LoopSpaceAlgebra
import ComputationalPaths.Path.Homotopy.LoopSpaceDeep

namespace ComputationalPaths.Path.Homotopy.LoopSpace

open ComputationalPaths.Path

universe u

abbrev BasedLoopSpace (A : Type u) (a : A) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.LoopSpace A a

abbrev DoubleLoopSpace (A : Type u) (a : A) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.DoubleLoopSpace A a

abbrev BarConstruction (A : Type u) (a : A) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.BarConstruction A a

abbrev SuspData (A : Type u) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.SuspData A

abbrev LoopHomotopy {A : Type u} {a : A}
    (ℓ₁ ℓ₂ : BasedLoopSpace A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.LoopHomotopy ℓ₁ ℓ₂

abbrev PointedMap (A B : Type u) (a : A) (b : B) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.PointedMap A B a b

abbrev FormalWord (A : Type u) (a : A) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.FormalWord A a

/-! ## Representative loop-space operations -/

@[inline] noncomputable def loopMul {A : Type u} {a : A}
    (p q : BasedLoopSpace A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopMul p q

@[inline] noncomputable def loopOne {A : Type u} (a : A) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopOne a

@[inline] noncomputable def loopInv {A : Type u} {a : A}
    (p : BasedLoopSpace A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopInv p

theorem loopMul_one_left {A : Type u} {a : A} (p : BasedLoopSpace A a) :
    loopMul (loopOne a) p = Path.trans (Path.refl a) p :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopMul_one_left p

theorem loopMul_one_right {A : Type u} {a : A} (p : BasedLoopSpace A a) :
    loopMul p (loopOne a) = Path.trans p (Path.refl a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopMul_one_right p

@[inline] noncomputable def loopConj {A : Type u} {a b : A}
    (p : Path a b) (ℓ : BasedLoopSpace A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopConj p ℓ

@[inline] noncomputable def loopMap {A B : Type u} (f : A → B)
    {a : A} (ℓ : BasedLoopSpace A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopMap f ℓ

theorem loopMap_one_eq {A B : Type u} (f : A → B) (a : A) :
    loopMap f (loopOne a) = Path.refl (f a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopMap_one_eq f a

theorem loopMap_mul_eq {A B : Type u} (f : A → B)
    {a : A} (ℓ₁ ℓ₂ : BasedLoopSpace A a) :
    loopMap f (loopMul ℓ₁ ℓ₂) = Path.trans (loopMap f ℓ₁) (loopMap f ℓ₂) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopMap_mul_eq f ℓ₁ ℓ₂

@[inline] noncomputable def jamesSingleton {A : Type u} {a : A}
    (ℓ : BasedLoopSpace A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.jamesSingleton ℓ

@[inline] noncomputable def jamesLength {A : Type u} {a : A}
    (w : ComputationalPaths.Path.Homotopy.LoopSpaceDeep.JamesWord A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.jamesLength w

theorem jamesLength_singleton {A : Type u} {a : A} (ℓ : BasedLoopSpace A a) :
    jamesLength (jamesSingleton ℓ) = 1 :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.jamesLength_singleton ℓ

@[inline] noncomputable def loopSuspUnit {A : Type u}
    (S : SuspData A) (a₀ : A) (a : A) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopSuspUnit S a₀ a

theorem loopSuspUnit_base {A : Type u} (S : SuspData A) (a₀ : A) :
    loopSuspUnit S a₀ a₀ = Path.trans (S.merid a₀) (Path.symm (S.merid a₀)) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopSuspUnit_base S a₀

@[inline] noncomputable def loopHomotopyTrans {A : Type u} {a : A}
    {ℓ₁ ℓ₂ ℓ₃ : BasedLoopSpace A a}
    (h₁ : LoopHomotopy ℓ₁ ℓ₂) (h₂ : LoopHomotopy ℓ₂ ℓ₃) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.loopHomotopyTrans h₁ h₂

@[inline] noncomputable def pointedMapPath {A B : Type u} {a : A} {b : B}
    (f : PointedMap A B a b) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.pointedMapPath f

@[inline] noncomputable def formalConcat {A : Type u} {a : A}
    (w₁ w₂ : FormalWord A a) :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.formalConcat w₁ w₂

theorem formalConcat_empty_left {A : Type u} {a : A} (w : FormalWord A a) :
    formalConcat .empty w = w :=
  ComputationalPaths.Path.Homotopy.LoopSpaceDeep.formalConcat_empty_left w

end ComputationalPaths.Path.Homotopy.LoopSpace
