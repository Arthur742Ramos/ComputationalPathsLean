/- 
# Hochschild Cohomology via Computational Paths

This module provides a lightweight Hochschild-cohomology interface built
from computational paths.  We use Path-typed witnesses for the key laws
of cochain complexes and cocycles.

## Main Definitions

- `HochschildAlgebra`: algebra data with Path-witnessed laws
- `HochschildCochain`: n-cochains as functions `(Fin n → A) → A`
- `HochschildDifferential`: cochain differential with Path-typed `d ∘ d = 0`
- `HochschildCocycle`: cocycles defined by Path-typed closure
- `HochschildCohomology`: quotient of cocycles by pointwise Path

## References

- Loday, "Cyclic Homology"
- Weibel, "An Introduction to Homological Algebra"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HochschildCohomology

universe u

/-! ## Algebra data -/

/-- Algebra data needed for Hochschild cochains. -/
structure HochschildAlgebra (A : Type u) where
  /-- Additive identity. -/
  zero : A
  /-- Addition. -/
  add : A → A → A
  /-- Additive inverse. -/
  neg : A → A
  /-- Multiplication. -/
  mul : A → A → A
  /-- Multiplicative identity. -/
  one : A
  /-- Addition is associative. -/
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  /-- Addition is commutative. -/
  add_comm : ∀ x y, add x y = add y x
  /-- Left identity for addition. -/
  add_zero : ∀ x, add zero x = x
  /-- Left inverse for addition. -/
  add_left_neg : ∀ x, add (neg x) x = zero
  /-- Multiplication is associative. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left identity for multiplication. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity for multiplication. -/
  mul_one : ∀ x, mul x one = x

namespace HochschildAlgebra

variable {A : Type u} (Alg : HochschildAlgebra A)

/-- `Path` witness for left additive identity. -/
def add_zero_path (x : A) : Path (Alg.add Alg.zero x) x :=
  Path.stepChain (Alg.add_zero x)

/-- `Path` witness for additive inverse. -/
def add_left_neg_path (x : A) : Path (Alg.add (Alg.neg x) x) Alg.zero :=
  Path.stepChain (Alg.add_left_neg x)

/-- `Path` witness for left multiplicative identity. -/
def one_mul_path (x : A) : Path (Alg.mul Alg.one x) x :=
  Path.stepChain (Alg.one_mul x)

/-- `Path` witness for right multiplicative identity. -/
def mul_one_path (x : A) : Path (Alg.mul x Alg.one) x :=
  Path.stepChain (Alg.mul_one x)

end HochschildAlgebra

/-! ## Hochschild cochains -/

/-- Hochschild n-cochains: functions `(Fin n → A) → A`. -/
def HochschildCochain (A : Type u) (n : Nat) : Type u :=
  (Fin n → A) → A

variable {A : Type u} (Alg : HochschildAlgebra A)

/-- Constant zero cochain. -/
def cochainZero (n : Nat) : HochschildCochain A n :=
  fun _ => Alg.zero

/-- Pointwise addition of cochains. -/
def cochainAdd (n : Nat) (f g : HochschildCochain A n) : HochschildCochain A n :=
  fun x => Alg.add (f x) (g x)

/-- Pointwise negation of a cochain. -/
def cochainNeg (n : Nat) (f : HochschildCochain A n) : HochschildCochain A n :=
  fun x => Alg.neg (f x)

/-- Pointwise `Path` between cochains. -/
def CochainPath {n : Nat} (f g : HochschildCochain A n) : Type u :=
  ∀ x, Path (f x) (g x)

/-- Reflexivity of pointwise `Path`. -/
def cochainPath_refl {n : Nat} (f : HochschildCochain A n) : CochainPath f f :=
  fun x => Path.refl (f x)

/-- Build a pointwise `Path` from definitional equality. -/
def cochainPath_ofEq {n : Nat} {f g : HochschildCochain A n} (h : f = g) :
    CochainPath f g := by
  subst h
  exact cochainPath_refl f

/-! ## Differentials and cocycles -/

/-- A Hochschild differential with a Path-typed square-zero law. -/
structure HochschildDifferential (A : Type u) (Alg : HochschildAlgebra A) where
  /-- The differential `d : C^n → C^{n+1}`. -/
  d : ∀ n, HochschildCochain A n → HochschildCochain A (n + 1)
  /-- Square-zero law `d ∘ d = 0` as definitional equality. -/
  d_sq_zero : ∀ n (f : HochschildCochain A n),
    d (n + 1) (d n f) = cochainZero (Alg := Alg) (n + 2)

namespace HochschildDifferential

variable {A : Type u} {Alg : HochschildAlgebra A} (D : HochschildDifferential A Alg)

/-- Path witness of the square-zero law. -/
def d_sq_zero_path (n : Nat) (f : HochschildCochain A n) :
    Path (D.d (n + 1) (D.d n f)) (cochainZero (Alg := Alg) (n + 2)) :=
  Path.stepChain (D.d_sq_zero n f)

end HochschildDifferential

/-- A Hochschild n-cocycle: a cochain closed under the differential. -/
structure HochschildCocycle (A : Type u) (Alg : HochschildAlgebra A)
    (D : HochschildDifferential A Alg) (n : Nat) where
  /-- The underlying cochain. -/
  cochain : HochschildCochain A n
  /-- Closure under the differential, witnessed by `Path`. -/
  closed : Path (D.d n cochain) (cochainZero (Alg := Alg) (n + 1))

/-! ## Cohomology quotient -/

/-- Pointwise `Path` relation on cocycles. -/
def cocycleRel {A : Type u} {Alg : HochschildAlgebra A}
    {D : HochschildDifferential A Alg} {n : Nat}
    (f g : HochschildCocycle A Alg D n) : Prop :=
  Nonempty (CochainPath f.cochain g.cochain)

/-- Hochschild cohomology as a quotient by pointwise `Path`. -/
def HochschildCohomology (A : Type u) (Alg : HochschildAlgebra A)
    (D : HochschildDifferential A Alg) (n : Nat) : Type u :=
  Quot (cocycleRel (A := A) (Alg := Alg) (D := D) (n := n))

/-! ## Summary -/

/-!
We introduced a minimal Hochschild cohomology interface based on computational
paths, including cochains, differentials, and cocycles, together with a
Path-quotient cohomology type.
-/

end HochschildCohomology
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HochschildCohomology

theorem hochschild_add_zero {A : Type _} (Alg : HochschildAlgebra A) (x : A) :
    Alg.add Alg.zero x = x :=
  Alg.add_zero x

theorem hochschild_mul_one {A : Type _} (Alg : HochschildAlgebra A) (x : A) :
    Alg.mul x Alg.one = x :=
  Alg.mul_one x

theorem cochainZero_eval {A : Type _} (Alg : HochschildAlgebra A)
    (n : Nat) (x : Fin n → A) :
    cochainZero (Alg := Alg) n x = Alg.zero :=
  rfl

theorem cochainAdd_eval {A : Type _} (Alg : HochschildAlgebra A)
    (n : Nat) (f g : HochschildCochain A n) (x : Fin n → A) :
    cochainAdd (Alg := Alg) n f g x = Alg.add (f x) (g x) :=
  rfl

theorem cochainNeg_eval {A : Type _} (Alg : HochschildAlgebra A)
    (n : Nat) (f : HochschildCochain A n) (x : Fin n → A) :
    cochainNeg (Alg := Alg) n f x = Alg.neg (f x) :=
  rfl

theorem cochainPath_refl_apply {A : Type _} (Alg : HochschildAlgebra A)
    {n : Nat} (f : HochschildCochain A n) (x : Fin n → A) :
    cochainPath_refl (Alg := Alg) f x = Path.refl (f x) :=
  rfl

theorem differential_sq_zero_eq {A : Type _} {Alg : HochschildAlgebra A}
    (D : HochschildDifferential A Alg) (n : Nat) (f : HochschildCochain A n) :
    D.d (n + 1) (D.d n f) = cochainZero (Alg := Alg) (n + 2) :=
  D.d_sq_zero n f

theorem cocycle_closed_path {A : Type _} {Alg : HochschildAlgebra A}
    {D : HochschildDifferential A Alg} {n : Nat}
    (z : HochschildCocycle A Alg D n) :
    Path (D.d n z.cochain) (cochainZero (Alg := Alg) (n + 1)) :=
  z.closed

theorem cocycleRel_refl {A : Type _} {Alg : HochschildAlgebra A}
    {D : HochschildDifferential A Alg} {n : Nat}
    (z : HochschildCocycle A Alg D n) :
    cocycleRel z z :=
  ⟨cochainPath_refl (Alg := Alg) z.cochain⟩

end HochschildCohomology
end Algebra
end Path
end ComputationalPaths
