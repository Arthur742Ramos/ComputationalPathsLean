/-
# Fundamental group interface for computational paths

This module packages the loop-quotient machinery into the traditional
`π₁(A, a)` notation used throughout the thesis.  We work entirely in the
computational-path setting: loops are computational paths, two loops are
identified when they are related by rewrite equality, and the resulting
quotient inherits the strict group structure supplied by `LoopGroup`.
-/

import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path

universe u

/-- Fundamental group elements at `a : A` are rewrite classes of loops. -/
abbrev PiOne (A : Type u) (a : A) : Type u :=
  LoopQuot A a

/-- Strict group structure carried by `π₁(A, a)`. -/
abbrev PiOneGroup (A : Type u) (a : A) : LoopGroup A a :=
  loopGroup A a

notation "π₁(" A ", " a ")" => PiOne A a

/-- Identity element of `π₁(A, a)`. -/
@[simp] def PiOne.id {A : Type u} {a : A} : π₁(A, a) :=
  LoopQuot.id (A := A) (a := a)

/-- Group multiplication in `π₁(A, a)` is induced by loop concatenation. -/
@[simp] def PiOne.mul {A : Type u} {a : A} :
    π₁(A, a) → π₁(A, a) → π₁(A, a) :=
  LoopQuot.comp (A := A) (a := a)

/-- Loop inversion in `π₁(A, a)` comes from reversing paths. -/
@[simp] def PiOne.inv {A : Type u} {a : A} :
    π₁(A, a) → π₁(A, a) :=
  LoopQuot.inv (A := A) (a := a)

@[simp] theorem PiOne.mul_assoc {A : Type u} {a : A}
    (x y z : π₁(A, a)) :
    PiOne.mul (PiOne.mul x y) z = PiOne.mul x (PiOne.mul y z) :=
  LoopQuot.comp_assoc (A := A) (a := a) x y z

@[simp] theorem PiOne.id_mul {A : Type u} {a : A}
    (x : π₁(A, a)) : PiOne.mul PiOne.id x = x :=
  LoopQuot.id_comp (A := A) (a := a) x

@[simp] theorem PiOne.mul_id {A : Type u} {a : A}
    (x : π₁(A, a)) : PiOne.mul x PiOne.id = x :=
  LoopQuot.comp_id (A := A) (a := a) x

@[simp] theorem PiOne.mul_left_inv {A : Type u} {a : A}
    (x : π₁(A, a)) :
    PiOne.mul (PiOne.inv x) x = PiOne.id :=
  LoopQuot.inv_comp (A := A) (a := a) x

@[simp] theorem PiOne.mul_right_inv {A : Type u} {a : A}
    (x : π₁(A, a)) :
    PiOne.mul x (PiOne.inv x) = PiOne.id :=
  LoopQuot.comp_inv (A := A) (a := a) x

/-- View a concrete loop as an element of `π₁(A, a)`. -/
@[simp] def PiOne.ofLoop {A : Type u} {a : A} :
    LoopSpace A a → π₁(A, a) :=
  LoopQuot.ofLoop (A := A) (a := a)

/-- Iterate a fundamental-group element `n` times (natural powers). -/
@[simp] def PiOne.pow {A : Type u} {a : A} :
    π₁(A, a) → Nat → π₁(A, a) :=
  LoopQuot.pow (A := A) (a := a)

/-- Iterate a fundamental-group element an integer number of times. -/
@[simp] def PiOne.zpow {A : Type u} {a : A} :
    π₁(A, a) → Int → π₁(A, a) :=
  LoopQuot.zpow (A := A) (a := a)

end Path
end ComputationalPaths
