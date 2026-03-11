/-
# Fundamental group interface for computational paths

This module packages the loop-quotient machinery into the traditional
`π₁(A, a)` notation.  We work entirely in the
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

/-- Strict monoid structure carried by `π₁(A, a)`. -/
noncomputable abbrev PiOneMonoid (A : Type u) (a : A) : LoopMonoid A a :=
  loopMonoid A a

/-- Strict group structure carried by `π₁(A, a)`. -/
noncomputable abbrev PiOneGroup (A : Type u) (a : A) : LoopGroup A a :=
  loopGroup A a

notation "π₁(" A ", " a ")" => PiOne A a

/-- Identity element of `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.id {A : Type u} {a : A} : π₁(A, a) :=
  LoopQuot.id (A := A) (a := a)

/-- Group multiplication in `π₁(A, a)` is induced by loop concatenation. -/
@[simp] noncomputable def PiOne.mul {A : Type u} {a : A} :
    π₁(A, a) → π₁(A, a) → π₁(A, a) :=
  LoopQuot.comp (A := A) (a := a)

/-- Loop inversion in `π₁(A, a)` comes from reversing paths. -/
@[simp] noncomputable def PiOne.inv {A : Type u} {a : A} :
    π₁(A, a) → π₁(A, a) :=
  LoopQuot.inv (A := A) (a := a)

@[simp] theorem PiOne.mul_assoc {A : Type u} {a : A}
    (x y z : π₁(A, a)) :
    PiOne.mul (PiOne.mul x y) z = PiOne.mul x (PiOne.mul y z) :=
  LoopQuot.comp_assoc (A := A) (a := a) x y z

/-- `Path` witness for associativity in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.mul_assoc_path {A : Type u} {a : A}
    (x y z : π₁(A, a)) :
    Path (PiOne.mul (PiOne.mul x y) z) (PiOne.mul x (PiOne.mul y z)) :=
  Path.stepChain (PiOne.mul_assoc x y z)

@[simp] theorem PiOne.id_mul {A : Type u} {a : A}
    (x : π₁(A, a)) : PiOne.mul PiOne.id x = x :=
  LoopQuot.id_comp (A := A) (a := a) x

/-- `Path` witness for the left unit law in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.id_mul_path {A : Type u} {a : A}
    (x : π₁(A, a)) : Path (PiOne.mul PiOne.id x) x :=
  Path.stepChain (PiOne.id_mul x)

@[simp] theorem PiOne.mul_id {A : Type u} {a : A}
    (x : π₁(A, a)) : PiOne.mul x PiOne.id = x :=
  LoopQuot.comp_id (A := A) (a := a) x

/-- `Path` witness for the right unit law in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.mul_id_path {A : Type u} {a : A}
    (x : π₁(A, a)) : Path (PiOne.mul x PiOne.id) x :=
  Path.stepChain (PiOne.mul_id x)

@[simp] theorem PiOne.mul_left_inv {A : Type u} {a : A}
    (x : π₁(A, a)) :
    PiOne.mul (PiOne.inv x) x = PiOne.id :=
  LoopQuot.inv_comp (A := A) (a := a) x

/-- `Path` witness for the left inverse law in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.mul_left_inv_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.mul (PiOne.inv x) x) PiOne.id :=
  Path.stepChain (PiOne.mul_left_inv x)

@[simp] theorem PiOne.mul_right_inv {A : Type u} {a : A}
    (x : π₁(A, a)) :
    PiOne.mul x (PiOne.inv x) = PiOne.id :=
  LoopQuot.comp_inv (A := A) (a := a) x

/-- `Path` witness for the right inverse law in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.mul_right_inv_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.mul x (PiOne.inv x)) PiOne.id :=
  Path.stepChain (PiOne.mul_right_inv x)

/-- View a concrete loop as an element of `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.ofLoop {A : Type u} {a : A} :
    LoopSpace A a → π₁(A, a) :=
  LoopQuot.ofLoop (A := A) (a := a)

/-- `Path` witness for loop concatenation under the quotient map. -/
@[simp] noncomputable def PiOne.ofLoop_trans_path {A : Type u} {a : A}
    (p q : LoopSpace A a) :
    Path (PiOne.ofLoop (Path.trans p q)) (PiOne.mul (PiOne.ofLoop p) (PiOne.ofLoop q)) :=
  Path.stepChain (LoopQuot.ofLoop_trans (A := A) (a := a) p q)

/-- `Path` witness for loop inversion under the quotient map. -/
@[simp] noncomputable def PiOne.ofLoop_symm_path {A : Type u} {a : A}
    (p : LoopSpace A a) :
    Path (PiOne.ofLoop (Path.symm p)) (PiOne.inv (PiOne.ofLoop p)) :=
  Path.stepChain (LoopQuot.ofLoop_symm (A := A) (a := a) p)

/-- `Path` witness for the reflexive loop under the quotient map. -/
@[simp] noncomputable def PiOne.ofLoop_refl_path {A : Type u} {a : A} :
    Path (PiOne.ofLoop (Path.refl a)) PiOne.id :=
  Path.stepChain (LoopQuot.ofLoop_refl (A := A) (a := a))

/-- Iterate a fundamental-group element `n` times (natural powers). -/
@[simp] noncomputable def PiOne.pow {A : Type u} {a : A} :
    π₁(A, a) → Nat → π₁(A, a) :=
  LoopQuot.pow (A := A) (a := a)

/-- `Path` witness for zeroth power in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.pow_zero_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.pow x 0) PiOne.id :=
  Path.stepChain (LoopQuot.pow_zero (A := A) (a := a) x)

/-- `Path` witness for successor powers in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.pow_succ_path {A : Type u} {a : A}
    (x : π₁(A, a)) (n : Nat) :
    Path (PiOne.pow x n.succ) (PiOne.mul (PiOne.pow x n) x) :=
  Path.stepChain (LoopQuot.pow_succ (A := A) (a := a) x n)

/-- `Path` witness for first powers in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.pow_one_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.pow x 1) x :=
  Path.stepChain (LoopQuot.pow_one (A := A) (a := a) x)

/-- `Path` witness for additive power splitting in `π₁(A, a)`. -/
noncomputable def PiOne.pow_add_path {A : Type u} {a : A}
    (x : π₁(A, a)) (m n : Nat) :
    Path (PiOne.pow x (m + n)) (PiOne.mul (PiOne.pow x m) (PiOne.pow x n)) :=
  Path.stepChain (LoopQuot.pow_add (A := A) (a := a) x m n)

/-- Iterate a fundamental-group element an integer number of times. -/
@[simp] noncomputable def PiOne.zpow {A : Type u} {a : A} :
    π₁(A, a) → Int → π₁(A, a) :=
  LoopQuot.zpow (A := A) (a := a)

/-- `Path` witness for zeroth integer power in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.zpow_zero_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.zpow x 0) PiOne.id :=
  Path.stepChain (LoopQuot.zpow_zero (A := A) (a := a) x)

/-- `Path` witness for first integer power in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.zpow_one_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.zpow x 1) x :=
  Path.stepChain (LoopQuot.zpow_one (A := A) (a := a) x)

/-- `Path` witness for negative-one power in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.zpow_neg_one_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.zpow x (-1)) (PiOne.inv x) :=
  Path.stepChain (LoopQuot.zpow_neg_one (A := A) (a := a) x)

/-- `Path` witness for inversion of the identity element in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.inv_id_path {A : Type u} {a : A} :
    Path (@PiOne.inv A a (@PiOne.id A a)) (@PiOne.id A a) :=
  Path.stepChain (LoopQuot.inv_id (A := A) (a := a))

/-- `Path` witness for involutivity of inversion in `π₁(A, a)`. -/
@[simp] noncomputable def PiOne.inv_inv_path {A : Type u} {a : A}
    (x : π₁(A, a)) :
    Path (PiOne.inv (PiOne.inv x)) x :=
  Path.stepChain (LoopQuot.inv_inv (A := A) (a := a) x)

/-- `Path` witness for inversion reversing multiplication order in `π₁(A, a)`. -/
noncomputable def PiOne.inv_mul_rev_path {A : Type u} {a : A}
    (x y : π₁(A, a)) :
    Path (PiOne.inv (PiOne.mul x y)) (PiOne.mul (PiOne.inv y) (PiOne.inv x)) :=
  Path.stepChain (LoopQuot.inv_comp_eq (A := A) (a := a) x y)

/-- `Path` witness for additive integer power splitting in `π₁(A, a)`. -/
noncomputable def PiOne.zpow_add_path {A : Type u} {a : A}
    (x : π₁(A, a)) (m n : Int) :
    Path (PiOne.zpow x (m + n)) (PiOne.mul (PiOne.zpow x m) (PiOne.zpow x n)) :=
  Path.stepChain (LoopQuot.zpow_add (A := A) (a := a) x m n)

end Path
end ComputationalPaths
