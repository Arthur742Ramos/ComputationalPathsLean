/-
# Loop spaces via computational paths

This module packages the basic loop-space operations induced by computational
paths.  Loops at a point `base : A` are simply computational paths from `base`
to itself.  We expose the corresponding composition, inversion, and identity
operations both on raw paths and on their rewrite-quotients, so later modules
can reason with loop groups without reproving the algebraic laws.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u v

/-- The loop space of a pointed type `(A, base)` consists of computational paths
from `base` to itself. -/
abbrev LoopSpace (A : Type u) (base : A) : Type u :=
  Path base base

namespace LoopSpace

variable {A : Type u} {a : A}

/-- Identity loop at the chosen base point. -/
@[simp] def id : LoopSpace A a :=
  Path.refl a

/-- Loop composition inherits path composition. -/
@[simp] def comp (p q : LoopSpace A a) : LoopSpace A a :=
  Path.trans p q

/-- Loop inversion coincides with path symmetry. -/
@[simp] def inv (p : LoopSpace A a) : LoopSpace A a :=
  Path.symm p

@[simp] theorem comp_assoc (p q r : LoopSpace A a) :
    comp (comp p q) r = comp p (comp q r) :=
  Path.trans_assoc p q r

@[simp] theorem comp_id_left (p : LoopSpace A a) :
    comp id p = p :=
  Path.trans_refl_left p

@[simp] theorem comp_id_right (p : LoopSpace A a) :
    comp p id = p :=
  Path.trans_refl_right p

@[simp] theorem comp_inv_left (p : LoopSpace A a) :
    Rw (comp (inv p) p) id := by
  simpa using
    (rw_of_step (Step.symm_trans (A := A) (a := a) (b := a) p))

@[simp] theorem comp_inv_right (p : LoopSpace A a) :
    Rw (comp p (inv p)) id := by
  simpa using
    (rw_of_step (Step.trans_symm (A := A) (a := a) (b := a) p))

end LoopSpace

/-- Quotiented loop space obtained by modding out rewrite equality.  This is the
carrier that will receive the strict group structure. -/
abbrev LoopQuot (A : Type u) (base : A) : Type u :=
  PathRwQuot A base base

namespace LoopQuot

open Quot

variable {A : Type u} {a : A}

/-- Identity element in the loop quotient. -/
@[simp] def id : LoopQuot A a :=
  PathRwQuot.refl (A := A) a

/-- Composition in the loop quotient, inherited from rewrite concatenation. -/
@[simp] def comp (x y : LoopQuot A a) : LoopQuot A a :=
  PathRwQuot.trans (A := A) x y

/-- Inversion in the loop quotient. -/
@[simp] def inv (x : LoopQuot A a) : LoopQuot A a :=
  PathRwQuot.symm (A := A) x

/-- Canonical map from concrete loops to their quotient. -/
@[simp] def ofLoop (p : LoopSpace A a) : LoopQuot A a :=
  Quot.mk _ p

@[simp] theorem comp_assoc (x y z : LoopQuot A a) :
    comp (comp x y) z = comp x (comp y z) :=
  PathRwQuot.trans_assoc (A := A)
    (a := a) (b := a) (c := a) (d := a) x y z

@[simp] theorem comp_id_left (x : LoopQuot A a) :
    comp id x = x :=
  PathRwQuot.trans_refl_left (A := A) (a := a) (b := a) x

@[simp] theorem comp_id_right (x : LoopQuot A a) :
    comp x id = x :=
  PathRwQuot.trans_refl_right (A := A) (a := a) (b := a) x

@[simp] theorem comp_inv_left (x : LoopQuot A a) :
    comp (inv x) x = id :=
  PathRwQuot.symm_trans (A := A) (a := a) (b := a) x

@[simp] theorem comp_inv_right (x : LoopQuot A a) :
    comp x (inv x) = id :=
  PathRwQuot.trans_symm (A := A) (a := a) (b := a) x

@[simp] theorem inv_id :
    inv (LoopQuot.id (A := A) (a := a)) =
      LoopQuot.id := rfl

@[simp] theorem inv_inv (x : LoopQuot A a) :
    inv (inv x) = x :=
  PathRwQuot.symm_symm (A := A) (x := x)

theorem inv_congr {x y : LoopQuot A a} (h : x = y) :
    inv x = inv y := by
  cases h
  rfl

theorem toEq_ofLoop (p : LoopSpace A a) :
    PathRwQuot.toEq (A := A) (ofLoop (A := A) (a := a) p) =
      (p : Path a a).toEq := rfl

@[simp] theorem toEq (x : LoopQuot A a) :
    PathRwQuot.toEq (A := A) x = rfl := by
  refine Quot.inductionOn x (fun p => ?_)
  cases p with
  | mk steps proof =>
      cases proof
      simp

@[simp] theorem toEq_comp (x y : LoopQuot A a) :
    PathRwQuot.toEq (A := A) (comp x y) =
      (PathRwQuot.toEq (A := A) x).trans
        (PathRwQuot.toEq (A := A) y) :=
  PathRwQuot.toEq_trans (A := A) (x := x) (y := y)

@[simp] theorem toEq_inv (x : LoopQuot A a) :
    PathRwQuot.toEq (A := A) (inv x) =
      (PathRwQuot.toEq (A := A) x).symm :=
  PathRwQuot.toEq_symm (A := A) (x := x)

/-- Iterated loop composition (natural-number exponent). -/
def pow (x : LoopQuot A a) : Nat → LoopQuot A a
  | 0 => id
  | Nat.succ n => comp (pow x n) x

@[simp] theorem pow_zero (x : LoopQuot A a) :
    pow x 0 = id := rfl

@[simp] theorem pow_succ (x : LoopQuot A a) (n : Nat) :
    pow x (Nat.succ n) = comp (pow x n) x := rfl

@[simp] theorem pow_one (x : LoopQuot A a) :
    pow x 1 = x := by
  change comp (pow x 0) x = x
  have hpow0 : pow x 0 = id := rfl
  cases hpow0
  exact LoopQuot.comp_id_left (A := A) (a := a) (x := x)

theorem pow_add (x : LoopQuot A a) (m n : Nat) :
    pow x (m + n) = comp (pow x m) (pow x n) := by
  induction n with
  | zero =>
      have h₁ : pow x (m + 0) = pow x m :=
        _root_.congrArg (fun k => pow x k) (Nat.add_zero m)
      have h₂ : pow x m = comp (pow x m) id :=
        (LoopQuot.comp_id_right (A := A) (a := a)
          (x := pow x m)).symm
      have hpow0 : pow x 0 = id := rfl
      have h₃ : comp (pow x m) id =
          comp (pow x m) (pow x 0) :=
        _root_.congrArg (fun y => comp (pow x m) y) hpow0.symm
      exact h₁.trans (h₂.trans h₃)
  | succ n ih =>
      calc
  pow x (m + n.succ)
      = comp (pow x (m + n)) x := by
    exact (Nat.add_succ m n).symm ▸
      (pow_succ (A := A) (a := a) (x := x) (n := m + n))
  _ = comp (comp (pow x m) (pow x n)) x := by
    exact
      (_root_.congrArg (fun y => comp y x) ih)
  _ = comp (pow x m) (comp (pow x n) x) := by
    exact LoopQuot.comp_assoc (A := A)
      (x := pow x m) (y := pow x n) (z := x)
  _ = comp (pow x m) (pow x n.succ) := by
    exact
      (_root_.congrArg (fun y => comp (pow x m) y)
        (pow_succ (A := A) (a := a) (x := x) (n := n))).symm

/-- Integer exponentiation for loop quotients, extending `pow` by sending
negative exponents to inverses. -/
def zpow (x : LoopQuot A a) : Int → LoopQuot A a
  | Int.ofNat n => pow x n
  | Int.negSucc n => inv (pow x (Nat.succ n))

@[simp] theorem zpow_ofNat (x : LoopQuot A a) (n : Nat) :
    zpow x n = pow x n := rfl

@[simp] theorem zpow_zero (x : LoopQuot A a) :
    zpow x 0 = id :=
  pow_zero (A := A) (a := a) x

@[simp] theorem zpow_one (x : LoopQuot A a) :
    zpow x 1 = x :=
  pow_one (A := A) (a := a) x

@[simp] theorem zpow_negSucc (x : LoopQuot A a) (n : Nat) :
    zpow x (Int.negSucc n) =
      inv (pow x (Nat.succ n)) := rfl

@[simp] theorem zpow_neg_one (x : LoopQuot A a) :
    zpow x (-1) = inv x := by
  have h :=
    zpow_negSucc (A := A) (a := a) (x := x) (n := 0)
  have h' : inv (pow x 1) = inv x :=
    inv_congr (A := A) (a := a)
      (x := pow x 1) (y := x)
      (pow_one (A := A) (a := a) (x := x))
  exact h.trans h'

@[simp] theorem zpow_neg (x : LoopQuot A a) (n : Int) :
    zpow x (-n) = inv (zpow x n) := by
  cases n with
  | ofNat m =>
      cases m with
      | zero =>
          have hz := zpow_zero (A := A) (a := a) (x := x)
          have hid :=
            (LoopQuot.inv_id (A := A) (a := a)).symm
          have hrewrite : LoopQuot.inv LoopQuot.id = inv (zpow x 0) := by
            cases hz
            rfl
          calc
            zpow x 0 = LoopQuot.id := hz
            _ = LoopQuot.inv LoopQuot.id := hid
            _ = inv (zpow x 0) := hrewrite
      | succ k =>
          have hneg : - (Int.ofNat (Nat.succ k)) = Int.negSucc k := rfl
          have hlhs : zpow x (-(Int.ofNat (Nat.succ k))) =
              inv (pow x (Nat.succ k)) := by
            cases hneg
            rfl
          have hzpow : zpow x (Int.ofNat (Nat.succ k)) =
              pow x (Nat.succ k) := rfl
          have hrhs : inv (pow x (Nat.succ k)) =
              inv (zpow x (Int.ofNat (Nat.succ k))) := by
            cases hzpow
            rfl
          exact hlhs.trans hrhs
  | negSucc k =>
      have hneg : - (Int.negSucc k) = Int.ofNat (Nat.succ k) := rfl
      have hlhs : zpow x (- Int.negSucc k) =
          pow x (Nat.succ k) := by
        cases hneg
        rfl
      have hmid : pow x (Nat.succ k) =
          inv (inv (pow x (Nat.succ k))) := by
        exact
          (LoopQuot.inv_inv (A := A) (a := a)
            (x := pow x (Nat.succ k))).symm
      have hrhs : inv (inv (pow x (Nat.succ k))) =
          inv (zpow x (Int.negSucc k)) := rfl
      exact hlhs.trans (hmid.trans hrhs)

end LoopQuot

/-- Strict (definitional) group structure carried by the loop quotient at a
chosen base point.  This records multiplication, identity, and inverses as
concrete operations on `LoopQuot A base`, together with the accompanying laws.
-/
structure LoopGroup (A : Type u) (base : A) where
  /-- Loop composition. -/
  mul : LoopQuot A base → LoopQuot A base → LoopQuot A base
  /-- Identity loop. -/
  one : LoopQuot A base
  /-- Loop inversion. -/
  inv : LoopQuot A base → LoopQuot A base
  /-- Associativity of loop composition. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left identity law. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity law. -/
  mul_one : ∀ x, mul x one = x
  /-- Left inverse law. -/
  mul_left_inv : ∀ x, mul (inv x) x = one
  /-- Right inverse law. -/
  mul_right_inv : ∀ x, mul x (inv x) = one

/-- Canonical loop group supplied by the rewrite quotient operations. -/
@[simp] def loopGroup (A : Type u) (base : A) : LoopGroup A base where
  mul := LoopQuot.comp
  one := LoopQuot.id
  inv := LoopQuot.inv
  mul_assoc := LoopQuot.comp_assoc
  one_mul := LoopQuot.comp_id_left
  mul_one := LoopQuot.comp_id_right
  mul_left_inv := LoopQuot.comp_inv_left
  mul_right_inv := LoopQuot.comp_inv_right

namespace LoopGroup

variable {A : Type u} {a : A}

@[simp] theorem mul_apply (x y : LoopQuot A a) :
    (loopGroup A a).mul x y = LoopQuot.comp x y := rfl

@[simp] theorem one_apply : (loopGroup A a).one = LoopQuot.id := rfl

@[simp] theorem inv_apply (x : LoopQuot A a) :
    (loopGroup A a).inv x = LoopQuot.inv x := rfl

end LoopGroup

end Path
end ComputationalPaths
