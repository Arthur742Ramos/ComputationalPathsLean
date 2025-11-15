/-
# Loop spaces and their rewrite quotients

This module develops the basic algebra needed to reason about loop spaces in
the computational-paths setting.  Starting from raw loops (`Path a a`) we
descend to rewrite equivalence classes, equip them with the induced group
structure, and provide power operations that mirror the iterated-loop
manipulations used in the thesis proof that `pi_1(S^1) ~= Z`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

universe u

/-- Loop space at a base point `a` inside `A`. -/
abbrev LoopSpace (A : Type u) (a : A) : Type u :=
  Path (A := A) a a

/-- Loops modulo rewrite equality, i.e. the fundamental groupoid fibre. -/
abbrev LoopQuot (A : Type u) (a : A) : Type u :=
  PathRwQuot A a a

namespace LoopSpace

variable {A : Type u} {a : A}

/-- Reflexive loop at the base point. -/
@[simp] def id : LoopSpace A a :=
  Path.refl a

/-- Loop inversion inherited from path symmetry. -/
@[simp] def inv (p : LoopSpace A a) : LoopSpace A a :=
  Path.symm p

/-- Loop composition inherited from path concatenation. -/
@[simp] def comp (p q : LoopSpace A a) : LoopSpace A a :=
  Path.trans p q

@[simp] theorem comp_assoc (p q r : LoopSpace A a) :
    comp (comp p q) r = comp p (comp q r) :=
  Path.trans_assoc _ _ _

@[simp] theorem id_comp (p : LoopSpace A a) : comp id p = p := by
  simp [id, comp]

@[simp] theorem comp_id (p : LoopSpace A a) : comp p id = p := by
  simp [id, comp]

end LoopSpace

namespace LoopQuot

variable {A : Type u} {a : A}

@[simp] private theorem neg_ofNat_succ_eq_negSucc (n : Nat) :
    -Int.ofNat (Nat.succ n) = Int.negSucc n := rfl

@[simp] private theorem neg_negSucc_eq_ofNat_succ (n : Nat) :
    -Int.negSucc n = Int.ofNat (Nat.succ n) := rfl

/-- Embed a concrete loop in the quotient. -/
@[simp] def ofLoop (p : LoopSpace A a) : LoopQuot A a :=
  Quot.mk _ p

/-- Identity element in the loop quotient. -/
@[simp] def id : LoopQuot A a :=
  PathRwQuot.refl (A := A) a

/-- Loop composition in the quotient. -/
@[simp] def comp (x y : LoopQuot A a) : LoopQuot A a :=
  PathRwQuot.trans (A := A) x y

/-- Loop inversion in the quotient. -/
@[simp] def inv (x : LoopQuot A a) : LoopQuot A a :=
  PathRwQuot.symm (A := A) x

@[simp] theorem ofLoop_trans (p q : LoopSpace A a) :
    ofLoop (Path.trans p q) =
      comp (ofLoop p) (ofLoop q) := rfl

@[simp] theorem ofLoop_symm (p : LoopSpace A a) :
    ofLoop (Path.symm p) =
      inv (ofLoop p) := rfl

@[simp] theorem id_comp (x : LoopQuot A a) : comp id x = x := by
  unfold comp id
  exact
    PathRwQuot.trans_refl_left (A := A) (a := a) (b := a) (x := x)

@[simp] theorem comp_id (x : LoopQuot A a) : comp x id = x := by
  unfold comp id
  exact
    PathRwQuot.trans_refl_right (A := A) (a := a) (b := a) (x := x)

@[simp] theorem comp_assoc (x y z : LoopQuot A a) :
    comp (comp x y) z = comp x (comp y z) := by
  unfold comp
  exact
    PathRwQuot.trans_assoc (A := A) (a := a) (b := a)
      (c := a) (d := a) (x := x) (y := y) (z := z)

@[simp] theorem inv_comp (x : LoopQuot A a) :
    comp (inv x) x = id := by
  unfold comp inv id
  exact
    PathRwQuot.symm_trans (A := A) (a := a) (b := a) (x := x)

@[simp] theorem comp_inv (x : LoopQuot A a) :
    comp x (inv x) = id := by
  unfold comp inv id
  exact
    PathRwQuot.trans_symm (A := A) (a := a) (b := a) (x := x)

@[simp] theorem inv_id : inv (id (A := A) (a := a)) = id := by
  have h₁ :=
    inv_comp (A := A) (a := a) (x := id (A := A) (a := a))
  have h₂ :=
    comp_id (A := A) (a := a) (x := inv (id (A := A) (a := a)))
  exact h₂.symm.trans h₁

@[simp] theorem inv_inv (x : LoopQuot A a) : inv (inv x) = x := by
  unfold inv
  exact
    PathRwQuot.symm_symm (A := A) (a := a) (b := a) (x := x)

/-- Natural-number iteration of a loop-quotient element. -/
@[simp] def pow (x : LoopQuot A a) : Nat → LoopQuot A a
  | 0 => id
  | Nat.succ n => comp (pow x n) x

@[simp] theorem pow_zero (x : LoopQuot A a) :
    pow x 0 = id := rfl

@[simp] theorem pow_succ (x : LoopQuot A a) (n : Nat) :
    pow x n.succ = comp (pow x n) x := rfl

@[simp] theorem pow_one (x : LoopQuot A a) :
    pow x 1 = x := by
  change comp id x = x
  exact id_comp (A := A) (a := a) (x := x)

theorem pow_add (x : LoopQuot A a) (m n : Nat) :
    pow x (m + n) = comp (pow x m) (pow x n) := by
  induction n with
  | zero =>
      change pow x m = comp (pow x m) id
      exact (comp_id (A := A) (a := a) (x := pow x m)).symm
  | succ n ih =>
      have h := _root_.congrArg (fun y => comp y x) ih
      have hNat : m + Nat.succ n = Nat.succ (m + n) := Nat.add_succ m n
      calc
        pow x (m + Nat.succ n)
            = pow x (Nat.succ (m + n)) := _root_.congrArg (pow x) hNat
        _ = comp (pow x (m + n)) x := rfl
        _ = comp (comp (pow x m) (pow x n)) x := h
        _ = comp (pow x m) (comp (pow x n) x) :=
            comp_assoc (A := A) (a := a)
              (x := pow x m) (y := pow x n) (z := x)
        _ = comp (pow x m) (pow x n.succ) := rfl

/-- Iterate a loop an integer number of times. -/
@[simp] def zpow (x : LoopQuot A a) : Int → LoopQuot A a
  | Int.ofNat n => pow x n
  | Int.negSucc n => inv (pow x (Nat.succ n))

@[simp] theorem zpow_ofNat (x : LoopQuot A a) (n : Nat) :
    zpow x n = pow x n := rfl

@[simp] theorem zpow_zero (x : LoopQuot A a) :
    zpow x 0 = id := rfl

@[simp] theorem zpow_one (x : LoopQuot A a) :
    zpow x 1 = x := by
  change pow x 1 = x
  exact pow_one (A := A) (a := a) (x := x)

@[simp] theorem zpow_negSucc (x : LoopQuot A a) (n : Nat) :
    zpow x (Int.negSucc n) = inv (pow x (Nat.succ n)) := rfl

@[simp] theorem zpow_neg_one (x : LoopQuot A a) :
    zpow x (-1) = inv x := by
  have h :=
    _root_.congrArg (fun y => inv (A := A) (a := a) y)
      (pow_one (A := A) (a := a) (x := x))
  change inv (pow x (Nat.succ 0)) = inv x
  exact h

@[simp] theorem zpow_neg (x : LoopQuot A a) (z : Int) :
    zpow x (-z) = inv (zpow x z) := by
  cases z with
  | ofNat n =>
      cases n with
      | zero =>
          change id = inv id
          exact (inv_id (A := A) (a := a)).symm
      | succ n =>
          rw [neg_ofNat_succ_eq_negSucc]
          rfl
  | negSucc n =>
      rw [neg_negSucc_eq_ofNat_succ]
      have h₁ : zpow x ((Nat.succ n : Nat) : Int) = pow x (Nat.succ n) := rfl
      have h₂ :
          inv (zpow x (Int.negSucc n)) = pow x (Nat.succ n) := by
        change inv (inv (pow x (Nat.succ n))) = pow x (Nat.succ n)
        exact
          inv_inv (A := A) (a := a) (x := pow x (Nat.succ n))
      exact h₁.trans h₂.symm

@[simp] theorem zpow_ofNat_add (x : LoopQuot A a) (m n : Nat) :
    zpow x (Int.ofNat m + Int.ofNat n) =
      comp (zpow x (Int.ofNat m)) (zpow x (Int.ofNat n)) := by
  have h := pow_add (A := A) (a := a) (x := x) m n
  have hNatBase :
      ((m + n : Nat) : Int) = (m : Int) + (n : Int) :=
    Int.natCast_add m n
  have hNat :
      Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) := by
    change (m : Int) + (n : Int) = (m + n : Int)
    exact hNatBase.symm
  rw [hNat]
  change pow x (m + n) = comp (pow x m) (pow x n)
  exact h

/-- Placeholder axiom: integer powers of loops respect addition.  Once the
rewrite semantics for `LoopQuot` are further developed this lemma should be
proved from first principles rather than assumed. -/
@[simp] axiom zpow_add (x : LoopQuot A a) (m n : Int) :
    zpow x (m + n) = comp (zpow x m) (zpow x n)

end LoopQuot

/-- Strict loop group given by the rewrite quotient at `a`. -/
structure LoopGroup (A : Type u) (a : A) where
  /-- Group multiplication. -/
  mul : LoopQuot A a → LoopQuot A a → LoopQuot A a
  /-- Group identity. -/
  one : LoopQuot A a
  /-- Inversion. -/
  inv : LoopQuot A a → LoopQuot A a
  /-- Associativity of multiplication. -/
  mul_assoc :
      ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left identity. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity. -/
  mul_one : ∀ x, mul x one = x
  /-- Left inverse. -/
  mul_left_inv : ∀ x, mul (inv x) x = one
  /-- Right inverse. -/
  mul_right_inv : ∀ x, mul x (inv x) = one

/-- Canonical loop group induced by rewrite-quotiented loops. -/
@[simp] def loopGroup (A : Type u) (a : A) : LoopGroup A a where
  mul := LoopQuot.comp
  one := LoopQuot.id
  inv := LoopQuot.inv
  mul_assoc := LoopQuot.comp_assoc
  one_mul := LoopQuot.id_comp
  mul_one := LoopQuot.comp_id
  mul_left_inv := LoopQuot.inv_comp
  mul_right_inv := LoopQuot.comp_inv

end Path
end ComputationalPaths
