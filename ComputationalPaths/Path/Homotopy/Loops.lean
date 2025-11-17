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

/-!
Support lemmas: cancellation and inverse-of-composition.
These are used to derive exponent arithmetic from
the strict group laws on `LoopQuot`.
-/

@[simp] theorem comp_right_cancel {x y z : LoopQuot A a}
    (h : comp x z = comp y z) : x = y := by
  -- compose both sides on the right by inv z
  have h' := _root_.congrArg (fun t => comp t (inv (A := A) (a := a) z)) h
  -- associativity rearrangements
  have hx : comp (comp x z) (inv z) = comp x (comp z (inv z)) :=
    comp_assoc (A := A) (a := a) (x := x) (y := z) (z := inv z)
  have hy : comp (comp y z) (inv z) = comp y (comp z (inv z)) :=
    comp_assoc (A := A) (a := a) (x := y) (y := z) (z := inv z)
  -- cancel z ⋅ z⁻¹ on the right
  have hz : comp z (inv z) = id := comp_inv (A := A) (a := a) (x := z)
  have hx' : comp (comp x z) (inv z) = comp x id := by
    exact Eq.trans hx (by rw [hz])
  have hy' : comp (comp y z) (inv z) = comp y id := by
    exact Eq.trans hy (by rw [hz])
  -- rewrite both sides and conclude with right identity
  have h'' : comp x id = comp y id := by
    exact (Eq.trans (Eq.symm hx') (Eq.trans h' hy'))
  have hxid : comp x id = x := comp_id (A := A) (a := a) (x := x)
  have hyid : comp y id = y := comp_id (A := A) (a := a) (x := y)
  exact (Eq.trans (Eq.trans (Eq.symm hxid) h'') hyid)

@[simp] theorem comp_left_cancel {x y z : LoopQuot A a}
    (h : comp x y = comp x z) : y = z := by
  -- compose both sides on the left by inv x
  have h' := _root_.congrArg (fun t => comp (inv (A := A) (a := a) x) t) h
  -- associativity rearrangements
  have hx : comp (inv x) (comp x y) = comp (comp (inv x) x) y :=
    (comp_assoc (A := A) (a := a) (x := inv x) (y := x) (z := y)).symm
  have hz' : comp (inv x) (comp x z) = comp (comp (inv x) x) z :=
    (comp_assoc (A := A) (a := a) (x := inv x) (y := x) (z := z)).symm
  -- cancel x⁻¹ ⋅ x on the left
  have hxinv : comp (inv x) x = id := inv_comp (A := A) (a := a) (x := x)
  have hx'' : comp (inv x) (comp x y) = comp id y := by
    exact Eq.trans hx (by rw [hxinv])
  have hz'' : comp (inv x) (comp x z) = comp id z := by
    exact Eq.trans hz' (by rw [hxinv])
  -- rewrite both sides and conclude with left identity
  have h'' : comp id y = comp id z := by
    exact (Eq.trans (Eq.symm hx'') (Eq.trans h' hz''))
  have hidy : comp id y = y := id_comp (A := A) (a := a) (x := y)
  have hidz : comp id z = z := id_comp (A := A) (a := a) (x := z)
  exact (Eq.trans (Eq.trans (Eq.symm hidy) h'') hidz)

@[simp] theorem inv_comp_rev (x y : LoopQuot A a) :
    inv (comp x y) = comp (inv y) (inv x) := by
  -- Both sides are right-inverses of `comp x y`, hence equal by right cancel.
  have hL : comp (inv (comp x y)) (comp x y) = id :=
    inv_comp (A := A) (a := a) (x := comp x y)
  have hR : comp (comp (inv y) (inv x)) (comp x y) = id := by
    -- associate to ((inv y) ∘ ((inv x) ∘ (x ∘ y))) and cancel
    have h1 : comp (comp (inv y) (inv x)) (comp x y)
            = comp (inv y) (comp (inv x) (comp x y)) :=
      comp_assoc (A := A) (a := a)
        (x := inv y) (y := inv x) (z := comp x y)
    have h2 : comp (inv x) (comp x y)
            = comp (comp (inv x) x) y :=
      (comp_assoc (A := A) (a := a) (x := inv x) (y := x) (z := y)).symm
    have h2' := _root_.congrArg (fun t => comp (A := A) (a := a) (inv y) t) h2
    have h3 : comp (comp (inv x) x) y = comp id y :=
      _root_.congrArg (fun t => comp (A := A) (a := a) t y)
        (inv_comp (A := A) (a := a) (x := x))
    have h3' := _root_.congrArg (fun t => comp (A := A) (a := a) (inv y) t) h3
    have h4 : comp (inv y) (comp id y) = comp (inv y) y :=
      _root_.congrArg (fun t => comp (A := A) (a := a) (inv y) t)
        (id_comp (A := A) (a := a) (x := y))
    have h5 : comp (inv y) y = id :=
      inv_comp (A := A) (a := a) (x := y)
    exact
      (Eq.trans h1 (Eq.trans h2' (Eq.trans h3' (Eq.trans h4 h5))))
  exact comp_right_cancel (A := A) (a := a) (x := inv (comp x y))
    (y := comp (inv y) (inv x)) (z := comp x y) (h := hL.trans hR.symm)

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


end LoopQuot

/-- Strict loop monoid given by the rewrite quotient at `a`. -/
structure LoopMonoid (A : Type u) (a : A) where
  /-- Multiplication induced by loop composition. -/
  mul : LoopQuot A a → LoopQuot A a → LoopQuot A a
  /-- Monoid identity (reflexive loop). -/
  one : LoopQuot A a
  /-- Associativity of multiplication. -/
  mul_assoc :
      ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Left identity law. -/
  one_mul : ∀ x, mul one x = x
  /-- Right identity law. -/
  mul_one : ∀ x, mul x one = x

/-- Canonical loop monoid induced by rewrite-quotiented loops. -/
@[simp] def loopMonoid (A : Type u) (a : A) : LoopMonoid A a where
  mul := LoopQuot.comp
  one := LoopQuot.id
  mul_assoc := LoopQuot.comp_assoc
  one_mul := LoopQuot.id_comp
  mul_one := LoopQuot.comp_id

/-- Strict loop group given by the rewrite quotient at `a`. -/
structure LoopGroup (A : Type u) (a : A) extends LoopMonoid A a where
  /-- Inversion induced by loop symmetry. -/
  inv : LoopQuot A a → LoopQuot A a
  /-- Left inverse. -/
  mul_left_inv : ∀ x, mul (inv x) x = one
  /-- Right inverse. -/
  mul_right_inv : ∀ x, mul x (inv x) = one

/-- Canonical loop group induced by rewrite-quotiented loops. -/
@[simp] def loopGroup (A : Type u) (a : A) : LoopGroup A a where
  toLoopMonoid := loopMonoid A a
  inv := LoopQuot.inv
  mul_left_inv := LoopQuot.inv_comp
  mul_right_inv := LoopQuot.comp_inv

end Path
end ComputationalPaths
