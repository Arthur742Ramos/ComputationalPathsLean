/-
# Semidirect product algebra for the Klein bottle

This module derives algebraic properties of the semidirect product Z semidirect Z used
to encode the Klein bottle fundamental group. We show the group laws,
construct the standard inclusions, and give a splitting lemma.

## Key Results

- `kleinBottleMul_assoc`, `kleinBottleMul_one_left`, `kleinBottleMul_one_right`
- `kleinBottleMul_left_inv`, `kleinBottleMul_right_inv`
- `kleinBottleInlHom`, `kleinBottleInrHom` inclusion homomorphisms
- `kleinBottleSplit` splitting lemma for pairs

## References

- Hatcher, Algebraic Topology, Section 1.3
- de Queiroz et al., "Computational Paths"
-/

import ComputationalPaths.Path.CompPath.KleinBottle
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.IntArith

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra

/-! ## Boolean helpers -/

/-- XOR is commutative on Bool. -/
theorem xor_comm (a b : Bool) : xor a b = xor b a := by
  cases a <;> cases b <;> rfl

/-- XOR cancels on the right. -/
theorem xor_right_cancel (a b : Bool) : xor (xor a b) b = a := by
  cases a <;> cases b <;> rfl

/-- XOR is false exactly when the inputs coincide. -/
theorem xor_eq_false_iff (a b : Bool) : xor a b = false ↔ a = b := by
  cases a <;> cases b <;> rfl

/-! ## Parity lemmas -/

/-- Parity of a natural sum is xor. -/
theorem natParity_add (m n : Nat) :
    natParity (m + n) = xor (natParity m) (natParity n) := by
  induction n with
  | zero =>
      simp [natParity]
  | succ n ih =>
      cases hm : natParity m <;>
        simp [Nat.add_succ, natParity_succ, ih, xor, hm]

/-- Parity of a natural difference when `n ≤ m`. -/
theorem natParity_sub (m n : Nat) (h : n ≤ m) :
    natParity (m - n) = xor (natParity m) (natParity n) := by
  have hsum : natParity m = xor (natParity (m - n)) (natParity n) := by
    have := natParity_add (m - n) n
    simpa [Nat.sub_add_cancel h] using this
  calc
    natParity (m - n)
        = xor (xor (natParity (m - n)) (natParity n)) (natParity n) := by
            simpa using (xor_right_cancel (natParity (m - n)) (natParity n)).symm
    _ = xor (natParity m) (natParity n) := by
            simp [hsum]

/-- Parity for a positive plus a negative integer. -/
theorem kleinBottleParity_add_ofNat_negSucc (m n : Nat) :
    kleinBottleParity (Int.ofNat m + Int.negSucc n) =
      xor (natParity m) (natParity (Nat.succ n)) := by
  cases m with
  | zero =>
      simp [kleinBottleParity, natParity, xor]
  | succ m =>
      cases natTrichotomyDec m n with
      | lt hlt =>
          have hsum := int_ofNat_succ_add_negSucc_lt m n hlt
          have hle : m + 1 ≤ n + 1 := by omega
          have hpar := natParity_sub (n + 1) (m + 1) hle
          have hpar' :
              natParity (n - m) = xor (natParity (n + 1)) (natParity (m + 1)) := by
            simpa [Nat.add_sub_add_right] using hpar
          calc
            kleinBottleParity (Int.ofNat (Nat.succ m) + Int.negSucc n)
                = natParity (n - m) := by
                    simpa [hsum, kleinBottleParity]
            _ = xor (natParity (m + 1)) (natParity (n + 1)) := by
                    simpa [xor_comm] using hpar'
            _ = xor (natParity (Nat.succ m)) (natParity (Nat.succ n)) := by
                    simp
      | eq heq =>
          subst heq
          have hsum := int_ofNat_succ_add_negSucc_self m
          simp [hsum, kleinBottleParity, natParity, xor, natParity_succ]
      | gt hgt =>
          have hsum := int_ofNat_succ_add_negSucc_gt m n hgt
          have hle : n + 1 ≤ m + 1 := by omega
          have hpar := natParity_sub (m + 1) (n + 1) hle
          have hpar' :
              natParity (m - n) = xor (natParity (m + 1)) (natParity (n + 1)) := by
            simpa [Nat.add_sub_add_right] using hpar
          calc
            kleinBottleParity (Int.ofNat (Nat.succ m) + Int.negSucc n)
                = natParity (m - n) := by
                    simpa [hsum, kleinBottleParity]
            _ = xor (natParity (m + 1)) (natParity (n + 1)) := hpar'
            _ = xor (natParity (Nat.succ m)) (natParity (Nat.succ n)) := by
                    simp

/-- Parity of integer addition is xor. -/
theorem kleinBottleParity_add (m n : Int) :
    kleinBottleParity (m + n) = xor (kleinBottleParity m) (kleinBottleParity n) := by
  cases m with
  | ofNat m =>
      cases n with
      | ofNat n =>
          simp [kleinBottleParity, natParity_add]
      | negSucc n =>
          simpa [kleinBottleParity, natParity_succ] using
            (kleinBottleParity_add_ofNat_negSucc m n)
  | negSucc m =>
      cases n with
      | ofNat n =>
          simpa [Int.add_comm, xor_comm] using
            (kleinBottleParity_add_ofNat_negSucc n m)
      | negSucc n =>
          have hsum := int_negSucc_add_negSucc m n
          have hpar := natParity_add (m + 1) (n + 1)
          calc
            kleinBottleParity (Int.negSucc m + Int.negSucc n)
                = natParity (m + n + 2) := by
                    simpa [hsum, kleinBottleParity, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
            _ = xor (natParity (m + 1)) (natParity (n + 1)) := by
                    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hpar
            _ = xor (kleinBottleParity (Int.negSucc m)) (kleinBottleParity (Int.negSucc n)) := by
                    simp [kleinBottleParity]

/-- Parity is invariant under negation. -/
theorem kleinBottleParity_neg (m : Int) :
    kleinBottleParity (-m) = kleinBottleParity m := by
  have hsum := kleinBottleParity_add m (-m)
  have hxor : xor (kleinBottleParity m) (kleinBottleParity (-m)) = false := by
    simpa [Int.add_right_neg, kleinBottleParity, natParity] using hsum
  exact (xor_eq_false_iff (kleinBottleParity m) (kleinBottleParity (-m))).1 hxor

/-! ## Action lemmas -/

/-- The Klein bottle action distributes over addition. -/
theorem kleinBottleAct_add (m n n' : Int) :
    kleinBottleAct m (n + n') = kleinBottleAct m n + kleinBottleAct m n' := by
  by_cases h : kleinBottleParity m <;>
    simp [kleinBottleAct, h, Int.neg_add, Int.add_assoc, Int.add_left_comm, Int.add_comm]

/-- Acting on a negated element negates the result. -/
theorem kleinBottleAct_neg (m n : Int) :
    kleinBottleAct m (-n) = -kleinBottleAct m n := by
  by_cases h : kleinBottleParity m <;> simp [kleinBottleAct, h]

/-- The action is involutive. -/
theorem kleinBottleAct_involutive (m n : Int) :
    kleinBottleAct m (kleinBottleAct m n) = n := by
  by_cases h : kleinBottleParity m <;> simp [kleinBottleAct, h]

/-- The action depends only on parity (negation leaves it unchanged). -/
theorem kleinBottleAct_neg_arg (m n : Int) :
    kleinBottleAct (-m) n = kleinBottleAct m n := by
  have hpar := kleinBottleParity_neg m
  by_cases h : kleinBottleParity m <;>
    simp [kleinBottleAct, h, hpar]

/-- Action composition: act n ∘ act m = act (m + n). -/
theorem kleinBottleAct_comp (m n k : Int) :
    kleinBottleAct n (kleinBottleAct m k) = kleinBottleAct (m + n) k := by
  by_cases hm : kleinBottleParity m <;>
    by_cases hn : kleinBottleParity n <;>
    simp [kleinBottleAct, hm, hn, kleinBottleParity_add, xor, xor_comm]

/-! ## Semidirect product group laws -/

/-- Identity element for the Klein bottle semidirect product. -/
@[simp] def kleinBottleOne : Int × Int := (0, 0)

/-- Associativity of `kleinBottleMul`. -/
theorem kleinBottleMul_assoc (x y z : Int × Int) :
    kleinBottleMul (kleinBottleMul x y) z = kleinBottleMul x (kleinBottleMul y z) := by
  cases x with
  | mk m n =>
      cases y with
      | mk m' n' =>
          cases z with
          | mk m'' n'' =>
              ext <;>
                simp [kleinBottleMul, kleinBottleAct_add, kleinBottleAct_comp,
                  Int.add_assoc, Int.add_left_comm, Int.add_comm]

/-- Left identity for `kleinBottleMul`. -/
theorem kleinBottleMul_one_left (x : Int × Int) :
    kleinBottleMul kleinBottleOne x = x := by
  cases x with
  | mk m n =>
      simp [kleinBottleMul, kleinBottleOne, kleinBottleAct_zero, Int.zero_add]

/-- Right identity for `kleinBottleMul`. -/
theorem kleinBottleMul_one_right (x : Int × Int) :
    kleinBottleMul x kleinBottleOne = x := by
  cases x with
  | mk m n =>
      simp [kleinBottleMul, kleinBottleOne, kleinBottleAct_zero_exp, Int.add_zero]

/-- Left inverse for `kleinBottleInv`. -/
theorem kleinBottleMul_left_inv (x : Int × Int) :
    kleinBottleMul (kleinBottleInv x) x = kleinBottleOne := by
  cases x with
  | mk m n =>
      simp [kleinBottleMul, kleinBottleInv, kleinBottleOne, kleinBottleAct_neg,
        kleinBottleAct_involutive, Int.add_left_neg, Int.add_right_neg, Int.add_assoc]

/-- Right inverse for `kleinBottleInv`. -/
theorem kleinBottleMul_right_inv (x : Int × Int) :
    kleinBottleMul x (kleinBottleInv x) = kleinBottleOne := by
  cases x with
  | mk m n =>
      simp [kleinBottleMul, kleinBottleInv, kleinBottleOne, kleinBottleAct_neg_arg,
        Int.add_right_neg, Int.add_left_neg, Int.add_assoc, Int.add_comm, Int.add_left_comm]

/-- The strict group structure on the Klein bottle semidirect product. -/
def kleinBottleStrictGroup : StrictGroup (Int × Int) where
  mul := kleinBottleMul
  one := kleinBottleOne
  mul_assoc := kleinBottleMul_assoc
  one_mul := kleinBottleMul_one_left
  mul_one := kleinBottleMul_one_right
  inv := kleinBottleInv
  mul_left_inv := kleinBottleMul_left_inv
  mul_right_inv := kleinBottleMul_right_inv

/-! ## Inclusion homomorphisms -/

/-- Additive strict group structure on integers. -/
def intStrictGroup : StrictGroup Int where
  mul := (· + ·)
  one := 0
  mul_assoc := by intro x y z; exact Int.add_assoc x y z
  one_mul := by intro x; exact Int.zero_add x
  mul_one := by intro x; exact Int.add_zero x
  inv := Int.neg
  mul_left_inv := by intro x; exact Int.add_left_neg x
  mul_right_inv := by intro x; exact Int.add_right_neg x

/-- Inclusion of the first factor. -/
@[simp] def kleinBottleInl (m : Int) : Int × Int := (m, 0)

/-- Inclusion of the second factor. -/
@[simp] def kleinBottleInr (n : Int) : Int × Int := (0, n)

/-- Inclusion of the first factor as a group homomorphism. -/
def kleinBottleInlHom :
    GroupHom Int (Int × Int) intStrictGroup kleinBottleStrictGroup where
  toMonoidHom :=
    { toFun := kleinBottleInl
      map_mul := by
        intro x y
        simp [kleinBottleMul, kleinBottleInl, kleinBottleAct_zero]
      map_one := by
        simp [kleinBottleInl, kleinBottleOne] }
  map_inv := by
    intro x
    simp [kleinBottleInl, kleinBottleInv, kleinBottleAct_zero]

/-- Inclusion of the second factor as a group homomorphism. -/
def kleinBottleInrHom :
    GroupHom Int (Int × Int) intStrictGroup kleinBottleStrictGroup where
  toMonoidHom :=
    { toFun := kleinBottleInr
      map_mul := by
        intro x y
        simp [kleinBottleMul, kleinBottleInr, kleinBottleAct_zero_exp]
      map_one := by
        simp [kleinBottleInr, kleinBottleOne] }
  map_inv := by
    intro x
    simp [kleinBottleInr, kleinBottleInv, kleinBottleAct_zero_exp]

/-! ## Splitting lemmas -/

/-- Projection onto the first factor as a group homomorphism. -/
def kleinBottleProjHom :
    GroupHom (Int × Int) Int kleinBottleStrictGroup intStrictGroup where
  toMonoidHom :=
    { toFun := fun x => x.1
      map_mul := by
        intro x y
        cases x with
        | mk m n =>
            cases y with
            | mk m' n' =>
                rfl
      map_one := by
        rfl }
  map_inv := by
    intro x
    simp [kleinBottleInv]

/-- Splitting lemma: any pair is the product of the inclusions. -/
theorem kleinBottleSplit (m n : Int) :
    kleinBottleMul (kleinBottleInl m) (kleinBottleInr n) = (m, n) := by
  simp [kleinBottleMul, kleinBottleInl, kleinBottleInr, kleinBottleAct_zero_exp]

/-- The projection is a left inverse of the first inclusion. -/
theorem kleinBottleProj_inl (m : Int) :
    kleinBottleProjHom (kleinBottleInl m) = m := rfl

end CompPath
end Path
end ComputationalPaths
