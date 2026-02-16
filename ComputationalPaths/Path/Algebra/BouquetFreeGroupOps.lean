/-
# Bouquet Free Group Operations

This module packages additional algebraic structure for the bouquet free group
constructed in `CompPath/BouquetN.lean`.  We record word-level operations and
lift them to the quotient, providing a strict monoid structure together with
power operations and inversion identities.

## Key results

- Word concatenation and inverse lemmas
- Strict monoid structure on `BouquetFreeGroup n`
- Power laws on `BouquetFreeGroup n`
- Inversion as an anti-automorphism on the monoid
-/

import ComputationalPaths.Path.CompPath.BouquetN
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace Algebra

open BouquetWord

universe u

/-! ## Word operations -/

namespace BouquetWord

variable {n : Nat}

/-- Left identity for word concatenation. -/
@[simp] theorem wordConcat_nil_left (w : BouquetWord n) :
    wordConcat .nil w = w := rfl

/-- Right identity for word concatenation. -/
@[simp] theorem wordConcat_nil_right (w : BouquetWord n) :
    wordConcat w .nil = w := by
  induction w with
  | nil => rfl
  | cons l rest ih =>
      simp only [wordConcat, ih]

/-- Associativity of word concatenation. -/
@[simp] theorem wordConcat_assoc (w₁ w₂ w₃ : BouquetWord n) :
    wordConcat (wordConcat w₁ w₂) w₃ =
      wordConcat w₁ (wordConcat w₂ w₃) := by
  induction w₁ with
  | nil => rfl
  | cons l rest ih =>
      simp only [wordConcat, ih]

/-- Length of a concatenated word. -/
@[simp] theorem length_wordConcat (w₁ w₂ : BouquetWord n) :
    (wordConcat w₁ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil => exact (Nat.zero_add _).symm
  | cons l rest ih =>
      show 1 + (wordConcat rest w₂).length = 1 + rest.length + w₂.length
      rw [ih, Nat.add_assoc]

/-- Length of an inverse word equals the length of the word. -/
@[simp] theorem length_inverse (w : BouquetWord n) :
    (inverse w).length = w.length := by
  induction w with
  | nil => rfl
  | cons l rest ih =>
    show (wordConcat (inverse rest) _).length = 1 + rest.length
    rw [length_wordConcat, ih]
    show rest.length + (1 + 0) = 1 + rest.length
    omega

/-- Inverse of the empty word. -/
@[simp] theorem inverse_nil : inverse (n := n) .nil = .nil := rfl

/-- Inverse of a singleton word. -/
@[simp] theorem inverse_singleton (l : BouquetLetter n) :
    inverse (BouquetWord.cons l .nil) =
      BouquetWord.cons
        ⟨l.gen, -l.power, fun h => l.power_ne_zero (Int.neg_eq_zero.mp h)⟩
        .nil := by
  simp [inverse]

/-- Inverse respects word concatenation. -/
@[simp] theorem inverse_wordConcat (w₁ w₂ : BouquetWord n) :
    inverse (wordConcat w₁ w₂) =
      wordConcat (inverse w₂) (inverse w₁) := by
  induction w₁ with
  | nil =>
      simp [wordConcat]
  | cons l rest ih =>
      simp [wordConcat, inverse, wordConcat_assoc, ih]

/-- Inverse is involutive on words. -/
@[simp] theorem inverse_inverse (w : BouquetWord n) :
    inverse (inverse w) = w := by
  induction w with
  | nil => rfl
  | cons l rest ih =>
      cases l with
      | mk gen power power_ne_zero =>
          simp [inverse, inverse_wordConcat, ih, wordConcat]

/-- Word exponentiation by natural numbers. -/
@[simp] def wordPow (w : BouquetWord n) : Nat → BouquetWord n
  | 0 => .nil
  | Nat.succ k => wordConcat (wordPow w k) w

/-- Zero power gives the empty word. -/
@[simp] theorem wordPow_zero (w : BouquetWord n) : wordPow w 0 = .nil := rfl

/-- Successor power appends one copy. -/
@[simp] theorem wordPow_succ (w : BouquetWord n) (k : Nat) :
    wordPow w (Nat.succ k) = wordConcat (wordPow w k) w := rfl

/-- One power is the word itself. -/
@[simp] theorem wordPow_one (w : BouquetWord n) : wordPow w 1 = w := by
  simp [wordPow, wordConcat_nil_left]

/-- Word powers respect addition. -/
@[simp] theorem wordPow_add (w : BouquetWord n) (m n : Nat) :
    wordPow w (m + n) = wordConcat (wordPow w m) (wordPow w n) := by
  induction n with
  | zero =>
      simp [wordPow, wordConcat_nil_right]
  | succ n ih =>
      simp [wordPow, wordConcat_assoc, ih]

/-- Left successor law for word powers. -/
@[simp] theorem wordPow_succ_left (w : BouquetWord n) (k : Nat) :
    wordConcat w (wordPow w k) = wordPow w (Nat.succ k) := by
  -- Use wordPow_add with m=1 and wordPow_one.
  have h := (wordPow_add w 1 k)
  simpa [wordPow_one, Nat.add_comm] using h.symm

/-- Word power of the empty word is empty. -/
@[simp] theorem wordPow_nil (k : Nat) : wordPow (.nil : BouquetWord n) k = .nil := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp [wordPow, ih]

/-- Inverse of a word power. -/
@[simp] theorem inverse_wordPow (w : BouquetWord n) (k : Nat) :
    inverse (wordPow w k) = wordPow (inverse w) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      calc
        inverse (wordPow w (Nat.succ k))
            = wordConcat (inverse w) (inverse (wordPow w k)) := by
                simp [wordPow, inverse_wordConcat]
        _ = wordConcat (inverse w) (wordPow (inverse w) k) := by
                simp [ih]
        _ = wordPow (inverse w) (Nat.succ k) := by
                simp

end BouquetWord

/-! ## Quotient-level structure -/

namespace BouquetFreeGroup

variable {n : Nat}

/-- Multiplication on representatives. -/
@[simp] theorem mul_mk (w₁ w₂ : BouquetWord n) :
    BouquetFreeGroup.mul (Quot.mk _ w₁) (Quot.mk _ w₂) =
      Quot.mk _ (BouquetWord.wordConcat w₁ w₂) := rfl

/-- Inversion on representatives. -/
@[simp] theorem inv_mk (w : BouquetWord n) :
    BouquetFreeGroup.inv (Quot.mk _ w) =
      Quot.mk _ (BouquetWord.inverse w) := rfl

/-- Associativity of multiplication. -/
@[simp] theorem mul_assoc (x y z : BouquetFreeGroup n) :
    BouquetFreeGroup.mul (BouquetFreeGroup.mul x y) z =
      BouquetFreeGroup.mul x (BouquetFreeGroup.mul y z) := by
  induction x using Quot.ind with
  | _ w₁ =>
      induction y using Quot.ind with
      | _ w₂ =>
          induction z using Quot.ind with
          | _ w₃ =>
              simp [BouquetFreeGroup.mul, BouquetWord.wordConcat_assoc]

/-- Left identity for multiplication. -/
@[simp] theorem one_mul (x : BouquetFreeGroup n) :
    BouquetFreeGroup.mul (BouquetFreeGroup.one (n := n)) x = x := by
  induction x using Quot.ind with
  | _ w =>
      simp [BouquetFreeGroup.mul, BouquetFreeGroup.one, BouquetWord.wordConcat_nil_left]

/-- Right identity for multiplication. -/
@[simp] theorem mul_one (x : BouquetFreeGroup n) :
    BouquetFreeGroup.mul x (BouquetFreeGroup.one (n := n)) = x := by
  induction x using Quot.ind with
  | _ w =>
      simp [BouquetFreeGroup.mul, BouquetFreeGroup.one, BouquetWord.wordConcat_nil_right]

/-- Inversion is involutive. -/
@[simp] theorem inv_inv (x : BouquetFreeGroup n) :
    BouquetFreeGroup.inv (BouquetFreeGroup.inv x) = x := by
  induction x using Quot.ind with
  | _ w =>
      simp [BouquetFreeGroup.inv, BouquetWord.inverse_inverse]

/-- Inversion preserves the identity element. -/
@[simp] theorem inv_one :
    BouquetFreeGroup.inv (BouquetFreeGroup.one (n := n)) =
      BouquetFreeGroup.one := by
  simp [BouquetFreeGroup.one, BouquetFreeGroup.inv]

/-- Inversion reverses multiplication. -/
@[simp] theorem inv_mul (x y : BouquetFreeGroup n) :
    BouquetFreeGroup.inv (BouquetFreeGroup.mul x y) =
      BouquetFreeGroup.mul (BouquetFreeGroup.inv y) (BouquetFreeGroup.inv x) := by
  induction x using Quot.ind with
  | _ w₁ =>
      induction y using Quot.ind with
      | _ w₂ =>
          simp [BouquetFreeGroup.mul, BouquetFreeGroup.inv, BouquetWord.inverse_wordConcat]

/-- Strict monoid structure on `BouquetFreeGroup`. -/
@[simp] noncomputable def strictMonoid (n : Nat) : StrictMonoid (BouquetFreeGroup n) where
  mul := BouquetFreeGroup.mul
  one := BouquetFreeGroup.one (n := n)
  mul_assoc := by intro x y z; exact mul_assoc (x := x) (y := y) (z := z)
  one_mul := by intro x; exact one_mul (x := x)
  mul_one := by intro x; exact mul_one (x := x)

/-- Natural power in the bouquet free group. -/
@[simp] noncomputable def pow (x : BouquetFreeGroup n) : Nat → BouquetFreeGroup n :=
  StrictMonoid.pow (S := strictMonoid n) x

/-- Zero power is the identity. -/
@[simp] theorem pow_zero (x : BouquetFreeGroup n) :
    pow (n := n) x 0 = BouquetFreeGroup.one := rfl

/-- Successor power multiplies once more. -/
@[simp] theorem pow_succ (x : BouquetFreeGroup n) (k : Nat) :
    pow (n := n) x (Nat.succ k) =
      BouquetFreeGroup.mul (pow (n := n) x k) x := rfl

/-- Power one is the element itself. -/
@[simp] theorem pow_one (x : BouquetFreeGroup n) :
    pow (n := n) x 1 = x := by
  simp [pow, strictMonoid]

/-- Power distributes over addition. -/
@[simp] theorem pow_add (x : BouquetFreeGroup n) (m k : Nat) :
    pow (n := n) x (m + k) =
      BouquetFreeGroup.mul (pow (n := n) x m) (pow (n := n) x k) := by
  simpa [pow, strictMonoid] using
    StrictMonoid.pow_add (S := strictMonoid n) (x := x) (m := m) (n := k)

-- pow_one_elem removed: unstable for non-reduced representatives.

-- inv_pow removed: power inversion needs group-level commuting lemmas.

/-! ### End of power lemmas -/
end BouquetFreeGroup

end Algebra
end Path
end ComputationalPaths
