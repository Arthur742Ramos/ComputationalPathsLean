/-
# Integer Arithmetic Helpers for Path Proofs

This module provides helper lemmas and tactics for integer arithmetic that
commonly arises in fundamental group calculations. When working with integer
powers of loops (l^n for n : Int), we frequently need to prove equalities
about Int.ofNat and Int.negSucc that omega doesn't handle directly.

## Key Lemmas

- Zero/identity lemmas for Int.ofNat
- Case analysis helpers for mixed sign addition
- Trichotomy helpers for natural number comparison

## Usage

Import this module when proving properties about integer powers of loops.
-/

namespace ComputationalPaths
namespace Path

/-! ## Int.ofNat Lemmas -/

@[simp] theorem int_ofNat_zero : Int.ofNat 0 = (0 : Int) := rfl

@[simp] theorem int_ofNat_one : Int.ofNat 1 = (1 : Int) := rfl

theorem int_ofNat_zero_add (n : Int) : Int.ofNat 0 + n = n := Int.zero_add n

theorem int_ofNat_add_zero (n : Int) : n + Int.ofNat 0 = n := Int.add_zero n

theorem int_negSucc_add_zero (n : Nat) : Int.negSucc n + Int.ofNat 0 = Int.negSucc n :=
  Int.add_zero _

theorem int_zero_add_negSucc (n : Nat) : Int.ofNat 0 + Int.negSucc n = Int.negSucc n :=
  Int.zero_add _

/-! ## Int.negSucc Basic Lemmas -/

@[simp] theorem int_negSucc_zero : Int.negSucc 0 = -1 := rfl

theorem int_negSucc_eq' (n : Nat) : Int.negSucc n = -↑(n + 1) := by
  rfl

/-! ## Mixed Sign Addition - Equality Case -/

/-- When m = n: (m+1) + (-(n+1)) = 0 -/
theorem int_ofNat_succ_add_negSucc_self (m : Nat) :
    Int.ofNat (m + 1) + Int.negSucc m = 0 := by
  simp only [Int.ofNat_eq_coe, Int.negSucc_eq]
  omega

/-- Symmetric: (-(m+1)) + (m+1) = 0 -/
theorem int_negSucc_add_ofNat_succ_self (m : Nat) :
    Int.negSucc m + Int.ofNat (m + 1) = 0 := by
  simp only [Int.ofNat_eq_coe, Int.negSucc_eq]
  omega

/-! ## Mixed Sign Addition - Greater Than Case -/

/-- When m > n: (m+1) + (-(n+1)) = m - n (positive result) -/
theorem int_ofNat_succ_add_negSucc_gt (m n : Nat) (h : m > n) :
    Int.ofNat (m + 1) + Int.negSucc n = Int.ofNat (m - n) := by
  simp only [Int.ofNat_eq_coe, Int.negSucc_eq]
  omega

/-- Symmetric: (-(n+1)) + (m+1) = m - n when m > n -/
theorem int_negSucc_add_ofNat_succ_lt (m n : Nat) (h : m < n) :
    Int.negSucc m + Int.ofNat (n + 1) = Int.ofNat (n - m) := by
  simp only [Int.ofNat_eq_coe, Int.negSucc_eq]
  omega

/-! ## Mixed Sign Addition - Less Than Case -/

/-- When m < n: (m+1) + (-(n+1)) = -(n - m) (negative result) -/
theorem int_ofNat_succ_add_negSucc_lt (m n : Nat) (h : m < n) :
    Int.ofNat (m + 1) + Int.negSucc n = Int.negSucc (n - m - 1) := by
  simp only [Int.ofNat_eq_coe, Int.negSucc_eq]
  omega

/-- Symmetric: (-(m+1)) + (n+1) = -(m - n) when m > n -/
theorem int_negSucc_add_ofNat_succ_gt (m n : Nat) (h : m > n) :
    Int.negSucc m + Int.ofNat (n + 1) = Int.negSucc (m - n - 1) := by
  simp only [Int.ofNat_eq_coe, Int.negSucc_eq]
  omega

/-! ## Both Negative -/

theorem int_negSucc_add_negSucc (m n : Nat) :
    Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := by
  simp only [Int.negSucc_eq]
  omega

/-! ## Both Positive -/

theorem int_ofNat_succ_add_ofNat_succ (m n : Nat) :
    Int.ofNat (m + 1) + Int.ofNat (n + 1) = Int.ofNat (m + n + 2) := by
  simp only [Int.ofNat_eq_coe]
  omega

/-! ## Trichotomy Helper -/

/-- Helper structure for trichotomy results -/
inductive NatTrichotomy (m n : Nat) where
  | lt : m < n → NatTrichotomy m n
  | eq : m = n → NatTrichotomy m n
  | gt : m > n → NatTrichotomy m n

/-- Decide the trichotomy of two natural numbers -/
def natTrichotomyDec (m n : Nat) : NatTrichotomy m n :=
  if h : m < n then NatTrichotomy.lt h
  else if h : m = n then NatTrichotomy.eq h
  else NatTrichotomy.gt (by omega)

/-! ## Conversion Lemmas -/

/-- Convert Int equality to a form suitable for omega -/
theorem int_eq_iff_sub_eq_zero (a b : Int) : a = b ↔ a - b = 0 := by
  constructor
  · intro h; simp [h]
  · intro h; omega

/-! ## Summary

This module provides arithmetic lemmas for Int operations commonly needed
in fundamental group calculations:

1. **Zero lemmas**: `int_ofNat_zero_add`, `int_ofNat_add_zero`
2. **Equality case**: `int_ofNat_succ_add_negSucc_self`
3. **Greater than case**: `int_ofNat_succ_add_negSucc_gt`
4. **Less than case**: `int_ofNat_succ_add_negSucc_lt`
5. **Both same sign**: `int_negSucc_add_negSucc`, `int_ofNat_succ_add_ofNat_succ`
6. **Trichotomy helper**: `natTrichotomyDec`

These lemmas help with proofs that case split on integer signs and compute
the resulting integer sum.
-/

end Path
end ComputationalPaths
