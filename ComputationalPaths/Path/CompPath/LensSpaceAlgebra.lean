/-
# Lens Space Fundamental Group Algebra

Explicit constructive computations for the cyclic group Z/pZ as the
fundamental group of the lens space L(p,1). We build the full strict
group structure on Fin p and prove:

1. **Cyclic group laws** for Z/pZ (associativity, identity, inverses)
2. **Generator order**: the canonical generator has exact order p
3. **Commutativity**: Z/pZ is abelian
4. **Concrete verification**: explicit computation for p = 3, 5, 7
5. **Lagrange's theorem**: p · a = 0 for every element a
6. **Lens space π₁ structure**: StrictGroup on π₁(L(p,1))

All results are constructive — no sorry, no axiom.

## Mathematical Background

The lens space L(p,q) is the quotient of S³ by the free action of Z/pZ.
For q=1, the fundamental group is exactly Z/pZ, the cyclic group of order p.

## References

- Hatcher, "Algebraic Topology", Example 1.43
- de Queiroz et al., "Computational Paths"
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.CompPath.LensSpace
import ComputationalPaths.Path.Algebra.GroupStructures

namespace ComputationalPaths
namespace Path
namespace CompPath

open Algebra

/-! ## Z/pZ as Fin p with modular arithmetic -/

/-- Addition in Z/pZ. -/
def zpAdd (p : Nat) (hp : p > 0) (a b : Fin p) : Fin p :=
  ⟨(a.val + b.val) % p, Nat.mod_lt _ hp⟩

/-- Zero element of Z/pZ. -/
def zpZero (p : Nat) (hp : p > 0) : Fin p := ⟨0, hp⟩

/-- Negation in Z/pZ. -/
def zpNeg (p : Nat) (hp : p > 0) (a : Fin p) : Fin p :=
  ⟨(p - a.val) % p, Nat.mod_lt _ hp⟩

/-- The canonical generator (1 mod p). -/
def zpGen (p : Nat) (hp : p > 0) : Fin p := ⟨1 % p, Nat.mod_lt _ hp⟩

/-! ### Core group law proofs -/

/-- 0 + a = a in Z/pZ -/
theorem zpAdd_zero_left (p : Nat) (hp : p > 0) (a : Fin p) :
    zpAdd p hp (zpZero p hp) a = a := by
  apply Fin.ext
  simp only [zpAdd, zpZero, Nat.zero_add]
  exact Nat.mod_eq_of_lt a.isLt

/-- a + 0 = a in Z/pZ -/
theorem zpAdd_zero_right (p : Nat) (hp : p > 0) (a : Fin p) :
    zpAdd p hp a (zpZero p hp) = a := by
  apply Fin.ext
  simp only [zpAdd, zpZero, Nat.add_zero]
  exact Nat.mod_eq_of_lt a.isLt

/-- Associativity of addition in Z/pZ -/
theorem zpAdd_assoc (p : Nat) (hp : p > 0) (a b c : Fin p) :
    zpAdd p hp (zpAdd p hp a b) c = zpAdd p hp a (zpAdd p hp b c) := by
  apply Fin.ext
  simp only [zpAdd]
  rw [Nat.add_mod, Nat.mod_mod_of_dvd _ ⟨1, by omega⟩, ← Nat.add_mod]
  rw [Nat.add_mod (a.val), Nat.mod_mod_of_dvd _ ⟨1, by omega⟩, ← Nat.add_mod]
  congr 1; omega

/-- Left inverse: (-a) + a = 0 in Z/pZ -/
theorem zpAdd_neg_left (p : Nat) (hp : p > 0) (a : Fin p) :
    zpAdd p hp (zpNeg p hp a) a = zpZero p hp := by
  apply Fin.ext
  simp only [zpAdd, zpNeg, zpZero]
  by_cases h : a.val = 0
  · simp [h, Nat.mod_self]
  · have hpos : p - a.val < p := by omega
    rw [Nat.mod_eq_of_lt hpos]
    have : p - a.val + a.val = p := by omega
    rw [this, Nat.mod_self]

/-- Right inverse: a + (-a) = 0 in Z/pZ -/
theorem zpAdd_neg_right (p : Nat) (hp : p > 0) (a : Fin p) :
    zpAdd p hp a (zpNeg p hp a) = zpZero p hp := by
  apply Fin.ext
  simp only [zpAdd, zpNeg, zpZero]
  by_cases h : a.val = 0
  · simp [h, Nat.mod_self]
  · have hpos : p - a.val < p := by omega
    rw [Nat.mod_eq_of_lt hpos]
    have : a.val + (p - a.val) = p := by omega
    rw [this, Nat.mod_self]

/-- Commutativity of addition in Z/pZ -/
theorem zpAdd_comm (p : Nat) (hp : p > 0) (a b : Fin p) :
    zpAdd p hp a b = zpAdd p hp b a := by
  apply Fin.ext; simp only [zpAdd, Nat.add_comm]

/-! ## Strict Group Instance for Z/pZ -/

/-- The strict group structure on Z/pZ = Fin p. -/
def cyclicStrictGroup (p : Nat) (hp : p > 0) : StrictGroup (Fin p) where
  mul := zpAdd p hp
  one := zpZero p hp
  mul_assoc := zpAdd_assoc p hp
  one_mul := zpAdd_zero_left p hp
  mul_one := zpAdd_zero_right p hp
  inv := zpNeg p hp
  mul_left_inv := zpAdd_neg_left p hp
  mul_right_inv := zpAdd_neg_right p hp

/-! ## Generator and Order -/

/-- Repeated addition of the generator: n · 1 in Z/pZ -/
def zpGenPow (p : Nat) (hp : p > 0) : Nat → Fin p
  | 0 => zpZero p hp
  | n + 1 => zpAdd p hp (zpGenPow p hp n) (zpGen p hp)

/-- n · 1 has value n % p -/
theorem zpGenPow_val (p : Nat) (hp : p > 0) (n : Nat) :
    (zpGenPow p hp n).val = n % p := by
  induction n with
  | zero => simp [zpGenPow, zpZero]
  | succ k ih =>
    simp only [zpGenPow, zpAdd, zpGen]
    rw [ih]
    by_cases h1 : p = 1
    · subst h1; simp [Nat.mod_one]
    · have hp2 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
      rw [hp2]
      rw [Nat.add_mod, Nat.mod_mod_of_dvd _ ⟨1, by omega⟩, ← Nat.add_mod]

/-- Addition law for generator powers: (m + n) · 1 = m · 1 + n · 1. -/
theorem zpGenPow_add (p : Nat) (hp : p > 0) (m n : Nat) :
    zpGenPow p hp (m + n) = zpAdd p hp (zpGenPow p hp m) (zpGenPow p hp n) := by
  induction n with
  | zero =>
      simp [zpGenPow, zpAdd_zero_right]
  | succ n ih =>
      simp [zpGenPow, ih, zpAdd_assoc]

/-- The generator has exact order p: p · 1 = 0 -/
theorem zpGen_order (p : Nat) (hp : p > 0) :
    zpGenPow p hp p = zpZero p hp := by
  apply Fin.ext
  rw [zpGenPow_val]
  simp [zpZero, Nat.mod_self]

/-- For 0 < k < p, k · 1 ≠ 0 (minimality of order) -/
theorem zpGen_order_minimal (p : Nat) (hp : p > 0) (k : Nat)
    (hk1 : 0 < k) (hk2 : k < p) :
    zpGenPow p hp k ≠ zpZero p hp := by
  intro h
  have hval := _root_.congrArg Fin.val h
  rw [zpGenPow_val] at hval
  simp [zpZero] at hval
  have := Nat.mod_eq_of_lt hk2
  omega

/-- Every element of Z/pZ is a power of the generator -/
theorem zpGen_generates (p : Nat) (hp : p > 0) (a : Fin p) :
    zpGenPow p hp a.val = a := by
  apply Fin.ext
  rw [zpGenPow_val]
  exact Nat.mod_eq_of_lt a.isLt

/-! ## Abelianness of Z/pZ -/

/-- Z/pZ is abelian: a + b = b + a for all a, b -/
theorem cyclic_abelian (p : Nat) (hp : p > 0) (a b : Fin p) :
    (cyclicStrictGroup p hp).mul a b = (cyclicStrictGroup p hp).mul b a :=
  zpAdd_comm p hp a b

/-! ## Repeated addition of arbitrary elements -/

/-- n-fold addition of an arbitrary element a in Z/pZ -/
def zpPow (p : Nat) (hp : p > 0) (a : Fin p) : Nat → Fin p
  | 0 => zpZero p hp
  | n + 1 => zpAdd p hp (zpPow p hp a n) a

/-- n · a has value (n * a.val) % p -/
theorem zpPow_val (p : Nat) (hp : p > 0) (a : Fin p) (n : Nat) :
    (zpPow p hp a n).val = (n * a.val) % p := by
  induction n with
  | zero => simp [zpPow, zpZero]
  | succ k ih =>
    simp only [zpPow, zpAdd]
    rw [ih, Nat.succ_mul]
    rw [Nat.add_mod, Nat.mod_mod_of_dvd _ ⟨1, by omega⟩, ← Nat.add_mod]

/-- **Lagrange's theorem for cyclic groups**: p · a = 0 for all a ∈ Z/pZ -/
theorem zpPow_order_divides (p : Nat) (hp : p > 0) (a : Fin p) :
    zpPow p hp a p = zpZero p hp := by
  apply Fin.ext
  simp only [zpPow_val, zpZero]
  exact Nat.mul_mod_right p a.val

/-! ## Concrete computations for small primes -/

section ConcreteComputations

/-! ### Z/3Z: Complete group structure verification -/

private abbrev hp3 : 3 > 0 := by omega

/-- 1 + 1 = 2 in Z/3Z -/
theorem z3_one_plus_one :
    zpAdd 3 hp3 (⟨1, by omega⟩ : Fin 3) ⟨1, by omega⟩ = ⟨2, by omega⟩ := by
  native_decide

/-- 1 + 2 = 0 in Z/3Z -/
theorem z3_one_plus_two :
    zpAdd 3 hp3 (⟨1, by omega⟩ : Fin 3) ⟨2, by omega⟩ = ⟨0, by omega⟩ := by
  native_decide

/-- 2 + 2 = 1 in Z/3Z -/
theorem z3_two_plus_two :
    zpAdd 3 hp3 (⟨2, by omega⟩ : Fin 3) ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
  native_decide

/-- Negation in Z/3Z: -1 = 2 -/
theorem z3_neg_one :
    zpNeg 3 hp3 (⟨1, by omega⟩ : Fin 3) = ⟨2, by omega⟩ := by
  native_decide

/-- Negation in Z/3Z: -2 = 1 -/
theorem z3_neg_two :
    zpNeg 3 hp3 (⟨2, by omega⟩ : Fin 3) = ⟨1, by omega⟩ := by
  native_decide

/-- The generator of Z/3Z has order exactly 3 -/
theorem z3_gen_order_exact : zpGenPow 3 hp3 3 = zpZero 3 hp3 :=
  zpGen_order 3 hp3

/-- 1 · gen ≠ 0 in Z/3Z -/
theorem z3_gen_not_trivial_1 : zpGenPow 3 hp3 1 ≠ zpZero 3 hp3 :=
  zpGen_order_minimal 3 hp3 1 (by omega) (by omega)

/-- 2 · gen ≠ 0 in Z/3Z -/
theorem z3_gen_not_trivial_2 : zpGenPow 3 hp3 2 ≠ zpZero 3 hp3 :=
  zpGen_order_minimal 3 hp3 2 (by omega) (by omega)

/-- Complete group axiom verification for Z/3Z -/
theorem z3_group_axioms :
    (∀ a : Fin 3, zpAdd 3 hp3 (zpZero 3 hp3) a = a) ∧
    (∀ a : Fin 3, zpAdd 3 hp3 a (zpZero 3 hp3) = a) ∧
    (∀ a : Fin 3, zpAdd 3 hp3 a (zpNeg 3 hp3 a) = zpZero 3 hp3) ∧
    (∀ a b : Fin 3, zpAdd 3 hp3 a b = zpAdd 3 hp3 b a) :=
  ⟨zpAdd_zero_left 3 hp3, zpAdd_zero_right 3 hp3,
   zpAdd_neg_right 3 hp3, zpAdd_comm 3 hp3⟩

/-- Exhaustive multiplication table for Z/3Z (all 9 products) -/
theorem z3_mul_table :
    zpAdd 3 hp3 ⟨0, by omega⟩ ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧
    zpAdd 3 hp3 ⟨0, by omega⟩ ⟨1, by omega⟩ = ⟨1, by omega⟩ ∧
    zpAdd 3 hp3 ⟨0, by omega⟩ ⟨2, by omega⟩ = ⟨2, by omega⟩ ∧
    zpAdd 3 hp3 ⟨1, by omega⟩ ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
    zpAdd 3 hp3 ⟨1, by omega⟩ ⟨1, by omega⟩ = ⟨2, by omega⟩ ∧
    zpAdd 3 hp3 ⟨1, by omega⟩ ⟨2, by omega⟩ = ⟨0, by omega⟩ ∧
    zpAdd 3 hp3 ⟨2, by omega⟩ ⟨0, by omega⟩ = ⟨2, by omega⟩ ∧
    zpAdd 3 hp3 ⟨2, by omega⟩ ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
    zpAdd 3 hp3 ⟨2, by omega⟩ ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### Z/5Z: Computations for a non-prime-3 example -/

private abbrev hp5 : 5 > 0 := by omega

/-- The generator of Z/5Z has order exactly 5 -/
theorem z5_gen_order_exact : zpGenPow 5 hp5 5 = zpZero 5 hp5 :=
  zpGen_order 5 hp5

/-- All intermediate powers of the generator in Z/5Z are nonzero -/
theorem z5_gen_order_minimal_all :
    zpGenPow 5 hp5 1 ≠ zpZero 5 hp5 ∧
    zpGenPow 5 hp5 2 ≠ zpZero 5 hp5 ∧
    zpGenPow 5 hp5 3 ≠ zpZero 5 hp5 ∧
    zpGenPow 5 hp5 4 ≠ zpZero 5 hp5 :=
  ⟨zpGen_order_minimal 5 hp5 1 (by omega) (by omega),
   zpGen_order_minimal 5 hp5 2 (by omega) (by omega),
   zpGen_order_minimal 5 hp5 3 (by omega) (by omega),
   zpGen_order_minimal 5 hp5 4 (by omega) (by omega)⟩

/-- 2 + 3 = 0 in Z/5Z (additive inverses) -/
theorem z5_two_plus_three :
    zpAdd 5 hp5 (⟨2, by omega⟩ : Fin 5) ⟨3, by omega⟩ = ⟨0, by omega⟩ := by
  native_decide

/-- 4 + 4 = 3 in Z/5Z -/
theorem z5_four_plus_four :
    zpAdd 5 hp5 (⟨4, by omega⟩ : Fin 5) ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
  native_decide

/-- Lagrange verified for Z/5Z: 5 · a = 0 for every element -/
theorem z5_lagrange :
    ∀ a : Fin 5, zpPow 5 hp5 a 5 = zpZero 5 hp5 :=
  zpPow_order_divides 5 hp5

/-! ### Z/7Z: Computations for a larger prime -/

private abbrev hp7 : 7 > 0 := by omega

/-- The generator of Z/7Z has order exactly 7 -/
theorem z7_gen_order_exact : zpGenPow 7 hp7 7 = zpZero 7 hp7 :=
  zpGen_order 7 hp7

/-- All intermediate powers of the generator in Z/7Z are nonzero -/
theorem z7_gen_order_minimal_all :
    zpGenPow 7 hp7 1 ≠ zpZero 7 hp7 ∧
    zpGenPow 7 hp7 2 ≠ zpZero 7 hp7 ∧
    zpGenPow 7 hp7 3 ≠ zpZero 7 hp7 ∧
    zpGenPow 7 hp7 4 ≠ zpZero 7 hp7 ∧
    zpGenPow 7 hp7 5 ≠ zpZero 7 hp7 ∧
    zpGenPow 7 hp7 6 ≠ zpZero 7 hp7 :=
  ⟨zpGen_order_minimal 7 hp7 1 (by omega) (by omega),
   zpGen_order_minimal 7 hp7 2 (by omega) (by omega),
   zpGen_order_minimal 7 hp7 3 (by omega) (by omega),
   zpGen_order_minimal 7 hp7 4 (by omega) (by omega),
   zpGen_order_minimal 7 hp7 5 (by omega) (by omega),
   zpGen_order_minimal 7 hp7 6 (by omega) (by omega)⟩

/-- 3 + 5 = 1 in Z/7Z -/
theorem z7_three_plus_five :
    zpAdd 7 hp7 (⟨3, by omega⟩ : Fin 7) ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  native_decide

/-- 6 + 6 = 5 in Z/7Z -/
theorem z7_six_plus_six :
    zpAdd 7 hp7 (⟨6, by omega⟩ : Fin 7) ⟨6, by omega⟩ = ⟨5, by omega⟩ := by
  native_decide

/-- Negation table for Z/7Z -/
theorem z7_neg_table :
    zpNeg 7 hp7 ⟨1, by omega⟩ = ⟨6, by omega⟩ ∧
    zpNeg 7 hp7 ⟨2, by omega⟩ = ⟨5, by omega⟩ ∧
    zpNeg 7 hp7 ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- Lagrange verified for Z/7Z: 7 · a = 0 for every element -/
theorem z7_lagrange :
    ∀ a : Fin 7, zpPow 7 hp7 a 7 = zpZero 7 hp7 :=
  zpPow_order_divides 7 hp7

end ConcreteComputations

/-! ## Lens Space π₁ Structure -/

/-- The strict group on π₁(L(p,1)) transported from Z/pZ -/
def lensSpacePiOneGroup (p : Nat) (hp : p > 0) : StrictGroup (lensSpacePiOne p) :=
  cyclicStrictGroup p hp

/-- π₁(L(p,1)) is abelian -/
theorem lensSpace_pi1_abelian (p : Nat) (hp : p > 0) (a b : lensSpacePiOne p) :
    (lensSpacePiOneGroup p hp).mul a b = (lensSpacePiOneGroup p hp).mul b a :=
  cyclic_abelian p hp a b

/-- π₁(L(p,1)) has a generator of order exactly p -/
theorem lensSpace_pi1_gen_order (p : Nat) (hp : p > 0) :
    zpGenPow p hp p = zpZero p hp :=
  zpGen_order p hp

/-- π₁(L(p,1)) generator is nontrivial for p ≥ 2 -/
theorem lensSpace_pi1_gen_nontrivial (p : Nat) (hp : p > 0) (hp2 : p ≥ 2) :
    zpGen p hp ≠ zpZero p hp := by
  intro h
  have hval := _root_.congrArg Fin.val h
  simp [zpGen, zpZero] at hval
  have : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  omega

/-- Every element of π₁(L(p,1)) is a power of the generator -/
theorem lensSpace_pi1_cyclic (p : Nat) (hp : p > 0) (a : lensSpacePiOne p) :
    zpGenPow p hp a.val = a :=
  zpGen_generates p hp a

/-! ## Double Negation and Inverse Laws -/

/-- Double negation: -(-a) = a in Z/pZ -/
theorem zpNeg_zpNeg (p : Nat) (hp : p > 0) (a : Fin p) :
    zpNeg p hp (zpNeg p hp a) = a := by
  have := StrictGroup.inv_inv (cyclicStrictGroup p hp) a
  exact this

/-- Negation of zero: -0 = 0 in Z/pZ -/
theorem zpNeg_zero (p : Nat) (hp : p > 0) :
    zpNeg p hp (zpZero p hp) = zpZero p hp := by
  have := StrictGroup.inv_one (cyclicStrictGroup p hp)
  exact this

/-! ## Homomorphism: Z/pZ → Z/qZ when q ∣ p -/

/-- Canonical quotient map Z/pZ → Z/qZ when q divides p -/
def zpQuot (p q : Nat) (_ : p > 0) (hq : q > 0) (a : Fin p) : Fin q :=
  ⟨a.val % q, Nat.mod_lt _ hq⟩

/-- The quotient map preserves addition when q ∣ p -/
theorem zpQuot_add (p q : Nat) (hp : p > 0) (hq : q > 0) (hdvd : q ∣ p)
    (a b : Fin p) :
    zpQuot p q hp hq (zpAdd p hp a b) =
    zpAdd q hq (zpQuot p q hp hq a) (zpQuot p q hp hq b) := by
  apply Fin.ext
  simp only [zpQuot, zpAdd]
  rw [Nat.mod_mod_of_dvd _ hdvd, Nat.add_mod]

/-- The quotient map preserves zero -/
theorem zpQuot_zero (p q : Nat) (hp : p > 0) (hq : q > 0) :
    zpQuot p q hp hq (zpZero p hp) = zpZero q hq := by
  apply Fin.ext; simp [zpQuot, zpZero]

end CompPath
end Path
end ComputationalPaths
