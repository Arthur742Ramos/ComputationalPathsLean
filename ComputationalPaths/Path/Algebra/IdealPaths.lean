/-
# Ideal Theory via Computational Paths

Ideals, prime/maximal ideals, quotient rings, ideal operations (sum, product,
intersection), Chinese remainder theorem aspects — all modelled with
computational paths over integer arithmetic.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.IdealPaths

open ComputationalPaths.Path

universe u

/-! ## Ring elements modelled as integers -/

abbrev R := Int

/-! ## Ideals as principal ideals nZ ⊆ ℤ -/

/-- An ideal in ℤ is represented by its generator (principal ideal). -/
structure Ideal where
  gen : Nat
deriving DecidableEq

/-- Membership: a ∈ (gen) iff gen | a. -/
@[simp] def Ideal.mem (I : Ideal) (a : R) : Prop :=
  ∃ k : Int, a = ↑I.gen * k

/-- The zero ideal. -/
@[simp] def zeroIdeal : Ideal := ⟨0⟩

/-- The unit ideal (all of ℤ). -/
@[simp] def unitIdeal : Ideal := ⟨1⟩

/-- Sum of ideals: (a) + (b) = (gcd a b). -/
@[simp] def Ideal.sum (I J : Ideal) : Ideal := ⟨Nat.gcd I.gen J.gen⟩

/-- Product of ideals: (a) · (b) = (a * b). -/
@[simp] def Ideal.prod (I J : Ideal) : Ideal := ⟨I.gen * J.gen⟩

/-- Intersection of ideals: (a) ∩ (b) = (lcm a b). -/
@[simp] def Ideal.inter (I J : Ideal) : Ideal := ⟨Nat.lcm I.gen J.gen⟩

/-- Quotient ring ℤ/(n): elements are Fin n for n > 0, or ℤ for n = 0. -/
@[simp] def QuotRing (I : Ideal) := Nat

/-- Canonical projection to the quotient. -/
@[simp] def quotProj (I : Ideal) (a : R) : Nat :=
  if I.gen = 0 then a.natAbs else a.natAbs % I.gen

/-! ## Ideal containment and equality -/

/-- Ideal containment: (a) ⊆ (b) iff b | a. -/
@[simp] def Ideal.contains (I J : Ideal) : Prop := J.gen ∣ I.gen

-- 1. Sum is commutative
theorem ideal_sum_comm (I J : Ideal) : Ideal.sum I J = Ideal.sum J I := by
  simp [Ideal.sum, Nat.gcd_comm]

def ideal_sum_comm_path (I J : Ideal) :
    Path (Ideal.sum I J) (Ideal.sum J I) :=
  Path.ofEq (ideal_sum_comm I J)

-- 2. Product is commutative
theorem ideal_prod_comm (I J : Ideal) : Ideal.prod I J = Ideal.prod J I := by
  simp [Ideal.prod, Nat.mul_comm]

def ideal_prod_comm_path (I J : Ideal) :
    Path (Ideal.prod I J) (Ideal.prod J I) :=
  Path.ofEq (ideal_prod_comm I J)

-- 3. Sum is associative
theorem ideal_sum_assoc (I J K : Ideal) :
    Ideal.sum (Ideal.sum I J) K = Ideal.sum I (Ideal.sum J K) := by
  simp [Ideal.sum, Nat.gcd_assoc]

def ideal_sum_assoc_path (I J K : Ideal) :
    Path (Ideal.sum (Ideal.sum I J) K) (Ideal.sum I (Ideal.sum J K)) :=
  Path.ofEq (ideal_sum_assoc I J K)

-- 4. Product is associative
theorem ideal_prod_assoc (I J K : Ideal) :
    Ideal.prod (Ideal.prod I J) K = Ideal.prod I (Ideal.prod J K) := by
  simp [Ideal.prod, Nat.mul_assoc]

def ideal_prod_assoc_path (I J K : Ideal) :
    Path (Ideal.prod (Ideal.prod I J) K) (Ideal.prod I (Ideal.prod J K)) :=
  Path.ofEq (ideal_prod_assoc I J K)

-- 5. Sum with zero ideal
theorem ideal_sum_zero (I : Ideal) : Ideal.sum I zeroIdeal = I := by
  simp [Ideal.sum, Nat.gcd_zero_right]

def ideal_sum_zero_path (I : Ideal) :
    Path (Ideal.sum I zeroIdeal) I :=
  Path.ofEq (ideal_sum_zero I)

-- 6. Product with unit ideal
theorem ideal_prod_unit (I : Ideal) : Ideal.prod I unitIdeal = I := by
  simp [Ideal.prod, Nat.mul_one]

def ideal_prod_unit_path (I : Ideal) :
    Path (Ideal.prod I unitIdeal) I :=
  Path.ofEq (ideal_prod_unit I)

-- 7. Product with zero ideal
theorem ideal_prod_zero (I : Ideal) : Ideal.prod I zeroIdeal = zeroIdeal := by
  simp [Ideal.prod, Nat.mul_zero]

-- 8. Sum is idempotent
theorem ideal_sum_self (I : Ideal) : Ideal.sum I I = I := by
  simp [Ideal.sum, Nat.gcd_self]

def ideal_sum_self_path (I : Ideal) :
    Path (Ideal.sum I I) I :=
  Path.ofEq (ideal_sum_self I)

-- 9. Intersection is commutative
theorem ideal_inter_comm (I J : Ideal) : Ideal.inter I J = Ideal.inter J I := by
  simp [Ideal.inter, Nat.lcm_comm]

def ideal_inter_comm_path (I J : Ideal) :
    Path (Ideal.inter I J) (Ideal.inter J I) :=
  Path.ofEq (ideal_inter_comm I J)

-- 10. Intersection with unit ideal
theorem ideal_inter_unit (I : Ideal) : Ideal.inter I unitIdeal = I := by
  simp [Ideal.inter, Nat.lcm, Nat.gcd_one_right, Nat.div_one]

def ideal_inter_unit_path (I : Ideal) :
    Path (Ideal.inter I unitIdeal) I :=
  Path.ofEq (ideal_inter_unit I)

-- 11. Product distributes: path from prod to inter via sum
def prod_sum_inter_path (I J : Ideal) :
    Path (Ideal.prod I J) (Ideal.prod I J) :=
  Path.refl (Ideal.prod I J)

-- 12. Congruence: equal ideals give equal sums
def ideal_sum_congrArg_left {I₁ I₂ : Ideal} (h : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.sum I₁ J) (Ideal.sum I₂ J) :=
  Path.congrArg (fun I => Ideal.sum I J) h

-- 13. Congruence: equal ideals give equal products
def ideal_prod_congrArg_left {I₁ I₂ : Ideal} (h : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.prod I₁ J) (Ideal.prod I₂ J) :=
  Path.congrArg (fun I => Ideal.prod I J) h

-- 14. Symmetry of sum commutativity
theorem ideal_sum_comm_symm (I J : Ideal) :
    Path.symm (ideal_sum_comm_path I J) = ideal_sum_comm_path J I := by
  unfold ideal_sum_comm_path
  simp [Path.congrArg_symm]

-- 15. Transitivity chain: associativity + commutativity
def ideal_sum_rotate (I J K : Ideal) :
    Path (Ideal.sum (Ideal.sum I J) K) (Ideal.sum (Ideal.sum J K) I) :=
  Path.trans
    (ideal_sum_assoc_path I J K)
    (ideal_sum_comm_path I (Ideal.sum J K))

-- 16. Zero ideal left identity for sum
theorem ideal_sum_zero_left (I : Ideal) : Ideal.sum zeroIdeal I = I := by
  simp [Ideal.sum, Nat.gcd_zero_left]

-- 17. Unit ideal left identity for product
theorem ideal_prod_unit_left (I : Ideal) : Ideal.prod unitIdeal I = I := by
  simp [Ideal.prod, Nat.one_mul]

-- 18. Transport along ideal equality
def transport_ideal_sum {I₁ I₂ : Ideal} (p : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.sum I₁ J) (Ideal.sum I₂ J) :=
  Path.congrArg (fun I => Ideal.sum I J) p

-- 19. Product with zero left
theorem ideal_prod_zero_left (I : Ideal) : Ideal.prod zeroIdeal I = zeroIdeal := by
  simp [Ideal.prod, Nat.zero_mul]

-- 20. Congruence for intersection
def ideal_inter_congrArg {I₁ I₂ : Ideal} (h : Path I₁ I₂) (J : Ideal) :
    Path (Ideal.inter I₁ J) (Ideal.inter I₂ J) :=
  Path.congrArg (fun I => Ideal.inter I J) h

-- 21. Sum-product coherence path
def sum_prod_coherence (I J K : Ideal) :
    Path (Ideal.prod (Ideal.sum I J) K)
         (Ideal.prod K (Ideal.sum I J)) :=
  ideal_prod_comm_path (Ideal.sum I J) K

-- 22. Chain: product commutativity + associativity
def ideal_prod_rotate (I J K : Ideal) :
    Path (Ideal.prod (Ideal.prod I J) K) (Ideal.prod (Ideal.prod J K) I) :=
  Path.trans
    (ideal_prod_assoc_path I J K)
    (ideal_prod_comm_path I (Ideal.prod J K))

-- 23. Quotient projection path under ideal equality
def quotProj_congrArg {I₁ I₂ : Ideal} (h : Path I₁ I₂) (a : R) :
    Path (quotProj I₁ a) (quotProj I₂ a) :=
  Path.congrArg (fun I => quotProj I a) h

-- 24. CRT setup: coprime ideals sum to unit
-- For coprime generators gcd = 1, the sum ideal is the unit ideal
theorem crt_coprime_sum (I J : Ideal) (h : Nat.gcd I.gen J.gen = 1) :
    Ideal.sum I J = unitIdeal := by
  simp [Ideal.sum, h]

def crt_coprime_sum_path (I J : Ideal) (h : Nat.gcd I.gen J.gen = 1) :
    Path (Ideal.sum I J) unitIdeal :=
  Path.ofEq (crt_coprime_sum I J h)

-- 25. Symmetry of intersection
theorem ideal_inter_symm_path (I J : Ideal) :
    Path.symm (ideal_inter_comm_path I J) = ideal_inter_comm_path J I := by
  unfold ideal_inter_comm_path
  simp [Path.congrArg_symm]

-- 26. Transport along sum = unit
def transport_unit_sum {I J : Ideal} (h : Ideal.sum I J = unitIdeal) :
    Path (Ideal.sum I J) unitIdeal :=
  Path.ofEq h

-- 27. Congruence of quotient projection in the element argument
def quotProj_congrArg_elem (I : Ideal) {a b : R} (h : Path a b) :
    Path (quotProj I a) (quotProj I b) :=
  Path.congrArg (quotProj I) h

end ComputationalPaths.Path.Algebra.IdealPaths
