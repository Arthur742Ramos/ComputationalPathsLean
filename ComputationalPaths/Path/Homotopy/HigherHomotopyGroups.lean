/-
# Higher Homotopy Groups (Mathlib interface)

This module provides a Mathlib-based definition of the higher homotopy groups
`πₙ` for `n ≥ 2`, recording their commutative group structure and basic
algebraic laws.

## Key Results

- `PiN`: the n-th homotopy group (Mathlib's `π_ n`)
- `piN_commGroup`: commutative group structure for `n ≥ 2`
- basic group laws (`piN_mul_assoc`, `piN_one_mul`, `piN_mul_one`,
  `piN_inv_mul_self`, `piN_mul_inv_self`, `piN_mul_comm`)

## References

- Mathlib `Topology/Homotopy/HomotopyGroup`
-/

import Mathlib.Topology.Homotopy.HomotopyGroup

open scoped Topology

namespace ComputationalPaths
namespace Path
namespace HigherHomotopyGroups

variable {X : Type*} [TopologicalSpace X]

/-- The n-th homotopy group `πₙ(X, x)` from Mathlib's `π_ n`. -/
abbrev PiN (n : ℕ) (X : Type*) [TopologicalSpace X] (x : X) : Type _ :=
  π_ n X x

notation "πₙ(" n ", " X ", " x ")" => PiN n X x

/-- For `n ≥ 2`, `πₙ(n, X, x)` is a commutative group. -/
noncomputable instance piN_commGroup (n : ℕ) [Nat.AtLeastTwo n] (x : X) :
    CommGroup (πₙ(n, X, x)) :=
  inferInstance

@[simp] theorem piN_mul_assoc (n : ℕ) [Nat.AtLeastTwo n] {x : X}
    (a b c : πₙ(n, X, x)) : (a * b) * c = a * (b * c) := by
  simpa using (mul_assoc a b c)

@[simp] theorem piN_one_mul (n : ℕ) [Nat.AtLeastTwo n] {x : X}
    (a : πₙ(n, X, x)) : (1 : πₙ(n, X, x)) * a = a := by
  simp

@[simp] theorem piN_mul_one (n : ℕ) [Nat.AtLeastTwo n] {x : X}
    (a : πₙ(n, X, x)) : a * (1 : πₙ(n, X, x)) = a := by
  simp

@[simp] theorem piN_inv_mul_self (n : ℕ) [Nat.AtLeastTwo n] {x : X}
    (a : πₙ(n, X, x)) : a⁻¹ * a = (1 : πₙ(n, X, x)) := by
  simp

@[simp] theorem piN_mul_inv_self (n : ℕ) [Nat.AtLeastTwo n] {x : X}
    (a : πₙ(n, X, x)) : a * a⁻¹ = (1 : πₙ(n, X, x)) := by
  simp

theorem piN_mul_comm (n : ℕ) [Nat.AtLeastTwo n] {x : X}
    (a b : πₙ(n, X, x)) : a * b = b * a := by
  simpa using (mul_comm a b)

end HigherHomotopyGroups
end Path
end ComputationalPaths
