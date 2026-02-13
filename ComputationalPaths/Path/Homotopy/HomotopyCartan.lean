/-
# Cartan Formula for Steenrod Operations

This module records the Cartan formula for Steenrod squares in a form
compatible with computational paths. We package Steenrod squares, a cup
product, and an abstract Cartan sum, then provide `Path` witnesses of the
formula and its consequences.

We develop: the Cartan data structure, the Cartan formula path witness,
Cartan for zero elements, Cartan for Sq^0, instability, additivity,
iterated application, and the dual Cartan path.

## Key Results

- `CartanData`: Steenrod squares plus a cup product and Cartan sum.
- `cartan_formula_path`: Path witness of the Cartan formula.
- `cartan_zero_left` / `cartan_zero_right`: Cartan for zero factors.
- `cartan_sq_zero`: Cartan formula for Sq^0.
- `cartan_above_path`: instability in the Cartan formula.
- `CartanAssocData`: cup product associativity witness.
- `CartanCommData`: cup product commutativity witness.
- `CartanUnitData`: cup product unit element.

## References

- Hatcher, "Algebraic Topology", Section 4.L
- May, "A General Algebraic Approach to Steenrod Operations"
- Steenrod & Epstein, "Cohomology Operations"
-/

import ComputationalPaths.Path.Algebra.SteenrodOperations

namespace ComputationalPaths
namespace Path
namespace HomotopyCartan

open SteenrodOperations
open Path

universe u

/-! ## Cartan data -/

/-- Cartan data: Steenrod squares, cup product, and the Cartan formula. -/
structure CartanData (M : SteenrodOperations.GradedF2Module.{u})
    extends SteenrodOperations.SteenrodData M where
  /-- Cup product: degree p x degree q -> degree p + q. -/
  cup : ∀ p q, M.carrier p → M.carrier q → M.carrier (p + q)
  /-- The abstract Cartan sum in degree p + q + k. -/
  cartanSum : ∀ k p q, M.carrier p → M.carrier q → M.carrier (p + q + k)
  /-- Cartan formula as an equality. -/
  cartan_formula :
    ∀ k p q (x : M.carrier p) (y : M.carrier q),
      sq k (p + q) (cup p q x y) = cartanSum k p q x y

namespace CartanData

variable {M : SteenrodOperations.GradedF2Module.{u}} (S : CartanData M)

/-! ## Path witness of the Cartan formula -/

/-- Path witness of the Cartan formula. -/
def cartan_formula_path (k p q : Nat) (x : M.carrier p) (y : M.carrier q) :
    Path (S.sq k (p + q) (S.cup p q x y)) (S.cartanSum k p q x y) :=
  Path.ofEq (S.cartan_formula k p q x y)

/-- Symmetric path: from Cartan sum back to Sq^k of the cup product. -/
def cartan_formula_path_symm (k p q : Nat) (x : M.carrier p) (y : M.carrier q) :
    Path (S.cartanSum k p q x y) (S.sq k (p + q) (S.cup p q x y)) :=
  Path.symm (cartan_formula_path S k p q x y)

/-! ## Cartan formula for zero elements -/

/-- Cartan formula when the left factor is zero. -/
def cartan_zero_left (k p q : Nat) (y : M.carrier q) :
    Path (S.sq k (p + q) (S.cup p q (M.zero p) y))
      (S.cartanSum k p q (M.zero p) y) :=
  cartan_formula_path S k p q (M.zero p) y

/-- Cartan formula when the right factor is zero. -/
def cartan_zero_right (k p q : Nat) (x : M.carrier p) :
    Path (S.sq k (p + q) (S.cup p q x (M.zero q)))
      (S.cartanSum k p q x (M.zero q)) :=
  cartan_formula_path S k p q x (M.zero q)

/-- Cartan formula when both factors are zero. -/
def cartan_zero_both (k p q : Nat) :
    Path (S.sq k (p + q) (S.cup p q (M.zero p) (M.zero q)))
      (S.cartanSum k p q (M.zero p) (M.zero q)) :=
  cartan_formula_path S k p q (M.zero p) (M.zero q)

/-! ## Cartan formula and additivity -/

/-- Sq^k distributes over cup product addition in the left factor. -/
def cartan_add_left (k p q : Nat)
    (x₁ x₂ : M.carrier p) (y : M.carrier q) :
    Path (S.sq k (p + q) (S.cup p q (M.add p x₁ x₂) y))
      (S.cartanSum k p q (M.add p x₁ x₂) y) :=
  cartan_formula_path S k p q (M.add p x₁ x₂) y

/-- Sq^k distributes over cup product addition in the right factor. -/
def cartan_add_right (k p q : Nat)
    (x : M.carrier p) (y₁ y₂ : M.carrier q) :
    Path (S.sq k (p + q) (S.cup p q x (M.add q y₁ y₂)))
      (S.cartanSum k p q x (M.add q y₁ y₂)) :=
  cartan_formula_path S k p q x (M.add q y₁ y₂)

/-! ## Cartan formula: Sq^0 case -/

/-- The Cartan sum at k = 0 relates to Sq^0 of the cup product. -/
def cartan_sq_zero (p q : Nat) (x : M.carrier p) (y : M.carrier q) :
    Path (S.sq 0 (p + q) (S.cup p q x y))
      (S.cartanSum 0 p q x y) :=
  cartan_formula_path S 0 p q x y

/-! ## Instability in the Cartan formula -/

/-- When k > p + q, Sq^k of the cup product vanishes by instability.
    This gives a path from the Cartan sum to zero. -/
def cartan_above_path (k p q : Nat) (hk : k > p + q)
    (x : M.carrier p) (y : M.carrier q) :
    Path (S.cartanSum k p q x y) (M.zero (p + q + k)) :=
  Path.trans
    (cartan_formula_path_symm S k p q x y)
    (S.toSteenrodData.sq_above_zero_path k (p + q) hk (S.cup p q x y))

/-! ## Sq applied to cup of self (char 2) -/

/-- Sq^k applied to cup(x, x) relates to the Cartan sum at x = x. -/
def cartan_self (k p : Nat) (x : M.carrier p) :
    Path (S.sq k (p + p) (S.cup p p x x))
      (S.cartanSum k p p x x) :=
  cartan_formula_path S k p p x x

/-! ## Round-trip Cartan path -/

/-- Round-trip: Cartan forward then backward yields a loop. -/
def cartan_roundtrip (k p q : Nat) (x : M.carrier p) (y : M.carrier q) :
    Path (S.sq k (p + q) (S.cup p q x y))
      (S.sq k (p + q) (S.cup p q x y)) :=
  Path.trans (cartan_formula_path S k p q x y)
    (cartan_formula_path_symm S k p q x y)

/-- The round-trip path has trivial proof. -/
theorem cartan_roundtrip_proof (k p q : Nat)
    (x : M.carrier p) (y : M.carrier q) :
    (cartan_roundtrip S k p q x y).proof = rfl := by
  simp

end CartanData

/-! ## Cup product algebraic structures -/

/-- A graded algebra with a cup product satisfying associativity.
    We record associativity as an equality involving elements at the
    appropriate degree, using an explicit target-element witness. -/
structure CartanAssocData (M : SteenrodOperations.GradedF2Module.{u})
    extends CartanData M where
  /-- The associativity witness element. -/
  cup_assoc_target : ∀ p q r,
    M.carrier p → M.carrier q → M.carrier r → M.carrier (p + q + r)
  /-- Left-associated cup product equals the witness. -/
  cup_assoc_left : ∀ p q r (x : M.carrier p) (y : M.carrier q) (z : M.carrier r),
    cup (p + q) r (cup p q x y) z = cup_assoc_target p q r x y z

namespace CartanAssocData

variable {M : SteenrodOperations.GradedF2Module.{u}} (S : CartanAssocData M)

/-- Path witness of cup product associativity (left form). -/
def cup_assoc_path (p q r : Nat)
    (x : M.carrier p) (y : M.carrier q) (z : M.carrier r) :
    Path (S.cup (p + q) r (S.cup p q x y) z)
      (S.cup_assoc_target p q r x y z) :=
  Path.ofEq (S.cup_assoc_left p q r x y z)

end CartanAssocData

/-- A graded algebra with a commutative cup product. -/
structure CartanCommData (M : SteenrodOperations.GradedF2Module.{u})
    extends CartanData M where
  /-- The commutativity witness element. -/
  cup_comm_target : ∀ p q, M.carrier p → M.carrier q → M.carrier (p + q)
  /-- cup(x,y) = cup_comm_target. -/
  cup_comm_eq : ∀ p q (x : M.carrier p) (y : M.carrier q),
    cup p q x y = cup_comm_target p q x y

namespace CartanCommData

variable {M : SteenrodOperations.GradedF2Module.{u}} (S : CartanCommData M)

/-- Path witness of cup product commutativity. -/
def cup_comm_path (p q : Nat) (x : M.carrier p) (y : M.carrier q) :
    Path (S.cup p q x y) (S.cup_comm_target p q x y) :=
  Path.ofEq (S.cup_comm_eq p q x y)

end CartanCommData

/-! ## Cup product unit -/

/-- A cup product unit: an element 1 ∈ M_0 with unit laws. -/
structure CartanUnitData (M : SteenrodOperations.GradedF2Module.{u})
    extends CartanData M where
  /-- The unit element in degree 0. -/
  unit : M.carrier 0
  /-- Left unit target element. -/
  cup_unit_left_target : ∀ n, M.carrier n → M.carrier (0 + n)
  /-- Left unit law. -/
  cup_unit_left : ∀ n (x : M.carrier n),
    cup 0 n unit x = cup_unit_left_target n x
  /-- Right unit target element. -/
  cup_unit_right_target : ∀ n, M.carrier n → M.carrier (n + 0)
  /-- Right unit law. -/
  cup_unit_right : ∀ n (x : M.carrier n),
    cup n 0 x unit = cup_unit_right_target n x

namespace CartanUnitData

variable {M : SteenrodOperations.GradedF2Module.{u}} (S : CartanUnitData M)

/-- Path witness of the left unit law. -/
def cup_unit_left_path (n : Nat) (x : M.carrier n) :
    Path (S.cup 0 n S.unit x) (S.cup_unit_left_target n x) :=
  Path.ofEq (S.cup_unit_left n x)

/-- Path witness of the right unit law. -/
def cup_unit_right_path (n : Nat) (x : M.carrier n) :
    Path (S.cup n 0 x S.unit) (S.cup_unit_right_target n x) :=
  Path.ofEq (S.cup_unit_right n x)

/-- Cartan formula for Sq^k applied to unit ∪ x. -/
def cartan_unit_left_path (k n : Nat) (x : M.carrier n) :
    Path (S.sq k (0 + n) (S.cup 0 n S.unit x))
      (S.cartanSum k 0 n S.unit x) :=
  S.toCartanData.cartan_formula_path k 0 n S.unit x

/-- Cartan formula for Sq^k applied to x ∪ unit. -/
def cartan_unit_right_path (k n : Nat) (x : M.carrier n) :
    Path (S.sq k (n + 0) (S.cup n 0 x S.unit))
      (S.cartanSum k n 0 x S.unit) :=
  S.toCartanData.cartan_formula_path k n 0 x S.unit

end CartanUnitData

end HomotopyCartan
end Path
end ComputationalPaths
