/-
# Cartan Formula for Steenrod Operations

This module records the Cartan formula for Steenrod squares in a form
compatible with computational paths. We package Steenrod squares, a cup
product, and an abstract Cartan sum, then provide a `Path` witness of the
formula.

## Key Results

- `CartanData`: Steenrod squares plus a cup product and Cartan sum.
- `cartan_formula_path`: Path witness of the Cartan formula.

## References

- Hatcher, "Algebraic Topology", Section 4.L
- May, "A General Algebraic Approach to Steenrod Operations"
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

/-- Path witness of the Cartan formula. -/
def cartan_formula_path (k p q : Nat) (x : M.carrier p) (y : M.carrier q) :
    Path (S.sq k (p + q) (S.cup p q x y)) (S.cartanSum k p q x y) :=
  Path.ofEq (S.cartan_formula k p q x y)

end CartanData

end HomotopyCartan
end Path
end ComputationalPaths
