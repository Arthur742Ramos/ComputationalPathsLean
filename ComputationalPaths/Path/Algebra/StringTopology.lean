/-
# String Topology Interfaces

This module provides lightweight interfaces for Chas-Sullivan string topology
in the computational paths setting. We package the loop product on H_plus(LM),
BV-algebra data with the BV operator Delta, the string bracket on S1-equivariant
homology, a BV-algebra package for H_plus(LS^n), and the Goldman bracket for
surfaces.

## Key Definitions

- `LoopProduct`
- `BVAlgebra`
- `StringTopology`
- `StringBracket`
- `LoopSphereBV`
- `GoldmanBracket`

## References

- Chas-Sullivan, "String Topology"
- Cohen-Jones-Yan, "The loop homology algebra of spheres and projective spaces"
- Goldman, "Invariant functions on Lie groups and Hamiltonian flows of surface group representations"
-/

import ComputationalPaths.Path.Algebra.CohomologyRing
import ComputationalPaths.Path.Algebra.LieAlgebraCohomology
import ComputationalPaths.Path.Homotopy.FreeLoopSpace

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace StringTopology

universe u

/-! ## Free loop space notation -/

/-- The free loop space LM. -/
abbrev LM (X : Type u) : Type u :=
  FreeLoopSpace.FreeLoopSpace X

/-! ## Graded homology and loop product -/

/-- Graded homology groups, reusing the cohomology-group interface. -/
abbrev HomologyGroups := CohomologyGroups

/-- Chas-Sullivan loop product data on H_plus(LM). -/
structure LoopProduct extends HomologyGroups where
  /-- Unit in degree 0 (class of the constant loop). -/
  unit : carrier 0
  /-- Loop product: H_p x H_q -> H_{p+q}. -/
  loopProduct : ∀ p q, carrier p → carrier q → carrier (p + q)
  /-- Loop product with zero on the left. -/
  loopProduct_zero_left : ∀ p q (y : carrier q),
    loopProduct p q (zero p) y = zero (p + q)
  /-- Loop product with zero on the right. -/
  loopProduct_zero_right : ∀ p q (x : carrier p),
    loopProduct p q x (zero q) = zero (p + q)
  /-- Left distributivity. -/
  loopProduct_add_left : ∀ p q (x x' : carrier p) (y : carrier q),
    loopProduct p q (add p x x') y =
      add (p + q) (loopProduct p q x y) (loopProduct p q x' y)
  /-- Right distributivity. -/
  loopProduct_add_right : ∀ p q (x : carrier p) (y y' : carrier q),
    loopProduct p q x (add q y y') =
      add (p + q) (loopProduct p q x y) (loopProduct p q x y')
  /-- Associativity (up to transport along `Nat.add_assoc`). -/
  loopProduct_assoc : ∀ p q r (x : carrier p) (y : carrier q) (z : carrier r),
    loopProduct (p + q) r (loopProduct p q x y) z =
      _root_.cast (_root_.congrArg carrier (Nat.add_assoc p q r).symm)
        (loopProduct p (q + r) x (loopProduct q r y z))
  /-- Graded commutativity (up to transport along `Nat.add_comm`). -/
  loopProduct_comm : ∀ p q (x : carrier p) (y : carrier q),
    loopProduct p q x y =
      _root_.cast (_root_.congrArg carrier (Nat.add_comm q p)) (loopProduct q p y x)
  /-- Left unit law. -/
  loopProduct_unit_left : ∀ n (x : carrier n),
    loopProduct 0 n unit x =
      _root_.cast (_root_.congrArg carrier (Nat.zero_add n).symm) x
  /-- Right unit law. -/
  loopProduct_unit_right : ∀ n (x : carrier n),
    loopProduct n 0 x unit =
      _root_.cast (_root_.congrArg carrier (Nat.add_zero n).symm) x

/-! ## BV-algebra structure -/

/-- BV-algebra structure on loop homology with operator Delta. -/
structure BVAlgebra extends LoopProduct where
  /-- BV operator Delta: H_n -> H_{n+1}. -/
  delta : ∀ n, carrier n → carrier (n + 1)
  /-- Delta is additive. -/
  delta_add : ∀ n (x y : carrier n),
    delta n (add n x y) = add (n + 1) (delta n x) (delta n y)
  /-- Delta squared is zero. -/
  delta_sq_zero : ∀ n (x : carrier n),
    delta (n + 1) (delta n x) = zero (n + 2)

/-- String topology data on H_plus(LM) as a BV-algebra. -/
structure StringTopology (X : Type u) extends BVAlgebra

/-! ## String bracket on equivariant homology -/

/-- S1-equivariant homology with the string bracket. -/
structure StringBracket (X : Type u) where
  /-- The equivariant homology carrier. -/
  equivariantHomology : Type u
  /-- Lie-algebra structure encoding the string bracket. -/
  lie : LieAlgebraCohomology.LieAlgebra equivariantHomology

namespace StringBracket

variable {X : Type u}

/-- The string bracket operation. -/
def bracket (S : StringBracket X) :
    S.equivariantHomology → S.equivariantHomology → S.equivariantHomology :=
  S.lie.bracket

end StringBracket

/-! ## Loop spheres as BV-algebras -/

/-- Free loop space on a sphere family. -/
abbrev LS (Sphere : Nat → Type u) (n : Nat) : Type u :=
  FreeLoopSpace.FreeLoopSpace (Sphere n)

/-- BV-algebra package for H_plus(LS^n). -/
structure LoopSphereBV (Sphere : Nat → Type u) (n : Nat) extends BVAlgebra

/-! ## Goldman bracket for surfaces -/

/-- Goldman bracket data on free homotopy classes of loops on a surface. -/
structure GoldmanBracket (Surface : Type u) where
  /-- The loop-class carrier. -/
  loopClass : Type u
  /-- Lie-algebra structure encoding the Goldman bracket. -/
  lie : LieAlgebraCohomology.LieAlgebra loopClass

namespace GoldmanBracket

variable {Surface : Type u}

/-- The Goldman bracket operation. -/
def bracket (G : GoldmanBracket Surface) : G.loopClass → G.loopClass → G.loopClass :=
  G.lie.bracket

end GoldmanBracket

/-! ## Summary -/

/-!
We introduced the loop product interface for free loop space homology, BV-algebra
data with the Delta operator, the string bracket on equivariant homology, a BV
package for loop spheres, and the Goldman bracket interface for surfaces.
-/

end StringTopology
end Algebra
end Path
end ComputationalPaths
