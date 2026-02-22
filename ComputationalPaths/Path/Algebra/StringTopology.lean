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

/-- Graded abelian group data for (co)homology. -/
structure CohomologyGroups where
  /-- The graded components. -/
  carrier : Nat → Type u
  /-- Zero element in each degree. -/
  zero : (n : Nat) → carrier n
  /-- Addition in each degree. -/
  add : (n : Nat) → carrier n → carrier n → carrier n

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

namespace LoopProduct

/-- Loop product with zero on the left. -/
theorem zero_left (L : LoopProduct) (p q : Nat) (y : L.carrier q) :
    L.loopProduct p q (L.zero p) y = L.zero (p + q) :=
  L.loopProduct_zero_left p q y

/-- Loop product with zero on the right. -/
theorem zero_right (L : LoopProduct) (p q : Nat) (x : L.carrier p) :
    L.loopProduct p q x (L.zero q) = L.zero (p + q) :=
  L.loopProduct_zero_right p q x

/-- Left distributivity for loop product. -/
theorem add_left (L : LoopProduct) (p q : Nat)
    (x x' : L.carrier p) (y : L.carrier q) :
    L.loopProduct p q (L.add p x x') y =
      L.add (p + q) (L.loopProduct p q x y) (L.loopProduct p q x' y) :=
  L.loopProduct_add_left p q x x' y

/-- Right distributivity for loop product. -/
theorem add_right (L : LoopProduct) (p q : Nat)
    (x : L.carrier p) (y y' : L.carrier q) :
    L.loopProduct p q x (L.add q y y') =
      L.add (p + q) (L.loopProduct p q x y) (L.loopProduct p q x y') :=
  L.loopProduct_add_right p q x y y'

/-- Associativity for loop product, up to transport. -/
theorem assoc (L : LoopProduct) (p q r : Nat)
    (x : L.carrier p) (y : L.carrier q) (z : L.carrier r) :
    L.loopProduct (p + q) r (L.loopProduct p q x y) z =
      _root_.cast (_root_.congrArg L.carrier (Nat.add_assoc p q r).symm)
        (L.loopProduct p (q + r) x (L.loopProduct q r y z)) :=
  L.loopProduct_assoc p q r x y z

/-- Graded commutativity for loop product, up to transport. -/
theorem comm (L : LoopProduct) (p q : Nat) (x : L.carrier p) (y : L.carrier q) :
    L.loopProduct p q x y =
      _root_.cast (_root_.congrArg L.carrier (Nat.add_comm q p)) (L.loopProduct q p y x) :=
  L.loopProduct_comm p q x y

/-- Left unit law for loop product. -/
theorem unit_left (L : LoopProduct) (n : Nat) (x : L.carrier n) :
    L.loopProduct 0 n L.unit x =
      _root_.cast (_root_.congrArg L.carrier (Nat.zero_add n).symm) x :=
  L.loopProduct_unit_left n x

/-- Right unit law for loop product. -/
theorem unit_right (L : LoopProduct) (n : Nat) (x : L.carrier n) :
    L.loopProduct n 0 x L.unit =
      _root_.cast (_root_.congrArg L.carrier (Nat.add_zero n).symm) x :=
  L.loopProduct_unit_right n x

end LoopProduct

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

namespace BVAlgebra

/-- Additivity of the BV operator. -/
theorem delta_additive (B : BVAlgebra) (n : Nat) (x y : B.carrier n) :
    B.delta n (B.add n x y) = B.add (n + 1) (B.delta n x) (B.delta n y) :=
  B.delta_add n x y

/-- Delta squared is zero. -/
theorem delta_squared_zero (B : BVAlgebra) (n : Nat) (x : B.carrier n) :
    B.delta (n + 1) (B.delta n x) = B.zero (n + 2) :=
  B.delta_sq_zero n x

-- delta_zero: requires additional axiom on BV operator (deleted)

end BVAlgebra

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
noncomputable def bracket (S : StringBracket X) :
    S.equivariantHomology → S.equivariantHomology → S.equivariantHomology :=
  S.lie.bracket

/-- The string bracket is exactly the Lie bracket from the packaged structure. -/
theorem bracket_eq_lie_bracket (S : StringBracket X)
    (x y : S.equivariantHomology) :
    StringBracket.bracket S x y = S.lie.bracket x y := rfl

/-- Skew-symmetry of the string bracket. -/
theorem bracket_skew (S : StringBracket X) (x y : S.equivariantHomology) :
    StringBracket.bracket S x y = S.lie.neg (StringBracket.bracket S y x) :=
  S.lie.bracket_skew x y

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
noncomputable def bracket (G : GoldmanBracket Surface) : G.loopClass → G.loopClass → G.loopClass :=
  G.lie.bracket

/-- The Goldman bracket is exactly the Lie bracket from the packaged structure. -/
theorem bracket_eq_lie_bracket (G : GoldmanBracket Surface) (x y : G.loopClass) :
    GoldmanBracket.bracket G x y = G.lie.bracket x y := rfl

/-- Skew-symmetry of the Goldman bracket. -/
theorem bracket_skew (G : GoldmanBracket Surface) (x y : G.loopClass) :
    GoldmanBracket.bracket G x y = G.lie.neg (GoldmanBracket.bracket G y x) :=
  G.lie.bracket_skew x y

end GoldmanBracket

private noncomputable def pathAnchor {A : Type u} (a : A) : Path a a := Path.refl a

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
