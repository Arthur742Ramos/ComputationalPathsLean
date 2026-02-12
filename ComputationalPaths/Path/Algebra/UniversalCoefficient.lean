/-
# Universal Coefficient Theorem (Homology)

A minimal interface packaging a degreewise splitting.

All proofs are complete.
-/

import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace UniversalCoefficient

universe u

/-- A coefficient system (abelian-group-like skeleton). -/
structure CoefficientSystem where
  carrier : Type u
  add : carrier → carrier → carrier
  zero : carrier

/-- UCT data as a family of splittings. -/
structure UCTData (M : CoefficientSystem.{u}) where
  homology : Nat → Type u
  tensorPart : Nat → Type u
  torPart : Nat → Type u
  fwd : (n : Nat) → homology n → tensorPart n × torPart n
  inv : (n : Nat) → tensorPart n × torPart n → homology n
  right_inv : ∀ n x, fwd n (inv n x) = x
  left_inv : ∀ n x, inv n (fwd n x) = x

/-- Integers as coefficients. -/
def intCoeffs : CoefficientSystem where
  carrier := Int
  add := (· + ·)
  zero := 0

private def pathAnchor {A : Type u} (a : A) : Path a a := Path.refl a

end UniversalCoefficient
end Algebra
end Path
end ComputationalPaths
