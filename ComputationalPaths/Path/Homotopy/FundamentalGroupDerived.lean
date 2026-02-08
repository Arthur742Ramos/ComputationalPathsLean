/-
# Derived algebraic results for fundamental groups

This module records derived equivalences for fundamental groups, focusing on
product decompositions and transport along factorwise equivalences.

## Key Results

- `piOneProdEquiv`: π₁(A × B, (a, b)) ≃ π₁(A, a) × π₁(B, b)
- `piOneProdEquivOf`: transport the product equivalence along factorwise maps

## References

- Product Fundamental Group Theorem (ProductFundamentalGroup.lean)
-/

import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup

namespace ComputationalPaths
namespace Path

universe u v w x

/-! ## Product fundamental group (derived) -/

section ProductDerived

variable {A : Type u} {B : Type v}
variable {G : Type w} {H : Type x}
variable (a : A) (b : B)

/-- Derived form of the product fundamental group theorem. -/
noncomputable def piOneProdEquiv :
    SimpleEquiv (π₁(A × B, (a, b))) (π₁(A, a) × π₁(B, b)) :=
  prodPiOneEquiv (A := A) (B := B) a b

/-- Transport the product equivalence along equivalences on each factor. -/
noncomputable def piOneProdEquivOf
    (eA : SimpleEquiv (π₁(A, a)) G) (eB : SimpleEquiv (π₁(B, b)) H) :
    SimpleEquiv (π₁(A × B, (a, b))) (G × H) :=
  SimpleEquiv.comp (piOneProdEquiv (A := A) (B := B) a b)
    (SimpleEquiv.prodBoth' eA eB)

end ProductDerived

end Path
end ComputationalPaths
