/-
# Derived Algebraic Results for Fundamental Groups

This module records consequences of the product theorem and truncation results,
including triviality of π₁ for PUnit' and collapsing product factors.

## Key Results
- `piOne_trivial_of_set`: If A is a set, then π₁(A, a) is trivial.
- `punit_piOne_trivial`: π₁(PUnit') is trivial.
- `piOneProdSetEquiv`: If B is a set, π₁(A × B) ≃ π₁(A).
- `piOneProdPunitEquiv`: π₁(A × PUnit') ≃ π₁(A).

## References
- HoTT Book, Theorem 2.6.4 (paths in products)
- Hatcher, Algebraic Topology, Proposition 1.12
-/

import ComputationalPaths.Path.Homotopy.ProductFundamentalGroup
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path

open CompPath

universe u

/-! ## Triviality of π₁ for sets -/

/-- If `A` is a set, then `π₁(A, a)` is trivial. -/
theorem piOne_trivial_of_set {A : Type u} (h : Truncation.IsSet A) (a : A)
    (α : π₁(A, a)) : α = PiOne.id := by
  simpa [PiOne.id] using
    (Truncation.set_pi1_trivial (A := A) (a := a) (h := h) α)

/-- π₁(PUnit') is trivial. -/
theorem punit_piOne_trivial (α : π₁(PUnit', PUnit'.unit)) :
    α = PiOne.id := by
  exact piOne_trivial_of_set (A := PUnit') (a := PUnit'.unit)
    (h := Truncation.IsSet.punitSet) α

/-! ## Product consequences -/

/-- Collapse the trivial factor in `π₁(A, a) × π₁(B, b)` when `B` is a set. -/
noncomputable def piOneProdSetFactorEquiv {A : Type u} {B : Type u}
    (a : A) (b : B) (h : Truncation.IsSet B) :
    SimpleEquiv (π₁(A, a) × π₁(B, b)) (π₁(A, a)) where
  toFun := Prod.fst
  invFun := fun α => (α, PiOne.id (A := B) (a := b))
  left_inv := by
    intro x
    cases x with
    | mk α β =>
        apply Prod.ext
        · rfl
        ·
          exact (piOne_trivial_of_set (A := B) (a := b) (h := h) β).symm
  right_inv := by
    intro α
    rfl

/-- If `B` is a set, then `π₁(A × B, (a, b)) ≃ π₁(A, a)`. -/
noncomputable def piOneProdSetEquiv {A : Type u} {B : Type u}
    (a : A) (b : B) (h : Truncation.IsSet B) :
    SimpleEquiv (π₁(A × B, (a, b))) (π₁(A, a)) :=
  SimpleEquiv.comp
    (prodPiOneEquiv (A := A) (B := B) a b)
    (piOneProdSetFactorEquiv (A := A) (B := B) a b h)

/-- `π₁(A × PUnit', (a, ⋆)) ≃ π₁(A, a)`. -/
noncomputable def piOneProdPunitEquiv {A : Type u} (a : A) :
    SimpleEquiv (π₁(A × PUnit', (a, PUnit'.unit))) (π₁(A, a)) :=
  piOneProdSetEquiv (A := A) (B := PUnit') a PUnit'.unit
    (Truncation.IsSet.punitSet)

end Path

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths
