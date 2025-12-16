/-
# Klein bottle π₁(K) ≃ ℤ × ℤ (assumption-free, opt-in)

The core development keeps `π₁(K) ≃ ℤ × ℤ` (normal-form coordinates for the
semidirect product ℤ ⋊ ℤ) *parametric* in the data interface `HasKleinPiOneEncode`
(see `KleinBottleStep.lean`) so the assumption stays explicit and discharge-friendly.

If you want to *use* the Klein bottle result without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasKleinPiOneEncode` as a **kernel axiom**, and
2. Exports a wrapper `kleinPiOneEquivIntProd'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.KleinBottleStep

namespace ComputationalPaths
namespace Path

universe u

/-- Global Klein bottle π₁ encode/decode data (kernel axiom, opt-in). -/
axiom instHasKleinPiOneEncodeAxiom : HasKleinPiOneEncode.{u}

attribute [instance] instHasKleinPiOneEncodeAxiom

/-- Assumption-free wrapper: π₁(K) ≃ ℤ × ℤ (normal-form coordinates). -/
noncomputable def kleinPiOneEquivIntProd' : SimpleEquiv (kleinPiOne.{u}) (Int × Int) :=
  kleinPiOneEquivIntProd.{u}

end Path
end ComputationalPaths
