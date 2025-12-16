/-
# Torus π₁(T²) ≃ ℤ × ℤ (assumption-free, opt-in)

The core development keeps `π₁(T²) ≃ ℤ × ℤ` *parametric* in the data interface
`HasTorusPiOneEncode` (see `TorusStep.lean`) so the assumption stays explicit
and discharge-friendly.

If you want to *use* the torus result without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasTorusPiOneEncode` as a **kernel axiom**, and
2. Exports a wrapper `torusPiOneEquivIntProd'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.TorusStep

namespace ComputationalPaths
namespace Path

universe u

/-- Global torus π₁ encode/decode data (kernel axiom, opt-in). -/
axiom instHasTorusPiOneEncodeAxiom : HasTorusPiOneEncode.{u}

attribute [instance] instHasTorusPiOneEncodeAxiom

/-- Assumption-free wrapper: π₁(T²) ≃ ℤ × ℤ. -/
noncomputable def torusPiOneEquivIntProd' : SimpleEquiv (torusPiOne.{u}) (Int × Int) :=
  torusPiOneEquivIntProd.{u}

end Path
end ComputationalPaths
