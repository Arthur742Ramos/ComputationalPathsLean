/-
# Circle π₁(S¹) ≃ ℤ (assumption-free, opt-in)

The core development keeps `π₁(S¹) ≃ ℤ` *parametric* in the data interface
`HasCirclePiOneEncode` (see `CircleStep.lean`) so the assumption stays explicit
and discharge-friendly.

If you want to *use* the circle result without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasCirclePiOneEncode` as a **kernel axiom**, and
2. Exports a wrapper `circlePiOneEquivInt'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.CircleStep

namespace ComputationalPaths
namespace Path

universe u

/-- Global circle π₁ encode/decode data (kernel axiom, opt-in). -/
axiom instHasCirclePiOneEncodeAxiom : HasCirclePiOneEncode.{u}

attribute [instance] instHasCirclePiOneEncodeAxiom

/-- Assumption-free wrapper: π₁(S¹) ≃ ℤ. -/
noncomputable def circlePiOneEquivInt' : SimpleEquiv (circlePiOne.{u}) Int :=
  circlePiOneEquivInt.{u}

end Path
end ComputationalPaths

