/-
# Torus π₁(T²) ≃ ℤ × ℤ (assumption-free, opt-in)

The core development keeps `π₁(T²) ≃ ℤ × ℤ` *parametric* in the data interface
`HasTorusPiOneEncode` (see `TorusStep.lean`) so the assumption stays explicit
and discharge-friendly.

If you want to *use* the torus result without threading that typeclass
hypothesis everywhere, import this file. It imports the (opt-in) circle π₁ axiom
bundle and uses the derived instance
`[HasCirclePiOneEncode] → HasTorusPiOneEncode` from `TorusStep.lean`.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.CirclePiOneAxiom
import ComputationalPaths.Path.HIT.TorusStep

namespace ComputationalPaths
namespace Path

universe u

/-- Assumption-free wrapper: π₁(T²) ≃ ℤ × ℤ. -/
noncomputable def torusPiOneEquivIntProd' : SimpleEquiv (torusPiOne.{u}) (Int × Int) :=
  torusPiOneEquivIntProd.{u}

end Path
end ComputationalPaths
