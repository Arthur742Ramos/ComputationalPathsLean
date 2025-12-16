/-
# Lens space π₁(L(p,1)) ≃ ℤ/pℤ (assumption-free, opt-in)

The core development keeps `π₁(L(p,1)) ≃ ℤ/pℤ` *parametric* in the data interface
`HasLensPiOneEncode` (see `LensSpace.lean`) so the assumption stays explicit
and discharge-friendly.

If you want to *use* the lens space result without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasLensPiOneEncode p hp` as a **kernel axiom**, and
2. Exports a wrapper `lensPiOneEquivZMod'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.LensSpace

namespace ComputationalPaths
namespace Path

universe u

/-- Global lens space π₁ encode/decode data (kernel axiom, opt-in). -/
axiom instHasLensPiOneEncodeAxiom (p : Nat) (hp : p > 0) : HasLensPiOneEncode.{u} p hp

attribute [instance] instHasLensPiOneEncodeAxiom

/-- Assumption-free wrapper: π₁(L(p,1)) ≃ ℤ/pℤ. -/
noncomputable def lensPiOneEquivZMod' (p : Nat) (hp : p > 0) :
    SimpleEquiv (lensPiOne.{u} p) (ZMod p hp) :=
  lensPiOneEquivZMod.{u} p hp

end Path
end ComputationalPaths
