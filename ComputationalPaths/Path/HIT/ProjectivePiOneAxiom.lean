/-
# Projective plane π₁(RP²) ≃ ℤ₂ (assumption-free, opt-in)

The core development keeps `π₁(RP²) ≃ Bool` (representing ℤ₂) *parametric* in the
data interface `HasProjectivePiOneEncode` (see `ProjectivePlaneStep.lean`) so the
assumption stays explicit and discharge-friendly.

If you want to *use* the projective plane result without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasProjectivePiOneEncode` as a **kernel axiom**, and
2. Exports a wrapper `projectivePiOneEquivZ2'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.ProjectivePlaneStep

namespace ComputationalPaths
namespace Path

universe u

/-- Global projective plane π₁ encode/decode data (kernel axiom, opt-in). -/
axiom instHasProjectivePiOneEncodeAxiom : HasProjectivePiOneEncode.{u}

attribute [instance] instHasProjectivePiOneEncodeAxiom

/-- Assumption-free wrapper: π₁(RP²) ≃ ℤ₂ (represented as Bool). -/
noncomputable def projectivePiOneEquivZ2' : SimpleEquiv (projectivePiOne.{u}) Bool :=
  projectivePiOneEquivZ2.{u}

end Path
end ComputationalPaths
