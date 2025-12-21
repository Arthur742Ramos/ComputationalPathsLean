/-
# Wedge SVK π₁(A ∨ B) ≃ π₁(A) * π₁(B) (assumption-free, opt-in)

The core development keeps the wedge encode/decode statement *parametric* in the
data interface `WedgeSVKInstances.HasWedgeSVKEncodeData` (see `PushoutPaths.lean`)
so importing `ComputationalPaths.Path.HIT.PushoutPaths` does not silently add
kernel axioms.

If you want to *use* the wedge SVK equivalence without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `WedgeSVKInstances.HasWedgeSVKEncodeData` as a **kernel axiom**, and
2. Exports a wrapper `wedgeFundamentalGroupEquiv'` with no extra parameters.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.PushoutPaths

namespace ComputationalPaths
namespace Path

universe u

/-- Global wedge encode/decode data (kernel axiom, opt-in). -/
axiom instHasWedgeSVKEncodeDataAxiom (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) :
    WedgeSVKInstances.HasWedgeSVKEncodeData A B a₀ b₀

attribute [instance] instHasWedgeSVKEncodeDataAxiom

/-- Assumption-free wrapper: π₁(A ∨ B) ≃ π₁(A) * π₁(B). -/
noncomputable def wedgeFundamentalGroupEquiv' (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :=
  wedgeFundamentalGroupEquiv (A := A) (B := B) a₀ b₀

end Path
end ComputationalPaths

