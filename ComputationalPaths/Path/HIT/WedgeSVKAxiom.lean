/-
# Wedge SVK π₁(A ∨ B) ≃ π₁(A) * π₁(B) (assumption-free, opt-in)

The core development keeps the wedge SVK statement *parametric* in small
interfaces (see `PushoutPaths.lean`)
so importing `ComputationalPaths.Path.HIT.PushoutPaths` does not silently add
kernel axioms.

If you want to *use* the wedge SVK equivalence without threading that typeclass
hypothesis everywhere, import this file. It:

1. Adds a global instance `HasWedgeSVKDecodeBijective` as a **kernel axiom**, and
2. Exports a wrapper `wedgeFundamentalGroupEquiv'` with no extra parameters.

Since `HasWedgeSVKDecodeBijective` is Prop-valued, the corresponding `encode`
map/equivalence is reconstructed noncomputably by classical choice.

This is intentionally **not** imported by `ComputationalPaths` by default.
-/

import ComputationalPaths.Path.HIT.PushoutPaths

namespace ComputationalPaths
namespace Path

universe u

/-- Global wedge SVK assumption (kernel axiom, opt-in): decode is bijective. -/
axiom instHasWedgeSVKDecodeBijectiveAxiom (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) :
    HasWedgeSVKDecodeBijective A B a₀ b₀

attribute [instance] instHasWedgeSVKDecodeBijectiveAxiom

/-- Assumption-free wrapper: π₁(A ∨ B) ≃ π₁(A) * π₁(B). -/
noncomputable def wedgeFundamentalGroupEquiv' (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode (A := A) (B := B) a₀ b₀) :=
  wedgeFundamentalGroupEquiv_of_decode_bijective (A := A) (B := B) a₀ b₀

end Path
end ComputationalPaths
