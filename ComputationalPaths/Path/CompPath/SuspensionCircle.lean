/-
# Suspension of the computational circle

This module packages the suspension of the computational-path circle and
recasts the triviality of its fundamental group using the sphere result.

## Key Results

- `SuspensionCircleCompPath`: suspension of `CircleCompPath`.
- `suspensionCircleCompPath_pi1_trivial`: π₁(Σ(S¹)) is trivial.
- `suspensionCircleCompPath_pi1_equiv_unit`: π₁(Σ(S¹)) ≃ 1.
-/

import ComputationalPaths.Path.CompPath.SphereCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Suspension of the computational circle -/

/-- The suspension of the computational circle. -/
def SuspensionCircleCompPath : Type u :=
  SuspensionCompPath CircleCompPath

/-- Basepoint of the suspension of the computational circle (north pole). -/
def suspensionCircleBasepoint : SuspensionCircleCompPath :=
  Sphere2CompPath.basepoint

/-- The fundamental group of Σ(S¹) is trivial. -/
theorem suspensionCircleCompPath_pi1_trivial :
    ∀ (α :
      π₁(SuspensionCircleCompPath, (suspensionCircleBasepoint : SuspensionCircleCompPath))),
      α = Quot.mk _ (Path.refl _) := by
  intro α
  simpa [SuspensionCircleCompPath, suspensionCircleBasepoint] using
    (Sphere2CompPath.sphere2CompPath_pi1_trivial (α := α))

/-- π₁(Σ(S¹)) ≃ 1 (the trivial group). -/
noncomputable def suspensionCircleCompPath_pi1_equiv_unit :
    SimpleEquiv
      (π₁(SuspensionCircleCompPath, (suspensionCircleBasepoint : SuspensionCircleCompPath)))
      Unit :=
  by
    simpa [SuspensionCircleCompPath, suspensionCircleBasepoint] using
      Sphere2CompPath.sphere2CompPath_pi1_equiv_unit

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
