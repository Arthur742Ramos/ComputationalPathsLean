/-
# Suspension Theorems (Path-based)

This module records additional suspension lemmas using the computational-path
`Path` equality.  The focus is on meridian cancellation and the base loop
appearing in the Freudenthal preview.

## Key Results

- `merid_cancel_right`: meridian followed by its inverse reduces to refl (north)
- `merid_cancel_left`: inverse meridian followed by meridian reduces to refl (south)
- `suspBaseLoop_rweq_refl`: the Freudenthal base loop reduces to refl
- `suspensionMap_rweq_refl`: the suspension map is null on loops

## References

- HoTT Book, Chapter 8 (Suspension)
- `SuspensionLoop` and `FreudenthalSuspension`
-/

import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.FreudenthalSuspension

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace SuspensionTheorems

open SuspensionLoop
open FreudenthalSuspension

universe u

/-! ## Meridian cancellation -/

variable {X : Type u}

/-- Meridian followed by its inverse is rewrite-equivalent to refl at the north pole. -/
noncomputable def merid_cancel_right (x : X) :
    RwEq
      (Path.trans (Suspension.merid (X := X) x)
        (Path.symm (Suspension.merid (X := X) x)))
      (Path.refl (Suspension.north (X := X))) := by
  simpa using rweq_cmpA_inv_right (Suspension.merid (X := X) x)

/-- Inverse meridian followed by meridian is rewrite-equivalent to refl at the south pole. -/
noncomputable def merid_cancel_left (x : X) :
    RwEq
      (Path.trans (Path.symm (Suspension.merid (X := X) x))
        (Suspension.merid (X := X) x))
      (Path.refl (Suspension.south (X := X))) := by
  simpa using rweq_cmpA_inv_left (Suspension.merid (X := X) x)

/-! ## Base loop consequences -/

/-- The Freudenthal base loop reduces to the reflexive path at the north pole. -/
noncomputable def suspBaseLoop_rweq_refl (x0 : X) :
    RwEq (suspBaseLoop (X := X) x0)
      (Path.refl (Suspension.north (X := X))) := by
  simpa [suspBaseLoop] using merid_cancel_right (X := X) x0

/-- The Freudenthal suspension map is null on loops, up to rewrite equivalence. -/
noncomputable def suspensionMap_rweq_refl (x0 : X) (l : LoopSpace X x0) :
    RwEq (suspensionMap (X := X) x0 l)
      (Path.refl (Suspension.north (X := X))) := by
  simpa [suspensionMap] using suspBaseLoop_rweq_refl (X := X) x0

/-! ## Summary -/

end SuspensionTheorems
end Homotopy
end Path
end ComputationalPaths
