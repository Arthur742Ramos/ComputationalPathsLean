/-!
# Higher Route 2-cells for Suspension Loops

This module adds explicit rewrite-equivalence witnesses connecting alternate
computational routes built from suspension meridians.
-/

import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace Suspension

universe u

variable {X : Type u}

/-- Meridian-based loop from north to north using points `x` and `y`. -/
abbrev meridianLoop (x y : X) :
    LoopSpace (SuspensionLoop.Suspension X) (SuspensionLoop.Suspension.north (X := X)) :=
  Path.trans
    (SuspensionLoop.Suspension.merid (X := X) x)
    (Path.symm (SuspensionLoop.Suspension.merid (X := X) y))

/-- Inserting a right unit on the first meridian route yields a 2-cell-equivalent loop. -/
theorem meridian_right_unit_route_2cell (x y : X) :
    RwEq
      (Path.trans
        (Path.trans
          (SuspensionLoop.Suspension.merid (X := X) x)
          (Path.refl (SuspensionLoop.Suspension.south (X := X))))
        (Path.symm (SuspensionLoop.Suspension.merid (X := X) y)))
      (meridianLoop (X := X) x y) := by
  have h :
      RwEq
        (Path.trans
          (SuspensionLoop.Suspension.merid (X := X) x)
          (Path.refl (SuspensionLoop.Suspension.south (X := X))))
        (SuspensionLoop.Suspension.merid (X := X) x) :=
    rweq_cmpA_refl_right (SuspensionLoop.Suspension.merid (X := X) x)
  exact rweq_trans_congr_left
    (Path.symm (SuspensionLoop.Suspension.merid (X := X) y)) h

/-- The meridian loop with equal endpoints contracts to reflexivity by a 2-cell. -/
theorem meridian_cancel_routes_2cell (x : X) :
    RwEq
      (meridianLoop (X := X) x x)
      (Path.refl (SuspensionLoop.Suspension.north (X := X))) :=
  rweq_cmpA_inv_right (SuspensionLoop.Suspension.merid (X := X) x)

end Suspension
end Homotopy
end Path
end ComputationalPaths
