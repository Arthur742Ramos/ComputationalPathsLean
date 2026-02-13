/-!
# Higher Route 2-cells for Homotopy Groups

This module records explicit higher-path witnesses (`RwEq` / 2-cells) connecting
different computational routes that start and end at the same loops.
-/

import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HomotopyGroup

universe u

variable {A : Type u} {a : A}

/-- Two associativity routes for triple loop composition are connected by a 2-cell. -/
theorem pi1_assoc_routes_2cell (p q r : LoopSpace A a) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- The unit-then-cancel route contracts to reflexivity via a 2-cell. -/
theorem pi1_unit_inverse_routes_2cell (p : LoopSpace A a) :
    RwEq
      (Path.trans (Path.trans (Path.refl a) p) (Path.symm p))
      (Path.refl a) := by
  have h₁ :
      RwEq
        (Path.trans (Path.trans (Path.refl a) p) (Path.symm p))
        (Path.trans p (Path.symm p)) :=
    rweq_trans_congr_left (Path.symm p) (rweq_cmpA_refl_left p)
  exact rweq_trans h₁ (rweq_cmpA_inv_right p)

/-- In `π₂`, vertical and horizontal routes are connected by a higher 2-cell witness. -/
theorem pi2_vertical_horizontal_routes_2cell
    (α β : HigherHomotopy.Loop2Space A a) :
    HigherHomotopy.Loop2Eq
      (HigherHomotopy.Loop2Space.vcomp α β)
      (HigherHomotopy.Loop2Space.hcomp α β) :=
  HigherHomotopy.eckmann_hilton_vcomp_eq_hcomp α β

end HomotopyGroup
end Homotopy
end Path
end ComputationalPaths
