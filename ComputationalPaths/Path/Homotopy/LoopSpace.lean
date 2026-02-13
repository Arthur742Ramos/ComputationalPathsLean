/-!
# Higher Route 2-cells for Loop Spaces

This module records rewrite-equivalence 2-cells between alternate loop
composition routes.
-/

import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpaceRoutes

universe u

variable {A : Type u} {a : A}

/-- The two parenthesizations of triple loop composition are connected by a 2-cell. -/
theorem assoc_routes_2cell (p q r : LoopSpace A a) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Left- and right-whiskered unit routes are connected by a 2-cell. -/
theorem whisker_unit_routes_2cell (p q : LoopSpace A a) :
    RwEq
      (Path.trans (Path.refl a) (Path.trans p q))
      (Path.trans (Path.trans p q) (Path.refl a)) := by
  have h₁ :
      RwEq
        (Path.trans (Path.refl a) (Path.trans p q))
        (Path.trans p q) :=
    rweq_cmpA_refl_left (Path.trans p q)
  have h₂ :
      RwEq
        (Path.trans (Path.trans p q) (Path.refl a))
        (Path.trans p q) :=
    rweq_cmpA_refl_right (Path.trans p q)
  exact rweq_trans h₁ (rweq_symm h₂)

/-- Cancellation followed by right-unit normalizes to reflexivity through a 2-cell chain. -/
theorem inverse_cancellation_routes_2cell (p : LoopSpace A a) :
    RwEq
      (Path.trans (Path.trans p (Path.symm p)) (Path.refl a))
      (Path.refl a) := by
  have h₁ :
      RwEq
        (Path.trans (Path.trans p (Path.symm p)) (Path.refl a))
        (Path.trans (Path.refl a) (Path.refl a)) :=
    rweq_trans_congr_left (Path.refl a) (rweq_cmpA_inv_right p)
  exact rweq_trans h₁ (rweq_cmpA_refl_left (Path.refl a))

end LoopSpaceRoutes
end Homotopy
end Path
end ComputationalPaths
