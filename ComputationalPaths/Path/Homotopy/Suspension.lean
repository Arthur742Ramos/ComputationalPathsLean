import ComputationalPaths.Path.Homotopy.SuspensionLoop

/-!
# Suspension higher-path routes

This module records 2-cells connecting alternative computational routes that
appear in suspension-loop constructions.
-/

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace Suspension

open SuspensionLoop

universe u

/-- A 2-cell between parallel computational paths. -/
abbrev TwoCell {A : Type u} {x y : A} (p q : Path x y) : Prop := RwEq p q

/-- The adjunction basepoint loop contracts to reflexivity through a 2-cell. -/
theorem adjMap_basepoint_two_cell {X : Type u} (x₀ : X) {Y : Pointed}
    (f : SuspensionLoop.Suspension X → Y.carrier)
    (hf : f (SuspensionLoop.Suspension.north (X := X)) = Y.pt) :
    TwoCell (adjMap x₀ f hf x₀) (Path.refl Y.pt) :=
  adjMap_basepoint_rweq x₀ f hf

/-- Rebracketing a whiskered meridian cancellation yields a 2-cell in `ΣX`. -/
theorem meridian_whisker_assoc_two_cell {X : Type u} (x y : X) :
    TwoCell
      (Path.trans
        (Path.trans
          (SuspensionLoop.Suspension.merid (X := X) x)
          (Path.symm (SuspensionLoop.Suspension.merid (X := X) x)))
        (SuspensionLoop.Suspension.merid (X := X) y))
      (Path.trans
        (SuspensionLoop.Suspension.merid (X := X) x)
        (Path.trans
          (Path.symm (SuspensionLoop.Suspension.merid (X := X) x))
          (SuspensionLoop.Suspension.merid (X := X) y))) :=
  rweq_tt
    (SuspensionLoop.Suspension.merid (X := X) x)
    (Path.symm (SuspensionLoop.Suspension.merid (X := X) x))
    (SuspensionLoop.Suspension.merid (X := X) y)

/-- The whiskered cancellation route contracts to the direct meridian route. -/
theorem meridian_whisker_contracts_two_cell {X : Type u} (x y : X) :
    TwoCell
      (Path.trans
        (Path.trans
          (SuspensionLoop.Suspension.merid (X := X) x)
          (Path.symm (SuspensionLoop.Suspension.merid (X := X) x)))
        (SuspensionLoop.Suspension.merid (X := X) y))
      (SuspensionLoop.Suspension.merid (X := X) y) := by
  refine RwEq.trans ?_ (rweq_cmpA_refl_left (SuspensionLoop.Suspension.merid (X := X) y))
  exact rweq_trans_congr_left
    (SuspensionLoop.Suspension.merid (X := X) y)
    (rweq_cmpA_inv_right (SuspensionLoop.Suspension.merid (X := X) x))

end Suspension
end Homotopy
end Path
end ComputationalPaths
