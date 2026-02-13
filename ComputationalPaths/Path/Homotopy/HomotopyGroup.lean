import ComputationalPaths.Path.Homotopy.HigherHomotopyGroups
import ComputationalPaths.Path.Homotopy.Loops

/-!
# Higher-path routes for homotopy groups

This module records explicit 2-cells (`RwEq`) showing that different
computational routes between the same loop endpoints are connected.
-/

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace HomotopyGroup

universe u

/-- A 2-cell between parallel computational paths. -/
abbrev TwoCell {A : Type u} {x y : A} (p q : Path x y) : Prop := RwEq p q

/-- Associative rerouting of loop composition gives a canonical 2-cell. -/
theorem loop_assoc_two_cell {A : Type u} {a : A}
    (p q r : LoopSpace A a) :
    TwoCell (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  LoopSpace.comp_assoc_rweq (A := A) (a := a) p q r

/-- The two standard cancellation routes are connected by a 2-cell. -/
theorem cancellation_route_two_cell {A : Type u} {a : A}
    (p : LoopSpace A a) :
    TwoCell
      (Path.trans (Path.trans p (Path.symm p)) p)
      (Path.trans p (Path.trans (Path.symm p) p)) :=
  rweq_tt p (Path.symm p) p

/-- Whiskering cancellation on the right contracts back to `p`. -/
theorem cancellation_contracts_two_cell {A : Type u} {a : A}
    (p : LoopSpace A a) :
    TwoCell (Path.trans p (Path.trans (Path.symm p) p)) p := by
  refine RwEq.trans ?_ (rweq_cmpA_refl_right p)
  exact rweq_trans_congr_right p (LoopSpace.loop_cancel_left (A := A) (a := a) p)

/-- Higher homotopy multiplication is path-associative (`n ≥ 2`). -/
def piN_mul_assoc_path {X : Type u} (n : Nat) [Nat.AtLeastTwo n] (x : X)
    (α β γ : HigherHomotopyGroups.PiN n X x) :
    Path
      (HigherHomotopyGroups.piN_mul n x (HigherHomotopyGroups.piN_mul n x α β) γ)
      (HigherHomotopyGroups.piN_mul n x α (HigherHomotopyGroups.piN_mul n x β γ)) :=
  HigherHomotopyGroups.piN_mul_assoc (n := n) (x := x) α β γ

end HomotopyGroup
end Homotopy
end Path
end ComputationalPaths
