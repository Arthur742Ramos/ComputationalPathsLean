import ComputationalPaths.Path.Homotopy.Loops

/-!
# Loop-space path-of-path routes

This module isolates explicit 2-cells connecting alternative
parenthesizations of iterated loop composition.
-/

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpace

universe u

/-- Local alias for ordinary loops. -/
abbrev BaseLoop (A : Type u) (a : A) : Type u :=
  ComputationalPaths.Path.LoopSpace A a

/-- A 2-cell between parallel computational paths. -/
abbrev TwoCell {A : Type u} {x y : A} (p q : Path x y) : Prop := RwEq p q

/-- Left-associated route through four loop composites. -/
def routeLeft {A : Type u} {a : A} (p q r s : BaseLoop A a) : BaseLoop A a :=
  Path.trans (Path.trans (Path.trans p q) r) s

/-- Middle route through four loop composites. -/
def routeMiddle {A : Type u} {a : A} (p q r s : BaseLoop A a) : BaseLoop A a :=
  Path.trans p (Path.trans (Path.trans q r) s)

/-- Right-associated route through four loop composites. -/
def routeRight {A : Type u} {a : A} (p q r s : BaseLoop A a) : BaseLoop A a :=
  Path.trans p (Path.trans q (Path.trans r s))

/-- The first rerouting step (left to middle) is a 2-cell. -/
theorem left_to_middle_two_cell {A : Type u} {a : A}
    (p q r s : BaseLoop A a) :
    TwoCell (routeLeft p q r s) (routeMiddle p q r s) := by
  exact RwEq.trans
    (rweq_trans_congr_left s (rweq_tt p q r))
    (rweq_tt p (Path.trans q r) s)

/-- The second rerouting step (middle to right) is a 2-cell. -/
theorem middle_to_right_two_cell {A : Type u} {a : A}
    (p q r s : BaseLoop A a) :
    TwoCell (routeMiddle p q r s) (routeRight p q r s) :=
  rweq_trans_congr_right p (rweq_tt q r s)

/-- Any two standard routes from left-associated to right-associated coincide up to a 2-cell. -/
theorem left_to_right_two_cell {A : Type u} {a : A}
    (p q r s : BaseLoop A a) :
    TwoCell (routeLeft p q r s) (routeRight p q r s) := by
  exact RwEq.trans (left_to_middle_two_cell p q r s) (middle_to_right_two_cell p q r s)

/-! ## Unit, inverse, and iterated-path routes -/

/-- Left-unit route for loops. -/
def leftUnitRoute {A : Type u} {a : A} (p : BaseLoop A a) : BaseLoop A a :=
  Path.trans (Path.refl a) p

/-- Right-unit route for loops. -/
def rightUnitRoute {A : Type u} {a : A} (p : BaseLoop A a) : BaseLoop A a :=
  Path.trans p (Path.refl a)

/-- Left unit contraction is a 2-cell. -/
theorem left_unit_two_cell {A : Type u} {a : A} (p : BaseLoop A a) :
    TwoCell (leftUnitRoute p) p :=
  rweq_cmpA_refl_left p

/-- Right unit contraction is a 2-cell. -/
theorem right_unit_two_cell {A : Type u} {a : A} (p : BaseLoop A a) :
    TwoCell (rightUnitRoute p) p :=
  rweq_cmpA_refl_right p

/-- Left inverse cancellation is a 2-cell. -/
theorem inverse_left_two_cell {A : Type u} {a : A} (p : BaseLoop A a) :
    TwoCell (Path.trans (Path.symm p) p) (Path.refl a) :=
  rweq_cmpA_inv_left p

/-- Right inverse cancellation is a 2-cell. -/
theorem inverse_right_two_cell {A : Type u} {a : A} (p : BaseLoop A a) :
    TwoCell (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right p

/-- Pointed data for iterated loop/path spaces. -/
def iteratedLoopPointedData {A : Type u} (a : A) : Nat → Sigma fun X : Type u => X
  | 0 => ⟨A, a⟩
  | n + 1 =>
      let prev := iteratedLoopPointedData a n
      ⟨LoopSpace prev.1 prev.2, Path.refl prev.2⟩

/-- The `n`-fold iterated loop space is an iterated path space. -/
abbrev iteratedPathSpace {A : Type u} (a : A) (n : Nat) : Type u :=
  (iteratedLoopPointedData a n).1

end LoopSpace
end Homotopy
end Path
end ComputationalPaths
