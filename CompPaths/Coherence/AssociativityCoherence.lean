import CompPaths.Core

namespace CompPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- The associator higher path witnessing associativity of `Path.trans`. -/
@[simp] theorem associator (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

/-- Left route in Mac Lane's pentagon for four composable paths. -/
theorem pentagon_left_route (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  apply RwEq.trans (rweq_trans_congr_left s (associator p q r))
  apply RwEq.trans (associator p (Path.trans q r) s)
  exact rweq_trans_congr_right p (associator q r s)

/-- Right route in Mac Lane's pentagon for four composable paths. -/
theorem pentagon_right_route (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  exact RwEq.trans (associator (Path.trans p q) r s) (associator p q (Path.trans r s))

/-- Mac Lane pentagon coherence: both canonical pentagon routes coincide. -/
theorem mac_lane_pentagon (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    pentagon_left_route p q r s = pentagon_right_route p q r s := by
  apply Subsingleton.elim

end CompPaths.Coherence
