/-
# Higher Groupoid Coherence for the Path Bicategory

This module proves the bicategorical pentagon identity for associator 2-cells
in the path bicategory, showing the five-way reassociation diagram commutes.

## Key Results

- `pentagon_left`/`pentagon_right`: the two composite associator 2-cells
- `pentagon_identity`: the pentagon diagram commutes

## References

- Mac Lane, "Categories for the Working Mathematician"
- Leinster, "Higher Operads, Higher Categories"
-/

import ComputationalPaths.Path.BicategoryDerived

namespace ComputationalPaths
namespace Path

/-! ## Pentagon identity for associators -/

namespace HigherGroupoidCoherence

open TwoCell

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- Left route in the pentagon: two associators. -/
def pentagon_left (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  comp (assoc (Path.trans p q) r s) (assoc p q (Path.trans r s))

/-- Right route in the pentagon: three associators with whiskering. -/
def pentagon_right (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    TwoCell (A := A) (a := a) (b := e)
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) :=
  comp
    (comp (whiskerRight (h := s) (assoc p q r))
      (assoc p (Path.trans q r) s))
    (whiskerLeft (f := p) (assoc q r s))

/-- Pentagon identity: the five-way reassociation diagram commutes. -/
@[simp] theorem pentagon_identity (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    pentagon_left p q r s = pentagon_right p q r s := by
  apply Subsingleton.elim

end HigherGroupoidCoherence

/-! ## Summary -/

/-!
We record the pentagon identity for path associators as the equality of the two
composite 2-cells between the extreme parenthesizations.
-/

end Path
end ComputationalPaths
