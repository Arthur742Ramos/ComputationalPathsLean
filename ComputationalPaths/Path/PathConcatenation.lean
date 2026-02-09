/-
# Path concatenation laws

Advanced associativity and unit results for concatenation in the path groupoid
(`PathRwQuot`). These lemmas provide right-associated normal forms and triangle
identities for nested concatenations.

## Key Results
- `trans_four_assoc`: Four-fold associativity.
- `trans_five_assoc`: Five-fold associativity.
- `trans_triangle`: Triangle identity for units.
- `trans_refl_left_assoc`: Remove a left unit inside nested concatenation.
- `trans_refl_right_assoc`: Remove a right unit inside nested concatenation.

## References
- Mac Lane, Categories for the Working Mathematician.
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths".
-/

import Mathlib
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths.Path

/-! ## Concatenation laws for `PathRwQuot` -/

namespace PathConcatenation

universe u

variable {A : Type u} {a b c d e f : A}

/-- Four-fold associativity for path concatenation in the quotient groupoid. -/
theorem trans_four_assoc (p : PathRwQuot A a b) (q : PathRwQuot A b c)
    (r : PathRwQuot A c d) (s : PathRwQuot A d e) :
    PathRwQuot.trans (PathRwQuot.trans (PathRwQuot.trans p q) r) s =
      PathRwQuot.trans p (PathRwQuot.trans q (PathRwQuot.trans r s)) := by
  simp

/-- Five-fold associativity for path concatenation in the quotient groupoid. -/
theorem trans_five_assoc (p : PathRwQuot A a b) (q : PathRwQuot A b c)
    (r : PathRwQuot A c d) (s : PathRwQuot A d e) (t : PathRwQuot A e f) :
    PathRwQuot.trans
        (PathRwQuot.trans (PathRwQuot.trans (PathRwQuot.trans p q) r) s) t =
      PathRwQuot.trans p
        (PathRwQuot.trans q (PathRwQuot.trans r (PathRwQuot.trans s t))) := by
  simp

/-- Triangle identity: (p * refl) * q collapses to p * q. -/
theorem trans_triangle (p : PathRwQuot A a b) (q : PathRwQuot A b c) :
    PathRwQuot.trans (PathRwQuot.trans p (PathRwQuot.refl (A := A) b)) q =
      PathRwQuot.trans p q := by
  simp

/-- Left unit inside a nested concatenation can be removed. -/
theorem trans_refl_left_assoc (p : PathRwQuot A a b) (q : PathRwQuot A b c) :
    PathRwQuot.trans (PathRwQuot.trans (PathRwQuot.refl (A := A) a) p) q =
      PathRwQuot.trans p q := by
  simp

/-- Right unit inside a nested concatenation can be removed. -/
theorem trans_refl_right_assoc (p : PathRwQuot A a b) (q : PathRwQuot A b c) :
    PathRwQuot.trans p (PathRwQuot.trans (PathRwQuot.refl (A := A) b) q) =
      PathRwQuot.trans p q := by
  simp

/-! ## Summary -/

/-!
This module records higher associativity and triangle-style unit identities for
path concatenation in the strict path groupoid `PathRwQuot`.
-/

end PathConcatenation
end ComputationalPaths.Path
