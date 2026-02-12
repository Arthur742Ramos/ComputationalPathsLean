/-
# Path concatenation laws

Advanced associativity and unit results for concatenation in the path groupoid
(`Path`) up to `RwEq`. These lemmas provide right-associated normal forms and
triangle identities for nested concatenations.

## Key Results
- `trans_four_assoc`: Four-fold associativity.
- `trans_five_assoc`: Five-fold associativity.
- `trans_triangle`: Triangle identity for units.
- `trans_refl_left_assoc`: Remove a left unit inside nested concatenation.
- `trans_refl_right_assoc`: Remove a right unit inside nested concatenation.
- `trans_unit_swap`: Left- and right-unit insertions are RwEq-equivalent.

## References
- Mac Lane, Categories for the Working Mathematician.
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths".
-/

import ComputationalPaths.Path.PathAlgebraDerived
import ComputationalPaths.Path.CoherenceDerived

namespace ComputationalPaths.Path

/-! ## Concatenation laws for `Path` -/

namespace PathConcatenation

universe u

variable {A : Type u} {a b c d e f : A}

/-- Four-fold associativity for path concatenation. -/
theorem trans_four_assoc (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s) (trans p (trans q (trans r s))) := by
  exact PathAlgebraDerived.rweq_trans_four_assoc (p := p) (q := q) (r := r) (s := s)

/-- Five-fold associativity for path concatenation. -/
theorem trans_five_assoc (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e)
    (t : Path e f) :
    RwEq (trans (trans (trans (trans p q) r) s) t) (trans p (trans q (trans r (trans s t)))) := by
  exact CoherenceDerived.rweq_trans_five_assoc p q r s t

/-- Triangle identity: (p · refl) · q collapses to p · q. -/
theorem trans_triangle (p : Path a b) (q : Path b c) :
    RwEq (trans (trans p (refl b)) q) (trans p q) := by
  exact CoherenceDerived.rweq_triangle_full p q

/-- Left unit inside a nested concatenation can be removed. -/
theorem trans_refl_left_assoc (p : Path a b) (q : Path b c) :
    RwEq (trans (trans (refl a) p) q) (trans p q) := by
  exact rweq_trans_congr_left q (PathAlgebraDerived.rweq_refl_trans p)

/-- Right unit inside a nested concatenation can be removed. -/
theorem trans_refl_right_assoc (p : Path a b) (q : Path b c) :
    RwEq (trans p (trans (refl b) q)) (trans p q) := by
  exact rweq_trans_congr_right p (PathAlgebraDerived.rweq_refl_trans q)

/-! ## RwEq examples -/

/-- Two different unit insertions for a path are RwEq-equivalent. -/
theorem trans_unit_swap (p : Path a b) :
    RwEq (trans (refl a) p) (trans p (refl b)) := by
  apply rweq_trans (rweq_cmpA_refl_left (p := p))
  exact rweq_symm (rweq_cmpA_refl_right (p := p))

/-! ## Summary -/

/-!
This module records higher associativity and triangle-style unit identities for
path concatenation in terms of `RwEq` on `Path`.
-/

end PathConcatenation
end ComputationalPaths.Path
