/-
# Derived Path Algebra Lemmas

This module provides higher associativity and unit lemmas for path
concatenation, expressed as rewrite equivalences.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace PathAlgebraDerived

universe u

variable {A : Type u} {a b c d e : A}

/-! ## Higher associativity -/

/-- Four-fold associativity for path concatenation. -/
theorem rweq_trans_four_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
      (trans p (trans q (trans r s))) := by
  have h1 :
      RwEq (trans (trans (trans p q) r) s)
        (trans (trans p q) (trans r s)) :=
    rweq_tt (trans p q) r s
  have h2 :
      RwEq (trans (trans p q) (trans r s))
        (trans p (trans q (trans r s))) :=
    rweq_tt p q (trans r s)
  exact RwEq.trans h1 h2

/-! ## Unit laws -/

/-- Left unit for path concatenation. -/
theorem rweq_refl_trans (p : Path a b) :
    RwEq (trans (refl a) p) p :=
  rweq_cmpA_refl_left (p := p)

end PathAlgebraDerived
end Path
end ComputationalPaths
