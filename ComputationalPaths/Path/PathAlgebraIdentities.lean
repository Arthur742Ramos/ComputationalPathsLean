/-
# Path Algebra Identities

Additional axiom-free algebraic identities for computational paths, extending
the coherence results in `CoherenceDerived`.

## Key Results

- `rweq_mac_lane_five_split`: Mac Lane coherence beyond the pentagon.
- `rweq_triangle_identity`: triangle identity for associator and unit.
- `rweq_hexagon_braiding`: hexagon identity for the inversion braiding.

## References

- Mac Lane, "Categories for the Working Mathematician"
- Lumsdaine, "Weak omega-categories from intensional type theory"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.CoherenceDerived

namespace ComputationalPaths
namespace Path
namespace PathAlgebraIdentities

open Step

universe u

variable {A : Type u} {a b c d e f' : A}

/-! ## Mac Lane Coherence Beyond Pentagon -/

/-- Reassociate ((p * q) * r) * (s * t) to p * (q * (r * (s * t))). -/
noncomputable def rweq_mac_lane_five_split {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} {t : Path e f'} :
    RwEq (trans (trans (trans p q) r) (trans s t))
         (trans p (trans q (trans r (trans s t)))) := by
  have h1 :
      RwEq (trans (trans (trans p q) r) (trans s t))
           (trans (trans p q) (trans r (trans s t))) :=
    rweq_of_step (Step.trans_assoc (trans p q) r (trans s t))
  have h2 :
      RwEq (trans (trans p q) (trans r (trans s t)))
           (trans p (trans q (trans r (trans s t)))) :=
    rweq_of_step (Step.trans_assoc p q (trans r (trans s t)))
  exact RwEq.trans h1 h2

/-! ## Triangle Identity -/

/-- Triangle identity: (f * refl) * g reduces to f * g. -/
noncomputable def rweq_triangle_identity (f : Path a b) (g : Path b c) :
    RwEq (trans (trans f (refl b)) g) (trans f g) :=
  CoherenceDerived.rweq_triangle_full f g

/-! ## Hexagon Identity for the Inversion Braiding -/

/-- Hexagon identity for inversion: symm (p * q * r) reduces to symm r * symm q * symm p. -/
noncomputable def rweq_hexagon_braiding (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (trans (trans p q) r))
         (trans (symm r) (trans (symm q) (symm p))) :=
  CoherenceDerived.rweq_symm_trans_assoc p q r

/-! ## Summary -/

/-!
This module records additional coherence identities derived from the
computational path rewrite system, focusing on Mac Lane coherence beyond the
pentagon, the triangle identity, and a hexagon identity for inversion.
-/

end PathAlgebraIdentities
end Path
end ComputationalPaths
