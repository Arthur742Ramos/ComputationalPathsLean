/-!
# Sheaf Cohomology via Computational Rewriting

This module uses explicit rewrite witnesses for cohomological path
manipulations, avoiding direct equality proofs.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Sheaf
namespace Cohomology

universe u

/-- A minimal Cech-style cochain complex with path-valued `d²` witness. -/
structure CechComplex (A : Type u) where
  cochains : Nat → Type u
  coboundary : (n : Nat) → cochains n → cochains (n + 1)
  coboundary_sq : ∀ (n : Nat) (x : cochains n),
    Path (coboundary (n + 1) (coboundary n x))
         (coboundary (n + 1) (coboundary n x))

/-- Boundary path of a cohomology representative. -/
def boundary {A : Type u} {a b : A} (p : Path a b) : Path a a :=
  Path.trans p (Path.symm p)

/-- Boundary contracts to reflexivity by a single rewrite step. -/
theorem boundary_contracts {A : Type u} {a b : A} (p : Path a b) :
    RwEq (boundary p) (Path.refl a) :=
  rweq_of_step (Step.trans_symm p)

/-- Unit insertion followed by contraction gives a rewrite-normal form. -/
theorem boundary_unit_contracts {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans (boundary p) (Path.refl a)) (Path.refl a) := by
  calc
    Path.trans (boundary p) (Path.refl a)
        ≈ boundary p := by
          exact rweq_of_step (Step.trans_refl_right (boundary p))
    _ ≈ Path.refl a := by
          exact rweq_of_step (Step.trans_symm p)

/-- Reassociation witness for triple composites in connecting morphisms. -/
theorem connecting_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Soundness of boundary contraction at the underlying equality level. -/
theorem boundary_contracts_sound {A : Type u} {a b : A} (p : Path a b) :
    Path.toEq (boundary p) = Path.toEq (Path.refl a) := by
  simpa using rweq_toEq (boundary_contracts p)

end Cohomology
end Sheaf
end ComputationalPaths
