/-!
# Stack Condition via Computational Rewriting

This module records stack-condition coherence with explicit rewrite witnesses.
Equalities are represented by `Path`, and proof normalization is exposed via
`Step`-generated `RwEq` chains.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Sheaf
namespace StackCondition

universe u

/-- Descent transport data indexed by computational paths. -/
structure DescentTransition (Idx : Type u) (Fiber : Idx → Type u) where
  transport : {i j : Idx} → Path i j → Fiber i → Fiber j
  transport_refl : ∀ (i : Idx) (x : Fiber i),
    Path (transport (Path.refl i) x) x
  transport_trans : ∀ {i j k : Idx} (p : Path i j) (q : Path j k) (x : Fiber i),
    Path (transport (Path.trans p q) x) (transport q (transport p x))

/-- Left-unit normalization for stack transport composition. -/
theorem transport_left_unit {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Right-unit normalization for stack transport composition. -/
theorem transport_right_unit {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Associativity witness for triple transport composition. -/
theorem transport_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- A two-step rewrite witness replacing direct equality reasoning. -/
theorem transport_cancel_normalize {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) q) q := by
  calc
    Path.trans (Path.trans p (Path.symm p)) q
        ≈ Path.trans (Path.refl a) q := by
          exact rweq_trans_congr_left q (rweq_of_step (Step.trans_symm p))
    _ ≈ q := by
          exact rweq_of_step (Step.trans_refl_left q)

/-- The rewrite witness induces the expected propositional equality. -/
theorem transport_cancel_sound {A : Type u} {a b c : A}
    (p : Path a b) (q : Path a c) :
    Path.toEq (Path.trans (Path.trans p (Path.symm p)) q) = Path.toEq q := by
  simpa using rweq_toEq (transport_cancel_normalize p q)

end StackCondition
end Sheaf
end ComputationalPaths
