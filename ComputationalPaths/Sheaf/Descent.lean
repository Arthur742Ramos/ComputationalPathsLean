 /-
# Descent via Computational Rewriting

Descent coherence is expressed with explicit `Step`-based normalization,
replacing direct equality proofs by `RwEq` witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Sheaf
namespace Descent

universe u

open Path

/-- A descent datum with path-level cocycle witnesses. -/
structure DescentDatum (Idx : Type u) (Obj : Type u) where
  sec : Idx → Obj
  overlap : {i j : Idx} → Path i j → Path (sec i) (sec j)
  overlap_refl : ∀ (i : Idx),
    Path (overlap (Path.refl i)) (Path.refl (sec i))
  overlap_trans : ∀ {i j k : Idx} (p : Path i j) (q : Path j k),
    Path (overlap (Path.trans p q)) (Path.trans (overlap p) (overlap q))

/-- Cocycle reassociation as a single rewrite step. -/
noncomputable def cocycle_assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc p q r)

/-- Left inverse cancellation in descent gluing chains. -/
noncomputable def cancel_left_inverse {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_step (Step.symm_trans p)

/-- Right inverse cancellation in descent gluing chains. -/
noncomputable def cancel_right_inverse {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_step (Step.trans_symm p)

/-- Whiskered cancellation: normalize a descent composite by rewrite steps. -/
noncomputable def whisker_cancel {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans (Path.symm p) p) q) q := by
  exact rweq_trans
    (rweq_trans_congr_left q (rweq_of_step (Step.symm_trans p)))
    (rweq_of_step (Step.trans_refl_left q))

/-- Soundness of whiskered cancellation at the propositional layer. -/
theorem whisker_cancel_sound {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    Path.toEq (Path.trans (Path.trans (Path.symm p) p) q) = Path.toEq q := by
  exact rweq_toEq (whisker_cancel p q)

end Descent
end Sheaf
end ComputationalPaths
