/- 
# Spectral sequence differentials with computational paths

This module packages differential data with explicit `Path` witnesses for
`d² = 0` and page-transition compatibility, together with `RwEq` consequences.
-/

import ComputationalPaths.SpectralSequence.Pages

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- Path-level data for differentials on a page package. -/
structure Differentials (E : Pages.{u}) where
  /-- Differential map on each page and bidegree. -/
  d : (r p q : Nat) → E.term p q → E.term p q
  /-- Path witness for `d² = 0` at the chosen base term. -/
  dSquaredPath :
    ∀ (r p q : Nat),
      Path (d r p q (d r p q (E.base p q))) (E.base p q)
  /-- Primitive rewrite witness for right-unit normalization on `d² = 0`. -/
  dSquaredStep :
    ∀ (r p q : Nat),
      Path.Step
        (Path.trans (dSquaredPath r p q) (Path.refl (E.base p q)))
        (dSquaredPath r p q)
  /-- Path witness that differential commutes with page transition on base terms. -/
  commutePath :
    ∀ (r p q : Nat),
      Path (E.shift r p q (d r p q (E.base p q)))
        (d (r + 1) p q (E.shift r p q (E.base p q)))
  /-- Primitive rewrite witness for left-unit normalization on commutation paths. -/
  commuteStep :
    ∀ (r p q : Nat),
      Path.Step
        (Path.trans
          (Path.refl (E.shift r p q (d r p q (E.base p q))))
          (commutePath r p q))
        (commutePath r p q)

namespace Differentials

variable {E : Pages.{u}} (D : Differentials E)

noncomputable def d_squared_rweq (r p q : Nat) :
    RwEq
      (Path.trans (D.dSquaredPath r p q) (Path.refl (E.base p q)))
      (D.dSquaredPath r p q) :=
  rweq_of_step (D.dSquaredStep r p q)

noncomputable def d_squared_cancel_rweq (r p q : Nat) :
    RwEq
      (Path.trans (Path.symm (D.dSquaredPath r p q)) (D.dSquaredPath r p q))
      (Path.refl (E.base p q)) :=
  rweq_cmpA_inv_left (D.dSquaredPath r p q)

noncomputable def commute_rweq (r p q : Nat) :
    RwEq
      (Path.trans
        (Path.refl (E.shift r p q (D.d r p q (E.base p q))))
        (D.commutePath r p q))
      (D.commutePath r p q) :=
  rweq_of_step (D.commuteStep r p q)

noncomputable def commute_cancel_rweq (r p q : Nat) :
    RwEq
      (Path.trans (Path.symm (D.commutePath r p q)) (D.commutePath r p q))
      (Path.refl (D.d (r + 1) p q (E.shift r p q (E.base p q)))) :=
  rweq_cmpA_inv_left (D.commutePath r p q)

/-- Composite boundary loop induced by the `d² = 0` witness. -/
def boundaryLoop (r p q : Nat) :
    Path (D.d r p q (D.d r p q (E.base p q))) (D.d r p q (D.d r p q (E.base p q))) :=
  Path.trans (D.dSquaredPath r p q) (Path.symm (D.dSquaredPath r p q))

noncomputable def boundaryLoop_contracts (r p q : Nat) :
    RwEq (D.boundaryLoop r p q)
      (Path.refl (D.d r p q (D.d r p q (E.base p q)))) := by
  unfold boundaryLoop
  exact rweq_cmpA_inv_right (D.dSquaredPath r p q)

/-- Apply page transition to the `d² = 0` witness. -/
def stabilizedBoundary (r p q : Nat) :
    Path
      (E.shift r p q (D.d r p q (D.d r p q (E.base p q))))
      (E.shift r p q (E.base p q)) :=
  Path.congrArg (E.shift r p q) (D.dSquaredPath r p q)

noncomputable def stabilizedBoundary_contracts (r p q : Nat) :
    RwEq
      (Path.trans (D.stabilizedBoundary r p q) (Path.symm (D.stabilizedBoundary r p q)))
      (Path.refl (E.shift r p q (D.d r p q (D.d r p q (E.base p q))))) :=
  rweq_cmpA_inv_right (D.stabilizedBoundary r p q)

end Differentials

/-- Trivial differential package over the trivial page package. -/
def trivialDifferentials : Differentials trivialPages where
  d := fun _ _ _ _ => PUnit.unit
  dSquaredPath := fun _ _ _ => Path.refl PUnit.unit
  dSquaredStep := fun _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  commutePath := fun _ _ _ => Path.refl PUnit.unit
  commuteStep := fun _ _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

end SpectralSequence
end ComputationalPaths
