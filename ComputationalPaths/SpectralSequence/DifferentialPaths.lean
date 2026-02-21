/- 
# Spectral sequence differentials with computational paths

This module packages differential data with explicit `Path` witnesses for
`d² = 0` and page-transition compatibility, together with `RwEq` consequences.
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.SpectralSequence.PagePaths

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- Path-level data for differentials on a spectral-page package. -/
structure DifferentialPaths (E : SpectralPagePaths.{u}) where
  /-- Differential map on each page and bidegree. -/
  d : (r p q : Nat) → E.term p q → E.term p q
  /-- Path witness for `d² = 0` at the chosen base term. -/
  dSquaredZeroPath :
    ∀ (r p q : Nat),
      Path (d r p q (d r p q (E.base p q))) (E.base p q)
  /-- Primitive rewrite witness for right-unit normalization on `d² = 0`. -/
  dSquaredZeroStep :
    ∀ (r p q : Nat),
      Path.Step
        (Path.trans (dSquaredZeroPath r p q) (Path.refl (E.base p q)))
        (dSquaredZeroPath r p q)
  /-- Path witness that differential commutes with page transition on base terms. -/
  commutePath :
    ∀ (r p q : Nat),
      Path (E.next r p q (d r p q (E.base p q)))
        (d (r + 1) p q (E.next r p q (E.base p q)))
  /-- Primitive rewrite witness for left-unit normalization on commutation paths. -/
  commuteStep :
    ∀ (r p q : Nat),
      Path.Step
        (Path.trans
          (Path.refl (E.next r p q (d r p q (E.base p q))))
          (commutePath r p q))
        (commutePath r p q)

namespace DifferentialPaths

variable {E : SpectralPagePaths.{u}} (D : DifferentialPaths E)

@[simp] theorem d_squared_rweq (r p q : Nat) :
    RwEq
      (Path.trans (D.dSquaredZeroPath r p q) (Path.refl (E.base p q)))
      (D.dSquaredZeroPath r p q) :=
  rweq_of_step (D.dSquaredZeroStep r p q)

@[simp] theorem d_squared_cancel_rweq (r p q : Nat) :
    RwEq
      (Path.trans (Path.symm (D.dSquaredZeroPath r p q)) (D.dSquaredZeroPath r p q))
      (Path.refl (E.base p q)) :=
  rweq_cmpA_inv_left (D.dSquaredZeroPath r p q)

@[simp] theorem commute_rweq (r p q : Nat) :
    RwEq
      (Path.trans
        (Path.refl (E.next r p q (D.d r p q (E.base p q))))
        (D.commutePath r p q))
      (D.commutePath r p q) :=
  rweq_of_step (D.commuteStep r p q)

@[simp] theorem commute_cancel_rweq (r p q : Nat) :
    RwEq
      (Path.trans (Path.symm (D.commutePath r p q)) (D.commutePath r p q))
      (Path.refl (D.d (r + 1) p q (E.next r p q (E.base p q)))) :=
  rweq_cmpA_inv_left (D.commutePath r p q)

/-- Composite boundary loop induced by the `d² = 0` witness. -/
def boundaryLoop (r p q : Nat) :
    Path (D.d r p q (D.d r p q (E.base p q))) (D.d r p q (D.d r p q (E.base p q))) :=
  Path.trans (D.dSquaredZeroPath r p q) (Path.symm (D.dSquaredZeroPath r p q))

@[simp] theorem boundaryLoop_contracts (r p q : Nat) :
    RwEq (D.boundaryLoop r p q)
      (Path.refl (D.d r p q (D.d r p q (E.base p q)))) := by
  unfold boundaryLoop
  exact rweq_cmpA_inv_right (D.dSquaredZeroPath r p q)

end DifferentialPaths

/-- Trivial differential package over the trivial page package. -/
def trivialDifferentialPaths : DifferentialPaths trivialSpectralPagePaths where
  d := fun _ _ _ _ => PUnit.unit
  dSquaredZeroPath := fun _ _ _ => Path.refl PUnit.unit
  dSquaredZeroStep := fun _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  commutePath := fun _ _ _ => Path.refl PUnit.unit
  commuteStep := fun _ _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

/-- Full spectral-sequence path package. -/
structure SpectralSequencePaths where
  pages : SpectralPagePaths
  differentials : DifferentialPaths pages

/-- Canonical trivial spectral-sequence path package. -/
def trivialSpectralSequencePaths : SpectralSequencePaths where
  pages := trivialSpectralPagePaths
  differentials := trivialDifferentialPaths

end SpectralSequence
end ComputationalPaths
