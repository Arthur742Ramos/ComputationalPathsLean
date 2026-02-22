/- 
# Spectral sequence pages with computational paths

This module packages page transition data with explicit `Path.Step` witnesses
and derived `RwEq` coherence lemmas.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- Path-level data for spectral-sequence pages. -/
structure SpectralPagePaths where
  /-- Terms at each bidegree. -/
  term : Nat → Nat → Type u
  /-- Chosen base term at each bidegree. -/
  base : (p q : Nat) → term p q
  /-- Transition map `E_{r+1} → E_r`. -/
  next : (r p q : Nat) → term p q → term p q
  /-- Chosen two-step transition map `E_{r+2} → E_r`. -/
  twoStep : (r p q : Nat) → term p q → term p q
  /-- Coherence of two-step transition with iterated transition. -/
  twoStepPath :
    ∀ (r p q : Nat) (x : term p q),
      Path (twoStep r p q x) (next r p q (next (r + 1) p q x))
  /-- Primitive computational rewrite witness for right-unit normalization. -/
  twoStepStep :
    ∀ (r p q : Nat) (x : term p q),
      Path.Step
        (Path.trans (twoStepPath r p q x)
          (Path.refl (next r p q (next (r + 1) p q x))))
        (twoStepPath r p q x)

namespace SpectralPagePaths

variable (E : SpectralPagePaths)

noncomputable def twoStep_rweq (r p q : Nat) (x : E.term p q) :
    RwEq
      (Path.trans (E.twoStepPath r p q x)
        (Path.refl (E.next r p q (E.next (r + 1) p q x))))
      (E.twoStepPath r p q x) :=
  rweq_of_step (E.twoStepStep r p q x)

noncomputable def twoStep_cancel_left_rweq (r p q : Nat) (x : E.term p q) :
    RwEq
      (Path.trans (Path.symm (E.twoStepPath r p q x)) (E.twoStepPath r p q x))
      (Path.refl (E.next r p q (E.next (r + 1) p q x))) :=
  rweq_cmpA_inv_left (E.twoStepPath r p q x)

noncomputable def twoStep_cancel_right_rweq (r p q : Nat) (x : E.term p q) :
    RwEq
      (Path.trans (E.twoStepPath r p q x) (Path.symm (E.twoStepPath r p q x)))
      (Path.refl (E.twoStep r p q x)) :=
  rweq_cmpA_inv_right (E.twoStepPath r p q x)

end SpectralPagePaths

/-- Trivial spectral-page path package. -/
noncomputable def trivialSpectralPagePaths : SpectralPagePaths where
  term := fun _ _ => PUnit
  base := fun _ _ => PUnit.unit
  next := fun _ _ _ _ => PUnit.unit
  twoStep := fun _ _ _ _ => PUnit.unit
  twoStepPath := fun _ _ _ _ => Path.refl PUnit.unit
  twoStepStep := fun _ _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end SpectralSequence
end ComputationalPaths
