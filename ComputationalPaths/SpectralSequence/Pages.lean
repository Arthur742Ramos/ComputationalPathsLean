/- 
# Spectral sequence pages with computational paths

This module packages page-transition data with explicit `Path.Step` witnesses
and derived `RwEq` coherence lemmas.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- Path-level data for spectral-sequence pages. -/
structure Pages where
  /-- Terms at each bidegree. -/
  term : Nat → Nat → Type u
  /-- Chosen base term at each bidegree. -/
  base : (p q : Nat) → term p q
  /-- Transition map `E_{r+1} → E_r`. -/
  shift : (r p q : Nat) → term p q → term p q
  /-- Chosen two-step transition map `E_{r+2} → E_r`. -/
  twoShift : (r p q : Nat) → term p q → term p q
  /-- Coherence of two-step transition with iterated transition. -/
  shiftPath :
    ∀ (r p q : Nat) (x : term p q),
      Path (twoShift r p q x) (shift r p q (shift (r + 1) p q x))
  /-- Primitive computational rewrite witness for right-unit normalization. -/
  shiftStep :
    ∀ (r p q : Nat) (x : term p q),
      Path.Step
        (Path.trans (shiftPath r p q x)
          (Path.refl (shift r p q (shift (r + 1) p q x))))
        (shiftPath r p q x)

namespace Pages

variable (E : Pages)

/-- One-step page advancement from the chosen base term. -/
def advanceBase (r p q : Nat) : E.term p q :=
  E.shift r p q (E.base p q)

/-- Two-step page advancement from the chosen base term. -/
def advanceBaseTwice (r p q : Nat) : E.term p q :=
  E.twoShift r p q (E.base p q)

/-- Coherence witness between chosen two-step and iterated one-step advancement. -/
def advanceBasePath (r p q : Nat) :
    Path (E.advanceBaseTwice r p q)
      (E.shift r p q (E.advanceBase (r + 1) p q)) :=
  E.shiftPath r p q (E.base p q)

noncomputable def shift_rweq (r p q : Nat) (x : E.term p q) :
    RwEq
      (Path.trans (E.shiftPath r p q x)
        (Path.refl (E.shift r p q (E.shift (r + 1) p q x))))
      (E.shiftPath r p q x) :=
  rweq_of_step (E.shiftStep r p q x)

noncomputable def shift_cancel_left_rweq (r p q : Nat) (x : E.term p q) :
    RwEq
      (Path.trans (Path.symm (E.shiftPath r p q x)) (E.shiftPath r p q x))
      (Path.refl (E.shift r p q (E.shift (r + 1) p q x))) :=
  rweq_cmpA_inv_left (E.shiftPath r p q x)

noncomputable def shift_cancel_right_rweq (r p q : Nat) (x : E.term p q) :
    RwEq
      (Path.trans (E.shiftPath r p q x) (Path.symm (E.shiftPath r p q x)))
      (Path.refl (E.twoShift r p q x)) :=
  rweq_cmpA_inv_right (E.shiftPath r p q x)

/-- Composite loop induced by the chosen page-transition coherence witness. -/
def transitionLoop (r p q : Nat) (x : E.term p q) :
    Path (E.twoShift r p q x) (E.twoShift r p q x) :=
  Path.trans (E.shiftPath r p q x) (Path.symm (E.shiftPath r p q x))

noncomputable def transitionLoop_contracts (r p q : Nat) (x : E.term p q) :
    RwEq (E.transitionLoop r p q x) (Path.refl (E.twoShift r p q x)) := by
  unfold transitionLoop
  exact rweq_cmpA_inv_right (E.shiftPath r p q x)

end Pages

/-- Trivial page package. -/
def trivialPages : Pages where
  term := fun _ _ => PUnit
  base := fun _ _ => PUnit.unit
  shift := fun _ _ _ _ => PUnit.unit
  twoShift := fun _ _ _ _ => PUnit.unit
  shiftPath := fun _ _ _ _ => Path.refl PUnit.unit
  shiftStep := fun _ _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)

end SpectralSequence
end ComputationalPaths
