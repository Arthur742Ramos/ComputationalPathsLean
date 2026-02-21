/- 
# Spectral sequence convergence with computational paths

This module packages convergence data as explicit path witnesses that page
transitions stabilize and boundaries map to the limiting terms.
-/

import ComputationalPaths.SpectralSequence.Differentials

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- Path-level convergence data for a spectral sequence package. -/
structure Convergence (E : Pages.{u}) (D : Differentials E) where
  /-- Limiting terms at each bidegree. -/
  limit : Nat → Nat → Type u
  /-- Structural map from page terms to limiting terms. -/
  embed : (p q : Nat) → E.term p q → limit p q
  /-- Stabilization witness for shifted base terms. -/
  stabilizePath :
    ∀ (r p q : Nat),
      Path (embed p q (E.shift r p q (E.base p q)))
        (embed p q (E.base p q))
  /-- Primitive rewrite witness for right-unit normalization on stabilization. -/
  stabilizeStep :
    ∀ (r p q : Nat),
      Path.Step
        (Path.trans (stabilizePath r p q)
          (Path.refl (embed p q (E.base p q))))
        (stabilizePath r p q)
  /-- Boundary classes become trivial in the limit. -/
  boundaryToLimit :
    ∀ (r p q : Nat),
      Path (embed p q (D.d r p q (D.d r p q (E.base p q))))
        (embed p q (E.base p q))

namespace Convergence

variable {E : Pages.{u}} {D : Differentials E} (C : Convergence E D)

/-- Canonical limiting representative at a bidegree. -/
def eventualTerm (p q : Nat) : C.limit p q :=
  C.embed p q (E.base p q)

/-- Shifted limiting representative at a bidegree and page. -/
def shiftedTerm (r p q : Nat) : C.limit p q :=
  C.embed p q (E.shift r p q (E.base p q))

noncomputable def stabilize_rweq (r p q : Nat) :
    RwEq
      (Path.trans (C.stabilizePath r p q) (Path.refl (C.eventualTerm p q)))
      (C.stabilizePath r p q) :=
  rweq_of_step (C.stabilizeStep r p q)

/-- Loop induced by stabilization and its inverse. -/
def stabilizationLoop (r p q : Nat) :
    Path (C.shiftedTerm r p q) (C.shiftedTerm r p q) :=
  Path.trans (C.stabilizePath r p q) (Path.symm (C.stabilizePath r p q))

noncomputable def stabilizationLoop_contracts (r p q : Nat) :
    RwEq (C.stabilizationLoop r p q) (Path.refl (C.shiftedTerm r p q)) := by
  unfold stabilizationLoop
  exact rweq_cmpA_inv_right (C.stabilizePath r p q)

/-- Transported boundary witness after shifting. -/
def boundaryShiftToLimit (r p q : Nat) :
    Path
      (C.embed p q (E.shift r p q (D.d r p q (D.d r p q (E.base p q)))))
      (C.embed p q (E.shift r p q (E.base p q))) :=
  Path.congrArg (fun x => C.embed p q (E.shift r p q x)) (D.dSquaredPath r p q)

/-- Composite convergence witness: shifted boundaries converge to the limit base term. -/
def convergedBoundary (r p q : Nat) :
    Path
      (C.embed p q (E.shift r p q (D.d r p q (D.d r p q (E.base p q)))))
      (C.eventualTerm p q) :=
  Path.trans (C.boundaryShiftToLimit r p q) (C.stabilizePath r p q)

noncomputable def convergedBoundary_normalizes (r p q : Nat) :
    RwEq
      (Path.trans (C.convergedBoundary r p q) (Path.refl (C.eventualTerm p q)))
      (C.convergedBoundary r p q) :=
  rweq_cmpA_refl_right (C.convergedBoundary r p q)

end Convergence

/-- Trivial convergence package over trivial pages and differentials. -/
def trivialConvergence : Convergence trivialPages trivialDifferentials where
  limit := fun _ _ => PUnit
  embed := fun _ _ _ => PUnit.unit
  stabilizePath := fun _ _ _ => Path.refl PUnit.unit
  stabilizeStep := fun _ _ _ => Path.Step.trans_refl_right (Path.refl PUnit.unit)
  boundaryToLimit := fun _ _ _ => Path.refl PUnit.unit

end SpectralSequence
end ComputationalPaths
