/- 
# Adams spectral sequence paths

This module assembles pages, differentials, and convergence into an Adams-style
spectral sequence package with explicit computational path witnesses.
-/

import ComputationalPaths.SpectralSequence.Convergence

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- A computational-path package for an Adams-style spectral sequence. -/
structure AdamsSequence where
  /-- Underlying page system. -/
  pages : Pages.{u}
  /-- Differential data with `d² = 0` witnesses. -/
  differentials : Differentials pages
  /-- Convergence data into limiting terms. -/
  convergence : Convergence pages differentials
  /-- A filtration operation on the bidegree `(0,0)` term. -/
  filtration : Nat → Nat → pages.term 0 0 → pages.term 0 0
  /-- Filtration monotonicity path witness on the chosen base term. -/
  filtrationPath :
    ∀ (s r : Nat),
      Path (filtration (s + 1) r (pages.base 0 0))
        (filtration s r (pages.base 0 0))
  /-- Primitive rewrite witness for left-unit normalization on filtration paths. -/
  filtrationStep :
    ∀ (s r : Nat),
      Path.Step
        (Path.trans
          (Path.refl (filtration (s + 1) r (pages.base 0 0)))
          (filtrationPath s r))
        (filtrationPath s r)

namespace AdamsSequence

variable (A : AdamsSequence.{u})

/-- The distinguished `E₂` representative at bidegree `(0,0)`. -/
noncomputable def e2Base : A.pages.term 0 0 :=
  A.pages.base 0 0

/-- The `d₂ ∘ d₂ = 0` witness at `(0,0)`. -/
noncomputable def d2Boundary :
    Path
      (A.differentials.d 2 0 0 (A.differentials.d 2 0 0 A.e2Base))
      A.e2Base :=
  A.differentials.dSquaredPath 2 0 0

/-- Stabilization witness in the limiting term at `(0,0)`. -/
noncomputable def convergenceWitness (r : Nat) :
    Path
      (A.convergence.embed 0 0 (A.pages.shift r 0 0 A.e2Base))
      (A.convergence.embed 0 0 A.e2Base) :=
  A.convergence.stabilizePath r 0 0

noncomputable def filtration_rweq (s r : Nat) :
    RwEq
      (Path.trans
        (Path.refl (A.filtration (s + 1) r A.e2Base))
        (A.filtrationPath s r))
      (A.filtrationPath s r) :=
  rweq_of_step (A.filtrationStep s r)

/-- Loop induced by a filtration step and its inverse. -/
noncomputable def filtrationLoop (s r : Nat) :
    Path (A.filtration (s + 1) r A.e2Base) (A.filtration (s + 1) r A.e2Base) :=
  Path.trans (A.filtrationPath s r) (Path.symm (A.filtrationPath s r))

noncomputable def filtrationLoop_contracts (s r : Nat) :
    RwEq (A.filtrationLoop s r) (Path.refl (A.filtration (s + 1) r A.e2Base)) := by
  unfold filtrationLoop
  exact rweq_cmpA_inv_right (A.filtrationPath s r)

/-- Boundary witness mapped into the limiting term. -/
noncomputable def boundaryInLimit (r : Nat) :
    Path
      (A.convergence.embed 0 0
        (A.differentials.d r 0 0 (A.differentials.d r 0 0 A.e2Base)))
      (A.convergence.embed 0 0 A.e2Base) :=
  A.convergence.boundaryToLimit r 0 0

/-- Shifted `d² = 0` witness mapped into the limiting term. -/
noncomputable def shiftedBoundaryInLimit (r : Nat) :
    Path
      (A.convergence.embed 0 0
        (A.pages.shift r 0 0
          (A.differentials.d r 0 0 (A.differentials.d r 0 0 A.e2Base))))
      (A.convergence.embed 0 0 (A.pages.shift r 0 0 A.e2Base)) :=
  Path.congrArg
    (fun x => A.convergence.embed 0 0 (A.pages.shift r 0 0 x))
    (A.differentials.dSquaredPath r 0 0)

noncomputable def convergenceWitness_rweq (r : Nat) :
    RwEq
      (Path.trans (A.convergenceWitness r) (Path.refl (A.convergence.embed 0 0 A.e2Base)))
      (A.convergenceWitness r) :=
  rweq_cmpA_refl_right (A.convergenceWitness r)

end AdamsSequence

/-- Canonical trivial Adams package. -/
noncomputable def trivialAdamsSequence : AdamsSequence where
  pages := trivialPages
  differentials := trivialDifferentials
  convergence := trivialConvergence
  filtration := fun _ _ _ => PUnit.unit
  filtrationPath := fun _ _ => Path.refl PUnit.unit
  filtrationStep := fun _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)

end SpectralSequence
end ComputationalPaths
