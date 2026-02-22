import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Floer.FloerComplex

/-!
# Floer theory paths: pseudo-holomorphic curves

This module packages a minimal pseudo-holomorphic-curve interface for Floer
theory with explicit computational paths. Cauchy-Riemann compatibility,
asymptotic boundary behavior, energy/action transport, and compactification
coherence are represented by `Path`, normalized by `Path.Step`, and compared
by `RwEq`.
-/

namespace ComputationalPaths
namespace Floer
namespace PseudoHolomorphicCurves

open Path
open FloerComplex

universe u

/-- Domain-specific rewrite tags for pseudo-holomorphic coherence moves. -/
inductive PseudoHolomorphicStep : Type
  | cauchyRiemann
  | asymptoticBoundary
  | energyAction
  | compactification
  | boundaryAfterCompactification
  | cancellation

/--
Path-level interface for pseudo-holomorphic curves in Floer theory.
The fields model strip equations, compactification/boundary behavior,
and energy compatibility with action filtration.
-/
structure PseudoHolomorphicPathData (Gen : Type u) where
  complex : FloerComplexPathData Gen
  strip : Gen → Gen
  compactify : Gen → Gen
  energy : Gen → Nat
  cauchyRiemannPath :
    ∀ x : Gen,
      Path (strip (complex.differential x)) (complex.differential (strip x))
  asymptoticBoundaryPath :
    ∀ x : Gen,
      Path (compactify (strip x)) (complex.continuation x)
  energyActionPath :
    ∀ x : Gen,
      Path (energy (strip x)) (complex.actionLevel x)
  compactificationPath :
    ∀ x : Gen,
      Path
        (compactify (complex.differential (strip x)))
        (complex.continuation (complex.differential x))

namespace PseudoHolomorphicPathData

variable {Gen : Type u} (P : PseudoHolomorphicPathData Gen)

/-- Boundary transport induced by compactifying a Cauchy-Riemann strip. -/
noncomputable def boundaryAfterCompactificationPath (x : Gen) :
    Path
      (P.compactify (P.strip (P.complex.differential x)))
      (P.complex.continuation (P.complex.differential x)) :=
  Path.trans
    (Path.congrArg P.compactify (P.cauchyRiemannPath x))
    (P.compactificationPath x)

/-- Step witness: right-unit normalization for Cauchy-Riemann compatibility. -/
noncomputable def cauchyRiemann_step (x : Gen) :
    Path.Step
      (Path.trans
        (P.cauchyRiemannPath x)
        (Path.refl (P.complex.differential (P.strip x))))
      (P.cauchyRiemannPath x) :=
  Path.Step.trans_refl_right (P.cauchyRiemannPath x)

noncomputable def cauchyRiemann_rweq (x : Gen) :
    RwEq
      (Path.trans
        (P.cauchyRiemannPath x)
        (Path.refl (P.complex.differential (P.strip x))))
      (P.cauchyRiemannPath x) :=
  rweq_of_step (P.cauchyRiemann_step x)

/-- Step witness: right-unit normalization for asymptotic boundary behavior. -/
noncomputable def asymptoticBoundary_step (x : Gen) :
    Path.Step
      (Path.trans
        (P.asymptoticBoundaryPath x)
        (Path.refl (P.complex.continuation x)))
      (P.asymptoticBoundaryPath x) :=
  Path.Step.trans_refl_right (P.asymptoticBoundaryPath x)

noncomputable def asymptoticBoundary_rweq (x : Gen) :
    RwEq
      (Path.trans
        (P.asymptoticBoundaryPath x)
        (Path.refl (P.complex.continuation x)))
      (P.asymptoticBoundaryPath x) :=
  rweq_of_step (P.asymptoticBoundary_step x)

/-- Step witness: left-unit normalization for energy/action transport. -/
noncomputable def energyAction_step (x : Gen) :
    Path.Step
      (Path.trans
        (Path.refl (P.energy (P.strip x)))
        (P.energyActionPath x))
      (P.energyActionPath x) :=
  Path.Step.trans_refl_left (P.energyActionPath x)

noncomputable def energyAction_rweq (x : Gen) :
    RwEq
      (Path.trans
        (Path.refl (P.energy (P.strip x)))
        (P.energyActionPath x))
      (P.energyActionPath x) :=
  rweq_of_step (P.energyAction_step x)

/-- Step witness: right-unit normalization for compactification transport. -/
noncomputable def compactification_step (x : Gen) :
    Path.Step
      (Path.trans
        (P.compactificationPath x)
        (Path.refl (P.complex.continuation (P.complex.differential x))))
      (P.compactificationPath x) :=
  Path.Step.trans_refl_right (P.compactificationPath x)

noncomputable def compactification_rweq (x : Gen) :
    RwEq
      (Path.trans
        (P.compactificationPath x)
        (Path.refl (P.complex.continuation (P.complex.differential x))))
      (P.compactificationPath x) :=
  rweq_of_step (P.compactification_step x)

/-- Step witness: right-unit normalization for compactified strip boundary paths. -/
noncomputable def boundaryAfterCompactification_step (x : Gen) :
    Path.Step
      (Path.trans
        (P.boundaryAfterCompactificationPath x)
        (Path.refl (P.complex.continuation (P.complex.differential x))))
      (P.boundaryAfterCompactificationPath x) :=
  Path.Step.trans_refl_right (P.boundaryAfterCompactificationPath x)

noncomputable def boundaryAfterCompactification_rweq (x : Gen) :
    RwEq
      (Path.trans
        (P.boundaryAfterCompactificationPath x)
        (Path.refl (P.complex.continuation (P.complex.differential x))))
      (P.boundaryAfterCompactificationPath x) :=
  rweq_of_step (P.boundaryAfterCompactification_step x)

noncomputable def asymptoticBoundary_cancel_rweq (x : Gen) :
    RwEq
      (Path.trans (Path.symm (P.asymptoticBoundaryPath x)) (P.asymptoticBoundaryPath x))
      (Path.refl (P.complex.continuation x)) :=
  rweq_cmpA_inv_left (P.asymptoticBoundaryPath x)

end PseudoHolomorphicPathData

/-- Trivial model instantiating pseudo-holomorphic computational-path data. -/
noncomputable def trivialPseudoHolomorphicPathData : PseudoHolomorphicPathData PUnit where
  complex := FloerComplex.trivialFloerComplexPathData
  strip := fun _ => PUnit.unit
  compactify := fun _ => PUnit.unit
  energy := fun _ => 0
  cauchyRiemannPath := fun _ => Path.refl PUnit.unit
  asymptoticBoundaryPath := fun _ => Path.refl PUnit.unit
  energyActionPath := fun _ => Path.refl 0
  compactificationPath := fun _ => Path.refl PUnit.unit

end PseudoHolomorphicCurves
end Floer
end ComputationalPaths
