/- 
# Leray-Serre spectral sequence paths

This module assembles pages, differentials, and convergence into a Leray-Serre
package with explicit computational-path witnesses for transgression and
stabilization of base/fiber filtrations.
-/

import ComputationalPaths.SpectralSequence.Convergence

namespace ComputationalPaths
namespace SpectralSequence

open Path

universe u

/-- A computational-path package for a Leray-Serre style spectral sequence. -/
structure LeraySerreSequence where
  /-- Underlying page system. -/
  pages : Pages.{u}
  /-- Differential data with `d² = 0` witnesses. -/
  differentials : Differentials pages
  /-- Convergence data into limiting terms. -/
  convergence : Convergence pages differentials
  /-- Base-degree filtration action on `(0,0)` terms. -/
  baseFiltration : Nat → Nat → pages.term 0 0 → pages.term 0 0
  /-- Fiber-degree filtration action on `(0,0)` terms. -/
  fiberFiltration : Nat → Nat → pages.term 0 0 → pages.term 0 0
  /-- Transgression witness from base filtration to fiber filtration. -/
  transgressionPath :
    ∀ (s r : Nat),
      Path (baseFiltration (s + 1) r (pages.base 0 0))
        (fiberFiltration s r (pages.base 0 0))
  /-- Primitive rewrite witness for left-unit normalization on transgression. -/
  transgressionStep :
    ∀ (s r : Nat),
      Path.Step
        (Path.trans
          (Path.refl (baseFiltration (s + 1) r (pages.base 0 0)))
          (transgressionPath s r))
        (transgressionPath s r)
  /-- Stabilization witness for base filtration classes in the limit. -/
  baseStabilizePath :
    ∀ (s r : Nat),
      Path
        (convergence.embed 0 0
          (pages.shift r 0 0 (baseFiltration s r (pages.base 0 0))))
        (convergence.embed 0 0 (baseFiltration s r (pages.base 0 0)))
  /-- Stabilization witness for fiber filtration classes in the limit. -/
  fiberStabilizePath :
    ∀ (s r : Nat),
      Path
        (convergence.embed 0 0
          (pages.shift r 0 0 (fiberFiltration s r (pages.base 0 0))))
        (convergence.embed 0 0 (fiberFiltration s r (pages.base 0 0)))

namespace LeraySerreSequence

variable (L : LeraySerreSequence.{u})

/-- Distinguished `E₂` representative at bidegree `(0,0)`. -/
def e2Base : L.pages.term 0 0 :=
  L.pages.base 0 0

/-- Base filtration class extracted from the distinguished representative. -/
def baseClass (s r : Nat) : L.pages.term 0 0 :=
  L.baseFiltration s r L.e2Base

/-- Fiber filtration class extracted from the distinguished representative. -/
def fiberClass (s r : Nat) : L.pages.term 0 0 :=
  L.fiberFiltration s r L.e2Base

/-- Leray-Serre transgression path at filtration level `s` and page `r`. -/
def transgression (s r : Nat) :
    Path (L.baseClass (s + 1) r) (L.fiberClass s r) :=
  L.transgressionPath s r

@[simp] theorem transgression_rweq (s r : Nat) :
    RwEq
      (Path.trans (Path.refl (L.baseClass (s + 1) r)) (L.transgression s r))
      (L.transgression s r) :=
  rweq_of_step (L.transgressionStep s r)

/-- Loop induced by transgression and its inverse. -/
def transgressionLoop (s r : Nat) :
    Path (L.baseClass (s + 1) r) (L.baseClass (s + 1) r) :=
  Path.trans (L.transgression s r) (Path.symm (L.transgression s r))

@[simp] theorem transgressionLoop_contracts (s r : Nat) :
    RwEq
      (L.transgressionLoop s r)
      (Path.refl (L.baseClass (s + 1) r)) := by
  unfold transgressionLoop
  exact rweq_cmpA_inv_right (L.transgression s r)

/-- Shifted transgression witness mapped into the limiting term. -/
def shiftedTransgression (s r : Nat) :
    Path
      (L.convergence.embed 0 0 (L.pages.shift r 0 0 (L.baseClass (s + 1) r)))
      (L.convergence.embed 0 0 (L.pages.shift r 0 0 (L.fiberClass s r))) :=
  Path.congrArg
    (fun x => L.convergence.embed 0 0 (L.pages.shift r 0 0 x))
    (L.transgression s r)

/-- Transgression witness after stabilization in the fiber filtration. -/
def transgressionToFiberLimit (s r : Nat) :
    Path
      (L.convergence.embed 0 0 (L.pages.shift r 0 0 (L.baseClass (s + 1) r)))
      (L.convergence.embed 0 0 (L.fiberClass s r)) :=
  Path.trans (L.shiftedTransgression s r) (L.fiberStabilizePath s r)

@[simp] theorem transgressionToFiberLimit_rweq (s r : Nat) :
    RwEq
      (Path.trans
        (L.transgressionToFiberLimit s r)
        (Path.refl (L.convergence.embed 0 0 (L.fiberClass s r))))
      (L.transgressionToFiberLimit s r) :=
  rweq_cmpA_refl_right (L.transgressionToFiberLimit s r)

/-- `d² = 0` transported through the fiber filtration at `(0,0)`. -/
def fiberBoundaryCompression (s r : Nat) :
    Path
      (L.fiberFiltration s r
        (L.differentials.d r 0 0 (L.differentials.d r 0 0 L.e2Base)))
      (L.fiberClass s r) :=
  Path.congrArg (L.fiberFiltration s r) (L.differentials.dSquaredPath r 0 0)

/-- Shifted boundary compression mapped into the limiting term. -/
def shiftedFiberBoundaryCompression (s r : Nat) :
    Path
      (L.convergence.embed 0 0
        (L.pages.shift r 0 0
          (L.fiberFiltration s r
            (L.differentials.d r 0 0 (L.differentials.d r 0 0 L.e2Base)))))
      (L.convergence.embed 0 0 (L.pages.shift r 0 0 (L.fiberClass s r))) :=
  Path.congrArg
    (fun x => L.convergence.embed 0 0 (L.pages.shift r 0 0 x))
    (L.fiberBoundaryCompression s r)

/-- Shifted fiber boundaries converge to the stabilized fiber class. -/
def fiberBoundaryToLimit (s r : Nat) :
    Path
      (L.convergence.embed 0 0
        (L.pages.shift r 0 0
          (L.fiberFiltration s r
            (L.differentials.d r 0 0 (L.differentials.d r 0 0 L.e2Base)))))
      (L.convergence.embed 0 0 (L.fiberClass s r)) :=
  Path.trans (L.shiftedFiberBoundaryCompression s r) (L.fiberStabilizePath s r)

@[simp] theorem fiberBoundaryToLimit_rweq (s r : Nat) :
    RwEq
      (Path.trans
        (L.fiberBoundaryToLimit s r)
        (Path.refl (L.convergence.embed 0 0 (L.fiberClass s r))))
      (L.fiberBoundaryToLimit s r) :=
  rweq_cmpA_refl_right (L.fiberBoundaryToLimit s r)

end LeraySerreSequence

/-- Canonical trivial Leray-Serre package. -/
def trivialLeraySerreSequence : LeraySerreSequence where
  pages := trivialPages
  differentials := trivialDifferentials
  convergence := trivialConvergence
  baseFiltration := fun _ _ _ => PUnit.unit
  fiberFiltration := fun _ _ _ => PUnit.unit
  transgressionPath := fun _ _ => Path.refl PUnit.unit
  transgressionStep := fun _ _ => Path.Step.trans_refl_left (Path.refl PUnit.unit)
  baseStabilizePath := fun _ _ => Path.refl PUnit.unit
  fiberStabilizePath := fun _ _ => Path.refl PUnit.unit

end SpectralSequence
end ComputationalPaths
