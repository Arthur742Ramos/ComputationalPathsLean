/-
# Omega-spectra for Computational Paths

This module defines Omega-spectra using the computational-path loop space.
We keep the structure minimal: levels are pointed types and structure maps
land in loop spaces defined with `Path`.

## Key Results

- `OmegaSpectrum`
- `OmegaSpectrum.shift`
- `iteratedLoopPointed`, `pathOmegaSpectrum`

## References

- HoTT Book, Chapter 8
- `SuspensionLoop` for pointed types and loop spaces
-/

import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy

open SuspensionLoop

universe u

/-! ## Omega-spectra -/

/-- An Omega-spectrum with structure maps into computational loop spaces. -/
structure OmegaSpectrum where
  /-- The levelwise pointed types. -/
  level : Nat → Pointed
  /-- Structure maps level n -> loopPointed(level (n+1)). -/
  structureMap : (n : Nat) → PointedMap (level n) (loopPointed (level (n + 1)))

/-- Constant pointed map to the basepoint. -/
def basepointMap (X Y : Pointed) : PointedMap X Y where
  toFun := fun _ => Y.pt
  map_pt := rfl

namespace OmegaSpectrum

/-- Shift an Omega-spectrum by one level. -/
def shift (E : OmegaSpectrum) : OmegaSpectrum where
  level := fun n => E.level (n + 1)
  structureMap := fun n => E.structureMap (n + 1)

end OmegaSpectrum

/-! ## Path-space spectra -/

/-- n-fold iterated loop space as a pointed type. -/
noncomputable def iteratedLoopPointed (n : Nat) (X : Pointed) : Pointed :=
  Nat.recOn n X (fun _ acc => loopPointed acc)

/-- Omega-spectrum built from iterated loop spaces with constant structure maps. -/
noncomputable def pathOmegaSpectrum (X : Pointed) : OmegaSpectrum where
  level := fun n => iteratedLoopPointed n X
  structureMap := fun n =>
    basepointMap (iteratedLoopPointed n X) (loopPointed (iteratedLoopPointed (n + 1) X))


private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
This module introduces Omega-spectra using computational-path loop spaces,
including a shift operation and a canonical spectrum from iterated loops.
-/

end Homotopy
end Path
end ComputationalPaths
