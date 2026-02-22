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
noncomputable def basepointMap (X Y : Pointed) : PointedMap X Y where
  toFun := fun _ => Y.pt
  map_pt := rfl

namespace OmegaSpectrum

/-- Shift an Omega-spectrum by one level. -/
noncomputable def shift (E : OmegaSpectrum) : OmegaSpectrum where
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


private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

/-!
This module introduces Omega-spectra using computational-path loop spaces,
including a shift operation and a canonical spectrum from iterated loops.
-/

/-! ## Theorems -/

/-- Shifting an OmegaSpectrum shifts levels by one. -/
@[simp] theorem omegaSpectrum_shift_level (E : OmegaSpectrum) (n : Nat) :
    E.shift.level n = E.level (n + 1) := by
  rfl

/-- Shifting an OmegaSpectrum shifts structure maps by one. -/
@[simp] theorem omegaSpectrum_shift_structureMap (E : OmegaSpectrum) (n : Nat) :
    E.shift.structureMap n = E.structureMap (n + 1) := by
  rfl

/-- Double shift composes correctly. -/
@[simp] theorem omegaSpectrum_shift_shift_level (E : OmegaSpectrum) (n : Nat) :
    E.shift.shift.level n = E.level (n + 2) := by
  rfl

/-- Iterated loop at zero is the identity. -/
@[simp] theorem iteratedLoopPointed_zero (X : Pointed) :
    iteratedLoopPointed 0 X = X := by
  rfl

/-- Iterated loop at succ wraps in loopPointed. -/
@[simp] theorem iteratedLoopPointed_succ (n : Nat) (X : Pointed) :
    iteratedLoopPointed (n + 1) X = loopPointed (iteratedLoopPointed n X) := by
  rfl

/-- The basepoint map sends all elements to the basepoint. -/
theorem basepointMap_apply_eq (X Y : Pointed) (x : X.carrier) :
    (basepointMap X Y).toFun x = Y.pt := by
  rfl

/-- The basepoint map preserves basepoints. -/
theorem basepointMap_map_pt (X Y : Pointed) :
    (basepointMap X Y).map_pt = rfl := by
  rfl

/-- The path omega spectrum has the correct zero-th level. -/
@[simp] theorem pathOmegaSpectrum_level_zero (X : Pointed) :
    (pathOmegaSpectrum X).level 0 = X := by
  rfl

/-- Two OmegaSpectra with the same levels and maps are equal. -/
theorem omegaSpectrum_ext (E₁ E₂ : OmegaSpectrum)
    (hl : E₁.level = E₂.level)
    (hm : HEq E₁.structureMap E₂.structureMap) :
    E₁ = E₂ := by
  cases E₁; cases E₂; subst hl; cases hm; rfl

/-- Shifting the path omega spectrum shifts the iterated loop level. -/
theorem pathOmegaSpectrum_shift_level (X : Pointed) (n : Nat) :
    (pathOmegaSpectrum X).shift.level n = iteratedLoopPointed (n + 1) X := by
  rfl

/-- The pathAnchor produces a refl path. -/
theorem pathAnchor_is_refl {A : Type} (a : A) :
    pathAnchor a = Path.refl a := by
  rfl

end Homotopy
end Path
end ComputationalPaths
