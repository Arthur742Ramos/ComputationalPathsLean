/-
# Infinite Loop Spaces

This module formalizes infinite loop spaces in the computational paths
framework. We define spectrum objects, Omega-spectra with Path-based structure
maps, connective covers, and infinite loop space machines.

## Key Results

- `InfiniteLoopSpace`: a type with compatible n-fold deloopings for all n
- `SpectrumObject`: spectrum with Path-based adjoint structure maps
- `ConnectiveCover`: connective cover of a spectrum
- `InfiniteLoopSpaceMachine`: machine producing spectra from categorical input
- `omegaInfiniteFromSpectrum`: extract infinite loop space from a spectrum

## References

- May, "The Geometry of Iterated Loop Spaces"
- Adams, "Infinite Loop Spaces"
- Segal, "Categories and cohomology theories"
-/

import ComputationalPaths.Path.Homotopy.OmegaSpectrum
import ComputationalPaths.Path.Homotopy.SuspensionLoop
import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Homotopy.SpectrumTheory

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace InfiniteLoopSpace

open SuspensionLoop

universe u

/-! ## Iterated loop spaces -/

/-- Iterated loop space Ω^n(X, pt). -/
noncomputable def iteratedLoop (n : Nat) (X : Pointed) : Pointed :=
  Nat.recOn n X (fun _ acc => loopPointed acc)

/-- Iterated loop space unfolding: Ω^{n+1} X = Ω(Ω^n X). -/
theorem iteratedLoop_succ (n : Nat) (X : Pointed) :
    iteratedLoop (n + 1) X = loopPointed (iteratedLoop n X) := rfl

/-- The basepoint of Ω^n X is the n-fold reflexivity path. -/
noncomputable def iteratedLoop_pt (n : Nat) (X : Pointed) :
    (iteratedLoop n X).carrier :=
  (iteratedLoop n X).pt

/-! ## Infinite loop spaces -/

/-- An infinite loop space: a pointed type with compatible deloopings at every level. -/
structure InfLoopSpace where
  /-- The underlying pointed type. -/
  space : Pointed
  /-- The n-th delooping B^n(space). -/
  delooping : Nat → Pointed
  /-- Level 0 is the space itself. -/
  level_zero : delooping 0 = space
  /-- The loop space of level (n+1) maps into level n. -/
  structureMap : (n : Nat) →
    PointedMap (delooping n) (loopPointed (delooping (n + 1)))

/-- The trivial infinite loop space: a single point. -/
def trivialInfLoop : InfLoopSpace where
  space := { carrier := Unit, pt := () }
  delooping := fun _ => { carrier := Unit, pt := () }
  level_zero := rfl
  structureMap := fun _ =>
    { toFun := fun _ => Path.refl ()
      map_pt := rfl }

/-! ## Spectrum objects -/

/-- A spectrum object with adjoint structure maps using Path. -/
structure SpectrumObject where
  /-- The levelwise pointed types. -/
  level : Nat → Pointed
  /-- Adjoint structure maps: level n → Ω(level (n+1)). -/
  adjointMap : (n : Nat) →
    PointedMap (level n) (loopPointed (level (n + 1)))

/-- Convert an OmegaSpectrum to a SpectrumObject. -/
def SpectrumObject.ofOmega (E : Homotopy.OmegaSpectrum) : SpectrumObject where
  level := E.level
  adjointMap := E.structureMap
/-- The zeroth space of a spectrum is an infinite loop space. -/
def omegaInfiniteFromSpectrum (E : SpectrumObject) : InfLoopSpace where
  space := E.level 0
  delooping := E.level
  level_zero := rfl
  structureMap := E.adjointMap

/-- Constant spectrum: every level is the same pointed type. -/
def constantSpectrumObject (X : Pointed) : SpectrumObject where
  level := fun _ => X
  adjointMap := fun _ =>
    { toFun := fun _ => Path.refl X.pt
      map_pt := rfl }

/-! ## Connective covers -/

/-- A connective cover of a spectrum: a spectrum E' with a map to E
    such that π_n(E') = 0 for n < 0 (modeled as the spectrum itself
    for non-negative levels). -/
structure ConnectiveCover (E : SpectrumObject) where
  /-- The connective spectrum. -/
  cover : SpectrumObject
  /-- Map from the cover to the original spectrum. -/
  map : (n : Nat) → PointedMap (cover.level n) (E.level n)

/-- Trivial connective cover: the spectrum itself. -/
def ConnectiveCover.trivial (E : SpectrumObject) : ConnectiveCover E where
  cover := E
  map := fun n => PointedMap.id (E.level n)

/-! ## Infinite loop space machines -/

/-- Input data for an infinite loop space machine:
    a sequence of pointed types with structure. -/
structure MachineInput where
  /-- Input pointed types at each level. -/
  input : Nat → Pointed
  /-- Compatibility maps between levels. -/
  compat : (n : Nat) → PointedMap (input n) (input (n + 1))

/-- An infinite loop space machine: a functor from structured input
    to spectra. -/
structure InfLoopMachine where
  /-- Apply the machine to input data. -/
  apply : MachineInput → SpectrumObject
  /-- The machine preserves the zeroth level up to a pointed map. -/
  level_zero_map : (inp : MachineInput) →
    PointedMap (inp.input 0) ((apply inp).level 0)

/-- The trivial infinite loop space machine: sends everything to the
    constant spectrum. -/
def trivialMachine : InfLoopMachine where
  apply := fun inp => constantSpectrumObject (inp.input 0)
  level_zero_map := fun inp => PointedMap.id (inp.input 0)

/-! ## Shift and truncation -/

/-- Shift a spectrum object by k levels. -/
def SpectrumObject.shift (E : SpectrumObject) (k : Nat) : SpectrumObject where
  level := fun n => E.level (n + k)
  adjointMap := fun n =>
    have h : n + k + 1 = n + 1 + k := by omega
    h ▸ E.adjointMap (n + k)

/-- The underlying infinite loop space of a shifted spectrum. -/
def shiftedInfLoop (E : SpectrumObject) (k : Nat) : InfLoopSpace :=
  omegaInfiniteFromSpectrum (E.shift k)

/-- Two spectra are equivalent if there are levelwise pointed equivalences. -/
structure SpectrumEquiv (E F : SpectrumObject) where
  /-- Forward maps at each level. -/
  toMap : (n : Nat) → PointedMap (E.level n) (F.level n)
  /-- Inverse maps at each level. -/
  invMap : (n : Nat) → PointedMap (F.level n) (E.level n)
  /-- Left inverse at each level. -/
  left_inv : ∀ n x, (invMap n).toFun ((toMap n).toFun x) = x
  /-- Right inverse at each level. -/
  right_inv : ∀ n y, (toMap n).toFun ((invMap n).toFun y) = y

/-- Identity spectrum equivalence. -/
def SpectrumEquiv.refl (E : SpectrumObject) : SpectrumEquiv E E where
  toMap := fun n => PointedMap.id (E.level n)
  invMap := fun n => PointedMap.id (E.level n)
  left_inv := fun _ _ => rfl
  right_inv := fun _ _ => rfl


private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary -/

end InfiniteLoopSpace
end Homotopy
end Path
end ComputationalPaths
