/-
# Spectrum Objects via Computational Paths

This module introduces a minimal spectrum interface that records basepoint
preservation using the computational `Path` type. The definitions are intended
as lightweight data structures that parallel the classical pointed-spectrum
setup while remaining fully constructive.

## Key Results

- `PathPointedMap`: pointed maps with basepoint preservation witnessed by `Path`
- `sigmaPointed`: suspension of a pointed type
- `Spectrum`: spectra with Path-based structure maps

## References

- HoTT Book, Chapter 8
- `StableHomotopy` for a suspension/loop spectrum interface
-/

import ComputationalPaths.Path.Homotopy.SuspensionLoop

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace SpectrumTheory

open SuspensionLoop

universe u

/-! ## Path-pointed maps -/

/-- A pointed map whose basepoint preservation is witnessed by a computational path. -/
structure PathPointedMap (X Y : Pointed) where
  /-- The underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Basepoint preservation expressed as a path. -/
  map_pt : Path (toFun X.pt) Y.pt

namespace PathPointedMap

variable {X Y Z : Pointed}

/-- Composition of path-pointed maps. -/
def comp (g : PathPointedMap Y Z) (f : PathPointedMap X Y) : PathPointedMap X Z where
  toFun := g.toFun ∘ f.toFun
  map_pt := Path.trans (Path.congrArg g.toFun f.map_pt) g.map_pt

/-- Identity path-pointed map. -/
def id (X : Pointed) : PathPointedMap X X where
  toFun := _root_.id
  map_pt := Path.refl X.pt

/-- View a `PointedMap` as a `PathPointedMap`. -/
def ofPointedMap (f : PointedMap X Y) : PathPointedMap X Y where
  toFun := f.toFun
  map_pt := Path.stepChain f.map_pt

/-- Forget a `PathPointedMap` into a `PointedMap`. -/
def toPointedMap (f : PathPointedMap X Y) : PointedMap X Y where
  toFun := f.toFun
  map_pt := Path.toEq f.map_pt

/-- Constant map to the basepoint as a path-pointed map. -/
def basepointMap (X Y : Pointed) : PathPointedMap X Y where
  toFun := fun _ => Y.pt
  map_pt := Path.refl Y.pt

end PathPointedMap

/-! ## Suspension helper -/

/-- Suspension of a pointed type, using the north pole as the basepoint. -/
noncomputable def sigmaPointed (X : Pointed) : Pointed :=
  suspPointed X.carrier

/-! ## Spectrum objects -/

/-- A spectrum with structure maps recorded using computational paths. -/
structure Spectrum where
  /-- The levelwise pointed types. -/
  level : Nat → Pointed
  /-- Structure maps Sigma(level n) -> level (n+1). -/
  structureMap : (n : Nat) →
    PathPointedMap (sigmaPointed (level n)) (level (n + 1))

/-- Constant spectrum with trivial structure maps. -/
noncomputable def constantSpectrum (X : Pointed) : Spectrum where
  level := fun _ => X
  structureMap := fun _ => PathPointedMap.basepointMap (sigmaPointed X) X

end SpectrumTheory
end Homotopy
end Path
end ComputationalPaths
