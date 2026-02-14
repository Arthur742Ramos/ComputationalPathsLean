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

/-! ## Theorems -/

/-- Composition of pointed maps is associative on the underlying function. -/
theorem pathPointedMap_comp_assoc_fun
    {W X Y Z : Pointed}
    (h : PathPointedMap Y Z) (g : PathPointedMap X Y) (f : PathPointedMap W X) :
    (h.comp g).comp f = h.comp (g.comp f) := by
  sorry

/-- Left identity law for pointed-map composition on the underlying function. -/
theorem pathPointedMap_id_comp_fun {X Y : Pointed} (f : PathPointedMap X Y) :
    (PathPointedMap.id Y).comp f = f := by
  sorry

/-- Right identity law for pointed-map composition on the underlying function. -/
theorem pathPointedMap_comp_id_fun {X Y : Pointed} (f : PathPointedMap X Y) :
    f.comp (PathPointedMap.id X) = f := by
  sorry

/-- The constant spectrum has all levels equal to the input type. -/
@[simp] theorem constantSpectrum_level (X : Pointed) (n : Nat) :
    (constantSpectrum X).level n = X := by
  sorry

/-- The basepoint map sends everything to the basepoint. -/
theorem basepointMap_apply {X Y : Pointed} (x : X.carrier) :
    (PathPointedMap.basepointMap X Y).toFun x = Y.pt := by
  rfl

/-- Round-trip through `ofPointedMap` then `toPointedMap` preserves the function. -/
theorem ofPointedMap_toPointedMap_fun {X Y : Pointed} (f : PointedMap X Y) :
    (PathPointedMap.ofPointedMap f).toPointedMap.toFun = f.toFun := by
  rfl

/-- The composition basepoint path factors through the inner map. -/
theorem comp_map_pt_factoring {X Y Z : Pointed}
    (g : PathPointedMap Y Z) (f : PathPointedMap X Y) :
    (g.comp f).map_pt = Path.trans (Path.congrArg g.toFun f.map_pt) g.map_pt := by
  rfl

/-- Identity pointed map preserves the basepoint via `refl`. -/
theorem id_map_pt_is_refl (X : Pointed) :
    (PathPointedMap.id X).map_pt = Path.refl X.pt := by
  rfl

/-- Two spectra with the same levels and structure maps are equal. -/
theorem spectrum_ext (E₁ E₂ : Spectrum)
    (hlevel : E₁.level = E₂.level)
    (hmap : HEq E₁.structureMap E₂.structureMap) :
    E₁ = E₂ := by
  sorry

/-- Shifting a constant spectrum yields a constant spectrum. -/
theorem constantSpectrum_shift_level (X : Pointed) (n : Nat) :
    (constantSpectrum X).level (n + 1) = X := by
  sorry

/-- The identity pointed map composes to the identity. -/
theorem pathPointedMap_id_comp_id (X : Pointed) :
    (PathPointedMap.id X).comp (PathPointedMap.id X) = PathPointedMap.id X := by
  sorry

end SpectrumTheory
end Homotopy
end Path
end ComputationalPaths
