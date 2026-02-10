/-
# Loop-Suspension Adjunction (Pointed Spaces)

This module packages the loop-suspension adjunction for pointed spaces using
the computational-path `Path` equality. It reuses the adjunction maps already
constructed in `LoopSpaceAdjunction`.

## Key Results

- `loopSpaceSuspensionAdjunction`: Path-based equivalence for the adjunction
- `unit`, `counit`: adjunction unit and counit maps

## References

- HoTT Book, Chapter 8 (Suspension)
- `LoopSpaceAdjunction` for the underlying construction
-/

import ComputationalPaths.Path.Homotopy.LoopSpaceAdjunction

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpaceSuspension

open SuspensionLoop
open LoopSpaceAdjunction

universe u v

/-! ## Adjunction package -/

noncomputable section

/-- Path-based equivalence structure (inverse laws witnessed by `Path`). -/
structure PathSimpleEquiv (α : Type u) (β : Type v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse after forward map is the identity, as a `Path`. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Forward after inverse map is the identity, as a `Path`. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Convert a `SimpleEquiv` into a `PathSimpleEquiv`. -/
def simpleEquivToPathSimpleEquiv {α : Type u} {β : Type v} (e : SimpleEquiv α β) :
    PathSimpleEquiv α β :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := fun x => Path.ofEq (e.left_inv x)
    right_inv := fun y => Path.ofEq (e.right_inv y) }

/-- Loop-suspension adjunction as a `PathSimpleEquiv`. -/
def loopSpaceSuspensionAdjunction (X Y : SuspensionLoop.Pointed) :
    PathSimpleEquiv (PointedMap (sigmaPointed X) Y) (PointedMap X (omegaEqPointed Y)) :=
  simpleEquivToPathSimpleEquiv (LoopSpaceAdjunction.suspLoopAdjunction (X := X) (Y := Y))

/-- Unit of the loop-suspension adjunction. -/
def unit (X : SuspensionLoop.Pointed) :
    PointedMap X (omegaEqPointed (sigmaPointed X)) :=
  LoopSpaceAdjunction.unit X

/-- Counit of the loop-suspension adjunction. -/
def counit (Y : SuspensionLoop.Pointed) :
    PointedMap (sigmaPointed (omegaEqPointed Y)) Y :=
  LoopSpaceAdjunction.counit Y

end

/-! ## Summary -/

end LoopSpaceSuspension
end Homotopy
end Path
end ComputationalPaths
