/-
# Loop-Suspension Adjunction (Pointed Spaces)

This module packages the loop-suspension adjunction for pointed spaces in a
Mathlib-friendly form, reusing the adjunction maps already constructed in
`LoopSpaceAdjunction`.

## Key Results

- `loopSpaceSuspensionAdjunction`: `SimpleEquiv` form of the adjunction
- `loopSpaceSuspensionAdjunctionEquiv`: Mathlib `Equiv` form
- `unit`, `counit`: adjunction unit and counit maps

## References

- HoTT Book, Chapter 8 (Suspension)
- `LoopSpaceAdjunction` for the underlying construction
-/

import Mathlib
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

/-- Loop-suspension adjunction as a `SimpleEquiv`. -/
def loopSpaceSuspensionAdjunction (X Y : SuspensionLoop.Pointed) :
    SimpleEquiv (PointedMap (sigmaPointed X) Y) (PointedMap X (omegaEqPointed Y)) :=
  LoopSpaceAdjunction.suspLoopAdjunction (X := X) (Y := Y)

/-- Cast a `SimpleEquiv` to a Mathlib `Equiv`. -/
def simpleEquivToEquiv {α : Sort u} {β : Sort v} (e : SimpleEquiv α β) : Equiv α β :=
  { toFun := e.toFun
    invFun := e.invFun
    left_inv := e.left_inv
    right_inv := e.right_inv }

/-- Loop-suspension adjunction as a Mathlib `Equiv`. -/
def loopSpaceSuspensionAdjunctionEquiv (X Y : SuspensionLoop.Pointed) :
    Equiv (PointedMap (sigmaPointed X) Y) (PointedMap X (omegaEqPointed Y)) :=
  simpleEquivToEquiv (loopSpaceSuspensionAdjunction (X := X) (Y := Y))

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
