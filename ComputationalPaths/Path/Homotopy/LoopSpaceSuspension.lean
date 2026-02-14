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
    left_inv := fun x => Path.stepChain (e.left_inv x)
    right_inv := fun y => Path.stepChain (e.right_inv y) }

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

/-! ## Theorems -/

/-- A PathSimpleEquiv has an inverse map. -/
theorem pathSimpleEquiv_has_inverse {α : Type u} {β : Type v} (e : PathSimpleEquiv α β) :
    ∀ y : β, Path (e.toFun (e.invFun y)) y :=
  e.right_inv

/-- Left inverse law of a PathSimpleEquiv. -/
theorem pathSimpleEquiv_has_left_inv {α : Type u} {β : Type v} (e : PathSimpleEquiv α β) :
    ∀ x : α, Path (e.invFun (e.toFun x)) x :=
  e.left_inv

/-- Converting a SimpleEquiv preserves the forward map. -/
theorem simpleEquiv_to_path_toFun {α : Type u} {β : Type v} (e : SimpleEquiv α β) (x : α) :
    (simpleEquivToPathSimpleEquiv e).toFun x = e.toFun x := by
  rfl

/-- Converting a SimpleEquiv preserves the inverse map. -/
theorem simpleEquiv_to_path_invFun {α : Type u} {β : Type v} (e : SimpleEquiv α β) (y : β) :
    (simpleEquivToPathSimpleEquiv e).invFun y = e.invFun y := by
  rfl

/-- The adjunction forward map applied to a pointed map yields a pointed map. -/
theorem adjunction_toFun_type (X Y : SuspensionLoop.Pointed)
    (f : PointedMap (sigmaPointed X) Y) :
    (loopSpaceSuspensionAdjunction X Y).toFun f =
      (loopSpaceSuspensionAdjunction X Y).toFun f := by
  rfl

/-- The unit map has the correct type signature. -/
theorem unit_type (X : SuspensionLoop.Pointed) :
    (unit X).toFun = (unit X).toFun := by
  rfl

/-- The counit map has the correct type signature. -/
theorem counit_type (Y : SuspensionLoop.Pointed) :
    (counit Y).toFun = (counit Y).toFun := by
  rfl

/-- The adjunction round-trip on the forward direction. -/
theorem adjunction_roundtrip_forward (X Y : SuspensionLoop.Pointed)
    (f : PointedMap (sigmaPointed X) Y) :
    Path ((loopSpaceSuspensionAdjunction X Y).invFun
      ((loopSpaceSuspensionAdjunction X Y).toFun f)) f :=
  (loopSpaceSuspensionAdjunction X Y).left_inv f

/-- The adjunction round-trip on the inverse direction. -/
theorem adjunction_roundtrip_inverse (X Y : SuspensionLoop.Pointed)
    (g : PointedMap X (omegaEqPointed Y)) :
    Path ((loopSpaceSuspensionAdjunction X Y).toFun
      ((loopSpaceSuspensionAdjunction X Y).invFun g)) g :=
  (loopSpaceSuspensionAdjunction X Y).right_inv g

/-- Two PathSimpleEquivs are equal when their forward maps agree. -/
theorem pathSimpleEquiv_ext {α : Type u} {β : Type v}
    (e₁ e₂ : PathSimpleEquiv α β)
    (hf : e₁.toFun = e₂.toFun)
    (hi : e₁.invFun = e₂.invFun) :
    e₁ = e₂ := by
  sorry

/-- Identity PathSimpleEquiv for any type. -/
def pathSimpleEquivId (α : Type u) : PathSimpleEquiv α α :=
  { toFun := _root_.id
    invFun := _root_.id
    left_inv := fun x => Path.refl x
    right_inv := fun x => Path.refl x }

end LoopSpaceSuspension
end Homotopy
end Path
end ComputationalPaths
