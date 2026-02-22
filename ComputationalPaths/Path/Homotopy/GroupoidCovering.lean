/-
# Covering Spaces and Fundamental Groupoid Actions

This module packages the classification of covering spaces via actions of the
fundamental groupoid. Coverings are type families with set-valued fibers; groupoid
actions are type-valued functors with set-valued fibers. The two viewpoints are
equivalent, and the action on loops recovers the usual pi_1 action on fibers.

## Key Results

- `groupoidFiberAction`: action of the fundamental groupoid on fibers by transport
- `coveringGroupoidActionEquiv`: coverings ↔ groupoid actions
- `groupoidFiberAction_pi_one`: restriction to loops agrees with the pi_1 action

## References

- HoTT Book, Chapter 8.4
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.CoveringFibrationAlgebra
import ComputationalPaths.Path.Homotopy.CoveringSpace
import ComputationalPaths.Path.Homotopy.CoveringSpaceLifting
import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Homotopy.GrothendieckConstruction

namespace ComputationalPaths
namespace Path
namespace CoveringSpace

open Algebra
open Truncation

universe u

variable {A : Type u}

/-! ## Bundled coverings and groupoid actions -/

/-- A covering space over `A` as a type family with set-valued fibers. -/
structure Covering (A : Type u) : Type (u + 1) where
  /-- Underlying fiber family. -/
  fiber : A → Type u
  /-- Each fiber is a set. -/
  isCovering : IsCovering (A := A) fiber

/-- A set-valued action of the fundamental groupoid on `A`. -/
structure GroupoidAction (A : Type u) : Type (u + 1) where
  /-- Underlying type-valued functor on the fundamental groupoid. -/
  functor : FundamentalGroupoidTypeFunctor A
  /-- Each fiber of the functor is a set. -/
  fiberIsSet : (a : A) → IsSet (functor.obj a)

/-! ## Fundamental groupoid action on fibers -/

/-- Action of the fundamental groupoid on fibers via quotient transport. -/
noncomputable def groupoidFiberAction {P : A → Type u} {a b : A}
    (p : FundamentalGroupoid.Hom A a b) : P a → P b :=
  fiberTransportQuot (P := P) (a := a) (b := b) p

/-- Identity law for the groupoid action on fibers. -/
@[simp] theorem groupoidFiberAction_id {P : A → Type u} {a : A} (x : P a) :
    groupoidFiberAction (P := P) (a := a) (b := a)
        (FundamentalGroupoid.id' A a) x = x := by
  simp [groupoidFiberAction, FundamentalGroupoid.id']

/-- Composition law for the groupoid action on fibers. -/
@[simp] theorem groupoidFiberAction_comp {P : A → Type u} {a b c : A}
    (p : FundamentalGroupoid.Hom A a b) (q : FundamentalGroupoid.Hom A b c) (x : P a) :
    groupoidFiberAction (P := P) (a := a) (b := c)
        (FundamentalGroupoid.comp' A p q) x =
      groupoidFiberAction (P := P) (a := b) (b := c) q
        (groupoidFiberAction (P := P) (a := a) (b := b) p x) := by
  simp [groupoidFiberAction, FundamentalGroupoid.comp']

/-! ## Equivalence between coverings and groupoid actions -/

/-- Build the groupoid action associated to a covering space. -/
noncomputable def coveringToGroupoidAction (C : Covering A) : GroupoidAction A :=
  ⟨fibrationToFunctor (A := A) C.fiber, C.isCovering.fiberIsSet⟩

/-- Forget a groupoid action to obtain the underlying covering space. -/
noncomputable def groupoidActionToCovering (G : GroupoidAction A) : Covering A :=
  ⟨functorToFibration (A := A) G.functor, ⟨G.fiberIsSet⟩⟩

/-- Covering spaces are equivalent to set-valued fundamental groupoid actions. -/
noncomputable def coveringGroupoidActionEquiv (A : Type u) :
    SimpleEquiv (Covering A) (GroupoidAction A) where
  toFun := coveringToGroupoidAction
  invFun := groupoidActionToCovering
  left_inv := by
    intro C
    cases C with
    | mk P hP =>
        cases hP
        simp [coveringToGroupoidAction, groupoidActionToCovering,
          functorToFibration_right_inv]
  right_inv := by
    intro G
    cases G with
    | mk F hF =>
        simp [coveringToGroupoidAction, groupoidActionToCovering,
          functorToFibration_left_inv]

/-! ## Classification via pi_1 actions -/

/-- The pi_1 action associated to a covering space. -/
noncomputable def coveringPiOneAction (C : Covering A) (a : A) :
    GroupAction (LoopQuot A a)
      (Homotopy.CoveringFibrationAlgebra.loopGroupStructure A a) (C.fiber a) :=
  Homotopy.CoveringFibrationAlgebra.fiberActionGroupAction (P := C.fiber) a

/-- Classification via pi_1-actions: the groupoid action on a fiber restricts to
the standard pi_1 action on loops. -/
theorem groupoidFiberAction_pi_one {P : A → Type u} {a : A}
    (g : LoopQuot A a) (x : P a) :
    groupoidFiberAction (P := P) (a := a) (b := a) g x =
      fiberAction (P := P) (a := a) g x := by
  induction g using Quot.ind with
  | _ l => rfl

/-! ## Summary

1. Coverings can be bundled as type families with set-valued fibers.
2. Groupoid actions are functors to types with set-valued fibers.
3. Coverings and groupoid actions are equivalent.
4. The groupoid action restricts to the standard pi_1 action on each fiber.
-/

end CoveringSpace
end Path
end ComputationalPaths
