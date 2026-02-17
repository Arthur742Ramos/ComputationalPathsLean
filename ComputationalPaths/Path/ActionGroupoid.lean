/-
# Action Groupoids and Path Actions

This module records how strict group actions interact with computational paths.
We lift a group action to paths and rewrite-quotiented paths, define the
canonical loop actions on path spaces, and show that each path space is a
torsor for the loop group.  The final section recalls the covering-space
fiber action as a group action.

## Key Results

- `pathAction`, `pathQuotAction`: actions on paths and path quotients
- `leftPathAction`, `rightPathAction`: loop actions on path spaces
- `leftPathOrbitEquiv`: torsor/orbit-stabilizer equivalence for path spaces
- `leftPathStabilizer_eq_id`: stabilizers are trivial for left loop actions
- `coveringFiberAction`: covering-space fiber action as a group action
-/

import ComputationalPaths.Path.Algebra.GroupActionOps
import ComputationalPaths.Path.Homotopy.LoopGroupAlgebra
import ComputationalPaths.Path.Homotopy.CoveringFibrationAlgebra
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path
namespace ActionGroupoid

open Algebra
open Homotopy

universe u v

/-! ## Actions on computational paths -/

section PathActions

variable {G : Type u} {X : Type v} {S : StrictGroup G}
variable (A : GroupAction G S X)

/-- Act on a computational path by applying the group action to its endpoints. -/
def pathAction (g : G) {x y : X} :
    Path x y → Path (A.act g x) (A.act g y) :=
  Path.congrArg (A.act g)

/-- `pathAction` preserves reflexive paths. -/
@[simp] theorem pathAction_refl (g : G) (x : X) :
    pathAction A g (Path.refl x) = Path.refl (A.act g x) := by
  rfl

/-- `pathAction` preserves path concatenation. -/
@[simp] theorem pathAction_trans (g : G) {x y z : X}
    (p : Path x y) (q : Path y z) :
    pathAction A g (Path.trans p q) =
      Path.trans (pathAction A g p) (pathAction A g q) := by
  simp [pathAction]

/-- `pathAction` commutes with path reversal. -/
@[simp] theorem pathAction_symm (g : G) {x y : X} (p : Path x y) :
    pathAction A g (Path.symm p) = Path.symm (pathAction A g p) := by
  simp [pathAction]


/-- Act on rewrite-quotiented paths by applying the group action to endpoints. -/
def pathQuotAction (g : G) {x y : X} :
    PathRwQuot X x y → PathRwQuot X (A.act g x) (A.act g y) :=
  PathRwQuot.congrArg X X (A.act g)

/-- `pathQuotAction` preserves reflexive quotient paths. -/
@[simp] theorem pathQuotAction_refl (g : G) (x : X) :
    pathQuotAction A g (PathRwQuot.refl (A := X) x) =
      PathRwQuot.refl (A := X) (A.act g x) := by
  simp [pathQuotAction]

/-- `pathQuotAction` preserves quotient composition. -/
@[simp] theorem pathQuotAction_trans (g : G) {x y z : X}
    (p : PathRwQuot X x y) (q : PathRwQuot X y z) :
    pathQuotAction A g (PathRwQuot.trans p q) =
      PathRwQuot.trans (pathQuotAction A g p) (pathQuotAction A g q) := by
  simp [pathQuotAction]

/-- `pathQuotAction` commutes with quotient symmetry. -/
@[simp] theorem pathQuotAction_symm (g : G) {x y : X} (p : PathRwQuot X x y) :
    pathQuotAction A g (PathRwQuot.symm p) =
      PathRwQuot.symm (pathQuotAction A g p) := by
  simp [pathQuotAction]


end PathActions

/-! ## Loop actions on path spaces -/

section LoopActions

variable {A : Type u} {a b : A}

/-- Left action of the loop group on the path space `PathRwQuot A a b`. -/
def leftPathAction (A : Type u) (a b : A) :
    GroupAction (LoopQuot A a) (LoopGroupAlgebra.loopGroupStructure A a)
      (PathRwQuot A a b) where
  act := fun g p => PathRwQuot.trans g p
  act_one := by
    intro p
    simp [LoopGroupAlgebra.loopGroupStructure]
  act_mul := by
    intro g h p
    simp [LoopGroupAlgebra.loopGroupStructure, PathRwQuot.trans_assoc]

/-- Right action of the loop group on the path space, encoded via inversion. -/
def rightPathAction (A : Type u) (a b : A) :
    GroupAction (LoopQuot A b) (LoopGroupAlgebra.loopGroupStructure A b)
      (PathRwQuot A a b) where
  act := fun g p => PathRwQuot.trans p (LoopQuot.inv g)
  act_one := by
    intro p
    calc
      PathRwQuot.trans p (LoopQuot.inv (LoopQuot.id (A := A) (a := b)))
          = PathRwQuot.trans p (LoopQuot.id (A := A) (a := b)) := by
            rw [LoopQuot.inv_id]
      _ = p := by
            simp
  act_mul := by
    intro g h p
    calc
      PathRwQuot.trans p (LoopQuot.inv (LoopQuot.comp g h))
          = PathRwQuot.trans p (LoopQuot.comp (LoopQuot.inv h) (LoopQuot.inv g)) := by
              rw [LoopQuot.inv_comp_rev]
      _ = PathRwQuot.trans (PathRwQuot.trans p (LoopQuot.inv h)) (LoopQuot.inv g) := by
            simp [PathRwQuot.trans_assoc]

/-- Every path lies in the left orbit of any other path. -/
theorem leftPathOrbit (p q : PathRwQuot A a b) :
    GroupAction.Orbit (leftPathAction A a b) p q := by
  refine ⟨PathRwQuot.trans q (PathRwQuot.symm p), ?_⟩
  simp [leftPathAction, PathRwQuot.trans_assoc]

/-- The left loop action identifies the path space with the loop group (torsor). -/
def leftPathOrbitEquiv (p : PathRwQuot A a b) :
    SimpleEquiv (LoopQuot A a) (PathRwQuot A a b) where
  toFun := fun g => PathRwQuot.trans g p
  invFun := fun q => PathRwQuot.trans q (PathRwQuot.symm p)
  left_inv := by
    intro g
    simp [PathRwQuot.trans_assoc]
  right_inv := by
    intro q
    simp [PathRwQuot.trans_assoc]

/-- The stabilizer of a path under the left loop action is trivial. -/
theorem leftPathStabilizer_eq_id (p : PathRwQuot A a b) (g : LoopQuot A a)
    (h : (leftPathAction A a b).act g p = p) :
    g = LoopQuot.id := by
  have h' := _root_.congrArg (fun q => PathRwQuot.trans q (PathRwQuot.symm p)) h
  simpa [leftPathAction, PathRwQuot.trans_assoc] using h'

end LoopActions

/-! ## Covering space connection -/

section CoveringActions

variable {A : Type u}

/-- The π₁-action on fibers from covering space theory, packaged as a group action. -/
noncomputable abbrev coveringFiberAction {P : A → Type u} (a : A) :
    GroupAction (LoopQuot A a) (LoopGroupAlgebra.loopGroupStructure A a) (P a) :=
  CoveringFibrationAlgebra.fiberActionGroupAction (P := P) a

end CoveringActions

/-! ## Summary

This module packages actions of strict groups on computational paths,
constructs the left/right loop actions on path spaces, and records the torsor
equivalence underlying orbit-stabilizer for paths.  It also reuses the
covering-space fiber action as a canonical group action.
-/

end ActionGroupoid
end Path
end ComputationalPaths
