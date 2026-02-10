/-
# Loop-Delooping Adjunction (Pointed Spaces)

This module packages the loop-deloop adjunction for strict groups using
computational-path `Path` equality. It wraps the equivalence
`piOneBG ≃ G` from `DeloopingConstruction` into a `PathSimpleEquiv` and
records the associated unit and counit maps.

## Key Results

- `loopDeloopAdjunction`: Path-based equivalence `piOneBG ≃ G`
- `unit`, `counit`: adjunction unit and counit maps

## References

- HoTT Book, Chapter 6 (classifying spaces)
- `DeloopingConstruction` for the underlying equivalence
-/

import ComputationalPaths.Path.CompPath.DeloopingConstruction
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace LoopSpaceDelooping

open Algebra
open CompPath

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

/-- Loop-deloop adjunction as a `PathSimpleEquiv`. -/
def loopDeloopAdjunction {G : Type u} (S : StrictGroup G) :
    PathSimpleEquiv (piOneBG (S := S)) G :=
  simpleEquivToPathSimpleEquiv (piOneBGEquiv (S := S))

/-- Unit of the loop-deloop adjunction. -/
def unit {G : Type u} (S : StrictGroup G) : G → piOneBG (S := S) :=
  (loopDeloopAdjunction (S := S)).invFun

/-- Counit of the loop-deloop adjunction. -/
def counit {G : Type u} (S : StrictGroup G) : piOneBG (S := S) → G :=
  (loopDeloopAdjunction (S := S)).toFun

end

/-! ## Summary -/

end LoopSpaceDelooping
end Homotopy
end Path
end ComputationalPaths
