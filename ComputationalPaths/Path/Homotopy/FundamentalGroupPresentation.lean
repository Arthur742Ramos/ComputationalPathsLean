/-
# Fundamental group presentations

This module records generator/relator data for fundamental group computations
already formalized in the library, packaging them as explicit presentations and
connecting to the existing π₁ equivalences.

## Key Results
- `FundamentalGroupPresentation`: presentation data (generators + relations).
- `circlePresentation`, `torusPresentation`, `figureEightPresentation`,
  `spherePresentation`: presentations for standard computational-path spaces.

## References
- HoTT Book, Chapter 8
- de Queiroz et al., SAJL 2016
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.Torus
import ComputationalPaths.Path.CompPath.TorusStep
import ComputationalPaths.Path.CompPath.FigureEight
import ComputationalPaths.Path.CompPath.FigureEightStep
import ComputationalPaths.Path.CompPath.SphereCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

open CompPath
open SimpleEquiv

universe u v w x

/-! ## Presentation structure -/

/-- Presentation data for a fundamental-group type `G`. -/
structure FundamentalGroupPresentation (G : Type u) where
  /-- The group in which the presentation is stated. -/
  presentationGroup : Type v
  /-- Equivalence from `G` to the presented group. -/
  equiv : SimpleEquiv G presentationGroup
  /-- Generator indices. -/
  generators : Type w
  /-- Chosen generators inside the presented group. -/
  generator : generators → presentationGroup
  /-- Relation indices. -/
  relations : Type x
  /-- Left-hand side of a relation. -/
  relationLhs : relations → presentationGroup
  /-- Right-hand side of a relation. -/
  relationRhs : relations → presentationGroup
  /-- Proof that each relation holds. -/
  relationEq : ∀ r, relationLhs r = relationRhs r

/-! ## Circle presentation -/

/-- Generator for the circle presentation. -/
inductive CircleGenerator where
  | loop

/-- Presentation of π₁(S¹) as a single generator with no relations. -/
noncomputable def circlePresentation :
    FundamentalGroupPresentation circlePiOne.{u} where
  presentationGroup := Int
  equiv := circlePiOneEquivInt.{u}
  generators := CircleGenerator
  generator := fun
    | CircleGenerator.loop => circlePiOneEquivInt.{u} circlePiOneLoop.{u}
  relations := PEmpty
  relationLhs := by intro r; cases r
  relationRhs := by intro r; cases r
  relationEq := by intro r; cases r

/-- The circle generator corresponds to `1 : ℤ`. -/
@[simp] theorem circlePresentation_generator_value.{u₁} :
    circlePresentation.{u₁}.generator CircleGenerator.loop = (1 : Int) := by
  change circlePiOneEquivInt.{u₁}.toFun circlePiOneLoop.{u₁} = (1 : Int)
  dsimp [circlePiOneEquivInt, circlePiOneLoop]
  exact circlePiOneEncode_circleDecode.{u₁} (z := (1 : Int))

/-! ## Torus presentation -/

/-- Generators for the torus presentation. -/
inductive TorusGenerator where
  | loop1
  | loop2

/-- Relation expressing commutativity of the torus generators. -/
inductive TorusRelation where
  | comm

/-- Componentwise addition on `ℤ × ℤ`. -/
def intProdAdd (x y : Int × Int) : Int × Int :=
  (x.1 + y.1, x.2 + y.2)

/-- Presentation of π₁(T²) with two commuting generators. -/
noncomputable def torusPresentation :
    FundamentalGroupPresentation torusPiOne.{u} :=
  let torusGenerator : TorusGenerator → Int × Int
    | TorusGenerator.loop1 => torusPiOneEquivIntProdSimple.{u} (torusDecode.{u} (1, 0))
    | TorusGenerator.loop2 => torusPiOneEquivIntProdSimple.{u} (torusDecode.{u} (0, 1))
  { presentationGroup := Int × Int
    equiv := torusPiOneEquivIntProdSimple.{u}
    generators := TorusGenerator
    generator := torusGenerator
    relations := TorusRelation
    relationLhs := fun _ =>
      intProdAdd
        (torusGenerator TorusGenerator.loop1)
        (torusGenerator TorusGenerator.loop2)
    relationRhs := fun _ =>
      intProdAdd
        (torusGenerator TorusGenerator.loop2)
        (torusGenerator TorusGenerator.loop1)
    relationEq := by
      intro r
      cases r
      simp [intProdAdd, torusGenerator, Int.add_comm] }

/-- The first torus generator maps to `(1, 0)`. -/
@[simp] theorem torusPresentation_generator_loop1 :
    torusPresentation.generator TorusGenerator.loop1 = (1, 0) := by
  change torusPiOneEquivIntProdSimple.toFun (torusDecode (1, 0)) = (1, 0)
  dsimp [torusPiOneEquivIntProdSimple]
  exact torusPiOneEncode_torusDecode_eq (z := (1, 0))

/-- The second torus generator maps to `(0, 1)`. -/
@[simp] theorem torusPresentation_generator_loop2 :
    torusPresentation.generator TorusGenerator.loop2 = (0, 1) := by
  change torusPiOneEquivIntProdSimple.toFun (torusDecode (0, 1)) = (0, 1)
  dsimp [torusPiOneEquivIntProdSimple]
  exact torusPiOneEncode_torusDecode_eq (z := (0, 1))

/-! ## Figure-eight presentation -/

/-- Generators for the figure-eight presentation. -/
inductive FigureEightGenerator where
  | loopA
  | loopB

/-- Presentation of π₁(S¹ ∨ S¹) as a free product on two generators. -/
noncomputable def figureEightPresentation
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    FundamentalGroupPresentation FigureEight.FigureEightPiOne where
  presentationGroup := FigureEightFreeGroup
  equiv := FigureEight.figureEightPiOneEquivFreeGroup
  generators := FigureEightGenerator
  generator := fun
    | FigureEightGenerator.loopA =>
        FigureEight.figureEightPiOneEquivFreeGroup FigureEight.loopAClass
    | FigureEightGenerator.loopB =>
        FigureEight.figureEightPiOneEquivFreeGroup FigureEight.loopBClass
  relations := PEmpty
  relationLhs := by intro r; cases r
  relationRhs := by intro r; cases r
  relationEq := by intro r; cases r

/-! ## Sphere presentation -/

/-- Presentation of π₁(S²) as the trivial group. -/
noncomputable def spherePresentation :
    FundamentalGroupPresentation
      (π₁(Sphere2CompPath.{u},
        (Sphere2CompPath.basepoint : Sphere2CompPath.{u}))) where
  presentationGroup := Unit
  equiv := Sphere2CompPath.sphere2CompPath_pi1_equiv_unit
  generators := PEmpty
  generator := by intro r; cases r
  relations := PEmpty
  relationLhs := by intro r; cases r
  relationRhs := by intro r; cases r
  relationEq := by intro r; cases r

/-! ## Summary

We package the computational-path π₁ computations as explicit generator/relator
presentations for the circle, torus, figure-eight, and sphere.
-/

/-! ## Theorems -/

/-- A presentation's equivalence round-trips on the left. -/
theorem presentation_left_inv {G : Type u} (P : FundamentalGroupPresentation G)
    (x : G) :
    P.equiv.invFun (P.equiv.toFun x) = x :=
  P.equiv.left_inv x

/-- A presentation's equivalence round-trips on the right. -/
theorem presentation_right_inv {G : Type u} (P : FundamentalGroupPresentation G)
    (y : P.presentationGroup) :
    P.equiv.toFun (P.equiv.invFun y) = y :=
  P.equiv.right_inv y

/-- The circle presentation has exactly one generator type. -/
theorem circlePresentation_one_generator :
    (circlePresentation.generators) = CircleGenerator := by
  rfl

/-- The circle presentation has no relations. -/
theorem circlePresentation_no_relations :
    (circlePresentation.relations) = PEmpty := by
  rfl

/-- The torus presentation has two generators. -/
theorem torusPresentation_two_generators :
    (torusPresentation.generators) = TorusGenerator := by
  rfl

/-- The torus presentation has one relation (commutativity). -/
theorem torusPresentation_one_relation :
    (torusPresentation.relations) = TorusRelation := by
  rfl

/-- The sphere presentation has no generators. -/
theorem spherePresentation_no_generators :
    (spherePresentation.generators) = PEmpty := by
  rfl

/-- The sphere presentation has no relations. -/
theorem spherePresentation_no_relations :
    (spherePresentation.relations) = PEmpty := by
  rfl

/-- The figure-eight presentation has no relations (free group). -/
theorem figureEightPresentation_no_relations
    [HasWedgeSVKDecodeBijective Circle Circle circleBase circleBase] :
    (figureEightPresentation.relations) = PEmpty := by
  rfl

/-- intProdAdd is commutative. -/
theorem intProdAdd_comm (x y : Int × Int) :
    intProdAdd x y = intProdAdd y x := by
  simp [intProdAdd, Int.add_comm]

end Path
end ComputationalPaths
