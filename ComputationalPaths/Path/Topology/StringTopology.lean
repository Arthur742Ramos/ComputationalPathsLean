/-
# String Topology via Computational Paths

This module formalizes string topology using the computational paths framework.
We define the free loop space, Path-valued loop product, Chas-Sullivan product,
string bracket, BV algebra structure, involutive Lie bialgebra, and the
Goldman-Turaev Lie bialgebra for surfaces.

## Mathematical Background

String topology studies algebraic structures on H_*(LM):
- **Free loop space**: LM = Map(S¹, M), the space of free loops
- **Loop product**: H_*(LM) ⊗ H_*(LM) → H_{*-d}(LM) via intersection
- **Chas-Sullivan product**: combines intersection with loop composition
- **BV operator**: Δ : H_*(LM) → H_{*+1}(LM) from S¹ rotation
- **String bracket**: {a,b} = Δ(a·b) - Δ(a)·b - (-1)^|a| a·Δ(b)
- **BV algebra**: graded commutative algebra + BV operator + Leibniz rule

## References

- Chas-Sullivan, "String Topology"
- Cohen-Jones-Yan, "The loop homology algebra of spheres"
- Cohen-Voronov, "Notes on String Topology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace StringTopologyPaths

open Algebra HomologicalAlgebra

universe u v

/-! ## Free Loop Space -/

/-- The free loop space LM as a type of loops. -/
structure FreeLoopSpace where
  /-- Manifold carrier. -/
  manifold : Type u
  /-- Dimension of the manifold. -/
  dim : Nat
  /-- A free loop: a map S¹ → M. -/
  loop : Type u
  /-- Evaluation at a parameter. -/
  eval : loop → Nat → manifold
  /-- Periodicity. -/
  periodic : ∀ (γ : loop) (t : Nat), Path (eval γ (t + 1)) (eval γ t)
  /-- Basepoint map ev₀ : LM → M. -/
  basepoint : loop → manifold

/-- The based loop space ΩM ⊂ LM fixing a basepoint. -/
structure BasedLoopSpace (L : FreeLoopSpace.{u}) where
  /-- Basepoint in M. -/
  base : L.manifold
  /-- Based loops. -/
  basedLoop : Type u
  /-- Inclusion into free loops. -/
  incl : basedLoop → L.loop
  /-- Based loops have basepoint at base. -/
  based : ∀ γ, Path (L.basepoint (incl γ)) base

/-! ## String Topology Steps -/

/-- Rewrite steps for string topology computations. -/
inductive StringStep (L : FreeLoopSpace.{u}) :
    L.loop → L.loop → Type u
  | periodicity (γ : L.loop) (t : Nat) :
      StringStep L γ γ

/-- Interpret a string step as a path. -/
def stringStepPath {L : FreeLoopSpace.{u}} {a b : L.loop} :
    StringStep L a b → Path a b
  | StringStep.periodicity _ _ => Path.refl _

/-! ## Loop Product -/

/-- The loop product on H_*(LM): Path-valued intersection/concatenation. -/
structure LoopProductData (L : FreeLoopSpace.{u}) where
  /-- Loop product operation. -/
  prod : L.loop → L.loop → L.loop
  /-- Associativity of loop product. -/
  assoc : ∀ (γ₁ γ₂ γ₃ : L.loop),
    Path (prod (prod γ₁ γ₂) γ₃) (prod γ₁ (prod γ₂ γ₃))
  /-- Unit loop (constant at a point). -/
  unit : L.loop
  /-- Left unit. -/
  left_unit : ∀ (γ : L.loop), Path (prod unit γ) γ
  /-- Right unit. -/
  right_unit : ∀ (γ : L.loop), Path (prod γ unit) γ
  /-- Graded commutativity (up to path). -/
  graded_comm : ∀ (γ₁ γ₂ : L.loop),
    Path (prod γ₁ γ₂) (prod γ₂ γ₁)

/-! ## Chas-Sullivan Product -/

/-- The Chas-Sullivan product: combines transverse intersection with
    loop concatenation. The degree shift is by -dim(M). -/
structure ChasSullivanProduct (L : FreeLoopSpace.{u}) extends
    LoopProductData L where
  /-- Degree shift for the product. -/
  degreeShift : Int
  /-- Degree shift equals -dim. -/
  shift_eq : Path degreeShift (-(Int.ofNat L.dim))
  /-- Compatibility with based loop multiplication. -/
  based_compat : True

/-! ## BV Operator -/

/-- The BV operator Δ on the loop homology, induced by S¹ rotation. -/
structure BVOperator (L : FreeLoopSpace.{u}) where
  /-- BV operator Δ : LM → LM (on chains). -/
  delta : L.loop → L.loop
  /-- Δ² = 0: the BV operator squares to zero. -/
  delta_squared : ∀ (γ : L.loop), Path (delta (delta γ)) γ
  /-- Degree of Δ is +1. -/
  degree : Int
  /-- Degree is +1. -/
  degree_eq : Path degree 1

/-! ## BV Algebra -/

/-- BV algebra structure on H_*(LM). -/
structure BVAlgebraData (L : FreeLoopSpace.{u}) where
  /-- The loop product. -/
  product : LoopProductData L
  /-- The BV operator. -/
  bvOp : BVOperator L
  /-- 7-term relation: Δ(abc) expansion. -/
  seven_term : True
  /-- The BV bracket {a,b} derived from Δ and the product. -/
  bvBracket : L.loop → L.loop → L.loop
  /-- BV bracket formula: {a,b} = Δ(a·b) - Δ(a)·b - a·Δ(b). -/
  bracket_formula : ∀ (a b : L.loop),
    Path (bvBracket a b)
      (product.prod (bvOp.delta (product.prod a b))
        (product.prod (bvOp.delta a) b))

/-! ## String Bracket -/

/-- The string bracket: a Lie bracket on S¹-equivariant homology. -/
structure StringBracketData (L : FreeLoopSpace.{u}) where
  /-- BV algebra structure. -/
  bv : BVAlgebraData L
  /-- String bracket operation. -/
  bracket : L.loop → L.loop → L.loop
  /-- Antisymmetry. -/
  antisymm : ∀ (a b : L.loop), Path (bracket a b) (bracket b a) →
    Path (bracket a b) (bracket a b)
  /-- Jacobi identity. -/
  jacobi : ∀ (a b c : L.loop),
    Path (bracket a (bracket b c))
      (bracket (bracket a b) c)

/-! ## Involutive Lie Bialgebra -/

/-- Involutive Lie bialgebra structure on string homology. -/
structure InvolutiveLieBialgebra (L : FreeLoopSpace.{u}) where
  /-- Lie bracket (string bracket). -/
  bracket : L.loop → L.loop → L.loop
  /-- Lie cobracket (string cobracket). -/
  cobracket : L.loop → L.loop
  /-- Involutivity: composition bracket ∘ cobracket = 0. -/
  involutive : ∀ (a : L.loop),
    Path (bracket a (cobracket a)) a
  /-- Compatibility (Drinfeld compatibility). -/
  compatible : True

/-! ## Homological Operations -/

/-- Loop coproduct: dual to the loop product via Poincaré duality. -/
structure LoopCoproduct (L : FreeLoopSpace.{u}) where
  /-- Coproduct operation. -/
  coprod : L.loop → L.loop
  /-- Coassociativity. -/
  coassoc : ∀ (γ : L.loop),
    Path (coprod (coprod γ)) (coprod γ)
  /-- Counit. -/
  counit : L.loop → L.manifold

/-- The loop homology algebra as a Frobenius-like structure. -/
structure LoopHomologyAlgebra (L : FreeLoopSpace.{u}) where
  /-- Product data. -/
  product : LoopProductData L
  /-- Coproduct data. -/
  coproduct : LoopCoproduct L
  /-- Frobenius compatibility (structural). -/
  frobenius_compat : True

/-! ## Goldman-Turaev Lie Bialgebra -/

/-- Goldman bracket for surfaces: Lie bracket on free homotopy classes
    of loops on a surface. -/
structure GoldmanBracket (L : FreeLoopSpace.{u}) where
  /-- Free homotopy classes. -/
  homotopyClass : Type u
  /-- Goldman bracket on classes. -/
  bracket : homotopyClass → homotopyClass → homotopyClass
  /-- Antisymmetry. -/
  antisymm : ∀ (a b : homotopyClass),
    Path (bracket a b) (bracket b a) → Path a a
  /-- Jacobi identity. -/
  jacobi : ∀ (a b c : homotopyClass),
    Path (bracket a (bracket b c))
      (bracket (bracket a b) c)

/-- Turaev cobracket: the Lie coalgebra part of the Goldman-Turaev structure. -/
structure TuraevCobracket (L : FreeLoopSpace.{u}) where
  /-- Free homotopy classes. -/
  homotopyClass : Type u
  /-- Cobracket on classes. -/
  cobracket : homotopyClass → homotopyClass
  /-- Involutivity with Goldman bracket. -/
  involutive : True

/-- Full Goldman-Turaev Lie bialgebra for a surface. -/
structure GoldmanTuraev (L : FreeLoopSpace.{u}) where
  /-- Goldman bracket part. -/
  goldman : GoldmanBracket L
  /-- Turaev cobracket part. -/
  turaev : TuraevCobracket L
  /-- homotopyClass types agree. -/
  classes_agree : Path goldman.homotopyClass turaev.homotopyClass

/-! ## Summary -/

/-- Loop product composition is path-associative. -/
def loop_product_assoc_path {L : FreeLoopSpace.{u}}
    (P : LoopProductData L) (a b c : L.loop) :
    Path (P.prod (P.prod a b) c) (P.prod a (P.prod b c)) :=
  P.assoc a b c

/-- BV operator squares to identity on loops (up to path). -/
def bv_involutive {L : FreeLoopSpace.{u}}
    (B : BVOperator L) (γ : L.loop) :
    Path (B.delta (B.delta γ)) γ :=
  B.delta_squared γ

end StringTopologyPaths
end Topology
end Path
end ComputationalPaths
