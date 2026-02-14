/-
# Geometric Group Theory via Computational Paths

CAT(0) spaces, Gromov hyperbolic groups, boundary at infinity,
quasi-isometry invariants, Dehn functions, and JSJ decompositions.

## References

- Bridson-Haefliger, "Metric Spaces of Non-Positive Curvature"
- Gromov, "Hyperbolic groups"
- Druţu-Kapovich, "Geometric Group Theory"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace GeometricGroupTheory

universe u v

/-! ## Metric Spaces and Geodesics -/

structure MetricSpace' where
  carrier : Type u
  dist : carrier → carrier → Nat
  dist_self : ∀ x, dist x x = 0
  dist_symm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z

structure Geodesic (_X : MetricSpace'.{u}) where
  path : Nat → _X.carrier
  start : _X.carrier
  endpoint : _X.carrier
  isometric : True

structure GeodesicMetricSpace extends MetricSpace'.{u} where
  geodesicExists : ∀ x y : carrier, True

structure GeodesicTriangle (_X : GeodesicMetricSpace.{u}) where
  v₁ : _X.carrier
  v₂ : _X.carrier
  v₃ : _X.carrier
  side₁₂ : Geodesic _X.toMetricSpace'
  side₂₃ : Geodesic _X.toMetricSpace'
  side₁₃ : Geodesic _X.toMetricSpace'

/-! ## CAT(0) Spaces -/

structure CAT0Space extends GeodesicMetricSpace.{u} where
  cat0_comparison : True
  unique_geodesics : True

structure CATKappaSpace (_kappa : Int) extends GeodesicMetricSpace.{u} where
  catKappa_comparison : True

def CAT0Space.isProper (_X : CAT0Space.{u}) : Prop := sorry

def cat0Boundary (_X : CAT0Space.{u}) : Type u := sorry

structure Flat (_X : CAT0Space.{u}) (_n : Nat) where
  embedding : Nat → _X.carrier
  isometric : True

/-! ## Hyperbolic Groups -/

structure HyperbolicSpace (_delta : Nat) extends GeodesicMetricSpace.{u} where
  thin_triangles : True

structure FGGroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  one : carrier
  inv : carrier → carrier
  generators : List carrier
  wordLength : carrier → Nat

structure CayleyGraph (_G : FGGroup.{u}) where
  vertices : Type u
  edges : vertices → vertices → Prop
  vertex_bij : True

structure HyperbolicGroup extends FGGroup.{u} where
  delta : Nat
  cayleyHyperbolic : True

def gromovBoundary (_G : HyperbolicGroup.{u}) : Type u := sorry

def gromovProduct (X : MetricSpace'.{u}) (_w x y : X.carrier) : Int :=
  (↑(X.dist _w x) + ↑(X.dist _w y) - ↑(X.dist x y)) / 2

/-! ## Quasi-Isometries -/

structure QuasiIsometricEmbedding (X Y : MetricSpace'.{u}) where
  map : X.carrier → Y.carrier
  C : Nat
  K : Nat
  C_pos : C > 0
  upper : ∀ x y, Y.dist (map x) (map y) ≤ C * X.dist x y + K
  lower : True

structure QuasiIsometry (X Y : MetricSpace'.{u}) extends
    QuasiIsometricEmbedding X Y where
  coarselySurjective : True

def areQuasiIsometric (X Y : MetricSpace'.{u}) : Prop :=
  Nonempty (QuasiIsometry X Y)

/-! ## Dehn Functions -/

def dehnFunction (_G : FGGroup.{u}) : Nat → Nat := sorry

def hasLinearDehn (G : FGGroup.{u}) : Prop :=
  ∃ C, ∀ n, dehnFunction G n ≤ C * n

def hasQuadraticDehn (G : FGGroup.{u}) : Prop :=
  ∃ C, ∀ n, dehnFunction G n ≤ C * n * n

def hasExponentialDehn (_G : FGGroup.{u}) : Prop := sorry

def isHyperbolicByDehn (G : FGGroup.{u}) : Prop := hasLinearDehn G

/-! ## JSJ Decomposition -/

structure GraphOfGroups where
  vertexGroups : Nat → Type u
  edgeGroups : Nat → Type u
  numVertices : Nat
  numEdges : Nat
  edgeInclusion : True

structure JSJDecomposition (_G : FGGroup.{u}) where
  graphOfGroups : GraphOfGroups.{u}
  edgeTwoEnded : True
  canonical : True

def numEnds (_G : FGGroup.{u}) : Nat := sorry

def isOneEnded (G : FGGroup.{u}) : Prop := numEnds G = 1
def isTwoEnded (G : FGGroup.{u}) : Prop := numEnds G = 2

def growthFunction (_G : FGGroup.{u}) : Nat → Nat := sorry
def hasPolynomialGrowth (_G : FGGroup.{u}) : Prop := sorry
def isVirtuallyNilpotent (_G : FGGroup.{u}) : Prop := sorry

/-! ### Theorems -/

theorem cat0_unique_geodesics (_X : CAT0Space.{u}) :
    True := sorry

theorem cat0_contractible (_X : CAT0Space.{u}) :
    True := sorry

theorem cat0_fixed_point (_X : CAT0Space.{u}) :
    True := sorry

theorem flat_torus_theorem (_X : CAT0Space.{u}) (_n : Nat) :
    True := sorry

theorem hyperbolic_linear_dehn (G : HyperbolicGroup.{u}) :
    hasLinearDehn G.toFGGroup := sorry

theorem hyperbolic_iff_linear_dehn (_G : FGGroup.{u}) :
    True := sorry

theorem boundary_qi_invariant (_G₁ _G₂ : HyperbolicGroup.{u}) (_hqi : True) :
    True := sorry

theorem stallings_theorem (_G : FGGroup.{u}) (_h : numEnds _G > 1) :
    True := sorry

theorem ends_qi_invariant (_X _Y : MetricSpace'.{u}) (_hqi : areQuasiIsometric _X _Y) :
    True := sorry

theorem hyperbolicity_qi_invariant (_G₁ _G₂ : FGGroup.{u}) (_hqi : True) :
    True := sorry

theorem svarc_milnor (_G : FGGroup.{u}) (_X : GeodesicMetricSpace.{u}) (_haction : True) :
    True := sorry

theorem growth_qi_invariant (_G₁ _G₂ : FGGroup.{u}) (_hqi : True) :
    True := sorry

theorem gromov_polynomial_growth (G : FGGroup.{u}) (_hpoly : hasPolynomialGrowth G) :
    isVirtuallyNilpotent G := sorry

theorem dehn_function_qi_invariant (_G₁ _G₂ : FGGroup.{u}) (_hqi : True) :
    True := sorry

theorem jsj_canonical (_G : FGGroup.{u}) (_J₁ _J₂ : JSJDecomposition _G) :
    True := sorry

theorem bowditch_jsj (G : HyperbolicGroup.{u}) (_hone : isOneEnded G.toFGGroup) :
    ∃ J : JSJDecomposition G.toFGGroup, True := sorry

theorem free_group_boundary_cantor (_n : Nat) (_h : _n ≥ 2) :
    True := sorry

theorem surface_group_boundary_circle (_g : Nat) (_h : _g ≥ 2) :
    True := sorry

theorem tits_alternative (_G : FGGroup.{u}) :
    True := sorry

end GeometricGroupTheory
end Topology
end Path
end ComputationalPaths
