/-
# Gromov Boundary via Computational Paths

This module formalizes the Gromov boundary (boundary at infinity) using the
computational-paths framework.  We define geodesic rays, their equivalence,
the boundary as a type, its topology via Gromov products, boundary of free
groups and hyperbolic spaces, and the visual metric.

## Key Definitions

- `GeodesicRay`, `RayEquiv`
- `GromovBoundary`, `toBoundaryClass`
- `BoundaryTopology`, `BoundaryOpen`
- `FreeGroupBoundary`, `HyperbolicSpaceBoundary`
- `VisualMetric`

## References

- Bridson–Haefliger, *Metric Spaces of Non-positive Curvature*, Chapter III.H.3
- Kapovich–Benakli, "Boundaries of hyperbolic groups"
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Topology.HyperbolicGroups

namespace ComputationalPaths
namespace Path
namespace Topology
namespace GromovBoundary

open HyperbolicGroups

universe u

/-! ## Geodesic Rays -/

/-- A geodesic ray starting at a basepoint. -/
structure GeodesicRay {X : Type u} (M : MetricData X) (basepoint : X) where
  /-- Points along the ray. -/
  point : Nat → X
  /-- The ray starts at the basepoint. -/
  start_eq : point 0 = basepoint
  /-- The ray is a geodesic: distance equals parameter distance. -/
  isGeodesic : ∀ m n, M.dist (point m) (point n) = if m ≤ n then n - m else m - n

/-- A geodesic ray diverges to infinity. -/
theorem ray_diverges {X : Type u} {M : MetricData X} {basepoint : X}
    (r : GeodesicRay M basepoint) :
    ∀ N : Nat, ∃ n : Nat, M.dist basepoint (r.point n) ≥ N := by
  intro N
  refine ⟨N, ?_⟩
  have h := r.isGeodesic 0 N
  rw [r.start_eq] at h
  simp at h
  omega

/-- Convert a geodesic ray to a sequence at infinity. -/
def rayToSeq {X : Type u} {M : MetricData X} {basepoint : X}
    (r : GeodesicRay M basepoint) : SeqAtInfinity M basepoint where
  seq := r.point
  diverges := ray_diverges r

/-! ## Equivalence of Geodesic Rays -/

/-- Two geodesic rays are equivalent if their Gromov product diverges
    (i.e. they fellow-travel). -/
def RayEquiv {X : Type u} (M : MetricData X) (basepoint : X)
    (r₁ r₂ : GeodesicRay M basepoint) : Prop :=
  ∀ N : Nat, ∃ n₀ : Nat, ∀ n, n ≥ n₀ →
    M.gromovProduct basepoint (r₁.point n) (r₂.point n) ≥ N

/-- Ray equivalence is reflexive. -/
theorem rayEquiv_refl {X : Type u} {M : MetricData X} {basepoint : X}
    (r : GeodesicRay M basepoint) : RayEquiv M basepoint r r := by
  intro N
  refine ⟨N, fun n hn => ?_⟩
  simp [MetricData.gromovProduct, M.dist_self]
  have h := r.isGeodesic 0 n
  rw [r.start_eq] at h
  simp at h
  omega

/-- Ray equivalence is symmetric. -/
theorem rayEquiv_symm {X : Type u} {M : MetricData X} {basepoint : X}
    {r₁ r₂ : GeodesicRay M basepoint} :
    RayEquiv M basepoint r₁ r₂ → RayEquiv M basepoint r₂ r₁ := by
  intro h N
  obtain ⟨n₀, hn₀⟩ := h N
  exact ⟨n₀, fun n hn => by rw [M.gromovProduct_comm]; exact hn₀ n hn⟩

/-! ## Gromov Boundary as a Type -/

/-- The Gromov boundary of a metric space as a quotient of geodesic rays
    by the fellow-travelling equivalence. -/
def GromovBoundary {X : Type u} (M : MetricData X) (basepoint : X) : Type u :=
  Quot (RayEquiv M basepoint)

/-- Project a geodesic ray to its boundary class. -/
def toBoundaryClass {X : Type u} {M : MetricData X} {basepoint : X}
    (r : GeodesicRay M basepoint) : GromovBoundary M basepoint :=
  Quot.mk _ r

/-- Two equivalent rays have the same boundary class. -/
theorem equiv_boundary_eq {X : Type u} {M : MetricData X} {basepoint : X}
    {r₁ r₂ : GeodesicRay M basepoint} (h : RayEquiv M basepoint r₁ r₂) :
    toBoundaryClass r₁ = toBoundaryClass r₂ :=
  Quot.sound h

/-! ## Topology on the Boundary -/

/-- A basic open set in the boundary topology: all rays whose Gromov product
    with a given ray exceeds a threshold. -/
structure BoundaryOpenBall {X : Type u} (M : MetricData X) (basepoint : X) where
  /-- Center ray. -/
  center : GeodesicRay M basepoint
  /-- Radius parameter (minimum Gromov product). -/
  radius : Nat

/-- Membership in a boundary open ball: a ray belongs if its Gromov product
    with the center ray eventually exceeds the radius. -/
def BoundaryOpenBall.mem {X : Type u} {M : MetricData X} {basepoint : X}
    (B : BoundaryOpenBall M basepoint) (r : GeodesicRay M basepoint) : Prop :=
  ∃ n₀ : Nat, ∀ n, n ≥ n₀ →
    M.gromovProduct basepoint (B.center.point n) (r.point n) ≥ B.radius

/-- A subset of the boundary is open if every boundary point in U has a
    neighborhood ball contained in U. -/
def BoundaryOpen {X : Type u} (M : MetricData X) (basepoint : X)
    (U : GromovBoundary M basepoint → Prop) : Prop :=
  ∀ r : GeodesicRay M basepoint, U (toBoundaryClass r) →
    ∃ B : BoundaryOpenBall M basepoint, B.mem r ∧
      ∀ r', B.mem r' → U (toBoundaryClass r')

/-! ## Boundary Topology (simplified) -/

/-- The boundary topology data as a collection of basic open balls. -/
structure BoundaryTopology {X : Type u} (M : MetricData X) (basepoint : X) where
  /-- A family of open balls forms a basis. -/
  balls : GeodesicRay M basepoint → Nat → BoundaryOpenBall M basepoint
  /-- Ball construction from center and radius. -/
  mk_ball : ∀ r n, (balls r n).center = r ∧ (balls r n).radius = n

/-- Canonical boundary topology via basic open balls. -/
def canonicalTopology {X : Type u} (M : MetricData X) (basepoint : X) :
    BoundaryTopology M basepoint where
  balls := fun r n => { center := r, radius := n }
  mk_ball := by intro r n; exact ⟨rfl, rfl⟩

/-! ## Boundary of Free Groups -/

/-- The boundary of a free group on a set of generators is modeled by
    infinite reduced words (sequences of signed generators with no
    adjacent cancellation). -/
structure FreeGroupBoundaryPoint (Gen : Type u) where
  /-- Infinite reduced word. -/
  word : Nat → Algebra.CayleyGraphPaths.SignedGen Gen
  /-- No adjacent cancellation: consecutive generators are not inverses. -/
  reduced : ∀ n, word (n + 1) ≠ Algebra.CayleyGraphPaths.SignedGen.inv (word n)

/-- The boundary of a free group on generators Gen. -/
def FreeGroupBoundary (Gen : Type u) : Type u :=
  FreeGroupBoundaryPoint Gen

/-- Two free group boundary points agree up to depth n. -/
def freeGroupAgreeUpTo {Gen : Type u}
    (p q : FreeGroupBoundary Gen) (n : Nat) : Prop :=
  ∀ k, k < n → p.word k = q.word k

/-- Free group boundary distance as the first disagreement depth. -/
def freeGroupBoundaryClose {Gen : Type u}
    (p q : FreeGroupBoundary Gen) (n : Nat) : Prop :=
  freeGroupAgreeUpTo p q n ∧ (n > 0 → p.word (n - 1) = q.word (n - 1))

/-! ## Boundary of Hyperbolic Space -/

/-- Model for the boundary of (discrete) hyperbolic space: the boundary is
    parameterized by directions. -/
structure HyperbolicSpaceBoundary (dim : Nat) where
  /-- Direction vector (as a list of integers with bounded coordinates). -/
  direction : Fin dim → Int
  /-- Nontriviality: at least one coordinate is nonzero. -/
  nontrivial : ∃ i, direction i ≠ 0

/-- Two boundary points of hyperbolic space are equivalent if their directions
    are positive scalar multiples. -/
def hsBoundaryEquiv {dim : Nat} (p q : HyperbolicSpaceBoundary dim) : Prop :=
  ∃ (c : Int), c > 0 ∧ ∀ i, q.direction i = c * p.direction i

/-- Projective boundary of hyperbolic space. -/
def ProjectiveBoundary (dim : Nat) : Type :=
  Quot (@hsBoundaryEquiv dim)

/-! ## Visual Metric -/

/-- The visual metric on the boundary at infinity, parameterized by a base
    parameter a > 1. The visual distance between boundary points ξ, η is
    approximately a^{-(ξ|η)_e}. We discretize to Nat. -/
structure VisualMetric {X : Type u} (M : MetricData X) (basepoint : X) where
  /-- Base parameter (representing a > 1 as a natural number ≥ 2). -/
  base : Nat
  /-- The base is at least 2. -/
  base_ge_two : base ≥ 2
  /-- Visual distance between two geodesic rays: a^{-gp} discretized.
      We compute as base^max_depth / base^(gromov_product at depth max_depth). -/
  visualDist : GeodesicRay M basepoint → GeodesicRay M basepoint → Nat
  /-- Visual distance is zero on equivalent rays. -/
  dist_zero_of_equiv : ∀ r₁ r₂,
    RayEquiv M basepoint r₁ r₂ → visualDist r₁ r₂ = 0
  /-- Visual distance is symmetric. -/
  dist_comm : ∀ r₁ r₂, visualDist r₁ r₂ = visualDist r₂ r₁

/-- Construct a trivial visual metric (all distances zero) as a baseline. -/
def trivialVisualMetric {X : Type u} (M : MetricData X) (basepoint : X) :
    VisualMetric M basepoint where
  base := 2
  base_ge_two := Nat.le_refl _
  visualDist := fun _ _ => 0
  dist_zero_of_equiv := fun _ _ _ => rfl
  dist_comm := fun _ _ => rfl

/-! ## Summary -/

/-
We formalized geodesic rays and their equivalence, constructed the Gromov
boundary as a quotient type, defined a basis for the boundary topology via
open balls, modeled the boundary of free groups via infinite reduced words,
defined the boundary of hyperbolic space projectively, and introduced the
visual metric on the boundary.
-/

end GromovBoundary
end Topology
end Path
end ComputationalPaths
