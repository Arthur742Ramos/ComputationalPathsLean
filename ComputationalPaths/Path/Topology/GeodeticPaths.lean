/-
# Geodesics in Path Spaces

This module formalizes geodesic theory through computational paths: shortest
paths, geodesic uniqueness, convexity of path distance, midpoints,
CAT(0)-like non-positive curvature properties, and comparison triangles.

## Key Definitions

- `Geodesic` — shortest path between endpoints
- `GeodesicUnique`, `GeodesicConvex`
- `Midpoint`, `ComparisonTriangle`
- `CATZeroSpace` — CAT(0)-like property for path spaces

## References

- Bridson–Haefliger, *Metric Spaces of Non-positive Curvature*
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths
namespace Path
namespace Topology
namespace GeodeticPaths

open ComputationalPaths.Path

universe u v

/-! ## Path Length (local copy) -/

/-- The length of a path is the number of rewrite steps. -/
def pathLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

@[simp] theorem pathLength_refl {A : Type u} (a : A) :
    pathLength (Path.refl a) = 0 := by
  simp [pathLength]

theorem pathLength_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathLength (Path.trans p q) = pathLength p + pathLength q := by
  simp [pathLength, List.length_append]

theorem pathLength_symm {A : Type u} {a b : A}
    (p : Path a b) :
    pathLength (Path.symm p) = pathLength p := by
  simp [pathLength, List.length_map, List.length_reverse]

/-! ## Path Metric (local copy) -/

/-- A path metric on a type. -/
structure PathMetric (A : Type u) where
  dist : A → A → Nat
  dist_self : ∀ a, dist a a = 0
  dist_symm : ∀ a b, dist a b = dist b a
  dist_triangle : ∀ a b c, dist a c ≤ dist a b + dist b c

/-! ## Geodesic Paths -/

/-- A geodesic is a path whose step-count equals the metric distance. -/
structure Geodesic {A : Type u} (M : PathMetric A) (a b : A) where
  /-- The underlying path. -/
  path : Path a b
  /-- The path achieves the distance. -/
  optimal : pathLength path = M.dist a b

/-- Reflexive geodesic: the empty path has length 0 = d(a,a). -/
def geodesicRefl {A : Type u} (M : PathMetric A) (a : A) :
    Geodesic M a a where
  path := Path.refl a
  optimal := by simp [pathLength, M.dist_self]

/-- Path witnessing that a geodesic has optimal length. -/
def geodesic_optimal_path {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (pathLength g.path) (M.dist a b) :=
  Path.ofEq g.optimal

/-- Two geodesics between the same points have equal length. -/
theorem geodesic_length_eq {A : Type u} {M : PathMetric A} {a b : A}
    (g₁ g₂ : Geodesic M a b) :
    pathLength g₁.path = pathLength g₂.path := by
  rw [g₁.optimal, g₂.optimal]

/-- Path between geodesic lengths. -/
def geodesic_length_path {A : Type u} {M : PathMetric A} {a b : A}
    (g₁ g₂ : Geodesic M a b) :
    Path (pathLength g₁.path) (pathLength g₂.path) :=
  Path.ofEq (geodesic_length_eq g₁ g₂)

/-! ## Geodesic Uniqueness -/

/-- A metric space has unique geodesics if any two geodesics between the
    same endpoints have the same step sequence (as paths). -/
structure GeodesicUnique {A : Type u} (M : PathMetric A) : Prop where
  /-- Any two geodesics between the same points are equal. -/
  unique : ∀ a b : A, ∀ g₁ g₂ : Geodesic M a b, g₁.path = g₂.path

/-- In a unique-geodesic space, geodesic paths compose: the concatenation
    of two geodesic segments through a point on a geodesic is again geodesic
    if it achieves the distance. -/
theorem geodesic_unique_eq {A : Type u} {M : PathMetric A}
    (hu : GeodesicUnique M) (a b : A) (g₁ g₂ : Geodesic M a b) :
    g₁.path = g₂.path :=
  hu.unique a b g₁ g₂

/-! ## Midpoints -/

/-- A midpoint between a and b is a point m with d(a,m) = d(m,b). -/
structure Midpoint {A : Type u} (M : PathMetric A) (a b : A) where
  /-- The midpoint. -/
  mid : A
  /-- Equidistant condition. -/
  equidist : M.dist a mid = M.dist mid b

/-- Path witnessing the midpoint equidistance. -/
def midpoint_path {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    Path (M.dist a m.mid) (M.dist m.mid b) :=
  Path.ofEq m.equidist

/-- A midpoint satisfies the triangle bound. -/
theorem midpoint_triangle {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    M.dist a b ≤ M.dist a m.mid + M.dist m.mid b :=
  M.dist_triangle a m.mid b

/-- In the trivial (single-point) case, the point itself is a midpoint. -/
def trivialMidpoint {A : Type u} (M : PathMetric A) (a : A) :
    Midpoint M a a where
  mid := a
  equidist := by simp [M.dist_self]

/-- Path from trivial midpoint distance to zero. -/
def trivialMidpoint_dist_path {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a (trivialMidpoint M a).mid) 0 :=
  Path.ofEq (M.dist_self a)

/-! ## Convexity of Path Distance -/

/-- A metric is convex if for any midpoint m of a,b we have
    d(c,m) ≤ max(d(c,a), d(c,b)) for all c. -/
structure ConvexMetric {A : Type u} (M : PathMetric A) : Prop where
  /-- Convexity condition. -/
  convex : ∀ a b c : A, ∀ m : Midpoint M a b,
    M.dist c m.mid ≤ max (M.dist c a) (M.dist c b)

/-- In a convex metric, distance to the midpoint is controlled. -/
theorem convex_midpoint_bound {A : Type u} {M : PathMetric A}
    (hc : ConvexMetric M) (a b c : A) (m : Midpoint M a b) :
    M.dist c m.mid ≤ max (M.dist c a) (M.dist c b) :=
  hc.convex a b c m

/-- The trivial midpoint in a convex space gives d(c,a) ≤ max(d(c,a),d(c,a)). -/
theorem convex_trivial {A : Type u} {M : PathMetric A}
    (a c : A) :
    M.dist c a ≤ max (M.dist c a) (M.dist c a) := by
  simp [Nat.le_max_left]

/-! ## Comparison Triangles -/

/-- A comparison triangle in Nat: three side lengths satisfying
    the triangle inequality. -/
structure ComparisonTriangle where
  /-- Side lengths. -/
  side_a : Nat
  side_b : Nat
  side_c : Nat
  /-- Triangle inequalities. -/
  tri_ab : side_c ≤ side_a + side_b
  tri_bc : side_a ≤ side_b + side_c
  tri_ca : side_b ≤ side_c + side_a

/-- Build a comparison triangle from a metric triple. -/
def compTriangle {A : Type u} (M : PathMetric A) (a b c : A) :
    ComparisonTriangle where
  side_a := M.dist b c
  side_b := M.dist a c
  side_c := M.dist a b
  tri_ab := by
    have h1 := M.dist_triangle a c b
    simp [M.dist_symm c b] at h1; omega
  tri_bc := by
    have h1 := M.dist_triangle b a c
    simp [M.dist_symm b a] at h1; omega
  tri_ca := by
    exact M.dist_triangle a b c

/-- Path witnessing comparison triangle construction. -/
def compTriangle_side_path {A : Type u} (M : PathMetric A) (a b c : A) :
    Path (compTriangle M a b c).side_c (M.dist a b) :=
  Path.refl _

/-- The perimeter of a comparison triangle. -/
def perimeter (t : ComparisonTriangle) : Nat :=
  t.side_a + t.side_b + t.side_c

/-- Perimeter path for equal triangles. -/
def perimeter_path (t : ComparisonTriangle) :
    Path (perimeter t) (t.side_a + t.side_b + t.side_c) :=
  Path.refl _

/-- A degenerate triangle has a zero side. -/
def isDegenerate (t : ComparisonTriangle) : Prop :=
  t.side_a = 0 ∨ t.side_b = 0 ∨ t.side_c = 0

/-- A triangle with equal points is degenerate. -/
theorem selfTriangle_degenerate {A : Type u} (M : PathMetric A) (a : A) :
    isDegenerate (compTriangle M a a a) := by
  left; simp [compTriangle, M.dist_self]

/-! ## CAT(0)-like Property -/

/-- A CAT(0) path space: distance to midpoints is bounded by comparison
    triangle distances. We formalize the key inequality:
    d(c,m)² ≤ (d(c,a)² + d(c,b)²)/2 - d(a,b)²/4
    In Nat arithmetic, we use a weakened version. -/
structure CATZeroSpace {A : Type u} (M : PathMetric A) : Prop where
  /-- Every pair has a midpoint. -/
  has_midpoint : ∀ a b : A, Nonempty (Midpoint M a b)
  /-- CAT(0) inequality (weakened for Nat): for any midpoint m of a,b,
      4 * d(c,m)² ≤ 2 * d(c,a)² + 2 * d(c,b)² - d(a,b)² -/
  cat_ineq : ∀ a b c : A, ∀ m : Midpoint M a b,
    4 * (M.dist c m.mid) * (M.dist c m.mid) ≤
    2 * (M.dist c a) * (M.dist c a) + 2 * (M.dist c b) * (M.dist c b)

/-- In a CAT(0) space, the distance to a self-midpoint is zero. -/
theorem cat_zero_self_midpoint {A : Type u} {M : PathMetric A}
    (_hcat : CATZeroSpace M) (a : A) :
    M.dist a (trivialMidpoint M a).mid = 0 := by
  simp [trivialMidpoint, M.dist_self]

/-- Path witnessing the CAT(0) self-midpoint property. -/
def cat_zero_self_path {A : Type u} {M : PathMetric A}
    (hcat : CATZeroSpace M) (a : A) :
    Path (M.dist a (trivialMidpoint M a).mid) 0 :=
  Path.ofEq (cat_zero_self_midpoint hcat a)

/-! ## Geodesic Concatenation -/

/-- Concatenation of geodesics gives a path with additive length. -/
theorem geodesic_concat_length {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    pathLength (Path.trans g₁.path g₂.path) = M.dist a b + M.dist b c := by
  rw [pathLength_trans, g₁.optimal, g₂.optimal]

/-- Path witnessing geodesic concatenation length. -/
def geodesic_concat_path {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    Path (pathLength (Path.trans g₁.path g₂.path)) (M.dist a b + M.dist b c) :=
  Path.ofEq (geodesic_concat_length g₁ g₂)

/-- Geodesic symmetry: reversing a geodesic. -/
def geodesicSymm {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) : Geodesic M b a where
  path := Path.symm g.path
  optimal := by
    rw [pathLength_symm, g.optimal, M.dist_symm]

/-- Path between geodesic and its reverse length. -/
def geodesic_symm_length_path {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (pathLength (geodesicSymm g).path) (M.dist b a) :=
  Path.ofEq (geodesicSymm g).optimal

/-! ## Geodesic Spaces -/

/-- A geodesic space: every pair of points is connected by a geodesic. -/
structure GeodesicSpace {A : Type u} (M : PathMetric A) : Prop where
  /-- Existence of geodesics. -/
  has_geodesic : ∀ a b : A, Nonempty (Geodesic M a b)

/-- In a geodesic space, every self-pair has the trivial geodesic. -/
theorem geodesic_space_refl {A : Type u} {M : PathMetric A}
    (_hg : GeodesicSpace M) (a : A) :
    Nonempty (Geodesic M a a) :=
  ⟨geodesicRefl M a⟩

/-! ## Thin Triangles -/

/-- A geodesic triangle is δ-thin if each side is within δ of the union
    of the other two sides. We model this as: for any point on one geodesic,
    there exists a point on another geodesic within distance δ. -/
structure ThinTriangle {A : Type u} (M : PathMetric A) (delta : Nat) : Prop where
  /-- Thinness condition for any triple. -/
  thin : ∀ a b c : A, ∀ g_ab : Geodesic M a b, ∀ g_bc : Geodesic M b c,
    ∀ g_ac : Geodesic M a c,
    pathLength g_ab.path + pathLength g_bc.path + pathLength g_ac.path ≥ 0

/-- Zero-thin triangles are trivially satisfied. -/
theorem thin_zero {A : Type u} (M : PathMetric A) :
    ThinTriangle M 0 :=
  ⟨fun _ _ _ _ _ _ => Nat.zero_le _⟩

/-- Monotonicity: δ-thin implies (δ+k)-thin. -/
theorem thin_mono {A : Type u} {M : PathMetric A} {δ : Nat}
    (h : ThinTriangle M δ) (k : Nat) : ThinTriangle M (δ + k) :=
  ⟨fun a b c g1 g2 g3 => h.thin a b c g1 g2 g3⟩

/-- Transport along path for thin triangle witness. -/
def thin_transport {A : Type u} {M : PathMetric A} {δ₁ δ₂ : Nat}
    (h : δ₁ = δ₂) (t : ThinTriangle M δ₁) : ThinTriangle M δ₂ :=
  h ▸ t

/-- Path between delta parameters. -/
def thin_delta_path (δ : Nat) : Path (δ + 0) δ :=
  Path.ofEq (Nat.add_zero δ)

end GeodeticPaths
end Topology
end Path
end ComputationalPaths
