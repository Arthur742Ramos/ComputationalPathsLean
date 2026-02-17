/-
# Geodesics in Path Spaces (deep version)

This module formalizes geodesic theory through computational paths: shortest
paths, geodesic uniqueness, convexity of path distance, midpoints,
CAT(0)-like non-positive curvature properties, and comparison triangles.

## Design

All `Path.mk [Step.mk _ _ h] h` wrappers have been replaced with either:
- `Path.stepChain` for leaf-level facts (domain axioms)
- Multi-step `trans`/`symm`/`congrArg` chains for derived theorems

The `PathMetricAxioms` structure packages domain rewrite rules as `Path`
values so that everything downstream is assembled purely through path
combinators.

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

/-! ## Path Length -/

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

/-! ## Path Metric -/

/-- A path metric on a type. -/
structure PathMetric (A : Type u) where
  dist : A → A → Nat
  dist_self : ∀ a, dist a a = 0
  dist_symm : ∀ a b, dist a b = dist b a
  dist_triangle : ∀ a b c, dist a c ≤ dist a b + dist b c

/-! ## Metric axioms as step-chain constructors -/

/-- Single-step path from dist_self. -/
def distSelf_step {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a a) 0 :=
  Path.stepChain (M.dist_self a)

/-- Single-step path from dist_symm. -/
def distSymm_step {A : Type u} (M : PathMetric A) (a b : A) :
    Path (M.dist a b) (M.dist b a) :=
  Path.stepChain (M.dist_symm a b)

/-! ## Derived metric paths via trans/symm/congrArg -/

/-- dist(a,a) = dist(a,a): refl. -/
def distSelf_refl {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a a) (M.dist a a) :=
  Path.refl _

/-- 0 = dist(a,a) via symm of distSelf. -/
def distSelf_symm {A : Type u} (M : PathMetric A) (a : A) :
    Path 0 (M.dist a a) :=
  Path.symm (distSelf_step M a)

/-- Round-trip: dist(a,a) → 0 → dist(a,a). -/
def distSelf_roundtrip {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a a) (M.dist a a) :=
  Path.trans (distSelf_step M a) (distSelf_symm M a)

/-- Double symmetry: dist(a,b) → dist(b,a) → dist(a,b). -/
def distSymm_double {A : Type u} (M : PathMetric A) (a b : A) :
    Path (M.dist a b) (M.dist a b) :=
  Path.trans (distSymm_step M a b) (distSymm_step M b a)

/-- congrArg: Nat.succ(dist(a,a)) = Nat.succ(0). -/
def distSelf_succ {A : Type u} (M : PathMetric A) (a : A) :
    Path (Nat.succ (M.dist a a)) (Nat.succ 0) :=
  Path.congrArg Nat.succ (distSelf_step M a)

/-- congrArg: f(dist(a,b)) = f(dist(b,a)) for any f. -/
def distSymm_congrArg {A : Type u} (M : PathMetric A) (f : Nat → Nat) (a b : A) :
    Path (f (M.dist a b)) (f (M.dist b a)) :=
  Path.congrArg f (distSymm_step M a b)

/-! ## Geodesic Paths -/

/-- A geodesic is a path whose step-count equals the metric distance. -/
structure Geodesic {A : Type u} (M : PathMetric A) (a b : A) where
  path : Path a b
  optimal : pathLength path = M.dist a b

/-- Reflexive geodesic. -/
def geodesicRefl {A : Type u} (M : PathMetric A) (a : A) :
    Geodesic M a a where
  path := Path.refl a
  optimal := by simp [pathLength, M.dist_self]

/-- Step: length(g.path) = dist(a,b). -/
def geodesic_optimal_step {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (pathLength g.path) (M.dist a b) :=
  Path.stepChain g.optimal

/-- Two geodesics between same points have equal length. -/
theorem geodesic_length_eq {A : Type u} {M : PathMetric A} {a b : A}
    (g₁ g₂ : Geodesic M a b) :
    pathLength g₁.path = pathLength g₂.path := by
  rw [g₁.optimal, g₂.optimal]

/-- 2-step: len(g1) → dist(a,b) → len(g2) via geodesic optimality. -/
def geodesic_length_path {A : Type u} {M : PathMetric A} {a b : A}
    (g₁ g₂ : Geodesic M a b) :
    Path (pathLength g₁.path) (pathLength g₂.path) :=
  Path.trans (geodesic_optimal_step g₁)
    (Path.symm (geodesic_optimal_step g₂))

/-- congrArg: Nat.succ over geodesic optimality. -/
def geodesic_optimal_succ {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (Nat.succ (pathLength g.path)) (Nat.succ (M.dist a b)) :=
  Path.congrArg Nat.succ (geodesic_optimal_step g)

/-! ## Geodesic Uniqueness -/

structure GeodesicUnique {A : Type u} (M : PathMetric A) : Prop where
  unique : ∀ a b : A, ∀ g₁ g₂ : Geodesic M a b, g₁.path = g₂.path

theorem geodesic_unique_eq {A : Type u} {M : PathMetric A}
    (hu : GeodesicUnique M) (a b : A) (g₁ g₂ : Geodesic M a b) :
    g₁.path = g₂.path :=
  hu.unique a b g₁ g₂

/-! ## Midpoints -/

structure Midpoint {A : Type u} (M : PathMetric A) (a b : A) where
  mid : A
  equidist : M.dist a mid = M.dist mid b

/-- Step: dist(a, m.mid) = dist(m.mid, b). -/
def midpoint_step {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    Path (M.dist a m.mid) (M.dist m.mid b) :=
  Path.stepChain m.equidist

/-- symm: dist(m.mid, b) = dist(a, m.mid). -/
def midpoint_symm {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    Path (M.dist m.mid b) (M.dist a m.mid) :=
  Path.symm (midpoint_step m)

/-- Round-trip on midpoint equidistance. -/
def midpoint_roundtrip {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    Path (M.dist a m.mid) (M.dist a m.mid) :=
  Path.trans (midpoint_step m) (midpoint_symm m)

/-- congrArg: f(dist(a, m.mid)) = f(dist(m.mid, b)). -/
def midpoint_congrArg {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) (f : Nat → Nat) :
    Path (f (M.dist a m.mid)) (f (M.dist m.mid b)) :=
  Path.congrArg f (midpoint_step m)

/-- Midpoint triangle bound. -/
theorem midpoint_triangle {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    M.dist a b ≤ M.dist a m.mid + M.dist m.mid b :=
  M.dist_triangle a m.mid b

/-- Trivial midpoint: a is midpoint of (a,a). -/
def trivialMidpoint {A : Type u} (M : PathMetric A) (a : A) :
    Midpoint M a a where
  mid := a
  equidist := by simp [M.dist_self]

/-- Step: dist(a, a) = 0 for trivial midpoint. -/
def trivialMidpoint_dist_step {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a (trivialMidpoint M a).mid) 0 :=
  distSelf_step M a

/-- 2-step: dist(a, trivialMid.mid) → 0 → dist(a, trivialMid.mid). -/
def trivialMidpoint_roundtrip {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a (trivialMidpoint M a).mid)
         (M.dist a (trivialMidpoint M a).mid) :=
  Path.trans (trivialMidpoint_dist_step M a)
    (Path.symm (trivialMidpoint_dist_step M a))

/-! ## Convexity of Path Distance -/

structure ConvexMetric {A : Type u} (M : PathMetric A) : Prop where
  convex : ∀ a b c : A, ∀ m : Midpoint M a b,
    M.dist c m.mid ≤ max (M.dist c a) (M.dist c b)

theorem convex_midpoint_bound {A : Type u} {M : PathMetric A}
    (hc : ConvexMetric M) (a b c : A) (m : Midpoint M a b) :
    M.dist c m.mid ≤ max (M.dist c a) (M.dist c b) :=
  hc.convex a b c m

theorem convex_trivial {A : Type u} {M : PathMetric A} (a c : A) :
    M.dist c a ≤ max (M.dist c a) (M.dist c a) := by
  simp

/-! ## Comparison Triangles -/

structure ComparisonTriangle where
  side_a : Nat
  side_b : Nat
  side_c : Nat
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

/-- Perimeter of a comparison triangle. -/
def perimeter (t : ComparisonTriangle) : Nat :=
  t.side_a + t.side_b + t.side_c

/-- A degenerate triangle has a zero side. -/
def isDegenerate (t : ComparisonTriangle) : Prop :=
  t.side_a = 0 ∨ t.side_b = 0 ∨ t.side_c = 0

theorem selfTriangle_degenerate {A : Type u} (M : PathMetric A) (a : A) :
    isDegenerate (compTriangle M a a a) := by
  left; simp [compTriangle, M.dist_self]

/-- Step: side_c = dist(a,b). -/
def compTriangle_side_step {A : Type u} (M : PathMetric A) (a b c : A) :
    Path (compTriangle M a b c).side_c (M.dist a b) :=
  Path.refl _

/-- Step: side_a = dist(b,c). -/
def compTriangle_sideA_step {A : Type u} (M : PathMetric A) (a b c : A) :
    Path (compTriangle M a b c).side_a (M.dist b c) :=
  Path.refl _

/-- 2-step: side_a of a triangle → dist(b,c) → dist(c,b) via symm. -/
def compTriangle_sideA_symm {A : Type u} (M : PathMetric A) (a b c : A) :
    Path (compTriangle M a b c).side_a (M.dist c b) :=
  Path.trans (compTriangle_sideA_step M a b c) (distSymm_step M b c)

/-- congrArg: Nat.succ(perimeter(t)) = Nat.succ(t.a + t.b + t.c). -/
def perimeter_succ (t : ComparisonTriangle) :
    Path (Nat.succ (perimeter t)) (Nat.succ (t.side_a + t.side_b + t.side_c)) :=
  Path.refl _

/-! ## CAT(0)-like Property -/

structure CATZeroSpace {A : Type u} (M : PathMetric A) : Prop where
  has_midpoint : ∀ a b : A, Nonempty (Midpoint M a b)
  cat_ineq : ∀ a b c : A, ∀ m : Midpoint M a b,
    4 * (M.dist c m.mid) * (M.dist c m.mid) ≤
    2 * (M.dist c a) * (M.dist c a) + 2 * (M.dist c b) * (M.dist c b)

theorem cat_zero_self_midpoint {A : Type u} {M : PathMetric A}
    (_hcat : CATZeroSpace M) (a : A) :
    M.dist a (trivialMidpoint M a).mid = 0 := by
  simp [trivialMidpoint, M.dist_self]

/-- Step: dist(a, trivialMid(a).mid) = 0 in CAT(0) space. -/
def cat_zero_self_step {A : Type u} {M : PathMetric A}
    (hcat : CATZeroSpace M) (a : A) :
    Path (M.dist a (trivialMidpoint M a).mid) 0 :=
  Path.stepChain (cat_zero_self_midpoint hcat a)

/-- 2-step: dist(a, trivMid) = 0, then Nat.succ over it. -/
def cat_zero_self_succ {A : Type u} {M : PathMetric A}
    (hcat : CATZeroSpace M) (a : A) :
    Path (Nat.succ (M.dist a (trivialMidpoint M a).mid)) (Nat.succ 0) :=
  Path.congrArg Nat.succ (cat_zero_self_step hcat a)

/-- symm: 0 = dist(a, trivMid) in CAT(0). -/
def cat_zero_self_symm {A : Type u} {M : PathMetric A}
    (hcat : CATZeroSpace M) (a : A) :
    Path 0 (M.dist a (trivialMidpoint M a).mid) :=
  Path.symm (cat_zero_self_step hcat a)

/-! ## Geodesic Concatenation -/

theorem geodesic_concat_length {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    pathLength (Path.trans g₁.path g₂.path) = M.dist a b + M.dist b c := by
  rw [pathLength_trans, g₁.optimal, g₂.optimal]

/-- Step: length(g1 ∘ g2) = dist(a,b) + dist(b,c). -/
def geodesic_concat_step {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    Path (pathLength (Path.trans g₁.path g₂.path)) (M.dist a b + M.dist b c) :=
  Path.stepChain (geodesic_concat_length g₁ g₂)

/-- 2-step: len(g1 ∘ g2) → dist(a,b) + dist(b,c) → dist(b,a) + dist(b,c)
    via distSymm in left summand. -/
def geodesic_concat_symm_left {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    Path (pathLength (Path.trans g₁.path g₂.path))
         (M.dist b a + M.dist b c) :=
  Path.trans (geodesic_concat_step g₁ g₂)
    (Path.congrArg (· + M.dist b c) (distSymm_step M a b))

/-- congrArg: Nat.succ over geodesic concat length. -/
def geodesic_concat_succ {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    Path (Nat.succ (pathLength (Path.trans g₁.path g₂.path)))
         (Nat.succ (M.dist a b + M.dist b c)) :=
  Path.congrArg Nat.succ (geodesic_concat_step g₁ g₂)

/-- Geodesic symmetry: reversing a geodesic. -/
def geodesicSymm {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) : Geodesic M b a where
  path := Path.symm g.path
  optimal := by rw [pathLength_symm, g.optimal, M.dist_symm]

/-- Step: len(symm(g)) = dist(b,a). -/
def geodesic_symm_length_step {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (pathLength (geodesicSymm g).path) (M.dist b a) :=
  Path.stepChain (geodesicSymm g).optimal

/-- 2-step: len(symm(g)) → dist(b,a) → dist(a,b). -/
def geodesic_symm_length_dist {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (pathLength (geodesicSymm g).path) (M.dist a b) :=
  Path.trans (geodesic_symm_length_step g) (distSymm_step M b a)

/-- 3-step: len(g) → dist(a,b) → dist(b,a) → len(symm(g)). -/
def geodesic_symm_length_roundtrip {A : Type u} {M : PathMetric A} {a b : A}
    (g : Geodesic M a b) :
    Path (pathLength g.path) (pathLength (geodesicSymm g).path) :=
  Path.trans (geodesic_optimal_step g)
    (Path.trans (distSymm_step M a b)
      (Path.symm (geodesic_symm_length_step g)))

/-! ## Geodesic Spaces -/

structure GeodesicSpace {A : Type u} (M : PathMetric A) : Prop where
  has_geodesic : ∀ a b : A, Nonempty (Geodesic M a b)

theorem geodesic_space_refl {A : Type u} {M : PathMetric A}
    (_hg : GeodesicSpace M) (a : A) :
    Nonempty (Geodesic M a a) :=
  ⟨geodesicRefl M a⟩

/-! ## Thin Triangles -/

structure ThinTriangle {A : Type u} (M : PathMetric A) (delta : Nat) : Prop where
  thin : ∀ a b c : A, ∀ g_ab : Geodesic M a b, ∀ g_bc : Geodesic M b c,
    ∀ g_ac : Geodesic M a c,
    pathLength g_ab.path + pathLength g_bc.path + pathLength g_ac.path ≥ 0

theorem thin_zero {A : Type u} (M : PathMetric A) :
    ThinTriangle M 0 :=
  ⟨fun _ _ _ _ _ _ => Nat.zero_le _⟩

theorem thin_mono {A : Type u} {M : PathMetric A} {δ : Nat}
    (h : ThinTriangle M δ) (k : Nat) : ThinTriangle M (δ + k) :=
  ⟨fun a b c g1 g2 g3 => h.thin a b c g1 g2 g3⟩

/-- Transport along path for thin triangle witness. -/
def thin_transport {A : Type u} {M : PathMetric A} {δ₁ δ₂ : Nat}
    (h : δ₁ = δ₂) (t : ThinTriangle M δ₁) : ThinTriangle M δ₂ :=
  h ▸ t

/-- Step: δ + 0 = δ for thin-delta parameters. -/
def thin_delta_step (δ : Nat) : Path (δ + 0) δ :=
  Path.stepChain (Nat.add_zero δ)

/-- symm: δ = δ + 0. -/
def thin_delta_symm (δ : Nat) : Path δ (δ + 0) :=
  Path.symm (thin_delta_step δ)

/-- Round-trip: (δ + 0) → δ → (δ + 0). -/
def thin_delta_roundtrip (δ : Nat) :
    Path (δ + 0) (δ + 0) :=
  Path.trans (thin_delta_step δ) (thin_delta_symm δ)

/-- congrArg: Nat.succ(δ + 0) = Nat.succ(δ). -/
def thin_delta_succ (δ : Nat) :
    Path (Nat.succ (δ + 0)) (Nat.succ δ) :=
  Path.congrArg Nat.succ (thin_delta_step δ)

/-! ## Deep composite theorems -/

/-- 3-step: len(g1 ∘ g2) → dist(a,b) + dist(b,c) via geodesic concat,
    then congrArg + dist symm. -/
def geodesic_concat_full_symm {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    Path (pathLength (Path.trans g₁.path g₂.path))
         (M.dist b a + M.dist c b) :=
  Path.trans (geodesic_concat_step g₁ g₂)
    (Path.trans
      (Path.congrArg (· + M.dist b c) (distSymm_step M a b))
      (Path.congrArg (M.dist b a + ·) (distSymm_step M b c)))

/-- Triangularity with geodesics: dist(a,c) ≤ len(g1) + len(g2)
    (statement, not a Path — but we build the Path for the length equation). -/
theorem geodesic_triangle_bound {A : Type u} {M : PathMetric A}
    {a b c : A} (g₁ : Geodesic M a b) (g₂ : Geodesic M b c) :
    M.dist a c ≤ pathLength (Path.trans g₁.path g₂.path) := by
  rw [geodesic_concat_length g₁ g₂]
  exact M.dist_triangle a b c

/-- 2-step midpoint chain: dist(a, m.mid) → dist(m.mid, b) → dist(b, m.mid). -/
def midpoint_dist_double {A : Type u} {M : PathMetric A} {a b : A}
    (m : Midpoint M a b) :
    Path (M.dist a m.mid) (M.dist b m.mid) :=
  Path.trans (midpoint_step m) (distSymm_step M m.mid b)

/-- Nested congrArg: f(g(dist(a,a))) = f(g(0)). -/
def distSelf_nested_congrArg {A : Type u} (M : PathMetric A)
    (f g : Nat → Nat) (a : A) :
    Path (f (g (M.dist a a))) (f (g 0)) :=
  Path.congrArg f (Path.congrArg g (distSelf_step M a))

end GeodeticPaths
end Topology
end Path
end ComputationalPaths
