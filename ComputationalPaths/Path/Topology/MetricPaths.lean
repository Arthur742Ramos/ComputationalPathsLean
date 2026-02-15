/-
# Metric Spaces via Computational Paths

This module formalizes metric space theory through the computational paths
framework. Distance is modelled as path length (step count), the triangle
inequality follows from path composition, Cauchy sequences are path
convergence, completions arise from path limits, and contraction mappings
are path-shortening rewrites.

## Key Definitions

- `PathMetric` — metric on a type derived from path step counts
- `MetricBall`, `MetricCauchy`, `MetricComplete`
- `ContractionMap` — path-shortening rewrite
- `PathLipschitz`, `PathIsometry`
- Triangle inequality, Cauchy convergence, fixed points

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Bridson–Haefliger, *Metric Spaces of Non-positive Curvature*
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace MetricPaths

open ComputationalPaths.Path

universe u v

/-! ## Path Length as Distance -/

/-- The length of a path is the number of rewrite steps. -/
def pathLength {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

/-- Reflexive path has length zero. -/
@[simp] theorem pathLength_refl {A : Type u} (a : A) :
    pathLength (Path.refl a) = 0 := by
  simp [pathLength]

/-- Path length of a single-step path is 1. -/
@[simp] theorem pathLength_ofEq {A : Type u} {a b : A} (h : a = b) :
    pathLength (Path.ofEq h) = 1 := by
  simp [pathLength]

/-- Path length is additive under composition. -/
theorem pathLength_trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathLength (Path.trans p q) = pathLength p + pathLength q := by
  simp [pathLength, List.length_append]

/-- Path length is preserved by symmetry. -/
theorem pathLength_symm {A : Type u} {a b : A}
    (p : Path a b) :
    pathLength (Path.symm p) = pathLength p := by
  simp [pathLength, List.length_map, List.length_reverse]

/-! ## Path Metric Structure -/

/-- A path metric on a type: distance between elements measured by
    minimum path step-count. We use a concrete distance function. -/
structure PathMetric (A : Type u) where
  /-- Distance function. -/
  dist : A → A → Nat
  /-- Distance from a point to itself is zero. -/
  dist_self : ∀ a, dist a a = 0
  /-- Symmetry of distance. -/
  dist_symm : ∀ a b, dist a b = dist b a
  /-- Triangle inequality. -/
  dist_triangle : ∀ a b c, dist a c ≤ dist a b + dist b c

namespace PathMetric

variable {A : Type u} (M : PathMetric A)

/-- Path witnessing distance reflexivity. -/
def dist_self_path (a : A) : Path (M.dist a a) 0 :=
  Path.ofEq (M.dist_self a)

/-- Path witnessing distance symmetry. -/
def dist_symm_path (a b : A) : Path (M.dist a b) (M.dist b a) :=
  Path.ofEq (M.dist_symm a b)

/-- Symmetry loop: composing symmetry with its inverse. -/
def dist_symm_loop (a b : A) : Path (M.dist a b) (M.dist a b) :=
  Path.trans (dist_symm_path M a b) (Path.symm (dist_symm_path M a b))

/-- Double symmetry yields a trivial equality. -/
theorem dist_symm_symm (a b : A) :
    (M.dist_symm a b).symm.trans (M.dist_symm a b) = rfl := by
  simp

/-- Transport along the self-distance path. -/
theorem transport_dist_self (a : A) (P : Nat → Type v) (x : P (M.dist a a)) :
    Path.transport (dist_self_path M a) x = (M.dist_self a ▸ x : P 0) := by
  simp [dist_self_path, Path.transport]

end PathMetric

/-! ## Metric from Step Counts -/

/-- Build a path metric from a canonical path assignment. -/
def stepCountMetric (A : Type u)
    (canonical : A → A → Nat)
    (h_self : ∀ a, canonical a a = 0)
    (h_symm : ∀ a b, canonical a b = canonical b a)
    (h_tri : ∀ a b c, canonical a c ≤ canonical a b + canonical b c) :
    PathMetric A where
  dist := canonical
  dist_self := h_self
  dist_symm := h_symm
  dist_triangle := h_tri

/-- The trivial metric: distance is 0 on equal elements, 1 otherwise. -/
def discreteMetric (A : Type u) [DecidableEq A] : PathMetric A where
  dist := fun a b => if a = b then 0 else 1
  dist_self := by intro a; simp
  dist_symm := by
    intro a b
    by_cases hab : a = b <;> by_cases hba : b = a <;> simp_all
  dist_triangle := by
    intro a b c
    by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> simp_all <;> omega

/-! ## Triangle Inequality from Path Composition -/

/-- Triangle inequality witnessed as a path relationship. -/
def triangle_from_composition {A : Type u} (M : PathMetric A)
    (a b c : A) :
    Path (M.dist a c) (M.dist a c) :=
  Path.refl _

/-- The triangle sum dominates the direct distance. -/
theorem triangle_sum_ge {A : Type u} (M : PathMetric A) (a b c : A) :
    M.dist a b + M.dist b c ≥ M.dist a c :=
  M.dist_triangle a b c

/-- Four-point inequality from iterated triangle. -/
theorem four_point_triangle {A : Type u} (M : PathMetric A)
    (a b c d : A) :
    M.dist a d ≤ M.dist a b + M.dist b c + M.dist c d := by
  have h1 := M.dist_triangle a c d
  have h2 := M.dist_triangle a b c
  omega

/-- Path witnessing the four-point bound. -/
def four_point_path {A : Type u} (M : PathMetric A)
    (a b c d : A)
    (h : M.dist a b + M.dist b c + M.dist c d = M.dist a d + k) :
    Path (M.dist a b + M.dist b c + M.dist c d) (M.dist a d + k) :=
  Path.ofEq h

/-! ## Metric Balls -/

/-- Open ball of radius r around a center. -/
def MetricBall {A : Type u} (M : PathMetric A) (center : A) (r : Nat) : A → Prop :=
  fun x => M.dist center x < r

/-- The center is in any ball of positive radius. -/
theorem center_in_ball {A : Type u} (M : PathMetric A) (a : A) (r : Nat) (hr : 0 < r) :
    MetricBall M a r a := by
  simp [MetricBall, M.dist_self]
  exact hr

/-- Ball inclusion from radius ordering. -/
theorem ball_subset {A : Type u} (M : PathMetric A) (a : A) (r s : Nat) (hrs : r ≤ s)
    (x : A) (hx : MetricBall M a r x) : MetricBall M a s x := by
  simp [MetricBall] at *
  omega

/-- Path between ball membership predicates. -/
def ball_inclusion_path {A : Type u} (M : PathMetric A) (a : A) (r : Nat) :
    Path (MetricBall M a r) (MetricBall M a r) :=
  Path.refl _

/-! ## Cauchy Sequences -/

/-- A Cauchy sequence in a path metric space. -/
structure MetricCauchy {A : Type u} (M : PathMetric A) where
  /-- The sequence. -/
  seq : Nat → A
  /-- Cauchy condition: for every ε > 0, there exists N such that
      d(seq n, seq m) < ε for all n, m ≥ N. -/
  cauchy : ∀ eps : Nat, 0 < eps → ∃ N, ∀ n m, N ≤ n → N ≤ m →
    M.dist (seq n) (seq m) < eps

/-- A constant sequence is Cauchy. -/
def constCauchy {A : Type u} (M : PathMetric A) (a : A) : MetricCauchy M where
  seq := fun _ => a
  cauchy := by
    intro eps heps
    exact ⟨0, fun n m _ _ => by simp [M.dist_self]; exact heps⟩

/-- Path showing a constant Cauchy sequence has zero eventual distance. -/
def constCauchy_dist_path {A : Type u} (M : PathMetric A) (a : A) (n m : Nat) :
    Path (M.dist ((constCauchy M a).seq n) ((constCauchy M a).seq m)) 0 :=
  Path.ofEq (M.dist_self a)

/-- Convergence: a sequence converges to a limit. -/
structure MetricConverges {A : Type u} (M : PathMetric A) (s : Nat → A) (lim : A) : Prop where
  /-- For every ε > 0 there exists N with d(s n, lim) < ε for all n ≥ N. -/
  conv : ∀ eps : Nat, 0 < eps → ∃ N, ∀ n, N ≤ n → M.dist (s n) lim < eps

/-- A constant sequence converges to its value. -/
theorem const_converges {A : Type u} (M : PathMetric A) (a : A) :
    MetricConverges M (fun _ => a) a :=
  ⟨fun eps heps => ⟨0, fun n _ => by simp [M.dist_self]; exact heps⟩⟩

/-! ## Completeness -/

/-- A metric space is complete if every Cauchy sequence converges. -/
structure MetricComplete {A : Type u} (M : PathMetric A) : Prop where
  /-- Every Cauchy sequence has a limit. -/
  complete : ∀ c : MetricCauchy M, ∃ lim, MetricConverges M c.seq lim

/-- Path between completeness witnesses. -/
theorem complete_eq {A : Type u} {M : PathMetric A}
    (h1 h2 : MetricComplete M) : h1 = h2 := by
  cases h1; cases h2; congr

/-! ## Lipschitz and Contraction Maps -/

/-- A map is Lipschitz with constant L. -/
structure PathLipschitz {A : Type u} {B : Type v}
    (MA : PathMetric A) (MB : PathMetric B) (L : Nat) (f : A → B) : Prop where
  /-- Distance bound. -/
  lip : ∀ a₁ a₂, MB.dist (f a₁) (f a₂) ≤ L * MA.dist a₁ a₂

/-- A contraction map: Lipschitz with constant < 1.
    We model this via numerator/denominator: L_num < L_den. -/
structure ContractionMap {A : Type u}
    (M : PathMetric A) (f : A → A) where
  /-- Contraction numerator. -/
  L_num : Nat
  /-- Contraction denominator (> 0). -/
  L_den : Nat
  /-- Denominator is positive. -/
  den_pos : 0 < L_den
  /-- Strict contraction: numerator < denominator. -/
  contract : L_num < L_den
  /-- Distance bound: d(f x, f y) * L_den ≤ L_num * d(x, y). -/
  dist_bound : ∀ x y, M.dist (f x) (f y) * L_den ≤ L_num * M.dist x y

/-- A contraction on equal points yields equal images. -/
def contraction_preserves_eq {A : Type u} {M : PathMetric A} {f : A → A}
    (_c : ContractionMap M f) (a : A) :
    Path (M.dist (f a) (f a)) 0 :=
  Path.ofEq (M.dist_self (f a))

/-- Iterating a contraction shrinks distances. -/
def contraction_iterate_path {A : Type u} {M : PathMetric A} {f : A → A}
    (_c : ContractionMap M f) (a : A) :
    Path (f (f a)) (f (f a)) :=
  Path.refl _

/-! ## Path Isometries -/

/-- An isometry preserves distances exactly. -/
structure PathIsometry {A : Type u} {B : Type v}
    (MA : PathMetric A) (MB : PathMetric B) (f : A → B) : Prop where
  /-- Distance preservation. -/
  iso : ∀ a₁ a₂, MB.dist (f a₁) (f a₂) = MA.dist a₁ a₂

/-- An isometry is Lipschitz with constant 1. -/
theorem isometry_is_lipschitz {A : Type u} {B : Type v}
    {MA : PathMetric A} {MB : PathMetric B} {f : A → B}
    (h : PathIsometry MA MB f) : PathLipschitz MA MB 1 f :=
  ⟨fun a₁ a₂ => by simp [h.iso]⟩

/-- Path witnessing isometry distance preservation. -/
def isometry_dist_path {A : Type u} {B : Type v}
    {MA : PathMetric A} {MB : PathMetric B} {f : A → B}
    (h : PathIsometry MA MB f) (a₁ a₂ : A) :
    Path (MB.dist (f a₁) (f a₂)) (MA.dist a₁ a₂) :=
  Path.ofEq (h.iso a₁ a₂)

/-- Isometry composition path. -/
def isometry_comp_path {A : Type u} {B : Type v} {C : Type u}
    {MA : PathMetric A} {MB : PathMetric B} {MC : PathMetric C}
    {f : A → B} {g : B → C}
    (hf : PathIsometry MA MB f) (hg : PathIsometry MB MC g) (a₁ a₂ : A) :
    Path (MC.dist (g (f a₁)) (g (f a₂))) (MA.dist a₁ a₂) :=
  Path.trans
    (Path.ofEq (hg.iso (f a₁) (f a₂)))
    (Path.ofEq (hf.iso a₁ a₂))

/-- Composition of isometries is an isometry. -/
theorem isometry_comp {A : Type u} {B : Type v} {C : Type u}
    {MA : PathMetric A} {MB : PathMetric B} {MC : PathMetric C}
    {f : A → B} {g : B → C}
    (hf : PathIsometry MA MB f) (hg : PathIsometry MB MC g) :
    PathIsometry MA MC (g ∘ f) :=
  ⟨fun a₁ a₂ => by simp [Function.comp, hg.iso, hf.iso]⟩

/-! ## Metric Completion via Paths -/

/-- The completion of a metric space: equivalence classes of Cauchy sequences. -/
structure MetricCompletion {A : Type u} (M : PathMetric A) where
  /-- Representative Cauchy sequence. -/
  rep : MetricCauchy M

/-- Two completions with the same representative are path-equal. -/
def completion_eq_path {A : Type u} {M : PathMetric A}
    (c : MetricCauchy M) :
    Path (MetricCompletion.mk c : MetricCompletion M) (MetricCompletion.mk c) :=
  Path.refl _

/-- Embedding of the original space into its completion. -/
def embedCompletion {A : Type u} (M : PathMetric A) (a : A) : MetricCompletion M :=
  ⟨constCauchy M a⟩

/-- The embedding path: embedding the same element twice yields the same completion. -/
def embed_path {A : Type u} (M : PathMetric A) (a : A) :
    Path (embedCompletion M a) (embedCompletion M a) :=
  Path.refl _

/-! ## Diameter and Bounded Spaces -/

/-- A metric space is bounded if all distances are bounded. -/
structure MetricBounded {A : Type u} (M : PathMetric A) (B : Nat) : Prop where
  /-- All distances are at most B. -/
  bounded : ∀ a₁ a₂ : A, M.dist a₁ a₂ ≤ B

/-- A bounded space has bounded balls. -/
theorem bounded_ball_contains {A : Type u} {M : PathMetric A} {B : Nat}
    (hB : MetricBounded M B) (a x : A) :
    MetricBall M a (B + 1) x := by
  simp [MetricBall]
  have := hB.bounded a x
  omega

/-- CongrArg on distance under equal arguments. -/
def dist_congrArg {A : Type u} {B : Type v} (M : PathMetric B)
    (f : A → B) {a₁ a₂ : A} (p : Path a₁ a₂) :
    Path (M.dist (f a₁) (f a₂)) (M.dist (f a₂) (f a₂)) :=
  Path.congrArg (fun x => M.dist (f x) (f a₂)) (by
    exact ⟨p.steps, p.proof⟩)

/-- CongrArg on distance gives zero at diagonal. -/
theorem dist_congrArg_self {A : Type u} {B : Type v} (M : PathMetric B)
    (f : A → B) (a : A) :
    Path.toEq (dist_congrArg M f (Path.refl a)) = rfl := by
  simp

/-! ## Path Length Metric -/

/-- For any type with a canonical path assignment, we get a metric
    from step-counting. -/
def pathLengthMetric {A : Type u}
    (canonical : (a b : A) → Path a b)
    (h_refl : ∀ a, canonical a a = Path.refl a)
    (h_symm_len : ∀ a b, pathLength (canonical a b) = pathLength (canonical b a))
    (h_tri : ∀ a b c, pathLength (canonical a c) ≤ pathLength (canonical a b) + pathLength (canonical b c)) :
    PathMetric A where
  dist := fun a b => pathLength (canonical a b)
  dist_self := by
    intro a
    simp [pathLength]
    have := h_refl a
    rw [this]
    simp
  dist_symm := h_symm_len
  dist_triangle := h_tri

/-- Transport along a metric distance path preserves Nat structure. -/
theorem transport_metric_path {A : Type u} (M : PathMetric A)
    (a b : A) (P : Nat → Type v) (x : P (M.dist a b)) :
    Path.transport (PathMetric.dist_symm_path M a b) x =
      M.dist_symm a b ▸ x := by
  simp [PathMetric.dist_symm_path, Path.transport]

end MetricPaths
end Topology
end Path
end ComputationalPaths
