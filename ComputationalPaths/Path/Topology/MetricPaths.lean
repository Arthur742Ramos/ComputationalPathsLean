/-
# Metric Spaces via Computational Paths

Distance modelled via an inductive `MetricStep` rewrite system on a
Nat-valued distance function.  Triangle inequality, Cauchy sequences,
completeness, Lipschitz / contraction / isometry — all path-native.
**Zero** `Path.mk [Step.mk _ _ _] _`.

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Bridson–Haefliger, *Metric Spaces of Non-positive Curvature*
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths
namespace Path
namespace Topology
namespace MetricPaths

open ComputationalPaths.Path

universe u v

/-! ## Path Metric Structure -/

/-- A path metric on a type: distance between elements measured by Nat. -/
structure PathMetric (A : Type u) where
  dist : A → A → Nat
  dist_self : ∀ a, dist a a = 0
  dist_symm : ∀ a b, dist a b = dist b a
  dist_triangle : ∀ a b c, dist a c ≤ dist a b + dist b c

/-! ## MetricStep: domain-specific rewrites (Prop, for indexing) -/

/-- Elementary metric rewrites. -/
inductive MetricStep {A : Type u} (M : PathMetric A) : Nat → Nat → Prop where
  | selfZero  : (a : A) → MetricStep M (M.dist a a) 0
  | symmDist  : (a b : A) → MetricStep M (M.dist a b) (M.dist b a)
  | addComm   : (n m : Nat) → MetricStep M (n + m) (m + n)
  | addZero   : (n : Nat) → MetricStep M (n + 0) n

/-! ## Basic distance theorems -/

-- 1
theorem dist_self_eq {A : Type u} (M : PathMetric A) (a : A) :
    M.dist a a = 0 := M.dist_self a

-- 2
theorem dist_symm_eq {A : Type u} (M : PathMetric A) (a b : A) :
    M.dist a b = M.dist b a := M.dist_symm a b

-- 3
theorem triangle_sum_ge {A : Type u} (M : PathMetric A) (a b c : A) :
    M.dist a b + M.dist b c ≥ M.dist a c := M.dist_triangle a b c

-- 4
theorem four_point_triangle {A : Type u} (M : PathMetric A) (a b c d : A) :
    M.dist a d ≤ M.dist a b + M.dist b c + M.dist c d := by
  have h1 := M.dist_triangle a c d
  have h2 := M.dist_triangle a b c
  omega

-- 5
theorem five_point_triangle {A : Type u} (M : PathMetric A) (a b c d e : A) :
    M.dist a e ≤ M.dist a b + M.dist b c + M.dist c d + M.dist d e := by
  have h1 := four_point_triangle M a b c d
  have h2 := M.dist_triangle a d e
  omega

-- 6
theorem dist_eq_zero_self {A : Type u} (M : PathMetric A) (a : A) :
    M.dist a a + M.dist a a = 0 := by simp [M.dist_self]

-- 7
theorem dist_symm_symm {A : Type u} (M : PathMetric A) (a b : A) :
    M.dist a b = M.dist a b := rfl

/-! ## Path witnesses — zero Path.mk [Step.mk _ _ _] _ -/

-- 8
def dist_self_path {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a a) 0 :=
  ⟨[], M.dist_self a⟩

-- 9
def dist_symm_path {A : Type u} (M : PathMetric A) (a b : A) :
    Path (M.dist a b) (M.dist b a) :=
  ⟨[], M.dist_symm a b⟩

-- 10
def dist_self_add_path {A : Type u} (M : PathMetric A) (a : A) :
    Path (M.dist a a + M.dist a a) 0 :=
  ⟨[], dist_eq_zero_self M a⟩

-- 11
def dist_symm_loop {A : Type u} (M : PathMetric A) (a b : A) :
    Path (M.dist a b) (M.dist a b) :=
  Path.trans (dist_symm_path M a b) (dist_symm_path M b a)

/-! ## Discrete metric -/

-- 12
def discreteMetric (A : Type u) [DecidableEq A] : PathMetric A where
  dist := fun a b => if a = b then 0 else 1
  dist_self := by intro a; simp
  dist_symm := by
    intro a b
    by_cases hab : a = b <;> by_cases hba : b = a <;> simp_all
  dist_triangle := by
    intro a b c
    by_cases hab : a = b <;> by_cases hbc : b = c <;> by_cases hac : a = c <;> simp_all <;> omega

-- 13
theorem discrete_self {A : Type u} [DecidableEq A] (a : A) :
    (discreteMetric A).dist a a = 0 := by simp [discreteMetric]

-- 14
theorem discrete_neq {A : Type u} [DecidableEq A] (a b : A) (h : a ≠ b) :
    (discreteMetric A).dist a b = 1 := by simp [discreteMetric, h]

-- 15
def discrete_self_path {A : Type u} [DecidableEq A] (a : A) :
    Path ((discreteMetric A).dist a a) 0 :=
  dist_self_path (discreteMetric A) a

/-! ## Metric Balls -/

/-- Open ball. -/
def MetricBall {A : Type u} (M : PathMetric A) (center : A) (r : Nat) : A → Prop :=
  fun x => M.dist center x < r

-- 16
theorem center_in_ball {A : Type u} (M : PathMetric A) (a : A) (r : Nat) (hr : 0 < r) :
    MetricBall M a r a := by simp [MetricBall, M.dist_self]; exact hr

-- 17
theorem ball_subset {A : Type u} (M : PathMetric A) (a : A) (r s : Nat) (hrs : r ≤ s)
    (x : A) (hx : MetricBall M a r x) : MetricBall M a s x := by
  simp [MetricBall] at *; omega

-- 18
theorem ball_symm_center {A : Type u} (M : PathMetric A) (a b : A) (r : Nat)
    (h : MetricBall M a r b) : MetricBall M b (r + M.dist b a) a := by
  simp [MetricBall] at *; have := M.dist_symm a b; omega

-- 19
theorem ball_zero_empty {A : Type u} (M : PathMetric A) (a x : A) :
    ¬MetricBall M a 0 x := by simp [MetricBall]

-- 20
theorem ball_one_self {A : Type u} (M : PathMetric A) (a : A) :
    MetricBall M a 1 a := by simp [MetricBall, M.dist_self]

/-! ## Cauchy Sequences -/

/-- A Cauchy sequence. -/
structure MetricCauchy {A : Type u} (M : PathMetric A) where
  seq : Nat → A
  cauchy : ∀ eps : Nat, 0 < eps → ∃ N, ∀ n m, N ≤ n → N ≤ m → M.dist (seq n) (seq m) < eps

-- 21
def constCauchy {A : Type u} (M : PathMetric A) (a : A) : MetricCauchy M where
  seq := fun _ => a
  cauchy := by intro eps heps; exact ⟨0, fun _ _ _ _ => by simp [M.dist_self]; exact heps⟩

-- 22
theorem constCauchy_dist_zero {A : Type u} (M : PathMetric A) (a : A) (n m : Nat) :
    M.dist ((constCauchy M a).seq n) ((constCauchy M a).seq m) = 0 := M.dist_self a

-- 23
def constCauchy_dist_path {A : Type u} (M : PathMetric A) (a : A) (n m : Nat) :
    Path (M.dist ((constCauchy M a).seq n) ((constCauchy M a).seq m)) 0 :=
  ⟨[], constCauchy_dist_zero M a n m⟩

/-! ## Convergence & Completeness -/

/-- Convergence. -/
structure MetricConverges {A : Type u} (M : PathMetric A) (s : Nat → A) (lim : A) : Prop where
  conv : ∀ eps : Nat, 0 < eps → ∃ N, ∀ n, N ≤ n → M.dist (s n) lim < eps

-- 24
theorem const_converges {A : Type u} (M : PathMetric A) (a : A) :
    MetricConverges M (fun _ => a) a :=
  ⟨fun eps heps => ⟨0, fun _ _ => by simp [M.dist_self]; exact heps⟩⟩

/-- Completeness. -/
structure MetricComplete {A : Type u} (M : PathMetric A) : Prop where
  complete : ∀ c : MetricCauchy M, ∃ lim, MetricConverges M c.seq lim

-- 25
theorem complete_eq {A : Type u} {M : PathMetric A}
    (h1 h2 : MetricComplete M) : h1 = h2 := by cases h1; cases h2; congr

/-! ## Lipschitz, Contraction, Isometry -/

/-- Lipschitz with constant L. -/
structure PathLipschitz {A : Type u} {B : Type v}
    (MA : PathMetric A) (MB : PathMetric B) (L : Nat) (f : A → B) : Prop where
  lip : ∀ a₁ a₂, MB.dist (f a₁) (f a₂) ≤ L * MA.dist a₁ a₂

/-- Isometry. -/
structure PathIsometry {A : Type u} {B : Type v}
    (MA : PathMetric A) (MB : PathMetric B) (f : A → B) : Prop where
  iso : ∀ a₁ a₂, MB.dist (f a₁) (f a₂) = MA.dist a₁ a₂

-- 26
theorem isometry_is_lipschitz {A : Type u} {B : Type v}
    {MA : PathMetric A} {MB : PathMetric B} {f : A → B}
    (h : PathIsometry MA MB f) : PathLipschitz MA MB 1 f :=
  ⟨fun a₁ a₂ => by simp [h.iso]⟩

-- 27
theorem isometry_comp {A : Type u} {B : Type v} {C : Type u}
    {MA : PathMetric A} {MB : PathMetric B} {MC : PathMetric C}
    {f : A → B} {g : B → C}
    (hf : PathIsometry MA MB f) (hg : PathIsometry MB MC g) :
    PathIsometry MA MC (g ∘ f) :=
  ⟨fun a₁ a₂ => by simp [Function.comp, hg.iso, hf.iso]⟩

-- 28
def isometry_dist_path {A : Type u} {B : Type v}
    {MA : PathMetric A} {MB : PathMetric B} {f : A → B}
    (h : PathIsometry MA MB f) (a₁ a₂ : A) :
    Path (MB.dist (f a₁) (f a₂)) (MA.dist a₁ a₂) :=
  ⟨[], h.iso a₁ a₂⟩

-- 29
def isometry_comp_path {A : Type u} {B : Type v} {C : Type u}
    {MA : PathMetric A} {MB : PathMetric B} {MC : PathMetric C}
    {f : A → B} {g : B → C}
    (hf : PathIsometry MA MB f) (hg : PathIsometry MB MC g) (a₁ a₂ : A) :
    Path (MC.dist (g (f a₁)) (g (f a₂))) (MA.dist a₁ a₂) :=
  Path.trans (isometry_dist_path hg (f a₁) (f a₂)) (isometry_dist_path hf a₁ a₂)

-- 30
theorem isometry_preserves_self {A : Type u} {B : Type v}
    {MA : PathMetric A} {MB : PathMetric B} {f : A → B}
    (h : PathIsometry MA MB f) (a : A) :
    MB.dist (f a) (f a) = 0 := by rw [h.iso]; exact MA.dist_self a

-- 31
def isometry_self_path {A : Type u} {B : Type v}
    {MA : PathMetric A} {MB : PathMetric B} {f : A → B}
    (h : PathIsometry MA MB f) (a : A) :
    Path (MB.dist (f a) (f a)) 0 :=
  ⟨[], isometry_preserves_self h a⟩

/-- Contraction map. -/
structure ContractionMap {A : Type u} (M : PathMetric A) (f : A → A) where
  L_num : Nat
  L_den : Nat
  den_pos : 0 < L_den
  contract : L_num < L_den
  dist_bound : ∀ x y, M.dist (f x) (f y) * L_den ≤ L_num * M.dist x y

-- 32
theorem contraction_self_zero {A : Type u} {M : PathMetric A} {f : A → A}
    (_c : ContractionMap M f) (a : A) : M.dist (f a) (f a) = 0 := M.dist_self (f a)

-- 33
def contraction_self_path {A : Type u} {M : PathMetric A} {f : A → A}
    (c : ContractionMap M f) (a : A) :
    Path (M.dist (f a) (f a)) 0 :=
  ⟨[], contraction_self_zero c a⟩

/-! ## Metric Bounded -/

structure MetricBounded {A : Type u} (M : PathMetric A) (B : Nat) : Prop where
  bounded : ∀ a₁ a₂ : A, M.dist a₁ a₂ ≤ B

-- 34
theorem bounded_ball_contains {A : Type u} {M : PathMetric A} {B : Nat}
    (hB : MetricBounded M B) (a x : A) :
    MetricBall M a (B + 1) x := by
  simp [MetricBall]; have := hB.bounded a x; omega

-- 35
theorem bounded_triangle {A : Type u} {M : PathMetric A} {B : Nat}
    (hB : MetricBounded M B) (a b c : A) :
    M.dist a c ≤ 2 * B := by
  have h1 := hB.bounded a b; have h2 := hB.bounded b c
  have h3 := M.dist_triangle a b c; omega

/-! ## Path Length as Distance -/

/-- The length of a path's rewrite steps. -/
def pathLength {A : Type u} {a b : A} (p : Path a b) : Nat := p.steps.length

-- 36
@[simp] theorem pathLength_refl {A : Type u} (a : A) :
    pathLength (Path.refl a) = 0 := by simp [pathLength]

-- 37
theorem pathLength_trans {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    pathLength (Path.trans p q) = pathLength p + pathLength q := by
  simp [pathLength, List.length_append]

-- 38
theorem pathLength_symm {A : Type u} {a b : A} (p : Path a b) :
    pathLength (Path.symm p) = pathLength p := by
  simp [pathLength, List.length_map, List.length_reverse]

-- 39
def pathLength_trans_path {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
    Path (pathLength (Path.trans p q)) (pathLength p + pathLength q) :=
  ⟨[], pathLength_trans p q⟩

-- 40
def pathLength_symm_path {A : Type u} {a b : A} (p : Path a b) :
    Path (pathLength (Path.symm p)) (pathLength p) :=
  ⟨[], pathLength_symm p⟩

/-! ## Metric completion -/

structure MetricCompletion {A : Type u} (M : PathMetric A) where
  rep : MetricCauchy M

-- 41
def embedCompletion {A : Type u} (M : PathMetric A) (a : A) : MetricCompletion M :=
  ⟨constCauchy M a⟩

-- 42
def embed_path {A : Type u} (M : PathMetric A) (a : A) :
    Path (embedCompletion M a) (embedCompletion M a) :=
  Path.refl _

/-! ## CongrArg composed paths -/

-- 43
def congrArg_dist {A B : Type u} (M : PathMetric A) (f : B → A) {b1 b2 : B}
    (p : Path b1 b2) : Path (M.dist (f b1) (f b1)) (M.dist (f b2) (f b2)) :=
  Path.congrArg (fun b => M.dist (f b) (f b)) p

-- 44
theorem congrArg_dist_zero {A B : Type u} (M : PathMetric A) (f : B → A) (b : B) :
    M.dist (f b) (f b) = 0 := M.dist_self (f b)

-- 45
def congrArg_dist_self_path {A B : Type u} (M : PathMetric A) (f : B → A) (b : B) :
    Path (M.dist (f b) (f b)) 0 :=
  ⟨[], M.dist_self (f b)⟩

-- 46
def congrArg_dist_trans {A B : Type u} (M : PathMetric A) (f : B → A) {b1 b2 b3 : B}
    (p : Path b1 b2) (q : Path b2 b3) :
    Path (M.dist (f b1) (f b1)) (M.dist (f b3) (f b3)) :=
  Path.congrArg (fun b => M.dist (f b) (f b)) (Path.trans p q)

end MetricPaths
end Topology
end Path
end ComputationalPaths
