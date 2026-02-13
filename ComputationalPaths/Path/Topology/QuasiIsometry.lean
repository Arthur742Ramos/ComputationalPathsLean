/-
# Quasi-Isometries via Computational Paths

This module formalizes quasi-isometries and related coarse geometry in the
computational-paths framework.  We define quasi-isometric maps, coarse
equivalences, Lipschitz maps, nets, quasi-geodesic stability, and state
the Milnor-Švarc lemma.

## Key Definitions

- `QuasiIsometricMap`, `QuasiIsometry`
- `QuasiIsometryInvariant`
- `CoarseEquivalence`, `LipschitzMap`
- `Net`, `MilnorSvarcLemma`
- `QuasiGeodesicStability`

## References

- Bridson–Haefliger, *Metric Spaces of Non-positive Curvature*, Chapter I.8
- de la Harpe, *Topics in Geometric Group Theory*
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Topology.HyperbolicGroups
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace QuasiIsometry

open HyperbolicGroups

universe u v

/-! ## Quasi-Isometric Maps -/

/-- A (λ, ε)-quasi-isometric map between metric spaces. -/
structure QuasiIsometricMap {X : Type u} {Y : Type v}
    (MX : MetricData X) (MY : MetricData Y) (lam eps : Nat) where
  /-- Underlying function. -/
  toFun : X → Y
  /-- Upper bound: distances expand by at most λ·d + ε. -/
  upper_bound : ∀ x₁ x₂, MY.dist (toFun x₁) (toFun x₂) ≤ lam * MX.dist x₁ x₂ + eps
  /-- Lower bound: distances shrink by at most (d - ε) / λ. -/
  lower_bound : ∀ x₁ x₂, MX.dist x₁ x₂ ≤ lam * MY.dist (toFun x₁) (toFun x₂) + eps

namespace QuasiIsometricMap

variable {X : Type u} {Y : Type v}
variable {MX : MetricData X} {MY : MetricData Y}

/-- Identity is a (1, 0)-quasi-isometric map. -/
def id (M : MetricData X) : QuasiIsometricMap M M 1 0 where
  toFun := fun x => x
  upper_bound := by
    intro x₁ x₂
    simp [Nat.one_mul]
  lower_bound := by
    intro x₁ x₂
    simp [Nat.one_mul]

/-- The identity map yields a computational path on points. -/
def id_path (M : MetricData X) (x : X) :
    Path ((id M).toFun x) x :=
  Path.ofEqChain rfl

/-- Composing the identity path with its inverse gives a loop. -/
def id_path_loop (M : MetricData X) (x : X) : Path x x :=
  Path.trans (Path.symm (id_path (M:=M) x)) (id_path (M:=M) x)

end QuasiIsometricMap

/-! ## Quasi-Isometry (with quasi-inverse) -/

/-- A quasi-isometry between metric spaces: a quasi-isometric map with a
    quasi-inverse, where the compositions are within bounded distance of
    the identity. -/
structure QuasiIsometry {X : Type u} {Y : Type v}
    (MX : MetricData X) (MY : MetricData Y) (lam eps : Nat) where
  /-- Forward map. -/
  forward : QuasiIsometricMap MX MY lam eps
  /-- Quasi-inverse. -/
  backward : QuasiIsometricMap MY MX lam eps
  /-- Bound on how close forward ∘ backward is to the identity. -/
  coarseBound : Nat
  /-- Forward then backward is coarsely the identity. -/
  forward_backward : ∀ y, MY.dist (forward.toFun (backward.toFun y)) y ≤ coarseBound
  /-- Backward then forward is coarsely the identity. -/
  backward_forward : ∀ x, MX.dist (backward.toFun (forward.toFun x)) x ≤ coarseBound

/-- Symmetry of distance yields a loop along a quasi-isometry round-trip. -/
def forward_backward_dist_loop {X : Type u} {Y : Type v}
    {MX : MetricData X} {MY : MetricData Y} {lam eps : Nat}
    (qi : QuasiIsometry MX MY lam eps) (y : Y) :
    Path (MY.dist (qi.forward.toFun (qi.backward.toFun y)) y)
      (MY.dist (qi.forward.toFun (qi.backward.toFun y)) y) :=
  Path.trans
    (MY.dist_comm (qi.forward.toFun (qi.backward.toFun y)) y)
    (Path.symm (MY.dist_comm (qi.forward.toFun (qi.backward.toFun y)) y))

/-! ## Quasi-Isometry Invariants -/

/-- A property of metric spaces is a quasi-isometry invariant if it is
    preserved by quasi-isometries. -/
def QuasiIsometryInvariant (P : {X : Type u} → MetricData X → Prop) : Prop :=
  ∀ {X Y : Type u} (MX : MetricData X) (MY : MetricData Y)
    (lam eps : Nat),
    (∃ _qi : QuasiIsometry MX MY lam eps, True) →
    P MX → P MY

/-- δ-hyperbolicity is a quasi-isometry invariant (statement only). -/
def hyperbolicity_qi_invariant : Prop :=
  ∀ {X Y : Type u} (HX : DeltaHyperbolic X) (MY : MetricData Y)
    (lam eps : Nat),
    (∃ _qi : QuasiIsometry HX.toMetricData MY lam eps, True) →
    ∃ δ' : Nat, ∀ e x y z : Y,
      MY.gromovProduct e x z + δ' ≥
        min (MY.gromovProduct e x y) (MY.gromovProduct e y z)

/-! ## Coarse Equivalence -/

/-- A coarse equivalence: a quasi-isometry where the distance bounds
    are given uniformly. -/
structure CoarseEquivalence {X : Type u} {Y : Type v}
    (MX : MetricData X) (MY : MetricData Y) where
  /-- Forward function. -/
  forward : X → Y
  /-- Backward function. -/
  backward : Y → X
  /-- Uniform bound constant. -/
  bound : Nat
  /-- Forward is coarsely surjective. -/
  coarse_surj : ∀ y, MY.dist (forward (backward y)) y ≤ bound
  /-- Backward is coarsely surjective. -/
  coarse_surj' : ∀ x, MX.dist (backward (forward x)) x ≤ bound

/-! ## Lipschitz Maps -/

/-- A Lipschitz map with constant L. -/
structure LipschitzMap {X : Type u} {Y : Type v}
    (MX : MetricData X) (MY : MetricData Y) (L : Nat) where
  /-- Underlying function. -/
  toFun : X → Y
  /-- Lipschitz condition. -/
  lipschitz : ∀ x₁ x₂, MY.dist (toFun x₁) (toFun x₂) ≤ L * MX.dist x₁ x₂

namespace LipschitzMap

variable {X : Type u} {Y : Type v}
variable {MX : MetricData X} {MY : MetricData Y}

/-- Identity is a 1-Lipschitz map. -/
def id (M : MetricData X) : LipschitzMap M M 1 where
  toFun := fun x => x
  lipschitz := by
    intro x₁ x₂
    simp [Nat.one_mul]

end LipschitzMap

/-! ## Nets in Metric Spaces -/

/-- An R-net in a metric space: a subset where every point is within R of
    some net point. -/
structure Net {X : Type u} (M : MetricData X) (R : Nat) where
  /-- Predicate determining net points. -/
  isNetPoint : X → Prop
  /-- Covering property: every point is within R of a net point. -/
  covering : ∀ x, ∃ p, isNetPoint p ∧ M.dist x p ≤ R

/-- An R-separated net: net points are pairwise at least R apart. -/
structure SeparatedNet {X : Type u} (M : MetricData X) (R : Nat)
    extends Net M R where
  /-- Separation property: distinct net points are at least R apart. -/
  separated : ∀ p q, isNetPoint p → isNetPoint q → M.dist p q < R → Path p q

/-! ## Milnor-Švarc Lemma (Statement) -/

/-- The Milnor-Švarc lemma: if a group acts properly and cocompactly
    by isometries on a proper geodesic metric space X, then the group
    is finitely generated and quasi-isometric to X.
    We state this as a proposition. -/
def MilnorSvarcLemma
    {X : Type u}
    (MX : MetricData X)
    (G : Type u)
    (act : G → X → X)
    (_isom : ∀ g x₁ x₂, Path (MX.dist (act g x₁) (act g x₂)) (MX.dist x₁ x₂))
    (_cocompact : ∃ R : Nat, ∀ x, ∃ g, MX.dist x (act g x) ≤ R) :
    Prop :=
  ∃ (lam eps : Nat) (MG : MetricData G),
    ∃ _qi : QuasiIsometry MG MX lam eps, True

/-! ## Quasi-Geodesic Stability -/

/-- Quasi-geodesic stability: in a δ-hyperbolic space, quasi-geodesics with
    the same endpoints fellow-travel. -/
def QuasiGeodesicStability {X : Type u} (H : DeltaHyperbolic X)
    (lam eps : Nat) : Prop :=
  ∃ R : Nat,
    ∀ (qg₁ qg₂ : QuasiGeodesic H.toMetricData lam eps),
      Path (qg₁.point ⟨0, Nat.zero_lt_succ _⟩) (qg₂.point ⟨0, Nat.zero_lt_succ _⟩) →
      Path (qg₁.point ⟨qg₁.len, Nat.lt_succ_of_le (Nat.le_refl _)⟩)
        (qg₂.point ⟨qg₂.len, Nat.lt_succ_of_le (Nat.le_refl _)⟩) →
      ∀ (i : Fin (qg₁.len + 1)),
        ∃ (j : Fin (qg₂.len + 1)),
          H.toMetricData.dist (qg₁.point i) (qg₂.point j) ≤ R

/-! ## Summary -/

/-
We introduced quasi-isometric maps and quasi-isometries, defined
quasi-isometry invariants and stated hyperbolicity invariance,
formalized coarse equivalences, Lipschitz maps, nets, the Milnor-Švarc
lemma as a proposition, and quasi-geodesic stability in δ-hyperbolic spaces.
-/

end QuasiIsometry
end Topology
end Path
end ComputationalPaths
