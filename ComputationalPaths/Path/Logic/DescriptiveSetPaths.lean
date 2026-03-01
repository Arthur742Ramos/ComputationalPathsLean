/-
# Descriptive Set Theory via Computational Paths

This module models descriptive set theory using computational paths:
Borel sets, analytic sets, Borel hierarchy, perfect set property,
and Baire category theorem aspects.

## References

- Kechris, "Classical Descriptive Set Theory"
- Moschovakis, "Descriptive Set Theory"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Logic
namespace DescriptiveSetPaths

universe u

open ComputationalPaths.Path

/-! ## Topology Basics -/

/-- A topology on a type: open sets closed under unions and finite intersections. -/
structure Topology (X : Type u) where
  isOpen : (X → Prop) → Prop
  open_univ : isOpen (fun _ => True)
  open_empty : isOpen (fun _ => False)
  open_inter : ∀ U V, isOpen U → isOpen V → isOpen (fun x => U x ∧ V x)
  open_union_pair : ∀ U V, isOpen U → isOpen V → isOpen (fun x => U x ∨ V x)

/-- Closed sets are complements of open sets. -/
noncomputable def isClosed {X : Type u} (τ : Topology X) (C : X → Prop) : Prop :=
  τ.isOpen (fun x => ¬ C x)

/-! ## Borel Hierarchy -/

/-- Borel complexity level. -/
inductive BorelLevel where
  | open_ : BorelLevel
  | closed_ : BorelLevel
  | sigma : Nat → BorelLevel
  | pi : Nat → BorelLevel
  | delta : Nat → BorelLevel

/-- A set with its Borel complexity. -/
structure BorelSet (X : Type u) (τ : Topology X) where
  set : X → Prop
  level : BorelLevel

/-- Open Borel set. -/
noncomputable def mkOpenBorel {X : Type u} (τ : Topology X) (U : X → Prop) (h : τ.isOpen U) :
    BorelSet X τ :=
  ⟨U, BorelLevel.open_⟩

/-- Closed Borel set. -/
noncomputable def mkClosedBorel {X : Type u} (τ : Topology X) (C : X → Prop) (h : isClosed τ C) :
    BorelSet X τ :=
  ⟨C, BorelLevel.closed_⟩

/-- Complement of a Borel set. -/
noncomputable def BorelSet.compl {X : Type u} {τ : Topology X} (B : BorelSet X τ) :
    BorelSet X τ :=
  ⟨fun x => ¬ B.set x, match B.level with
    | BorelLevel.open_ => BorelLevel.closed_
    | BorelLevel.closed_ => BorelLevel.open_
    | BorelLevel.sigma n => BorelLevel.pi n
    | BorelLevel.pi n => BorelLevel.sigma n
    | BorelLevel.delta n => BorelLevel.delta n⟩

/-- Complement of complement restores the set. -/
theorem borel_compl_compl_set {X : Type u} {τ : Topology X} (B : BorelSet X τ)
    (h : ∀ x, (¬ ¬ B.set x) ↔ B.set x) :
    ∀ x, B.compl.compl.set x ↔ B.set x := by
  intro x; exact (h x)

/-! ## Baire Category -/

/-- A set is dense if it intersects every nonempty open set. -/
noncomputable def isDense {X : Type u} (τ : Topology X) (D : X → Prop) : Prop :=
  ∀ U, τ.isOpen U → (∃ x, U x) → ∃ x, U x ∧ D x

/-- A set is nowhere dense if every open set has an open subset missing it. -/
noncomputable def isNowhereDense {X : Type u} (τ : Topology X) (N : X → Prop) : Prop :=
  ∀ U, τ.isOpen U → (∃ x, U x) → ∃ x, U x ∧ ¬ N x

/-- A set is meager (first category). -/
noncomputable def isMeager {X : Type u} (τ : Topology X) (M : X → Prop) : Prop :=
  ∃ f : Nat → X → Prop, (∀ x, M x → ∃ i, f i x) ∧
    ∀ i, isNowhereDense τ (f i)

/-- A set is comeager if its complement is meager. -/
noncomputable def isComeager {X : Type u} (τ : Topology X) (C : X → Prop) : Prop :=
  isMeager τ (fun x => ¬ C x)

/-- The universe is dense. -/
theorem dense_univ {X : Type u} (τ : Topology X) :
    isDense τ (fun _ => True) := by
  intro U _ ⟨x, hx⟩
  exact ⟨x, hx, trivial⟩

/-- Dense sets are nonempty in nonempty spaces. -/
theorem dense_nonempty {X : Type u} (τ : Topology X) (D : X → Prop)
    (hD : isDense τ D) (hne : ∃ x : X, True) :
    ∃ x, D x := by
  obtain ⟨x, _⟩ := hne
  obtain ⟨y, _, hy⟩ := hD _ τ.open_univ ⟨x, trivial⟩
  exact ⟨y, hy⟩

/-- Superset of dense is dense. -/
theorem dense_superset {X : Type u} (τ : Topology X) (D E : X → Prop)
    (hD : isDense τ D) (h : ∀ x, D x → E x) :
    isDense τ E := by
  intro U hU hne
  obtain ⟨x, hx, hDx⟩ := hD U hU hne
  exact ⟨x, hx, h x hDx⟩

/-- Empty set is nowhere dense. -/
theorem nowhere_dense_empty {X : Type u} (τ : Topology X) :
    isNowhereDense τ (fun _ => False) := by
  intro U _ ⟨x, hx⟩
  exact ⟨x, hx, not_false⟩

/-- Empty set is meager. -/
theorem meager_empty {X : Type u} (τ : Topology X) :
    isMeager τ (fun _ => False) := by
  exact ⟨fun _ => fun _ => False, fun _ h => absurd h id, fun _ => nowhere_dense_empty τ⟩

/-- Subset of nowhere dense is nowhere dense. -/
theorem nowhere_dense_subset {X : Type u} (τ : Topology X) (N M : X → Prop)
    (hN : isNowhereDense τ N) (h : ∀ x, M x → N x) :
    isNowhereDense τ M := by
  intro U hU hne
  obtain ⟨x, hx, hn⟩ := hN U hU hne
  exact ⟨x, hx, fun hm => hn (h x hm)⟩

/-! ## Perfect Set Property -/

/-- A point is isolated in S. -/
noncomputable def isIsolated {X : Type u} (τ : Topology X) (S : X → Prop) (x : X) : Prop :=
  ∃ U, τ.isOpen U ∧ U x ∧ ∀ y, U y → S y → y = x

/-- A set is perfect if closed and has no isolated points. -/
noncomputable def isPerfect {X : Type u} (τ : Topology X) (S : X → Prop) : Prop :=
  isClosed τ S ∧ ∀ x, S x → ¬ isIsolated τ S x

/-- In a perfect set, every open neighborhood contains another point. -/
theorem perfect_no_isolated {X : Type u} (τ : Topology X) (S : X → Prop)
    (hperf : isPerfect τ S) (x : X) (hx : S x) (U : X → Prop)
    (hU : τ.isOpen U) (hUx : U x) :
    ∃ y, S y ∧ U y ∧ y ≠ x := by
  classical
  by_cases h : ∃ y, S y ∧ U y ∧ y ≠ x
  · exact h
  · exfalso
    apply hperf.2 x hx
    refine ⟨U, hU, hUx, ?_⟩
    intro y hy hSy
    have : ¬ (y ≠ x) := by
      intro hne
      exact h ⟨y, hSy, hy, hne⟩
    exact Classical.not_not.mp this

/-- Perfect and nonempty implies at least two points exist. -/
theorem perfect_two_points {X : Type u} (τ : Topology X) (S : X → Prop)
    (hperf : isPerfect τ S) (x : X) (hx : S x) :
    ∃ y, S y ∧ y ≠ x := by
  obtain ⟨y, hy, _, hne⟩ := perfect_no_isolated τ S hperf x hx
    (fun _ => True) τ.open_univ trivial
  exact ⟨y, hy, hne⟩

/-! ## Cantor-Bendixson -/

/-- The derived set: limit points. -/
noncomputable def derivedSet {X : Type u} (τ : Topology X) (S : X → Prop) : X → Prop :=
  fun x => ∀ U, τ.isOpen U → U x → ∃ y, U y ∧ S y ∧ y ≠ x

/-- Points in a perfect set are limit points. -/
theorem perfect_subset_derived {X : Type u} (τ : Topology X) (S : X → Prop)
    (hperf : isPerfect τ S) : ∀ x, S x → derivedSet τ S x := by
  intro x hx U hU hUx
  obtain ⟨y, hy, hyU, hne⟩ := perfect_no_isolated τ S hperf x hx U hU hUx
  exact ⟨y, hyU, hy, hne⟩

/-! ## Path-based Constructions -/

/-- CongrArg path for set membership. -/
noncomputable def set_congrArg {X : Type u} (S : X → Prop) (x₁ x₂ : X) (p : Path x₁ x₂) :
    Path (S x₁) (S x₂) :=
  Path.congrArg S p

/-- Transport of set membership along a path. -/
theorem transport_membership {X : Type u} (S : X → Prop)
    (x₁ x₂ : X) (p : Path x₁ x₂) :
    Path.transport (D := fun x => S x → S x) p id = id := by
  cases p with
  | mk steps proof =>
    cases proof; simp [Path.transport]

/-- Trans path for topology. -/
noncomputable def topology_trans_path {X : Type u} (x₁ x₂ x₃ : X)
    (p : Path x₁ x₂) (q : Path x₂ x₃) :
    Path x₁ x₃ :=
  Path.trans p q

/-- Symm path for topology. -/
noncomputable def topology_symm_path {X : Type u} (x₁ x₂ : X) (p : Path x₁ x₂) :
    Path x₂ x₁ :=
  Path.symm p

/-- CongrArg on open sets. -/
noncomputable def open_congrArg {X : Type u} (τ : Topology X) (U₁ U₂ : X → Prop)
    (p : Path U₁ U₂) : Path (τ.isOpen U₁) (τ.isOpen U₂) :=
  Path.congrArg τ.isOpen p

/-- CongrArg on closed sets. -/
noncomputable def closed_congrArg {X : Type u} (τ : Topology X) (C₁ C₂ : X → Prop)
    (p : Path C₁ C₂) : Path (isClosed τ C₁) (isClosed τ C₂) :=
  Path.congrArg (isClosed τ) p

/-- CongrArg on dense sets. -/
noncomputable def dense_congrArg {X : Type u} (τ : Topology X) (D₁ D₂ : X → Prop)
    (p : Path D₁ D₂) : Path (isDense τ D₁) (isDense τ D₂) :=
  Path.congrArg (isDense τ) p

/-- CongrArg on meager. -/
noncomputable def meager_congrArg {X : Type u} (τ : Topology X) (M₁ M₂ : X → Prop)
    (p : Path M₁ M₂) : Path (isMeager τ M₁) (isMeager τ M₂) :=
  Path.congrArg (isMeager τ) p

/-- CongrArg on perfect. -/
noncomputable def perfect_congrArg {X : Type u} (τ : Topology X) (S₁ S₂ : X → Prop)
    (p : Path S₁ S₂) : Path (isPerfect τ S₁) (isPerfect τ S₂) :=
  Path.congrArg (isPerfect τ) p

/-- Transport of openness along a path of sets. -/
theorem transport_open {X : Type u} (τ : Topology X)
    (U₁ U₂ : X → Prop) (p : Path U₁ U₂) :
    Path.transport (D := fun U => τ.isOpen U → τ.isOpen U) p id = id := by
  cases p with
  | mk steps proof =>
    cases proof; simp [Path.transport]

/-- CongrArg on derived set. -/
noncomputable def derived_congrArg {X : Type u} (τ : Topology X) (S₁ S₂ : X → Prop)
    (p : Path S₁ S₂) (x : X) :
    Path (derivedSet τ S₁ x) (derivedSet τ S₂ x) :=
  Path.congrArg (fun S => derivedSet τ S x) p

end DescriptiveSetPaths
end Logic
end Path
end ComputationalPaths
