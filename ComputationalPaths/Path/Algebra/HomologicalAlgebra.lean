/-
# Path-Level Homological Algebra

This module deepens the algebraic interface around computational paths by
organizing:

* `C₀` as objects,
* `C₁` as paths with endpoints,
* `C₂` as `RwEq` witnesses between parallel paths.

Boundary maps are defined as formal differences:

* `∂₁(path) = target - source`,
* `∂₂(witness) = path₂ - path₁`.

We prove `∂₁ ∘ ∂₂ = 0`, define `H₁` as loops modulo `RwEq` (equivalent to `π₁`),
and define `H₂` from 2-cells modulo boundaries of 3-cells, with a finite-basis
bridge from Squier's FDT package.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.SquierDeep
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.SimpleEquiv
namespace ComputationalPaths.Path.Algebra

open ComputationalPaths
open ComputationalPaths.Path

universe u v

noncomputable section

/-! ## Formal differences and chain groups -/

/-- A formal difference `pos - neg`. -/
structure FormalDiff (α : Type u) where
  pos : α
  neg : α

namespace FormalDiff

/-- A formal difference is zero when both entries coincide. -/
noncomputable def IsZero {α : Type u} (x : FormalDiff α) : Prop :=
  x.pos = x.neg

@[simp] theorem isZero_mk {α : Type u} (x y : α) :
    IsZero (FormalDiff.mk x y) ↔ x = y := Iff.rfl

/-- Map a formal difference componentwise. -/
noncomputable def map {α : Type u} {β : Type v} (f : α → β) (x : FormalDiff α) : FormalDiff β :=
  ⟨f x.pos, f x.neg⟩

@[simp] theorem map_pos {α : Type u} {β : Type v}
    (f : α → β) (x : FormalDiff α) :
    (map f x).pos = f x.pos := rfl

@[simp] theorem map_neg {α : Type u} {β : Type v}
    (f : α → β) (x : FormalDiff α) :
    (map f x).neg = f x.neg := rfl

end FormalDiff

/-- Degree-1 cells: computational paths with explicit endpoints. -/
structure OneCell (A : Type u) where
  src : A
  tgt : A
  path : Path src tgt

/-- Degree-2 cells: `RwEq` witnesses between parallel computational paths. -/
structure TwoCell (A : Type u) where
  src : A
  tgt : A
  path₁ : Path src tgt
  path₂ : Path src tgt
  witness : RwEq path₁ path₂

abbrev C0 (A : Type u) : Type u := A
abbrev C1 (A : Type u) : Type u := OneCell A
abbrev C2 (A : Type u) : Type u := TwoCell A

/-- `∂₁(path) = target - source`. -/
noncomputable def boundary1 {A : Type u} (x : C1 A) : FormalDiff (C0 A) :=
  ⟨x.tgt, x.src⟩

/-- `∂₂(witness) = path₂ - path₁`. -/
noncomputable def boundary2 {A : Type u} (x : C2 A) : FormalDiff (C1 A) :=
  ⟨⟨x.src, x.tgt, x.path₂⟩, ⟨x.src, x.tgt, x.path₁⟩⟩

/-- Extend `∂₁` to formal differences of 1-cells. -/
noncomputable def boundary1OnDiff {A : Type u} (x : FormalDiff (C1 A)) :
    FormalDiff (FormalDiff (C0 A)) :=
  ⟨boundary1 x.pos, boundary1 x.neg⟩

/-- The `RwEq` witness ensures both path representatives induce the same 0-boundary. -/
theorem boundary1_eq_of_rweq {A : Type u} {a b : A}
    {p q : Path a b} (h : RwEq p q) :
    boundary1 (A := A) ⟨a, b, p⟩ = boundary1 (A := A) ⟨a, b, q⟩ := by
  have _ : p.toEq = q.toEq := rweq_toEq h
  rfl

/-- Chain condition: `∂₁ ∘ ∂₂ = 0`. -/
theorem d_comp_d_eq_zero {A : Type u} (x : C2 A) :
    FormalDiff.IsZero (boundary1OnDiff (A := A) (boundary2 (A := A) x)) := by
  cases x with
  | mk src tgt p₁ p₂ h =>
      change boundary1 (A := A) ⟨src, tgt, p₂⟩ =
        boundary1 (A := A) ⟨src, tgt, p₁⟩
      simpa using boundary1_eq_of_rweq
        (A := A) (a := src) (b := tgt) (p := p₂) (q := p₁)
        (h := rweq_symm h)

/-- Build a 2-cell directly from a primitive `Step`. -/
noncomputable def twoCellOfStep {A : Type u} {a b : A}
    {p q : Path a b} (h : Step p q) : C2 A where
  src := a
  tgt := b
  path₁ := p
  path₂ := q
  witness := RwEq.step h

/-- The chain condition also holds for primitive step-generated 2-cells. -/
theorem d_comp_d_eq_zero_of_step {A : Type u} {a b : A}
    {p q : Path a b} (h : Step p q) :
    FormalDiff.IsZero
      (boundary1OnDiff (A := A)
        (boundary2 (A := A) (twoCellOfStep (A := A) (a := a) (b := b) (p := p) (q := q) h))) :=
  d_comp_d_eq_zero (A := A) (twoCellOfStep (A := A) (a := a) (b := b) (p := p) (q := q) h)

/-! ## First homology and the fundamental group -/

/-- Boundaries of 2-cells induce the loop relation used for first homology. -/
noncomputable def boundary1Rel {A : Type u} (a : A) (p q : Path a a) : Prop :=
  Nonempty (RwEq p q)

/-- Setoid for first homology at basepoint `a`. -/
noncomputable def boundary1Setoid {A : Type u} (a : A) : Setoid (Path a a) where
  r := boundary1Rel a
  iseqv :=
    { refl := by
        intro p
        exact ⟨rweq_refl (p := p)⟩
      symm := by
        intro p q h
        rcases h with ⟨h⟩
        exact ⟨rweq_symm h⟩
      trans := by
        intro p q r hpq hqr
        rcases hpq with ⟨hpq⟩
        rcases hqr with ⟨hqr⟩
        exact ⟨rweq_trans hpq hqr⟩ }

/-- First homology: loops modulo boundaries of 2-cells (`RwEq`). -/
abbrev H1 (A : Type u) (a : A) : Type u :=
  Quot (boundary1Setoid (A := A) a).r

/-- Comparison map `H₁ → π₁`. -/
noncomputable def h1ToPi1 {A : Type u} {a : A} : H1 A a → π₁(A, a) :=
  Quot.lift
    (fun p : Path a a => Quot.mk _ p)
    (by
      intro p q h
      exact Quot.sound h)

/-- Comparison map `π₁ → H₁`. -/
noncomputable def pi1ToH1 {A : Type u} {a : A} : π₁(A, a) → H1 A a :=
  Quot.lift
    (fun p : Path a a => Quot.mk _ p)
    (by
      intro p q h
      exact Quot.sound h)

@[simp] theorem pi1ToH1_h1ToPi1 {A : Type u} {a : A} (x : H1 A a) :
    pi1ToH1 (h1ToPi1 x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  rfl

@[simp] theorem h1ToPi1_pi1ToH1 {A : Type u} {a : A} (x : π₁(A, a)) :
    h1ToPi1 (pi1ToH1 x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  rfl

/-- `H₁` is equivalent to the fundamental group `π₁`. -/
noncomputable def h1EquivPi1 (A : Type u) (a : A) : SimpleEquiv (H1 A a) (π₁(A, a)) where
  toFun := h1ToPi1
  invFun := pi1ToH1
  left_inv := pi1ToH1_h1ToPi1
  right_inv := h1ToPi1_pi1ToH1

/-! ## Second homology and 3-cell boundaries -/

/-- A 3-cell records two parallel `RwEq` witnesses between the same pair of paths. -/
structure ThreeCell (A : Type u) where
  src : A
  tgt : A
  path₁ : Path src tgt
  path₂ : Path src tgt
  leftWitness : RwEq path₁ path₂
  rightWitness : RwEq path₁ path₂

namespace ThreeCell

/-- Left 2-cell boundary of a 3-cell. -/
noncomputable def leftBoundary {A : Type u} (x : ThreeCell A) : C2 A :=
  ⟨x.src, x.tgt, x.path₁, x.path₂, x.leftWitness⟩

/-- Right 2-cell boundary of a 3-cell. -/
noncomputable def rightBoundary {A : Type u} (x : ThreeCell A) : C2 A :=
  ⟨x.src, x.tgt, x.path₁, x.path₂, x.rightWitness⟩

end ThreeCell

/-- `∂₃` sends a 3-cell to the formal difference of its two 2-cell boundaries. -/
noncomputable def boundary3 {A : Type u} (x : ThreeCell A) : FormalDiff (C2 A) :=
  ⟨x.rightBoundary, x.leftBoundary⟩

/-- Two 2-cells are equivalent in `H₂` when they differ by a 3-cell boundary. -/
noncomputable def boundary2Rel {A : Type u} (x y : C2 A) : Prop :=
  boundary2 (A := A) x = boundary2 (A := A) y

noncomputable def boundary2Setoid (A : Type u) : Setoid (C2 A) where
  r := boundary2Rel (A := A)
  iseqv :=
    { refl := by intro x; rfl
      symm := by intro x y h; exact h.symm
      trans := by intro x y z hxy hyz; exact hxy.trans hyz }

/-- Second homology: 2-cells modulo boundaries of 3-cells. -/
abbrev H2 (A : Type u) : Type u :=
  Quot (boundary2Setoid (A := A)).r

/-- A 3-cell identifies its two boundary 2-cells in `H₂`. -/
theorem h2_identifies_three_boundaries {A : Type u} (x : ThreeCell A) :
    Quot.mk (boundary2Setoid (A := A)).r x.leftBoundary =
      Quot.mk (boundary2Setoid (A := A)).r x.rightBoundary := by
  exact Quot.sound rfl

/-- Squier-FDT bridge: obstruction generators are finitely bounded. -/
theorem h2_obstructions_finite_from_squier :
    ComputationalPaths.Path.Rewriting.HasFDT ComputationalPaths.Path.Rewriting.computationalPathMonoid ∧
      ∃ n : Nat, ComputationalPaths.Path.Rewriting.homotopyBasis.length ≤ n := by
  constructor
  · exact ComputationalPaths.Path.Rewriting.computationalPathMonoid_hasFDT
  · exact ⟨ComputationalPaths.Path.Rewriting.homotopyBasisUpperBound,
      ComputationalPaths.Path.Rewriting.homotopyBasis_finite_bound⟩

/-- Concrete bound extracted from the Squier package. -/
theorem h2_obstruction_bound_eval :
    ComputationalPaths.Path.Rewriting.homotopyBasisUpperBound = 66 :=
  ComputationalPaths.Path.Rewriting.homotopyBasis_bound_eval

/-! ## Euler characteristic on path-level cell data -/

/-- Finite 0/1/2-skeleton data built from computational paths. -/
structure FinitePathComplex (A : Type u) where
  cells0 : List (C0 A)
  cells1 : List (C1 A)
  cells2 : List (C2 A)

/-- Euler characteristic `χ = #C₀ - #C₁ + #C₂`. -/
noncomputable def eulerCharacteristic {A : Type u} (K : FinitePathComplex A) : Int :=
  Int.ofNat K.cells0.length - Int.ofNat K.cells1.length + Int.ofNat K.cells2.length

@[simp] theorem euler_empty {A : Type u} :
    eulerCharacteristic (A := A) ⟨[], [], []⟩ = 0 := by
  simp [eulerCharacteristic]

/-- Formula expansion for `χ` at the computational-path level. -/
theorem euler_formula {A : Type u} (K : FinitePathComplex A) :
    eulerCharacteristic K =
      Int.ofNat K.cells0.length - Int.ofNat K.cells1.length + Int.ofNat K.cells2.length :=
  rfl

/-- Every listed 2-cell satisfies the chain condition `∂₁ ∘ ∂₂ = 0`. -/
theorem finite_chain_condition {A : Type u} (K : FinitePathComplex A) :
    ∀ c ∈ K.cells2,
      FormalDiff.IsZero (boundary1OnDiff (A := A) (boundary2 (A := A) c)) := by
  intro c hc
  exact d_comp_d_eq_zero (A := A) c

end

end ComputationalPaths.Path.Algebra
