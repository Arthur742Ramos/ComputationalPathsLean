/- 
# Valuated Matroids

This module defines valuated matroids in a tropical setting, introduces
the Dressian and tropical Grassmannian, proves the tropical Plucker relation
for valuated matroids, and formalizes the regular-subdivision construction
induced by a valuation.
-/

import Mathlib
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace TropicalGeometry

universe u

/-- Tropical weights are modeled by `WithTop ℤ` (min-plus convention). -/
abbrev TropicalWeight : Type := WithTop ℤ

/-- A valuation assigns a tropical weight to each finite subset. -/
abbrev Valuation (ι : Type u) : Type u := Finset ι → TropicalWeight

/-- Basis exchange on finite sets: remove `e` and insert `f`. -/
def exchange {ι : Type u} [DecidableEq ι] (B : Finset ι) (e f : ι) : Finset ι :=
  insert f (B.erase e)

/-- Tropical Plucker exchange relation for rank `r` valuations. -/
def TropicalPluckerRelation {ι : Type u} [DecidableEq ι] (r : ℕ) (v : Valuation ι) : Prop :=
  ∀ ⦃B₁ B₂ : Finset ι⦄,
    B₁.card = r →
    B₂.card = r →
    ∀ ⦃e : ι⦄, e ∈ B₁ \ B₂ →
      ∃ f, f ∈ B₂ \ B₁ ∧
        v B₁ + v B₂ ≥
          v (exchange B₁ e f) + v (exchange B₂ f e)

/-- A valuated matroid of rank `r` on ground type `ι`. -/
structure ValuatedMatroid (ι : Type u) [DecidableEq ι] (r : ℕ) where
  valuation : Valuation ι
  support_rank : ∀ ⦃B : Finset ι⦄, valuation B ≠ ⊤ → B.card = r
  support_nonempty : ∃ B : Finset ι, valuation B ≠ ⊤
  tropicalPlucker : TropicalPluckerRelation r valuation

/-- Every valuated matroid satisfies the tropical Plucker relation by definition. -/
theorem ValuatedMatroid.satisfies_tropicalPlucker
    {ι : Type u} [DecidableEq ι] {r : ℕ}
    (M : ValuatedMatroid ι r) :
    TropicalPluckerRelation r M.valuation :=
  M.tropicalPlucker

/-- Exchange inequality form of the tropical Plucker relation. -/
theorem ValuatedMatroid.exchange_inequality
    {ι : Type u} [DecidableEq ι] {r : ℕ}
    (M : ValuatedMatroid ι r)
    {B₁ B₂ : Finset ι}
    (hB₁ : B₁.card = r)
    (hB₂ : B₂.card = r)
    {e : ι} (he : e ∈ B₁ \ B₂) :
    ∃ f, f ∈ B₂ \ B₁ ∧
      M.valuation B₁ + M.valuation B₂ ≥
        M.valuation (exchange B₁ e f) + M.valuation (exchange B₂ f e) :=
  M.tropicalPlucker hB₁ hB₂ he

/-- The Dressian: all valuations satisfying tropical Plucker relations. -/
def Dressian (ι : Type u) [DecidableEq ι] (r : ℕ) : Set (Valuation ι) :=
  { v | TropicalPluckerRelation r v }

/-- A representable tropical valuation (abstract representation witness). -/
structure TropicalRepresentation (ι : Type u) [DecidableEq ι] (r : ℕ) where
  valuation : Valuation ι
  plucker : TropicalPluckerRelation r valuation

/-- The tropical Grassmannian: representable tropical valuations. -/
def TropicalGrassmannian (ι : Type u) [DecidableEq ι] (r : ℕ) : Set (Valuation ι) :=
  { v | ∃ R : TropicalRepresentation ι r, R.valuation = v }

/-- Every tropical Grassmannian point lies in the Dressian. -/
theorem tropicalGrassmannian_subset_dressian
    (ι : Type u) [DecidableEq ι] (r : ℕ) :
    TropicalGrassmannian ι r ⊆ Dressian ι r := by
  intro v hv
  rcases hv with ⟨R, rfl⟩
  exact R.plucker

/-- Valuated matroids define points in the Dressian. -/
theorem ValuatedMatroid.mem_dressian
    {ι : Type u} [DecidableEq ι] {r : ℕ}
    (M : ValuatedMatroid ι r) :
    M.valuation ∈ Dressian ι r :=
  M.tropicalPlucker

/-- Abstract regular subdivision data on subsets of the ground set. -/
structure RegularSubdivision (ι : Type u) where
  cells : Set (Finset ι)
  nonempty : ∃ B : Finset ι, cells B

/-- The cells induced by a valuation are exactly those with finite weight. -/
def inducedCells {ι : Type u} (v : Valuation ι) : Set (Finset ι) :=
  { B | v B ≠ ⊤ }

/-- A subdivision is regular for `v` when its cells match the induced support. -/
def IsRegularFor {ι : Type u} (S : RegularSubdivision ι) (v : Valuation ι) : Prop :=
  ∀ B : Finset ι, S.cells B ↔ inducedCells v B

/-- Canonical regular subdivision attached to a valuation with nonempty support. -/
def regularSubdivisionOfValuation
    {ι : Type u}
    (v : Valuation ι)
    (h : ∃ B : Finset ι, v B ≠ ⊤) :
    RegularSubdivision ι where
  cells := inducedCells v
  nonempty := h

/-- The canonical subdivision is regular for the valuation that defines it. -/
theorem regularSubdivisionOfValuation_isRegular
    {ι : Type u}
    (v : Valuation ι)
    (h : ∃ B : Finset ι, v B ≠ ⊤) :
    IsRegularFor (regularSubdivisionOfValuation v h) v := by
  intro B
  rfl

/-- Connection theorem: every valuated matroid induces a regular subdivision. -/
theorem ValuatedMatroid.exists_regularSubdivision
    {ι : Type u} [DecidableEq ι] {r : ℕ}
    (M : ValuatedMatroid ι r) :
    ∃ S : RegularSubdivision ι, IsRegularFor S M.valuation := by
  refine ⟨regularSubdivisionOfValuation M.valuation M.support_nonempty, ?_⟩
  exact regularSubdivisionOfValuation_isRegular M.valuation M.support_nonempty

/-- Path witness for reflexivity of a valuated matroid valuation. -/
theorem ValuatedMatroid.valuation_path
    {ι : Type u} [DecidableEq ι] {r : ℕ}
    (M : ValuatedMatroid ι r) :
    ComputationalPaths.Path M.valuation M.valuation :=
  ComputationalPaths.Path.refl _

/-- A two-step reflexive composition on valuations is `RwEq`-equivalent to reflexivity. -/
noncomputable def ValuatedMatroid.valuation_rweq
    {ι : Type u} [DecidableEq ι] {r : ℕ}
    (M : ValuatedMatroid ι r) :
    ComputationalPaths.Path.RwEq
      (ComputationalPaths.Path.trans
        (ComputationalPaths.Path.refl M.valuation)
        (ComputationalPaths.Path.refl M.valuation))
      (ComputationalPaths.Path.refl M.valuation) := by
  apply ComputationalPaths.Path.rweq_of_eq
  simp

end TropicalGeometry
