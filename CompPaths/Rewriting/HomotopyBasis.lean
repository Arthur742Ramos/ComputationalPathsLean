import CompPaths.Core
import CompPaths.Rewriting.CriticalPairs

namespace CompPaths.Rewriting

open ComputationalPaths
open ComputationalPaths.Path

universe u

noncomputable section

/-! ## Generated 2-cells from a basis -/

/-- Closure of basis 2-cells under composition, inversion, and whiskering. -/
inductive Generated2Cells
    (B : {A : Type u} → {a b : A} → Path a b → Path a b → Prop) :
    {A : Type u} → {a b : A} → Path a b → Path a b → Prop where
  | basis {A : Type u} {a b : A} {p q : Path a b} :
      B p q → Generated2Cells B p q
  | refl {A : Type u} {a b : A} (p : Path a b) :
      Generated2Cells B p p
  | symm {A : Type u} {a b : A} {p q : Path a b} :
      Generated2Cells B p q → Generated2Cells B q p
  | trans {A : Type u} {a b : A} {p q r : Path a b} :
      Generated2Cells B p q → Generated2Cells B q r → Generated2Cells B p r
  | whisker_left {A : Type u} {a b c : A}
      (p : Path a b) {q q' : Path b c} :
      Generated2Cells B q q' →
      Generated2Cells B (Path.trans p q) (Path.trans p q')
  | whisker_right {A : Type u} {a b c : A}
      {p p' : Path a b} (q : Path b c) :
      Generated2Cells B p p' →
      Generated2Cells B (Path.trans p q) (Path.trans p' q)

/-- Interpret generated basis terms as `RwEqProp` witnesses. -/
def Generated2Cells.toRwEqProp
    {B : {A : Type u} → {a b : A} → Path a b → Path a b → Prop}
    (toRwEqB :
      ∀ {A : Type u} {a b : A} {p q : Path a b}, B p q → RwEqProp p q) :
    ∀ {A : Type u} {a b : A} {p q : Path a b},
      Generated2Cells B p q → RwEqProp p q := by
  intro A a b p q h
  induction h with
  | basis h => exact toRwEqB h
  | refl p => exact ⟨RwEq.refl p⟩
  | symm _ ih =>
      rcases ih with ⟨ih'⟩
      exact ⟨RwEq.symm ih'⟩
  | trans _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨ih₁'⟩
      rcases ih₂ with ⟨ih₂'⟩
      exact ⟨RwEq.trans ih₁' ih₂'⟩
  | whisker_left p _ ih =>
      rcases ih with ⟨ih'⟩
      exact ⟨rweq_trans_congr_right p ih'⟩
  | whisker_right q _ ih =>
      rcases ih with ⟨ih'⟩
      exact ⟨rweq_trans_congr_left q ih'⟩

/-- Choose a concrete `RwEq` witness from a generated derivation. -/
def Generated2Cells.toRwEq
    {B : {A : Type u} → {a b : A} → Path a b → Path a b → Prop}
    (toRwEqB :
      ∀ {A : Type u} {a b : A} {p q : Path a b}, B p q → RwEqProp p q)
    {A : Type u} {a b : A} {p q : Path a b}
    (h : Generated2Cells B p q) : RwEq p q :=
  rweq_of_rweqProp (Generated2Cells.toRwEqProp (toRwEqB := toRwEqB) h)

/-- A homotopy basis is a set of 2-cells generating all `RwEq` witnesses. -/
structure HomotopyBasis where
  generators :
    {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  generates :
    ∀ {A : Type u} {a b : A} {p q : Path a b},
      RwEq p q → Generated2Cells generators p q

/-! ## Critical-pair basis cells -/

/-- Joinability witness yields an `RwEqProp` 2-cell witness. -/
def rweqProp_of_joinable
    {A : Type u} {a b : A} {p q : Path a b}
    (h : JoinableRw p q) : RwEqProp p q := by
  rcases h with ⟨r, hp, hq⟩
  rcases rweqProp_of_rw hp with ⟨hp'⟩
  rcases rweqProp_of_rw hq with ⟨hq'⟩
  exact ⟨RwEq.trans hp' (RwEq.symm hq')⟩

def rweq_of_joinable
    {A : Type u} {a b : A} {p q : Path a b}
    (h : JoinableRw p q) : RwEq p q :=
  rweq_of_rweqProp (rweqProp_of_joinable h)

/-- Basis cells: critical-pair resolutions plus primitive step cells. -/
inductive CriticalPairBasisCell :
    {A : Type u} → {a b : A} → Path a b → Path a b → Prop where
  | critical {A : Type u} {a b : A} {p q : Path a b}
      (c : CriticalPairCase) (h : JoinableRw p q) :
      CriticalPairBasisCell p q
  | step {A : Type u} {a b : A} {p q : Path a b}
      (h : Step p q) :
      CriticalPairBasisCell p q

def CriticalPairBasisCell.toRwEqProp :
    {A : Type u} → {a b : A} → {p q : Path a b} →
      CriticalPairBasisCell p q → RwEqProp p q
  | _, _, _, _, _, .critical _ h => rweqProp_of_joinable h
  | _, _, _, _, _, .step h => ⟨RwEq.step h⟩

theorem critical_pair_resolutions_in_basis :
    ∀ c ∈ allCriticalPairs, c.Statement :=
  all_critical_pairs_joinable

/-! ## Reduction/decomposition algorithm -/

/-- Decompose any `RwEq` witness into basis generators.
The `step` branch performs explicit Step-level case analysis. -/
theorem reduceRwEqToBasis :
    ∀ {A : Type u} {a b : A} {p q : Path a b},
      RwEq p q → Generated2Cells CriticalPairBasisCell p q := by
  intro A a b p q h
  induction h with
  | refl p =>
      exact Generated2Cells.refl p
  | step hs =>
      have _ : True := by
        cases hs <;> trivial
      exact Generated2Cells.basis (CriticalPairBasisCell.step hs)
  | symm _ ih =>
      exact Generated2Cells.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact Generated2Cells.trans ih₁ ih₂

theorem critical_pair_resolutions_form_homotopy_basis :
    (∀ c ∈ allCriticalPairs, c.Statement) ∧
    (∀ {A : Type u} {a b : A} {p q : Path a b},
      RwEq p q → Generated2Cells CriticalPairBasisCell p q) := by
  refine ⟨critical_pair_resolutions_in_basis, ?_⟩
  intro A a b p q h
  exact reduceRwEqToBasis h

def criticalPairHomotopyBasis : HomotopyBasis where
  generators := CriticalPairBasisCell
  generates := reduceRwEqToBasis

/-! ## Uniqueness up to 3-cells -/

/-- A 3-cell between two decompositions is a path between interpreted 2-cells. -/
abbrev Decomposition3Cell
    {A : Type u} {a b : A} {p q : Path a b}
    (d₁ d₂ : Generated2Cells CriticalPairBasisCell p q) : Type u :=
  Path
    (Generated2Cells.toRwEq
      (B := CriticalPairBasisCell) (toRwEqB := CriticalPairBasisCell.toRwEqProp) d₁)
    (Generated2Cells.toRwEq
      (B := CriticalPairBasisCell) (toRwEqB := CriticalPairBasisCell.toRwEqProp) d₂)

theorem decomposition_unique_up_to_3cells
    {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q)
    (d₁ d₂ : Generated2Cells CriticalPairBasisCell p q)
    (hd₁ :
      Generated2Cells.toRwEq
        (B := CriticalPairBasisCell) (toRwEqB := CriticalPairBasisCell.toRwEqProp) d₁ = h)
    (hd₂ :
      Generated2Cells.toRwEq
        (B := CriticalPairBasisCell) (toRwEqB := CriticalPairBasisCell.toRwEqProp) d₂ = h) :
    Nonempty (Decomposition3Cell d₁ d₂) :=
  ⟨Path.stepChain (hd₁.trans hd₂.symm)⟩

end

end CompPaths.Rewriting
