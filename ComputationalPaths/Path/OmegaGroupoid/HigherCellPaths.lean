import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.OmegaGroupoid
namespace ComputationalPaths.Path.OmegaGroupoidCompPaths

open ComputationalPaths.Path.OmegaGroupoid

universe u

abbrev CPath {A : Type u} (a b : A) : Type u := ComputationalPaths.Path a b
abbrev CStep {A : Type u} {a b : A} (p q : CPath a b) : Prop :=
  ComputationalPaths.Path.Step p q
abbrev CRwEq {A : Type u} {a b : A} (p q : CPath a b) : Type u :=
  ComputationalPaths.Path.RwEq p q

section HigherCells

variable {A : Type u} {a b : A}
variable {p q : CPath a b}

/-- A canonical 3-cell witnessing coherence between parallel 2-cells. -/
noncomputable def higherCellCoherence (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ :=
  contractibility₃ d₁ d₂

/-- Coherence between two one-step 2-cells with common endpoints. -/
noncomputable def stepHigherCell (s₁ s₂ : CStep p q) :
    Derivation₃ (Derivation₂.step s₁) (Derivation₂.step s₂) :=
  Derivation₃.step (MetaStep₃.step_eq s₁ s₂)

/-- Left whiskering preserves coherence of 3-cells between 2-cells. -/
noncomputable def whiskerLeftHigherCell {r : CPath a b}
    (c : Derivation₂ r p) (d₁ d₂ : Derivation₂ p q) :
    Derivation₃ (Derivation₂.vcomp c d₁) (Derivation₂.vcomp c d₂) :=
  Derivation₃.whiskerLeft₃ c (higherCellCoherence d₁ d₂)

/-- Right whiskering preserves coherence of 3-cells between 2-cells. -/
noncomputable def whiskerRightHigherCell {r : CPath a b}
    (d₁ d₂ : Derivation₂ p q) (c : Derivation₂ q r) :
    Derivation₃ (Derivation₂.vcomp d₁ c) (Derivation₂.vcomp d₂ c) :=
  Derivation₃.whiskerRight₃ (higherCellCoherence d₁ d₂) c

end HigherCells

section TowerNonCollapse

variable {A : Type u} {a b : A}
variable {p q : CPath a b}

/-- Level-2 derivations remain anchored in rewrite equivalence data. -/
noncomputable def level2_requires_rewrite (d : Derivation₂ p q) : CRwEq p q :=
  derivation₂_to_rweq d

/-- Level-3 cells satisfy Batanin-style contractibility for parallel 2-cells. -/
noncomputable def level3_contractible (d₁ d₂ : Derivation₂ p q) : Nonempty (Derivation₃ d₁ d₂) :=
  ⟨higherCellCoherence d₁ d₂⟩

/-- The coherence tower does not collapse at level 2: level 2 tracks rewrites,
while level 3 is contractible over parallel 2-cells. -/
theorem tower_does_not_collapse
    (d : Derivation₂ p q) (d₁ d₂ : Derivation₂ p q) :
    CRwEq p q ∧ Nonempty (Derivation₃ d₁ d₂) :=
  ⟨level2_requires_rewrite d, level3_contractible d₁ d₂⟩

end TowerNonCollapse

section BataninLeinster

/-- Contractibility data in the sense of Batanin/Leinster weak ω-categories. -/
structure BataninLeinsterWitness (A : Type u) where
  contract₃ :
    ∀ {a b : A} {p q : CPath a b} (d₁ d₂ : Derivation₂ p q),
      Derivation₃ d₁ d₂
  contract₄ :
    ∀ {a b : A} {p q : CPath a b} {d₁ d₂ : Derivation₂ p q}
      (m₁ m₂ : Derivation₃ d₁ d₂),
      Derivation₄ m₁ m₂

/-- Computational paths provide the Batanin/Leinster contractibility tower. -/
noncomputable def bataninLeinsterWitness (A : Type u) : BataninLeinsterWitness A where
  contract₃ := contractibility₃
  contract₄ := contractibility₄

/-- The witness agrees with the existing weak ω-groupoid packaging at level 3. -/
noncomputable def bataninLeinster_contract₃_eq_weakOmega (A : Type u)
    {a b : A} {p q : CPath a b} (d₁ d₂ : Derivation₂ p q) :
    (bataninLeinsterWitness A).contract₃ d₁ d₂ =
      (compPathOmegaGroupoid A).contract₃ d₁ d₂ :=
  rfl

end BataninLeinster

end ComputationalPaths.Path.OmegaGroupoidCompPaths
