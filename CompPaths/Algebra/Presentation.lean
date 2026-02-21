/-
# Groupoid Presentations via Generators and Relations

Defines groupoid presentations from Step generators and RwEq relations,
shows the 78 Step constructors form a presentation, proves Tietze
transformation invariance, and connects to the word problem.

All constructions use explicit Path/Step/RwEq from CompPaths.Core.
-/

import CompPaths.Core
import CompPaths.Rewriting.CriticalPairs

namespace CompPaths.Algebra

open ComputationalPaths
open ComputationalPaths.Path
open CompPaths.Rewriting (StepRule allStepRules allStepRules_count allStepRules_complete)

universe u

noncomputable section

abbrev Loop {A : Type u} (a : A) := Path a a

/-! ## Groupoid Presentations -/

/-- A presentation of the path groupoid at a basepoint:
    generators (Step rules) and relations (RwEq witnesses). -/
structure GroupoidPresentation {A : Type u} (a : A) where
  /-- Generator predicate on pairs of loops. -/
  Generators : Loop a → Loop a → Prop
  /-- Relation predicate — the closure under which we quotient. -/
  Relations : Loop a → Loop a → Prop
  /-- Every generator is a relation. -/
  generator_sound : ∀ {p q : Loop a}, Generators p q → Relations p q

/-- Canonical presentation: generators are `Step`, relations are `RwEq`. -/
def stepPresentation {A : Type u} (a : A) : GroupoidPresentation a where
  Generators := fun p q => Nonempty (Step p q)
  Relations := fun p q => Nonempty (RwEq p q)
  generator_sound := fun ⟨h⟩ => ⟨RwEq.step h⟩

/-- The catalogue records 78 Step constructors. -/
theorem step_presentation_rule_count : allStepRules.length = 78 :=
  allStepRules_count

/-- Every catalogue rule is available. -/
theorem step_presentation_rules_complete : ∀ r : StepRule, r ∈ allStepRules :=
  allStepRules_complete

/-- Any generating `Step` yields a relation. -/
theorem step_generators_sound {A : Type u} {a : A}
    {p q : Loop a} (h : Step p q) :
    (stepPresentation a).Relations p q :=
  ⟨RwEq.step h⟩

/-! ## Presentation Invariance (Tietze Transformations) -/

/-- Bidirectional transport of relation witnesses between presentations. -/
structure PresentationEquiv {A : Type u} {a : A}
    (P Q : GroupoidPresentation a) where
  toRel : ∀ {p q : Loop a}, P.Relations p q → Q.Relations p q
  fromRel : ∀ {p q : Loop a}, Q.Relations p q → P.Relations p q

/-- Tietze move: add a redundant generator whose relation is derivable from `RwEq`. -/
def tietzeAddGenerator {A : Type u} {a : A}
    (g₁ g₂ : Loop a) (hg : RwEq g₁ g₂) :
    GroupoidPresentation a where
  Generators := fun p q => Nonempty (Step p q) ∨ (p = g₁ ∧ q = g₂)
  Relations := fun p q => Nonempty (RwEq p q)
  generator_sound := by
    intro p q h
    match h with
    | Or.inl ⟨hs⟩ => exact ⟨RwEq.step hs⟩
    | Or.inr ⟨hp, hq⟩ => subst hp; subst hq; exact ⟨hg⟩

/-- Adding a redundant generator preserves the presented groupoid. -/
def tietzeAddGenerator_equiv {A : Type u} {a : A}
    (g₁ g₂ : Loop a) (hg : RwEq g₁ g₂) :
    PresentationEquiv (tietzeAddGenerator g₁ g₂ hg) (stepPresentation a) where
  toRel := fun h => h
  fromRel := fun h => h

/-- Tietze move: add a redundant relation that already follows from existing relations. -/
def tietzeAddRelation {A : Type u} {a : A}
    (r₁ r₂ : Loop a) (hr : RwEq r₁ r₂) :
    GroupoidPresentation a where
  Generators := fun p q => Nonempty (Step p q)
  Relations := fun p q => Nonempty (RwEq p q) ∨ (p = r₁ ∧ q = r₂)
  generator_sound := fun ⟨h⟩ => Or.inl ⟨RwEq.step h⟩

/-- Adding a redundant relation preserves the presented groupoid. -/
def tietzeAddRelation_equiv {A : Type u} {a : A}
    (r₁ r₂ : Loop a) (hr : RwEq r₁ r₂) :
    PresentationEquiv (tietzeAddRelation r₁ r₂ hr) (stepPresentation a) where
  toRel := by
    intro p q h
    match h with
    | Or.inl hRw => exact hRw
    | Or.inr ⟨hp, hq⟩ => subst hp; subst hq; exact ⟨hr⟩
  fromRel := fun h => Or.inl h

/-! ## Word Problem -/

/-- The word problem: are two loops related by `RwEq` in the presented groupoid? -/
def WordProblem {A : Type u} (a : A) (p q : Loop a) : Prop :=
  (stepPresentation a).Relations p q

/-- The word problem is equivalent to `Nonempty (RwEq p q)`. -/
theorem wordProblem_iff {A : Type u} {a : A} {p q : Loop a} :
    WordProblem a p q ↔ Nonempty (RwEq p q) :=
  Iff.rfl

/-- Classical decidability of the word problem. -/
instance wordProblemDecidable {A : Type u}
    (a : A) (p q : Loop a) : Decidable (WordProblem a p q) := by
  classical
  exact Classical.propDecidable _

/-- Solved word problems give equality of underlying `Eq` proofs. -/
theorem wordProblem_sound {A : Type u} {a : A} {p q : Loop a}
    (h : WordProblem a p q) : p.toEq = q.toEq :=
  let ⟨w⟩ := h; rweq_toEq w

end

end CompPaths.Algebra
