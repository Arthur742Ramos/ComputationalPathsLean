import CompPaths.Core
import CompPaths.Rewriting.CriticalPairs

namespace CompPaths.Algebra

open ComputationalPaths
open ComputationalPaths.Path
open CompPaths.Rewriting (StepRule allStepRules allStepRules_count allStepRules_complete)

universe u

abbrev Loop {A : Type u} (a : A) := Path a a

/-- A presentation of loop paths at a basepoint by generators and relations. -/
structure GroupoidPresentation {A : Type u} (a : A) where
  Generators : Loop a → Loop a → Prop
  Relations : Loop a → Loop a → Type u
  generator_sound : ∀ {p q : Loop a}, Generators p q → Relations p q

/-- Canonical presentation: generators are `Step`, relations are `RwEq`. -/
def stepPresentation {A : Type u} (a : A) : GroupoidPresentation a where
  Generators := fun p q => Step p q
  Relations := fun p q => RwEq p q
  generator_sound := fun h => RwEq.step h

/-- The paper-indexed catalogue records 78 Step constructors/rules. -/
theorem step_presentation_rule_count : allStepRules.length = 78 :=
  allStepRules_count

/-- Every catalogue rule is available in the presentation generators. -/
theorem step_presentation_rules_complete : ∀ r : StepRule, r ∈ allStepRules :=
  allStepRules_complete

/-- Any generating `Step` yields a relation in the presented path groupoid. -/
theorem step_generators_present_path_groupoid {A : Type u} {a : A}
    {p q : Loop a} (h : Step p q) :
    (stepPresentation a).Relations p q :=
  (stepPresentation a).generator_sound h

/-- Bidirectional transport of relation witnesses between presentations. -/
structure PresentationInvariant {A : Type u} {a : A}
    (P Q : GroupoidPresentation a) where
  toRel : ∀ {p q : Loop a}, P.Relations p q → Q.Relations p q
  fromRel : ∀ {p q : Loop a}, Q.Relations p q → P.Relations p q

/-- Tietze move: add a redundant generator whose relation is already derivable. -/
def addRedundantGenerator {A : Type u} {a : A}
    (g₁ g₂ : Loop a) (hg : RwEq g₁ g₂) :
    GroupoidPresentation a where
  Generators := fun p q => Step p q ∨ (p = g₁ ∧ q = g₂)
  Relations := fun p q => RwEq p q
  generator_sound := by
    intro p q h
    rcases h with hs | hred
    · exact RwEq.step hs
    · rcases hred with ⟨hp, hq⟩
      subst hp
      subst hq
      exact hg

/-- Tietze move: add a redundant relation that already follows from `RwEq`. -/
def addRedundantRelation {A : Type u} {a : A}
    (r₁ r₂ : Loop a) :
    GroupoidPresentation a where
  Generators := fun p q => Step p q
  Relations := fun p q => (RwEq p q) ⊕ (p = r₁ ∧ q = r₂)
  generator_sound := fun h => Sum.inl (RwEq.step h)

/-- Adding/removing a redundant generator preserves the presented groupoid. -/
def tietze_add_remove_generator {A : Type u} {a : A}
    (g₁ g₂ : Loop a) (hg : RwEq g₁ g₂) :
    PresentationInvariant (addRedundantGenerator g₁ g₂ hg) (stepPresentation a) where
  toRel := fun h => h
  fromRel := fun h => h

/-- Adding/removing a redundant relation preserves the presented groupoid. -/
def tietze_add_remove_relation {A : Type u} {a : A}
    (r₁ r₂ : Loop a) (hr : RwEq r₁ r₂) :
    PresentationInvariant (addRedundantRelation r₁ r₂) (stepPresentation a) where
  toRel := by
    intro p q h
    rcases h with hRw | hRed
    · exact hRw
    · rcases hRed with ⟨hp, hq⟩
      subst hp
      subst hq
      exact hr
  fromRel := fun h => Sum.inl h

/-- Word problem for the presented groupoid: whether two loops are `RwEq`. -/
def PresentedWordProblem {A : Type u} (a : A) (p q : Loop a) : Prop :=
  Nonempty ((stepPresentation a).Relations p q)

noncomputable instance presentedWordProblemDecidable {A : Type u}
    (a : A) (p q : Loop a) : Decidable (PresentedWordProblem a p q) := by
  classical
  unfold PresentedWordProblem
  infer_instance

/-- Any solved word-problem instance gives equality of underlying `Eq` proofs. -/
theorem word_problem_sound {A : Type u} {a : A} {p q : Loop a} :
    PresentedWordProblem a p q → p.toEq = q.toEq := by
  intro h
  rcases h with ⟨hRw⟩
  exact rweq_toEq hRw

noncomputable def decideWordProblem {A : Type u}
    (a : A) (p q : Loop a) : Bool :=
  decide (PresentedWordProblem a p q)

theorem decideWordProblem_spec {A : Type u}
    (a : A) (p q : Loop a) :
    decideWordProblem a p q = true ↔ PresentedWordProblem a p q := by
  simp [decideWordProblem]

theorem word_problem_is_decidable {A : Type u}
    (a : A) (p q : Loop a) :
    Decidable (PresentedWordProblem a p q) :=
  presentedWordProblemDecidable a p q

end CompPaths.Algebra
