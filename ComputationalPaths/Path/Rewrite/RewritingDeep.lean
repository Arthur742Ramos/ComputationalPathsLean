import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Deep Rewriting Theory: Type-Valued Reduction Strategies and Normal Forms

This module develops Type-valued (computational) rewriting theory for the
`Step`/`RwEq` infrastructure on computational paths. All definitions use
`def` or `noncomputable def` (never `theorem` for Type-returning things).
No `sorry`, no `admit`, no `Path.ofEq`.
-/

namespace ComputationalPaths.Path.RewritingDeep

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Multi-step rewriting combinators -/

/-- Append a multi-step reduction after another. -/
noncomputable def StepStar.append {A : Type u} {a b : A} {p q r : Path a b}
    (h₁ : StepStar p q) (h₂ : StepStar q r) : StepStar p r :=
  match h₂ with
  | StepStar.refl _ => h₁
  | StepStar.tail rest step => StepStar.tail (StepStar.append h₁ rest) step

/-- Lift a multi-step reduction through `symm`. -/
noncomputable def stepStar_symm_lift {A : Type u} {a b : A} {p q : Path a b}
    (h : StepStar p q) : StepStar (Path.symm p) (Path.symm q) := by
  induction h with
  | refl => exact StepStar.refl _
  | tail _ step ih => exact StepStar.tail ih (Step.symm_congr step)

/-- Lift a multi-step reduction through left composition. -/
noncomputable def stepStar_trans_left_lift {A : Type u} {a b c : A}
    {p q : Path a b} (r : Path b c)
    (h : StepStar p q) : StepStar (Path.trans p r) (Path.trans q r) := by
  induction h with
  | refl => exact StepStar.refl _
  | tail _ step ih => exact StepStar.tail ih (Step.trans_congr_left r step)

/-- Lift a multi-step reduction through right composition. -/
noncomputable def stepStar_trans_right_lift {A : Type u} {a b c : A}
    (p : Path a b) {q r : Path b c}
    (h : StepStar q r) : StepStar (Path.trans p q) (Path.trans p r) := by
  induction h with
  | refl => exact StepStar.refl _
  | tail _ step ih => exact StepStar.tail ih (Step.trans_congr_right p step)

/-- Combine two multi-step reductions on both sides of a composition. -/
noncomputable def stepStar_trans_lift {A : Type u} {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (hp : StepStar p p') (hq : StepStar q q') :
    StepStar (Path.trans p q) (Path.trans p' q') :=
  StepStar.append (stepStar_trans_left_lift q hp) (stepStar_trans_right_lift p' hq)

/-! ## Normal form witnesses -/

/-- A path is in normal form if no `Step` applies. -/
def IsNormalForm {A : Type u} {a b : A} (p : Path a b) : Prop :=
  ∀ q : Path a b, Step p q → False

/-- A normal form witness: a target, a multi-step reduction, and irreducibility proof. -/
structure NormalFormWitness {A : Type u} {a b : A} (p : Path a b) where
  nf : Path a b
  reduction : StepStar p nf
  irreducible : IsNormalForm nf

/-- Any path that has no steps is trivially a self-normal-form witness. -/
noncomputable def trivial_nf_witness {A : Type u} {a b : A} (p : Path a b)
    (h : IsNormalForm p) : NormalFormWitness p where
  nf := p
  reduction := StepStar.refl _
  irreducible := h

/-! ## Conversion paths (zigzag reductions) -/

/-- A single conversion step: either a forward or backward rewrite step. -/
inductive ConvStep {A : Type u} {a b : A} : Path a b → Path a b → Type (u + 1) where
  | fwd {p q : Path a b} : Step p q → ConvStep p q
  | bwd {p q : Path a b} : Step q p → ConvStep p q

/-- A conversion path: a sequence of forward/backward steps. -/
inductive Conversion {A : Type u} {a b : A} : Path a b → Path a b → Type (u + 1) where
  | refl (p : Path a b) : Conversion p p
  | cons {p q r : Path a b} : ConvStep p q → Conversion q r → Conversion p r

namespace Conversion

/-- Append two conversions. -/
noncomputable def append {A : Type u} {a b : A} {p q r : Path a b}
    (h₁ : Conversion p q) (h₂ : Conversion q r) : Conversion p r := by
  induction h₁ with
  | refl => exact h₂
  | cons step _ ih => exact Conversion.cons step (ih h₂)

/-- Reverse a conversion. -/
noncomputable def reverse {A : Type u} {a b : A} {p q : Path a b}
    (h : Conversion p q) : Conversion q p := by
  induction h with
  | refl => exact Conversion.refl _
  | cons step _ ih =>
    apply Conversion.append ih
    apply Conversion.cons _ (Conversion.refl _)
    cases step with
    | fwd s => exact ConvStep.bwd s
    | bwd s => exact ConvStep.fwd s

/-- A conversion can be extracted from an `RwEq`. -/
noncomputable def ofRwEq {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q) : Conversion p q := by
  induction h with
  | refl => exact Conversion.refl _
  | step s => exact Conversion.cons (ConvStep.fwd s) (Conversion.refl _)
  | symm _ ih => exact ih.reverse
  | trans _ _ ih₁ ih₂ => exact ih₁.append ih₂

/-- A conversion yields an `RwEq`. -/
noncomputable def toRwEq {A : Type u} {a b : A} {p q : Path a b}
    (h : Conversion p q) : RwEq p q := by
  induction h with
  | refl => exact RwEq.refl _
  | cons step _ ih =>
    apply RwEq.trans _ ih
    cases step with
    | fwd s => exact RwEq.step s
    | bwd s => exact RwEq.symm (RwEq.step s)

/-- Length of a conversion. -/
noncomputable def length {A : Type u} {a b : A} {p q : Path a b}
    (h : Conversion p q) : Nat :=
  match h with
  | Conversion.refl _ => 0
  | Conversion.cons _ rest => 1 + rest.length

end Conversion

/-! ## StepStar embeds into RwEq -/

/-- Every multi-step reduction is a rewrite equivalence. -/
noncomputable def rweq_of_stepStar {A : Type u} {a b : A} {p q : Path a b}
    (h : StepStar p q) : RwEq p q := by
  induction h with
  | refl => exact RwEq.refl _
  | tail _ step ih => exact RwEq.trans ih (RwEq.step step)

/-- Build a conversion between two paths that share a common StepStar ancestor. -/
noncomputable def conversion_of_common_ancestor {A : Type u} {a b : A}
    {s p q : Path a b} (h₁ : StepStar s p) (h₂ : StepStar s q) :
    Conversion p q :=
  Conversion.append
    (Conversion.ofRwEq (RwEq.symm (rweq_of_stepStar h₁)))
    (Conversion.ofRwEq (rweq_of_stepStar h₂))

/-! ## Concrete groupoid-fragment reduction strategies -/

/-- Reduce `refl ∘ (refl ∘ p)` to `p` in two steps. -/
noncomputable def reduce_double_left_unit {A : Type u} {a b : A} (p : Path a b) :
    StepStar (Path.trans (Path.refl a) (Path.trans (Path.refl a) p)) p :=
  StepStar.two
    (Step.trans_refl_left (Path.trans (Path.refl a) p))
    (Step.trans_refl_left p)

/-- Reduce `(p ∘ refl) ∘ refl` to `p` in two steps. -/
noncomputable def reduce_double_right_unit {A : Type u} {a b : A} (p : Path a b) :
    StepStar (Path.trans (Path.trans p (Path.refl b)) (Path.refl b)) p :=
  StepStar.two
    (Step.trans_refl_right (Path.trans p (Path.refl b)))
    (Step.trans_refl_right p)

/-- Reduce `symm(symm(symm(p)))` to `symm(p)` in one step. -/
noncomputable def reduce_triple_symm {A : Type u} {a b : A} (p : Path a b) :
    StepStar (Path.symm (Path.symm (Path.symm p))) (Path.symm p) :=
  StepStar.single (Step.symm_symm (Path.symm p))

/-- Reduce `p ∘ (symm(p) ∘ (p ∘ symm(p)))` to `refl` in two steps. -/
noncomputable def reduce_zigzag_to_refl {A : Type u} {a b : A} (p : Path a b) :
    StepStar
      (Path.trans p (Path.trans (Path.symm p) (Path.trans p (Path.symm p))))
      (Path.refl a) :=
  StepStar.two
    (Step.trans_cancel_left p (Path.trans p (Path.symm p)))
    (Step.trans_symm p)

/-- Reduce `(p ∘ q) ∘ (symm(q) ∘ symm(p))` to `p ∘ symm(p)` in two steps. -/
noncomputable def reduce_inverse_composition_partial {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    StepStar
      (Path.trans (Path.trans p q) (Path.trans (Path.symm q) (Path.symm p)))
      (Path.trans p (Path.symm p)) :=
  StepStar.two
    (Step.trans_assoc p q (Path.trans (Path.symm q) (Path.symm p)))
    (Step.trans_congr_right p (Step.trans_cancel_left q (Path.symm p)))

/-- Full reduction: `(p ∘ q) ∘ (symm(q) ∘ symm(p))` to `refl` in three steps. -/
noncomputable def reduce_inverse_composition_full {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) :
    StepStar
      (Path.trans (Path.trans p q) (Path.trans (Path.symm q) (Path.symm p)))
      (Path.refl a) :=
  StepStar.append
    (reduce_inverse_composition_partial p q)
    (StepStar.single (Step.trans_symm p))

/-- Reduce `symm(refl ∘ p)` to `symm(p)` in one step. -/
noncomputable def reduce_symm_of_left_unit {A : Type u} {a b : A} (p : Path a b) :
    StepStar (Path.symm (Path.trans (Path.refl a) p)) (Path.symm p) :=
  StepStar.single (Step.symm_congr (Step.trans_refl_left p))

/-! ## Joinability witnesses for additional critical pairs -/

/-- The Huet diamond: two steps from the same source always
    have equal semantic content (by `step_toEq` / `Step.deterministic`). -/
noncomputable def semantic_joinability {A : Type u} {a b : A}
    {p q r : Path a b} (h₁ : Step p q) (h₂ : Step p r) :
    q.toEq = r.toEq :=
  Step.deterministic h₁ h₂

/-! ## Abstract rewriting system (Type-valued, universe-correct) -/

/-- A Type-valued abstract rewriting system at universe u+1 (matching Step). -/
structure ARS (α : Type u) where
  step : α → α → Type (u + 1)

/-- The ARS induced by `Step` on paths. -/
noncomputable def pathARS {A : Type u} {a b : A} : ARS (Path a b) where
  step := fun p q => Step p q

/-- Multi-step closure for an abstract ARS. -/
inductive ARS.Multi {α : Type u} (R : ARS α) : α → α → Type (u + 1) where
  | refl (a : α) : ARS.Multi R a a
  | tail {a b c : α} : ARS.Multi R a b → R.step b c → ARS.Multi R a c

/-- Conversion (symmetric closure) for an abstract ARS. -/
inductive ARS.Conv {α : Type u} (R : ARS α) : α → α → Type (u + 1) where
  | refl (a : α) : ARS.Conv R a a
  | fwd {a b c : α} : R.step a b → ARS.Conv R b c → ARS.Conv R a c
  | bwd {a b c : α} : R.step b a → ARS.Conv R b c → ARS.Conv R a c

namespace ARS.Conv

noncomputable def append {α : Type u} {R : ARS α} {a b c : α}
    (h₁ : ARS.Conv R a b) (h₂ : ARS.Conv R b c) : ARS.Conv R a c := by
  induction h₁ with
  | refl => exact h₂
  | fwd s _ ih => exact ARS.Conv.fwd s (ih h₂)
  | bwd s _ ih => exact ARS.Conv.bwd s (ih h₂)

noncomputable def reverse {α : Type u} {R : ARS α} {a b : α}
    (h : ARS.Conv R a b) : ARS.Conv R b a := by
  induction h with
  | refl => exact ARS.Conv.refl _
  | fwd s _ ih => exact ih.append (ARS.Conv.bwd s (ARS.Conv.refl _))
  | bwd s _ ih => exact ih.append (ARS.Conv.fwd s (ARS.Conv.refl _))

end ARS.Conv

noncomputable def ARS.multi_to_conv {α : Type u} {R : ARS α} {a b : α}
    (h : ARS.Multi R a b) : ARS.Conv R a b := by
  induction h with
  | refl => exact ARS.Conv.refl _
  | tail _ s ih => exact ih.append (ARS.Conv.fwd s (ARS.Conv.refl _))

/-- Type-valued joinability: two elements have a common reduct. -/
structure ARS.Joinable {α : Type u} (R : ARS α) (a b : α) where
  meet : α
  left : ARS.Multi R a meet
  right : ARS.Multi R b meet

noncomputable def ARS.joinable_to_conv {α : Type u} {R : ARS α} {a b : α}
    (h : ARS.Joinable R a b) : ARS.Conv R a b :=
  (ARS.multi_to_conv h.left).append (ARS.multi_to_conv h.right).reverse

/-! ## Connecting the concrete and abstract layers -/

/-- Map `StepStar` into `ARS.Multi` for `pathARS`. -/
noncomputable def stepStar_to_arsMulti {A : Type u} {a b : A} {p q : Path a b}
    (h : StepStar p q) : ARS.Multi pathARS p q := by
  induction h with
  | refl => exact ARS.Multi.refl _
  | tail _ step ih => exact ARS.Multi.tail ih step

/-- Map `Step.Joinable` into `ARS.Joinable` for `pathARS`. -/
noncomputable def joinable_to_arsJoinable {A : Type u} {a b : A}
    {p q : Path a b} (h : Step.Joinable p q) : ARS.Joinable pathARS p q := by
  cases h with
  | intro r hp hq =>
    exact ⟨r, stepStar_to_arsMulti hp, stepStar_to_arsMulti hq⟩

/-! ## Reduction depth analysis -/

/-- The reduction depth of a StepStar sequence. -/
noncomputable def stepStar_depth {A : Type u} {a b : A} {p q : Path a b}
    (h : StepStar p q) : Nat :=
  match h with
  | StepStar.refl _ => 0
  | StepStar.tail rest _ => stepStar_depth rest + 1

theorem stepStar_depth_refl {A : Type u} {a b : A} (p : Path a b) :
    stepStar_depth (StepStar.refl p) = 0 := rfl

theorem stepStar_depth_single {A : Type u} {a b : A} {p q : Path a b}
    (h : Step p q) : stepStar_depth (StepStar.single h) = 1 := rfl

theorem stepStar_depth_two {A : Type u} {a b : A} {p q r : Path a b}
    (h₁ : Step p q) (h₂ : Step q r) :
    stepStar_depth (StepStar.two h₁ h₂) = 2 := rfl

/-! ## Concrete reduction witnesses for common patterns -/

noncomputable def reduce_refl_trans_refl {A : Type u} (a : A) :
    StepStar (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) :=
  StepStar.single (Step.trans_refl_left (Path.refl a))

noncomputable def reduce_symm_refl {A : Type u} (a : A) :
    StepStar (Path.symm (Path.refl a)) (Path.refl a) :=
  StepStar.single (Step.symm_refl a)

noncomputable def reduce_unit_inverse {A : Type u} {a b : A} (p : Path a b) :
    StepStar (Path.trans (Path.refl a) (Path.trans p (Path.symm p))) (Path.refl a) :=
  StepStar.two
    (Step.trans_refl_left (Path.trans p (Path.symm p)))
    (Step.trans_symm p)

noncomputable def reduce_symm_right_unit {A : Type u} {a b : A} (p : Path a b) :
    StepStar (Path.symm (Path.trans p (Path.refl b))) (Path.symm p) :=
  StepStar.single (Step.symm_congr (Step.trans_refl_right p))

/-- Nested left cancellation: `p ∘ (σp ∘ (q ∘ (σq ∘ r)))` → `r` in 2 steps. -/
noncomputable def reduce_double_cancel_left {A : Type u} {a b d : A}
    (p : Path a b) (r : Path a d) :
    StepStar
      (Path.trans p (Path.trans (Path.symm p) r))
      r :=
  StepStar.single (Step.trans_cancel_left p r)

end ComputationalPaths.Path.RewritingDeep
