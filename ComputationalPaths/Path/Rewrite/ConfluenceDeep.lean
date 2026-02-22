import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths
namespace Confluence

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Abstract confluence infrastructure -/

inductive RTC {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : RTC R a a
  | step {a b c : α} : R a b → RTC R b c → RTC R a c

namespace RTC

variable {α : Type u} {R : α → α → Prop}

noncomputable def single {a b : α} (h : R a b) : RTC R a b :=
  RTC.step h (RTC.refl b)

noncomputable def trans {a b c : α} (h₁ : RTC R a b) (h₂ : RTC R b c) : RTC R a c := by
  induction h₁ with
  | refl _ =>
      exact h₂
  | step hab hbc ih =>
      exact RTC.step hab (ih h₂)

noncomputable def snoc {a b c : α} (h₁ : RTC R a b) (h₂ : R b c) : RTC R a c := by
  induction h₁ with
  | refl _ =>
      exact RTC.step h₂ (RTC.refl c)
  | step hab hbc ih =>
      exact RTC.step hab (ih h₂)

noncomputable def cases_head {a b : α} (h : RTC R a b) :
    a = b ∨ ∃ c, R a c ∧ RTC R c b := by
  cases h with
  | refl _ =>
      left
      rfl
  | step hab hbc =>
      right
      exact ⟨_, hab, hbc⟩

end RTC

noncomputable def LocallyConfluent {α : Type u} (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, RTC R b d ∧ RTC R c d

noncomputable def Confluent {α : Type u} (R : α → α → Prop) : Prop :=
  ∀ a b c, RTC R a b → RTC R a c → ∃ d, RTC R b d ∧ RTC R c d

noncomputable def Diamond {α : Type u} (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

noncomputable def newman_lemma {α : Type u} {R : α → α → Prop}
    (wf : WellFounded (fun y x => R x y))
    (hLocal : LocallyConfluent R) :
    Confluent R := by
  intro a
  induction a using wf.induction with
  | _ a ih =>
      intro b c hab hac
      rcases RTC.cases_head hab with rfl | ⟨a₁, ha₁, h₁b⟩
      · exact ⟨c, hac, RTC.refl c⟩
      · rcases RTC.cases_head hac with rfl | ⟨a₂, ha₂, h₂c⟩
        · exact ⟨b, RTC.refl b, RTC.step ha₁ h₁b⟩
        · obtain ⟨d₀, h₁d₀, h₂d₀⟩ := hLocal a a₁ a₂ ha₁ ha₂
          obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih a₁ ha₁ b d₀ h₁b h₁d₀
          obtain ⟨d₂, hcd₂, hd₁d₂⟩ := ih a₂ ha₂ c d₁ h₂c (RTC.trans h₂d₀ hd₀d₁)
          exact ⟨d₂, RTC.trans hbd₁ hd₁d₂, hcd₂⟩

noncomputable def diamond_lemma_terminating {α : Type u} {R : α → α → Prop}
    (wf : WellFounded (fun y x => R x y))
    (hDiamond : Diamond R) :
    Confluent R := by
  have hLocal : LocallyConfluent R := by
    intro a b c hab hac
    obtain ⟨d, hbd, hcd⟩ := hDiamond a b c hab hac
    exact ⟨d, RTC.single hbd, RTC.single hcd⟩
  exact newman_lemma wf hLocal

/-! ## Path-level specialization for computational paths -/

section PathLayer

variable {A : Type u} {a b : A}

abbrev StepRel : Path a b → Path a b → Prop := fun p q => Path.Step p q

noncomputable def rtc_of_rw {p q : Path a b} (h : Rw p q) :
    RTC (StepRel (A := A) (a := a) (b := b)) p q := by
  induction h with
  | refl =>
      exact RTC.refl _
  | tail _ h₂ ih =>
      exact RTC.snoc ih h₂

noncomputable def rw_of_rtc {p q : Path a b}
    (h : RTC (StepRel (A := A) (a := a) (b := b)) p q) :
    Rw p q := by
  induction h with
  | refl =>
      exact Rw.refl _
  | step hpq _ ih =>
      exact rw_trans (Rw.tail (Rw.refl _) hpq) ih

noncomputable def StepLocallyConfluent : Prop :=
  ∀ p q r : Path a b, Path.Step p q → Path.Step p r → ∃ m, Rw q m ∧ Rw r m

noncomputable def StepConfluent : Prop :=
  ∀ p q r : Path a b, Rw p q → Rw p r → ∃ m, Rw q m ∧ Rw r m

theorem step_newman_lemma
    (wf : WellFounded (fun y x : Path a b => Path.Step x y))
    (hLocal : StepLocallyConfluent (A := A) (a := a) (b := b)) :
    StepConfluent (A := A) (a := a) (b := b) := by
  have hLocalRTC : LocallyConfluent (StepRel (A := A) (a := a) (b := b)) := by
    intro p q r hpq hpr
    rcases hLocal p q r hpq hpr with ⟨m, hqm, hrm⟩
    exact ⟨m, rtc_of_rw hqm, rtc_of_rw hrm⟩
  have hConfRTC :
      Confluent (StepRel (A := A) (a := a) (b := b)) :=
    newman_lemma wf hLocalRTC
  intro p q r hpq hpr
  rcases hConfRTC p q r (rtc_of_rw hpq) (rtc_of_rw hpr) with ⟨m, hqm, hrm⟩
  exact ⟨m, rw_of_rtc hqm, rw_of_rtc hrm⟩

theorem church_rosser_rweq
    (hConf : StepConfluent (A := A) (a := a) (b := b))
    {p q : Path a b} (h : RwEq p q) :
    ∃ m, Rw p m ∧ Rw q m := by
  induction h with
  | refl =>
      exact ⟨_, Rw.refl _, Rw.refl _⟩
  | step hpq =>
      exact ⟨_, Rw.tail (Rw.refl _) hpq, Rw.refl _⟩
  | symm _ ih =>
      rcases ih with ⟨m, hpm, hqm⟩
      exact ⟨m, hqm, hpm⟩
  | trans _ _ ih₁ ih₂ =>
      rcases ih₁ with ⟨m₁, hpm₁, hqm₁⟩
      rcases ih₂ with ⟨m₂, hqm₂, hrm₂⟩
      rcases hConf _ _ _ hqm₁ hqm₂ with ⟨m, hm₁m, hm₂m⟩
      exact ⟨m, rw_trans hpm₁ hm₁m, rw_trans hrm₂ hm₂m⟩

end PathLayer

end Confluence
end ComputationalPaths
