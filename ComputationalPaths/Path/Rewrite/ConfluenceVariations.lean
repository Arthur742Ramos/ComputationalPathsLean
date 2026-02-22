/-
# Confluence Variations for Computational Paths

This module develops variations on confluence: ground confluence, confluence
modulo an equivalence, commutation of relations, and orthogonal systems.

## Main Results

- Ground confluence and its relation to general confluence (proved!)
- Confluence modulo an equivalence relation (proved!)
- Commutation lemmas: single-step → multi-step (proved!)
- Deterministic/orthogonal systems are confluent (proved!)
- Newman's lemma variant (proved!)
- Path-level RwEq consequences (proved!)

## References

- Huet, "Confluent Reductions" (1980)
- Jouannaud & Kirchner, "Completion of a Set of Rules Modulo" (1986)
- Terese, "Term Rewriting Systems" (2003), Chapters 2, 9, 14
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.Confluence

namespace ComputationalPaths.Path.Rewrite.ConfluenceVariations

open ComputationalPaths.Path

universe u v

/-! ## Abstract Reflexive-Transitive Closure (local) -/

inductive RTC {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl (a : α) : RTC R a a
  | step {a b c : α} : R a b → RTC R b c → RTC R a c

namespace RTC

variable {α : Type u} {R : α → α → Prop}

theorem single {a b : α} (h : R a b) : RTC R a b := .step h (.refl b)

theorem trans {a b c : α} (h₁ : RTC R a b) (h₂ : RTC R b c) : RTC R a c := by
  induction h₁ with
  | refl => exact h₂
  | step s _ ih => exact .step s (ih h₂)

theorem cases_head {a b : α} (h : RTC R a b) :
    (a = b) ∨ (∃ c, R a c ∧ RTC R c b) := by
  cases h with
  | refl => left; rfl
  | step s rest => right; exact ⟨_, s, rest⟩

end RTC

/-! ## Abstract Properties -/

section Defs
variable {α : Type u} (R : α → α → Prop)

noncomputable def Confluent : Prop := ∀ a b c, RTC R a b → RTC R a c → ∃ d, RTC R b d ∧ RTC R c d
noncomputable def LocallyConfluent : Prop := ∀ a b c, R a b → R a c → ∃ d, RTC R b d ∧ RTC R c d
noncomputable def IsNF (a : α) : Prop := ∀ b, ¬ R a b

end Defs

/-! ## Ground Confluence -/

section GroundConfluence

variable {α : Type u} {R : α → α → Prop}

/-- Ground confluence: confluence restricted to a subset. -/
noncomputable def GroundConfluent (P : α → Prop) : Prop :=
  ∀ a b c, P a → RTC R a b → RTC R a c → ∃ d, RTC R b d ∧ RTC R c d

/-- Full confluence implies ground confluence for any predicate. -/
theorem confluent_imp_ground (hC : Confluent R) (P : α → Prop) :
    GroundConfluent (R := R) P :=
  fun a b c _ hab hac => hC a b c hab hac

/-- Ground confluence for ⊤ is full confluence. -/
theorem ground_top_iff_confluent :
    GroundConfluent (R := R) (fun _ => True) ↔ Confluent R :=
  ⟨fun h a b c hab hac => h a b c True.intro hab hac,
   fun h => confluent_imp_ground h _⟩

/-- Ground confluence is monotone. -/
theorem ground_confluent_mono {P Q : α → Prop} (hPQ : ∀ a, Q a → P a)
    (hP : GroundConfluent (R := R) P) : GroundConfluent (R := R) Q :=
  fun a b c hqa => hP a b c (hPQ a hqa)

/-- Ground confluence with a unique normal form function. -/
theorem ground_confluent_of_unique_nf {P : α → Prop}
    (nf : α → α)
    (hnf_reach : ∀ a, P a → RTC R a (nf a))
    (hnf_preserved : ∀ a b, P a → R a b → P b)
    (hnf_eq : ∀ a b, P a → RTC R a b → nf a = nf b) :
    GroundConfluent (R := R) P := by
  intro a b c hpa hab hac
  -- Show P is preserved by RTC
  have rtc_pres : ∀ x y, P x → RTC R x y → P y := by
    intro x y hpx hxy; induction hxy with
    | refl => exact hpx
    | step s _ ih => exact ih (hnf_preserved _ _ hpx s)
  have hpb := rtc_pres a b hpa hab
  have hpc := rtc_pres a c hpa hac
  have heq : nf b = nf c := by rw [← hnf_eq a b hpa hab, ← hnf_eq a c hpa hac]
  exact ⟨nf b, hnf_reach b hpb, heq ▸ hnf_reach c hpc⟩

end GroundConfluence

/-! ## Confluence Modulo an Equivalence Relation -/

section ConfluenceModulo

variable {α : Type u}

/-- Reflexive-transitive-symmetric closure. -/
inductive EquivClosure (E : α → α → Prop) : α → α → Prop
  | refl_ec (a : α) : EquivClosure E a a
  | step_fwd {a b c : α} : E a b → EquivClosure E b c → EquivClosure E a c
  | step_bwd {a b c : α} : E b a → EquivClosure E b c → EquivClosure E a c

namespace EquivClosure

variable {E : α → α → Prop}

theorem trans_ec {a b c : α} (h₁ : EquivClosure E a b) (h₂ : EquivClosure E b c) :
    EquivClosure E a c := by
  induction h₁ with
  | refl_ec => exact h₂
  | step_fwd s _ ih => exact .step_fwd s (ih h₂)
  | step_bwd s _ ih => exact .step_bwd s (ih h₂)

theorem symm_ec {a b : α} (h : EquivClosure E a b) : EquivClosure E b a := by
  induction h with
  | refl_ec => exact .refl_ec _
  | step_fwd s _ ih => exact ih.trans_ec (.step_bwd s (.refl_ec _))
  | step_bwd s _ ih => exact ih.trans_ec (.step_fwd s (.refl_ec _))

end EquivClosure

variable (R E : α → α → Prop)

/-- Confluence modulo E: peaks can be closed up to E-equivalence. -/
noncomputable def ConfluentModulo : Prop :=
  ∀ a b c, RTC R a b → RTC R a c →
    ∃ b' c', RTC R b b' ∧ RTC R c c' ∧ EquivClosure E b' c'

/-- Standard confluence implies confluence modulo any E. -/
theorem confluent_imp_confluent_modulo (hC : Confluent R) :
    ConfluentModulo R E := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hC a b c hab hac
  exact ⟨d, d, hbd, hcd, .refl_ec d⟩

/-- Confluence modulo identity is just confluence. -/
theorem confluent_modulo_id_iff :
    ConfluentModulo R (fun a b => a = b) ↔ Confluent R := by
  constructor
  · intro h a b c hab hac
    obtain ⟨b', c', hbb', hcc', hbc'⟩ := h a b c hab hac
    suffices b' = c' by subst this; exact ⟨b', hbb', hcc'⟩
    clear h hab hac hbb' hcc' a b c
    induction hbc' with
    | refl_ec => rfl
    | step_fwd s _ ih => exact s.trans ih
    | step_bwd s _ ih => exact s.symm.trans ih
  · exact confluent_imp_confluent_modulo R _

/-- Confluence modulo is monotone in E. -/
theorem confluent_modulo_mono {E₁ E₂ : α → α → Prop}
    (hle : ∀ a b, E₁ a b → E₂ a b)
    (h : ConfluentModulo R E₁) : ConfluentModulo R E₂ := by
  intro a b c hab hac
  obtain ⟨b', c', hbb', hcc', hbc'⟩ := h a b c hab hac
  refine ⟨b', c', hbb', hcc', ?_⟩
  clear h hab hac hbb' hcc' a b c
  induction hbc' with
  | refl_ec => exact .refl_ec _
  | step_fwd s _ ih => exact .step_fwd (hle _ _ s) ih
  | step_bwd s _ ih => exact .step_bwd (hle _ _ s) ih

end ConfluenceModulo

/-! ## Newman's Lemma (local variant) -/

section Newman

variable {α : Type u} {R : α → α → Prop}

/-- Newman's Lemma: termination + local confluence → confluence. -/
theorem newman_lemma
    (wf : WellFounded (fun y x => R x y))
    (lc : LocallyConfluent R) : Confluent R := by
  intro a
  induction a using wf.induction with
  | _ a ih =>
    intro b c hab hac
    rcases hab.cases_head with rfl | ⟨a₁, ha₁, h₁b⟩
    · exact ⟨c, hac, .refl c⟩
    · rcases hac.cases_head with rfl | ⟨a₂, ha₂, h₂c⟩
      · exact ⟨b, .refl b, .step ha₁ h₁b⟩
      · obtain ⟨d₀, h₁d₀, h₂d₀⟩ := lc a a₁ a₂ ha₁ ha₂
        obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih a₁ ha₁ b d₀ h₁b h₁d₀
        obtain ⟨d₂, hcd₂, hd₁d₂⟩ := ih a₂ ha₂ c d₁ h₂c (h₂d₀.trans hd₀d₁)
        exact ⟨d₂, hbd₁.trans hd₁d₂, hcd₂⟩

/-- Confluence implies unique normal forms. -/
theorem confluent_unique_nf (hC : Confluent R) {a b c : α}
    (hab : RTC R a b) (hac : RTC R a c)
    (hb : IsNF R b) (hc : IsNF R c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := hC a b c hab hac
  rcases hbd.cases_head with rfl | ⟨e, hbe, _⟩
  · rcases hcd.cases_head with rfl | ⟨e, hce, _⟩
    · rfl
    · exact absurd hce (hc e)
  · exact absurd hbe (hb e)

end Newman

/-! ## Deterministic / Orthogonal Systems -/

section Deterministic

variable {α : Type u}

/-- A deterministic step function. -/
noncomputable def DetStep (step : α → Option α) (a b : α) : Prop := step a = some b

/-- Deterministic steps are functional. -/
theorem det_functional {step : α → Option α} {a b c : α}
    (hb : DetStep step a b) (hc : DetStep step a c) : b = c := by
  simp [DetStep] at hb hc; rw [hb] at hc; exact Option.some.inj hc

/-- A deterministic relation is confluent. -/
theorem det_confluent (step : α → Option α) : Confluent (DetStep step) := by
  intro a b c hab hac
  induction hab with
  | refl => exact ⟨c, hac, .refl c⟩
  | @step a' x b' hax hxb ih =>
    induction hac with
    | refl => exact ⟨b', .refl b', .step hax hxb⟩
    | @step _ y _ hay hyc _ =>
      have hxy := det_functional hax hay; subst hxy
      exact ih hyc

/-- A deterministic relation is locally confluent. -/
theorem det_locally_confluent (step : α → Option α) : LocallyConfluent (DetStep step) := by
  intro a b c hb hc
  have := det_functional hb hc; subst this
  exact ⟨b, .refl b, .refl b⟩

/-- Non-overlapping rules give deterministic steps → confluence. -/
theorem orthogonal_confluent (step : α → Option α) : Confluent (DetStep step) :=
  det_confluent step

end Deterministic

/-! ## Commutation of Relations -/

section Commutation

variable {α : Type u} {R S : α → α → Prop}

/-- Single-step commutation. -/
noncomputable def Commute1 : Prop :=
  ∀ a b c, R a b → S a c → ∃ d, S b d ∧ R c d

/-- Multi-step commutation. -/
noncomputable def StrongCommute : Prop :=
  ∀ a b c, RTC R a b → RTC S a c → ∃ d, RTC S b d ∧ RTC R c d

/-- Strip lemma for commutation: single R-step vs multi S-step. -/
theorem commute1_strip (hC : Commute1 (R := R) (S := S))
    {a b c : α} (hab : R a b) (hac : RTC S a c) :
    ∃ d, RTC S b d ∧ R c d := by
  induction hac generalizing b with
  | refl => exact ⟨b, .refl b, hab⟩
  | @step _ x _ hax _ ih =>
    obtain ⟨y, hby, hxy⟩ := hC _ _ _ hab hax
    obtain ⟨d, hyd, hcd⟩ := ih hxy
    exact ⟨d, .step hby hyd, hcd⟩

/-- Single-step commutation implies multi-step commutation. -/
theorem commute1_imp_strong (hC : Commute1 (R := R) (S := S)) :
    StrongCommute (R := R) (S := S) := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl => exact ⟨c, hac, .refl c⟩
  | @step _ x _ hax _ ih =>
    obtain ⟨d₀, hxd₀, hcd₀⟩ := commute1_strip hC hax hac
    obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih _ hxd₀
    exact ⟨d₁, hbd₁, (RTC.single hcd₀).trans hd₀d₁⟩

/-- Symmetric commutation. -/
theorem commute1_symm (hC : Commute1 (R := R) (S := S)) :
    Commute1 (R := S) (S := R) := by
  intro a b c hab hac
  obtain ⟨d, hcd, hbd⟩ := hC a c b hac hab
  exact ⟨d, hbd, hcd⟩

/-- Local confluence means single-step peaks are multi-step joinable. -/
theorem lc_self_commute_rtc (hLC : LocallyConfluent R) :
    ∀ a b c, R a b → R a c → ∃ d, RTC R b d ∧ RTC R c d :=
  hLC

/-- Strong commutation of R with itself follows from confluence. -/
theorem strong_commute_self_of_confluent (hC : Confluent R) :
    StrongCommute (R := R) (S := R) := hC

end Commutation

/-! ## Reflexive Closure Preserves Confluence -/

section ReflClosure

variable {α : Type u} {R : α → α → Prop}

/-- Reflexive closure of R. -/
noncomputable def ReflClosure (a b : α) : Prop := R a b ∨ a = b

theorem rtc_refl_embed {a b : α} (h : RTC R a b) :
    RTC (ReflClosure (R := R)) a b := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (.inl s) ih

theorem rtc_refl_project {a b : α} (h : RTC (ReflClosure (R := R)) a b) :
    RTC R a b := by
  induction h with
  | refl => exact .refl _
  | step s _ ih =>
    rcases s with h | rfl
    · exact .step h ih
    · exact ih

/-- Reflexive closure preserves confluence. -/
theorem confluent_refl_closure (hC : Confluent R) :
    Confluent (ReflClosure (R := R)) := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hC a b c (rtc_refl_project hab) (rtc_refl_project hac)
  exact ⟨d, rtc_refl_embed hbd, rtc_refl_embed hcd⟩

end ReflClosure

/-! ## Subset Relations -/

section Subset

variable {α : Type u} {R S : α → α → Prop}

/-- R-peaks are S-joinable when R ⊆ S and S is confluent. -/
theorem r_peaks_s_joinable (hRS : ∀ a b, R a b → S a b)
    (hS : Confluent S) {a b c : α}
    (hab : RTC R a b) (hac : RTC R a c) :
    ∃ d, RTC S b d ∧ RTC S c d := by
  have liftR : ∀ {x y}, RTC R x y → RTC S x y := by
    intro x y h; induction h with
    | refl => exact .refl _
    | step s _ ih => exact .step (hRS _ _ s) ih
  exact hS a b c (liftR hab) (liftR hac)

/-- RTC of a subrelation embeds into RTC of the superrelation. -/
theorem rtc_mono {a b : α} (hRS : ∀ x y, R x y → S x y) (h : RTC R a b) :
    RTC S a b := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (hRS _ _ s) ih

end Subset

/-! ## Path-Level RwEq Consequences -/

section PathLevel

variable {A : Type u} {a b : A}

open Confluence

/-- Equal paths are RwEq-equivalent. -/
noncomputable def rweq_of_eq {p q : Path a b} (h : p = q) : RwEq p q := by subst h; exact RwEq.refl p

/-- Path rewriting preserves toEq. -/
theorem rw_preserves_toEq {p q : Path a b} (h : Rw p q) : p.toEq = q.toEq :=
  rw_toEq h

/-- RwEq is transitive (re-export). -/
noncomputable def rweq_trans' {p q r : Path a b} (h₁ : RwEq p q) (h₂ : RwEq q r) : RwEq p r :=
  rweq_trans h₁ h₂

/-- RwEq is symmetric (re-export). -/
noncomputable def rweq_symm' {p q : Path a b} (h : RwEq p q) : RwEq q p :=
  rweq_symm h

/-- Rw implies RwEq. -/
noncomputable def rweq_of_rw' {p q : Path a b} (h : Rw p q) : RwEq p q :=
  rweq_of_rw h

/-- Single step implies RwEq. -/
noncomputable def rweq_of_step' {p q : Path a b} (h : Step (A := A) p q) : RwEq p q :=
  rweq_of_rw (Rw.tail (Rw.refl p) h)

/-- RwEq on paths is "confluent": any two RwEq-equivalent paths can be joined
(since RwEq is already an equivalence relation). -/
noncomputable def rweq_confluent_eq {p q r : Path a b}
    (hpq : RwEq p q) (hpr : RwEq p r) : RwEq q r :=
  rweq_trans (rweq_symm hpq) hpr

/-- Two single-step reductions from the same source are RwEq-joinable. -/
noncomputable def step_peak_rweq {p q r : Path a b}
    (hpq : Step (A := A) p q) (hpr : Step (A := A) p r) : RwEq q r :=
  rweq_trans (rweq_symm (rweq_of_step' hpq)) (rweq_of_step' hpr)

/-- Multi-step reductions preserve RwEq class. -/
noncomputable def rw_preserves_rweq_class {p q : Path a b} (h : Rw p q) : RwEq p q :=
  rweq_of_rw h

/-- RwEq-equivalent paths have equal toEq. -/
noncomputable def rweq_toEq {p q : Path a b} (h : RwEq p q) : p.toEq = q.toEq := by
  induction h with
  | refl => rfl
  | step s => exact step_toEq s
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end PathLevel

end ComputationalPaths.Path.Rewrite.ConfluenceVariations
