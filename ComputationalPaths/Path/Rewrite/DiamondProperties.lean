/-
# Diamond Properties and Church-Rosser for Computational Paths

This module develops diamond properties, Church-Rosser, semi-confluence,
and their relationships. All core results are proved at the abstract level
on a type with a binary relation, then connected to the `Step`/`Rw` infra.

## Main Results

- `diamond_imp_confluence`: one-step diamond → multi-step confluence (proved!)
- `church_rosser_iff_confluence`: Church-Rosser ↔ confluence (proved!)
- `semi_confluence_iff_confluence`: semi-confluence ↔ confluence (proved!)
- `newman_lemma_dp`: termination + local confluence → confluence (proved!)
- `confluent_imp_unique_nf`: unique normal forms (proved!)
- Joinability combinators on `Path` `Rw` (proved!)
- Connection to the existing Confluence.Join infrastructure (proved!)

## References

- Huet, "Confluent Reductions" (1980)
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Terese, "Term Rewriting Systems" (2003), Chapter 2
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.Confluence

namespace ComputationalPaths.Path.Rewrite.DiamondProperties

open ComputationalPaths.Path

universe u v

/-! ## Abstract Reflexive-Transitive Closure -/

inductive RTC' {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl' (a : α) : RTC' R a a
  | step {a b c : α} : R a b → RTC' R b c → RTC' R a c

namespace RTC'

variable {α : Type u} {R : α → α → Prop}

theorem single' {a b : α} (h : R a b) : RTC' R a b :=
  .step h (.refl' b)

theorem trans' {a b c : α} (h₁ : RTC' R a b) (h₂ : RTC' R b c) : RTC' R a c := by
  induction h₁ with
  | refl' => exact h₂
  | step s _ ih => exact .step s (ih h₂)

theorem tail' {a b c : α} (h₁ : RTC' R a b) (h₂ : R b c) : RTC' R a c :=
  h₁.trans' (.single' h₂)

theorem cases_on' {a b : α} (h : RTC' R a b) :
    (a = b) ∨ (∃ c, R a c ∧ RTC' R c b) := by
  cases h with
  | refl' => left; rfl
  | step s rest => right; exact ⟨_, s, rest⟩

theorem lift {β : Type v} {S : β → β → Prop} (f : α → β)
    (hf : ∀ x y, R x y → S (f x) (f y))
    {a b : α} (h : RTC' R a b) : RTC' S (f a) (f b) := by
  induction h with
  | refl' => exact .refl' _
  | step s _ ih => exact .step (hf _ _ s) ih

end RTC'

/-! ## Symmetric-Reflexive-Transitive Closure -/

inductive STC {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl_stc (a : α) : STC R a a
  | fwd {a b c : α} : R a b → STC R b c → STC R a c
  | bwd {a b c : α} : R b a → STC R b c → STC R a c

namespace STC

variable {α : Type u} {R : α → α → Prop}

theorem trans_stc {a b c : α} (h₁ : STC R a b) (h₂ : STC R b c) : STC R a c := by
  induction h₁ with
  | refl_stc => exact h₂
  | fwd s _ ih => exact .fwd s (ih h₂)
  | bwd s _ ih => exact .bwd s (ih h₂)

theorem symm_stc {a b : α} (h : STC R a b) : STC R b a := by
  induction h with
  | refl_stc => exact .refl_stc _
  | fwd s _ ih => exact ih.trans_stc (.bwd s (.refl_stc _))
  | bwd s _ ih => exact ih.trans_stc (.fwd s (.refl_stc _))

theorem of_rtc {a b : α} (h : RTC' R a b) : STC R a b := by
  induction h with
  | refl' => exact .refl_stc _
  | step s _ ih => exact .fwd s ih

theorem of_rtc_inv {a b : α} (h : RTC' R b a) : STC R a b :=
  (of_rtc h).symm_stc

end STC

/-! ## Abstract Properties -/

section Defs

variable {α : Type u} (R : α → α → Prop)

def Diamond : Prop := ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d
def LocallyConfluent : Prop := ∀ a b c, R a b → R a c → ∃ d, RTC' R b d ∧ RTC' R c d
def Confluent : Prop := ∀ a b c, RTC' R a b → RTC' R a c → ∃ d, RTC' R b d ∧ RTC' R c d
def SemiConfluent : Prop := ∀ a b c, R a b → RTC' R a c → ∃ d, RTC' R b d ∧ RTC' R c d
def ChurchRosser : Prop := ∀ a b, STC R a b → ∃ d, RTC' R a d ∧ RTC' R b d
def IsNF (a : α) : Prop := ∀ b, ¬ R a b

end Defs

/-! ## Diamond → Strip → Confluence -/

section DiamondToConfluence

variable {α : Type u} {R : α → α → Prop}

/-- Diamond implies strip: one step vs multi-step can be closed with multi-step
on one side and a single step on the other. -/
theorem diamond_strip (hD : Diamond R) {a b c : α} (hab : R a b) (hac : RTC' R a c) :
    ∃ d, RTC' R b d ∧ R c d := by
  induction hac generalizing b with
  | refl' => exact ⟨b, .refl' b, hab⟩
  | @step _ x _ hax _ ih =>
    obtain ⟨y, hby, hxy⟩ := hD _ _ _ hab hax
    obtain ⟨d, hyd, hcd⟩ := ih hxy
    exact ⟨d, .step hby hyd, hcd⟩

/-- **Diamond → Confluence**. -/
theorem diamond_imp_confluence (hD : Diamond R) : Confluent R := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl' => exact ⟨c, hac, .refl' c⟩
  | @step _ x _ hax _ ih =>
    obtain ⟨d₀, hxd₀, hcd₀⟩ := diamond_strip hD hax hac
    obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih _ hxd₀
    exact ⟨d₁, hbd₁, (RTC'.single' hcd₀).trans' hd₀d₁⟩

theorem diamond_imp_local (hD : Diamond R) : LocallyConfluent R := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hD a b c hab hac
  exact ⟨d, .single' hbd, .single' hcd⟩

theorem diamond_imp_semi (hD : Diamond R) : SemiConfluent R := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := diamond_strip hD hab hac
  exact ⟨d, hbd, .single' hcd⟩

/-- Confluence implies diamond on RTC' (the multi-step relation has the diamond property). -/
theorem confluent_imp_diamond_rtc (hC : Confluent R) : Diamond (RTC' R) := hC

end DiamondToConfluence

/-! ## Semi-Confluence ↔ Confluence -/

section SemiConfl

variable {α : Type u} {R : α → α → Prop}

theorem confluent_imp_semi (hC : Confluent R) : SemiConfluent R :=
  fun a b c hab hac => hC a b c (.single' hab) hac

theorem semi_imp_confluent (hS : SemiConfluent R) : Confluent R := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl' => exact ⟨c, hac, .refl' c⟩
  | @step _ x _ hax _ ih =>
    obtain ⟨d₀, hxd₀, hcd₀⟩ := hS _ _ c hax hac
    obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih _ hxd₀
    exact ⟨d₁, hbd₁, hcd₀.trans' hd₀d₁⟩

theorem semi_confluence_iff_confluence : SemiConfluent R ↔ Confluent R :=
  ⟨semi_imp_confluent, confluent_imp_semi⟩

/-- Local confluence implies semi-confluence when the relation is terminating. -/
theorem local_confluent_wf_imp_semi
    (wf : WellFounded (fun y x => R x y))
    (lc : LocallyConfluent R) : SemiConfluent R :=
  confluent_imp_semi (newman_lemma_dp wf lc)
where
  newman_lemma_dp (wf : WellFounded (fun y x => R x y))
      (lc : LocallyConfluent R) : Confluent R := by
    intro a
    induction a using wf.induction with
    | _ a ih =>
      intro b c hab hac
      rcases hab.cases_on' with rfl | ⟨a₁, ha₁, h₁b⟩
      · exact ⟨c, hac, .refl' c⟩
      · rcases hac.cases_on' with rfl | ⟨a₂, ha₂, h₂c⟩
        · exact ⟨b, .refl' b, .step ha₁ h₁b⟩
        · obtain ⟨d₀, h₁d₀, h₂d₀⟩ := lc a a₁ a₂ ha₁ ha₂
          obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih a₁ ha₁ b d₀ h₁b h₁d₀
          obtain ⟨d₂, hcd₂, hd₁d₂⟩ := ih a₂ ha₂ c d₁ h₂c (h₂d₀.trans' hd₀d₁)
          exact ⟨d₂, hbd₁.trans' hd₁d₂, hcd₂⟩

end SemiConfl

/-! ## Church-Rosser ↔ Confluence -/

section CR

variable {α : Type u} {R : α → α → Prop}

theorem church_rosser_of_confluence (hC : Confluent R) : ChurchRosser R := by
  intro a b hab
  induction hab with
  | refl_stc a => exact ⟨a, .refl' a, .refl' a⟩
  | fwd hax _ ih =>
    obtain ⟨d, hxd, hbd⟩ := ih
    exact ⟨d, .step hax hxd, hbd⟩
  | bwd hxa _ ih =>
    obtain ⟨d, hxd, hbd⟩ := ih
    obtain ⟨e, hae, hde⟩ := hC _ _ _ (.single' hxa) hxd
    exact ⟨e, hae, hbd.trans' hde⟩

theorem confluence_of_church_rosser (hCR : ChurchRosser R) : Confluent R := by
  intro a b c hab hac
  exact hCR b c ((STC.of_rtc hab).symm_stc.trans_stc (STC.of_rtc hac))

theorem church_rosser_iff_confluence : ChurchRosser R ↔ Confluent R :=
  ⟨confluence_of_church_rosser, church_rosser_of_confluence⟩

/-- Confluence and Church-Rosser are equivalent to semi-confluence. -/
theorem church_rosser_iff_semi : ChurchRosser R ↔ SemiConfluent R :=
  church_rosser_iff_confluence.trans semi_confluence_iff_confluence.symm

end CR

/-! ## Newman's Lemma -/

section Newman

variable {α : Type u} {R : α → α → Prop}

/-- **Newman's Lemma**: termination + local confluence → confluence. -/
theorem newman_lemma_dp
    (wf : WellFounded (fun y x => R x y))
    (lc : LocallyConfluent R) : Confluent R := by
  intro a
  induction a using wf.induction with
  | _ a ih =>
    intro b c hab hac
    rcases hab.cases_on' with rfl | ⟨a₁, ha₁, h₁b⟩
    · exact ⟨c, hac, .refl' c⟩
    · rcases hac.cases_on' with rfl | ⟨a₂, ha₂, h₂c⟩
      · exact ⟨b, .refl' b, .step ha₁ h₁b⟩
      · obtain ⟨d₀, h₁d₀, h₂d₀⟩ := lc a a₁ a₂ ha₁ ha₂
        obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih a₁ ha₁ b d₀ h₁b h₁d₀
        obtain ⟨d₂, hcd₂, hd₁d₂⟩ := ih a₂ ha₂ c d₁ h₂c (h₂d₀.trans' hd₀d₁)
        exact ⟨d₂, hbd₁.trans' hd₁d₂, hcd₂⟩

theorem church_rosser_of_newman
    (wf : WellFounded (fun y x => R x y))
    (lc : LocallyConfluent R) : ChurchRosser R :=
  church_rosser_of_confluence (newman_lemma_dp wf lc)

/-- Newman's lemma combined with Church-Rosser: termination + local confluence
implies STC-equivalence is decidable via joinability. -/
theorem newman_stc_joinable
    (wf : WellFounded (fun y x => R x y))
    (lc : LocallyConfluent R) {a b : α} (h : STC R a b) :
    ∃ d, RTC' R a d ∧ RTC' R b d :=
  church_rosser_of_newman wf lc a b h

end Newman

/-! ## Unique Normal Forms -/

section UniqueNF

variable {α : Type u} {R : α → α → Prop}

theorem confluent_imp_unique_nf (hC : Confluent R)
    {a b c : α} (hab : RTC' R a b) (hac : RTC' R a c)
    (hb : IsNF R b) (hc : IsNF R c) : b = c := by
  obtain ⟨d, hbd, hcd⟩ := hC a b c hab hac
  rcases hbd.cases_on' with rfl | ⟨e, hbe, _⟩
  · rcases hcd.cases_on' with rfl | ⟨e, hce, _⟩
    · rfl
    · exact absurd hce (hc e)
  · exact absurd hbe (hb e)

theorem church_rosser_nf (hCR : ChurchRosser R)
    {a b : α} (hab : STC R a b)
    (ha : IsNF R a) (hb : IsNF R b) : a = b := by
  obtain ⟨d, had, hbd⟩ := hCR a b hab
  rcases had.cases_on' with rfl | ⟨e, hae, _⟩
  · rcases hbd.cases_on' with rfl | ⟨e, hbe, _⟩
    · rfl
    · exact absurd hbe (hb e)
  · exact absurd hae (ha e)

theorem nf_of_confluent_stc_nf (hC : Confluent R)
    {a b : α} (hab : STC R a b) (hb : IsNF R b) :
    RTC' R a b := by
  obtain ⟨d, had, hbd⟩ := church_rosser_of_confluence hC a b hab
  rcases hbd.cases_on' with rfl | ⟨e, hbe, _⟩
  · exact had
  · exact absurd hbe (hb e)

theorem confluent_terminating_exists_unique_nf
    (hC : Confluent R) (wf : WellFounded (fun y x => R x y))
    (a : α) : ∃ b, RTC' R a b ∧ IsNF R b ∧
      ∀ c, RTC' R a c → IsNF R c → c = b := by
  have hnf : ∀ x, ∃ y, RTC' R x y ∧ IsNF R y := by
    intro x; induction x using wf.induction with
    | _ x ih =>
      by_cases h : ∃ y, R x y
      · obtain ⟨y, hxy⟩ := h
        obtain ⟨z, hyz, hz⟩ := ih y hxy
        exact ⟨z, .step hxy hyz, hz⟩
      · exact ⟨x, .refl' x, fun b hxb => h ⟨b, hxb⟩⟩
  obtain ⟨b, hab, hb⟩ := hnf a
  exact ⟨b, hab, hb, fun c hac hc => confluent_imp_unique_nf hC hac hab hc hb⟩

end UniqueNF

/-! ## Joinability Combinators on Path Rw -/

section PathJoinability

variable {A : Type u} {a b c : A}

open Confluence

/-- Prop-level joinability for paths. -/
def PathJoinable (p q : Path a b) : Prop :=
  ∃ s : Path a b, Rw p s ∧ Rw q s

theorem pathJoinable_refl (p : Path a b) : PathJoinable p p :=
  ⟨p, Rw.refl p, Rw.refl p⟩

theorem pathJoinable_symm {p q : Path a b} (h : PathJoinable p q) : PathJoinable q p := by
  obtain ⟨s, hps, hqs⟩ := h; exact ⟨s, hqs, hps⟩

theorem pathJoinable_of_rw {p q : Path a b} (h : Rw p q) : PathJoinable p q :=
  ⟨q, h, Rw.refl q⟩

theorem pathJoinable_of_step {p q : Path a b} (h : Step (A := A) p q) : PathJoinable p q :=
  pathJoinable_of_rw (rw_of_step h)

theorem pathJoinable_of_eq {p q : Path a b} (h : p = q) : PathJoinable p q := by
  subst h; exact pathJoinable_refl p

theorem pathJoinable_toEq {p q : Path a b} (h : PathJoinable p q) :
    p.toEq = q.toEq := by
  obtain ⟨s, hps, hqs⟩ := h
  exact (rw_toEq hps).trans (rw_toEq hqs).symm

/-- Joinability lifts through `symm`. -/
theorem pathJoinable_lift_symm {p q : Path a b}
    (h : PathJoinable p q) :
    PathJoinable (Path.symm p) (Path.symm q) := by
  obtain ⟨s, hps, hqs⟩ := h
  exact ⟨Path.symm s, rw_symm_congr hps, rw_symm_congr hqs⟩

/-- Joinability lifts through `trans` on the left. -/
theorem pathJoinable_lift_trans_left {p₁ p₂ : Path a b} (r : Path b c)
    (h : PathJoinable p₁ p₂) :
    PathJoinable (Path.trans p₁ r) (Path.trans p₂ r) := by
  obtain ⟨s, h₁, h₂⟩ := h
  exact ⟨Path.trans s r, rw_trans_congr_left r h₁, rw_trans_congr_left r h₂⟩

/-- Joinability lifts through `trans` on the right. -/
theorem pathJoinable_lift_trans_right (p : Path a b) {q₁ q₂ : Path b c}
    (h : PathJoinable q₁ q₂) :
    PathJoinable (Path.trans p q₁) (Path.trans p q₂) := by
  obtain ⟨s, h₁, h₂⟩ := h
  exact ⟨Path.trans p s, rw_trans_congr_right p h₁, rw_trans_congr_right p h₂⟩

/-- Joinability lifts through both components of trans. -/
theorem pathJoinable_lift_trans_both {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : PathJoinable p₁ p₂) (hq : PathJoinable q₁ q₂) :
    PathJoinable (Path.trans p₁ q₁) (Path.trans p₂ q₂) := by
  obtain ⟨sp, hp₁, hp₂⟩ := hp
  obtain ⟨sq, hq₁, hq₂⟩ := hq
  exact ⟨Path.trans sp sq,
    rw_trans (rw_trans_congr_left q₁ hp₁) (rw_trans_congr_right sp hq₁),
    rw_trans (rw_trans_congr_left q₂ hp₂) (rw_trans_congr_right sp hq₂)⟩

/-- Converting from `Confluence.Join` to `PathJoinable`. -/
theorem pathJoinable_of_join {p q : Path a b}
    (j : Confluence.Join p q) : PathJoinable p q :=
  ⟨j.meet, j.left, j.right⟩

/-- Converting from `PathJoinable` to `Confluence.Join` (requires Choice). -/
noncomputable def join_of_pathJoinable {p q : Path a b}
    (h : PathJoinable p q) : Confluence.Join p q :=
  h.choose_spec.elim (fun hps hqs => ⟨h.choose, hps, hqs⟩)

/-- `RwEq` implies joinability (given the Join → RwEq direction from Confluence). -/
noncomputable def pathJoinable_of_rweq_join {p q : Path a b}
    (j : Confluence.Join p q) : RwEq p q :=
  j.rweq

end PathJoinability

/-! ## Connections: abstract confluence ↔ path-level confluence -/

section Connection

variable {A : Type u} {a b : A}

/-- The abstract RTC of `Step` embeds into `Rw`. -/
theorem rtc_step_to_rw {p q : Path a b} (h : RTC' (Step (A := A) (a := a) (b := b)) p q) :
    Rw p q := by
  induction h with
  | refl' => exact Rw.refl _
  | @step _ x _ hpx _ ih => exact rw_trans (rw_of_step hpx) ih

/-- Conversely, `Rw` is an RTC of `Step`. -/
theorem rw_to_rtc_step {p q : Path a b} (h : Rw p q) :
    RTC' (Step (A := A) (a := a) (b := b)) p q := by
  induction h with
  | refl => exact .refl' _
  | tail _ s ih => exact RTC'.tail' ih s

/-- `PathJoinable` is a path-level instantiation of the abstract `Confluent`
applied to `Step`. -/
theorem pathJoinable_iff_confluent_instance {p q r : Path a b}
    (hpq : Rw p q) (hpr : Rw p r)
    (hConfl : Confluent (Step (A := A) (a := a) (b := b))) :
    PathJoinable q r := by
  obtain ⟨d, hqd, hrd⟩ := hConfl p q r (rw_to_rtc_step hpq) (rw_to_rtc_step hpr)
  exact ⟨d, rtc_step_to_rw hqd, rtc_step_to_rw hrd⟩

end Connection

/-! ## Additional Consequences -/

section Extra

variable {α : Type u} {R : α → α → Prop}

/-- Confluent relations are weakly Church-Rosser: if a →* b and a →* c,
then ∃ d with b →* d and c →* d. -/
theorem confluent_weakly_cr (hC : Confluent R) :
    ∀ a b c, RTC' R a b → RTC' R a c → ∃ d, RTC' R b d ∧ RTC' R c d := hC

/-- In a confluent relation, STC-equivalence implies joinability. -/
theorem confluent_stc_imp_joinable (hC : Confluent R) {a b : α} (h : STC R a b) :
    ∃ d, RTC' R a d ∧ RTC' R b d :=
  church_rosser_of_confluence hC a b h

/-- Semi-confluence plus termination yields confluence (alternate route). -/
theorem semi_confluent_wf_confluent
    (hS : SemiConfluent R) : Confluent R :=
  semi_imp_confluent hS

/-- If a relation is confluent and a is R-equivalent to b (STC), then they
have the same set of normal forms. -/
theorem confluent_stc_same_nf (hC : Confluent R) {a b : α} (hab : STC R a b)
    {c : α} (hc : IsNF R c) :
    RTC' R a c ↔ RTC' R b c := by
  constructor
  · intro hac
    exact nf_of_confluent_stc_nf hC (hab.symm_stc.trans_stc (STC.of_rtc hac)) hc
  · intro hbc
    exact nf_of_confluent_stc_nf hC (hab.trans_stc (STC.of_rtc hbc)) hc

/-- Diamond property is preserved by restriction to a subset. -/
theorem diamond_restrict {P : α → Prop} (hD : Diamond R)
    (hclosed : ∀ a b, P a → R a b → P b) :
    Diamond (fun a b => R a b ∧ P a ∧ P b) := by
  intro a b c ⟨hab, hpa, hpb⟩ ⟨hac, _, hpc⟩
  obtain ⟨d, hbd, hcd⟩ := hD a b c hab hac
  exact ⟨d, ⟨hbd, hpb, hclosed b d hpb hbd⟩, ⟨hcd, hpc, hclosed c d hpc hcd⟩⟩

/-- Reflexive closure preserves confluence. -/
theorem confluent_refl_closure (hC : Confluent R) :
    Confluent (fun a b => R a b ∨ a = b) := by
  intro a b c hab hac
  have embed : ∀ {x y}, RTC' (fun a b => R a b ∨ a = b) x y → RTC' R x y := by
    intro x y h
    induction h with
    | refl' => exact .refl' _
    | step s _ ih =>
      rcases s with h | rfl
      · exact .step h ih
      · exact ih
  obtain ⟨d, hbd, hcd⟩ := hC a b c (embed hab) (embed hac)
  have lift : ∀ {x y}, RTC' R x y → RTC' (fun a b => R a b ∨ a = b) x y := by
    intro x y h
    induction h with
    | refl' => exact .refl' _
    | step s _ ih => exact .step (.inl s) ih
  exact ⟨d, lift hbd, lift hcd⟩

end Extra

end ComputationalPaths.Path.Rewrite.DiamondProperties
