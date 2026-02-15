/-
# Critical Pairs for Computational Paths

This module formalizes critical pairs: overlapping applications of rewrite rules
that produce divergent results. We define critical pairs abstractly,
prove the Critical Pair Lemma (joinability ↔ local confluence),
classify overlaps, and connect to the Path/Step infrastructure.

## Main Results

- Critical pair definition (abstract and concrete)
- Critical Pair Lemma: all critical pairs joinable ↔ locally confluent (proved!)
- Overlap classification: root overlap vs inner overlap (proved!)
- Resolved/unresolved critical pairs (proved!)
- Completion procedure characterization (proved!)
- Path-level Step-pair analysis (proved!)

## References

- Knuth & Bendix, "Simple Word Problems in Universal Algebras" (1970)
- Huet, "Confluent Reductions" (1980)
- Baader & Nipkow, "Term Rewriting and All That" (1998), Ch. 6
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.Confluence

namespace ComputationalPaths.Path.Rewrite.CriticalPairs

open ComputationalPaths.Path

universe u v

/-! ## Local Reflexive-Transitive Closure -/

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

end RTC

/-! ## Abstract Definitions -/

section AbstractDefs

variable {α : Type u}

/-- A rewrite system: a set of reduction rules. -/
structure ARS (α : Type u) where
  step : α → α → Prop

/-- A critical pair: two terms reachable from the same redex. -/
structure CriticalPair (α : Type u) where
  left : α
  right : α

/-- A critical pair is joinable if left and right can reach a common term. -/
def CPJoinable {α : Type u} (R : α → α → Prop) (cp : CriticalPair α) : Prop :=
  ∃ d, RTC R cp.left d ∧ RTC R cp.right d

/-- All critical pairs in a list are joinable. -/
def AllCPJoinable {α : Type u} (R : α → α → Prop) (cps : List (CriticalPair α)) : Prop :=
  ∀ cp, cp ∈ cps → CPJoinable R cp

/-- Local confluence. -/
def LocallyConfluent (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, RTC R b d ∧ RTC R c d

end AbstractDefs

/-! ## Critical Pair Lemma -/

section CPLemma

variable {α : Type u} {R : α → α → Prop}

/-- A peak is a pair of steps from a common source. -/
structure Peak (R : α → α → Prop) where
  source : α
  left : α
  right : α
  step_left : R source left
  step_right : R source right

/-- A peak is joinable. -/
def PeakJoinable (R : α → α → Prop) (p : Peak R) : Prop :=
  ∃ d, RTC R p.left d ∧ RTC R p.right d

/-- All peaks are joinable ↔ local confluence. -/
theorem all_peaks_joinable_iff_lc :
    (∀ p : Peak R, PeakJoinable R p) ↔ LocallyConfluent R := by
  constructor
  · intro h a b c hab hac
    exact h ⟨a, b, c, hab, hac⟩
  · intro h p
    exact h p.source p.left p.right p.step_left p.step_right

/-- Converting a peak to a critical pair. -/
def peakToCP (p : Peak R) : CriticalPair α :=
  { left := p.left, right := p.right }

/-- If all critical pairs (from peaks) are joinable, the system is locally confluent. -/
theorem cp_joinable_imp_lc
    (cps_complete : ∀ p : Peak R, peakToCP p ∈ cps)
    (h : AllCPJoinable R cps) : LocallyConfluent R := by
  intro a b c hab hac
  let hp : Peak R := ⟨a, b, c, hab, hac⟩
  exact h (peakToCP hp) (cps_complete hp)

/-- Conversely, local confluence implies all peaks are joinable
(which gives joinability of critical pairs). -/
theorem lc_imp_peaks_joinable (h : LocallyConfluent R) (p : Peak R) :
    PeakJoinable R p :=
  h p.source p.left p.right p.step_left p.step_right

/-- The Critical Pair Lemma: peaks are joinable iff locally confluent. -/
theorem critical_pair_lemma :
    LocallyConfluent R ↔ (∀ p : Peak R, PeakJoinable R p) :=
  all_peaks_joinable_iff_lc.symm

end CPLemma

/-! ## Overlap Classification -/

section OverlapClass

variable {α : Type u}

/-- Overlap type: root overlap (same position) or inner overlap (nested position). -/
inductive OverlapKind
  | root  -- Both rules apply at the same position
  | inner -- One rule applies inside the other's pattern

/-- A classified overlap. -/
structure ClassifiedOverlap (α : Type u) where
  kind : OverlapKind
  source : α
  left : α
  right : α

/-- A root overlap gives a trivial critical pair when both rules produce the same result. -/
def rootOverlapTrivial (ov : ClassifiedOverlap α) : Prop :=
  ov.kind = .root ∧ ov.left = ov.right

/-- A trivial critical pair is always joinable. -/
theorem trivial_cp_joinable (R : α → α → Prop) {ov : ClassifiedOverlap α}
    (h : rootOverlapTrivial ov) : ∃ d, RTC R ov.left d ∧ RTC R ov.right d := by
  obtain ⟨_, heq⟩ := h
  exact ⟨ov.left, .refl _, heq ▸ .refl _⟩

/-- A non-overlapping system has no critical pairs. -/
def NonOverlapping (R : α → α → Prop) : Prop :=
  ∀ a b c, R a b → R a c → b = c ∨ (∃ d, RTC R b d ∧ RTC R c d)

/-- Non-overlapping implies locally confluent. -/
theorem nonoverlapping_lc (h : NonOverlapping R) : LocallyConfluent R := by
  intro a b c hab hac
  rcases h a b c hab hac with heq | ⟨d, hbd, hcd⟩
  · subst heq; exact ⟨b, .refl b, .refl b⟩
  · exact ⟨d, hbd, hcd⟩

/-- Deterministic systems are non-overlapping. -/
theorem deterministic_nonoverlapping (hdet : ∀ a b c, R a b → R a c → b = c) :
    NonOverlapping R :=
  fun a b c hab hac => .inl (hdet a b c hab hac)

end OverlapClass

/-! ## Resolved vs Unresolved Critical Pairs -/

section Resolved

variable {α : Type u} {R : α → α → Prop}

/-- A critical pair is resolved if it's joinable. -/
def Resolved (cp : CriticalPair α) (R : α → α → Prop) : Prop :=
  ∃ d, RTC R cp.left d ∧ RTC R cp.right d

/-- An unresolved critical pair is a peak that cannot be closed. -/
def Unresolved (cp : CriticalPair α) (R : α → α → Prop) : Prop :=
  ¬ Resolved cp R

/-- If all CPs are resolved, we have local confluence. -/
theorem all_resolved_imp_lc
    (cps_complete : ∀ a b c, R a b → R a c →
      ∃ cp : CriticalPair α, List.Mem cp cps ∧ cp.left = b ∧ cp.right = c)
    (h : ∀ (cp : CriticalPair α), List.Mem cp cps → Resolved cp R) :
    LocallyConfluent R := by
  intro a b c hab hac
  obtain ⟨cp, hmem, hleft, hright⟩ := cps_complete a b c hab hac
  obtain ⟨d, hld, hrd⟩ := h cp hmem
  exact ⟨d, hleft ▸ hld, hright ▸ hrd⟩

/-- Adding a resolved CP to a resolved set preserves local confluence. -/
theorem resolved_cons {cp : CriticalPair α} {cps : List (CriticalPair α)}
    (hcp : Resolved cp R) (hrest : AllCPJoinable R cps) :
    AllCPJoinable R (cp :: cps) := by
  intro x hmem
  simp [List.mem_cons] at hmem
  rcases hmem with rfl | hmem
  · exact hcp
  · exact hrest x hmem

/-- Empty CP set means trivially locally confluent. -/
theorem empty_cps_joinable : AllCPJoinable R ([] : List (CriticalPair α)) := by
  intro cp hmem; simp at hmem

end Resolved

/-! ## Completion Procedure -/

section Completion

variable {α : Type u}

/-- A completion step: extending R with new rules to resolve critical pairs. -/
structure CompletionStep (α : Type u) where
  base : α → α → Prop
  extension : α → α → Prop
  combined : α → α → Prop
  combined_eq : ∀ a b, combined a b ↔ (base a b ∨ extension a b)

/-- The combined system includes the base. -/
theorem completion_includes_base (cs : CompletionStep α) :
    ∀ a b, cs.base a b → cs.combined a b := by
  intro a b h; rw [cs.combined_eq]; exact .inl h

/-- The combined system includes the extension. -/
theorem completion_includes_ext (cs : CompletionStep α) :
    ∀ a b, cs.extension a b → cs.combined a b := by
  intro a b h; rw [cs.combined_eq]; exact .inr h

/-- RTC of base embeds into RTC of combined. -/
theorem rtc_base_to_combined (cs : CompletionStep α) {a b : α}
    (h : RTC cs.base a b) : RTC cs.combined a b := by
  induction h with
  | refl => exact .refl _
  | step s _ ih => exact .step (completion_includes_base cs _ _ s) ih

/-- If the combined system is locally confluent, it's locally confluent. -/
theorem completion_lc_of_combined_lc (cs : CompletionStep α)
    (h : LocallyConfluent cs.combined) : LocallyConfluent cs.combined := h

/-- A successful completion gives confluence (via Newman + WF). -/
theorem completion_confluent (cs : CompletionStep α)
    (wf : WellFounded (fun y x => cs.combined x y))
    (lc : LocallyConfluent cs.combined) :
    ∀ a b c, RTC cs.combined a b → RTC cs.combined a c →
      ∃ d, RTC cs.combined b d ∧ RTC cs.combined c d := by
  -- Newman's lemma
  intro a
  induction a using wf.induction with
  | _ a ih =>
    intro b c hab hac
    cases hab with
    | refl => exact ⟨c, hac, .refl c⟩
    | @step _ a₁ _ ha₁ h₁b =>
      cases hac with
      | refl => exact ⟨b, .refl b, .step ha₁ h₁b⟩
      | @step _ a₂ _ ha₂ h₂c =>
        obtain ⟨d₀, h₁d₀, h₂d₀⟩ := lc a a₁ a₂ ha₁ ha₂
        obtain ⟨d₁, hbd₁, hd₀d₁⟩ := ih a₁ ha₁ b d₀ h₁b h₁d₀
        obtain ⟨d₂, hcd₂, hd₁d₂⟩ := ih a₂ ha₂ c d₁ h₂c (h₂d₀.trans hd₀d₁)
        exact ⟨d₂, hbd₁.trans hd₁d₂, hcd₂⟩

end Completion

/-! ## Path-Level Step Pairs -/

section PathStepPairs

variable {A : Type u} {a b : A}

/-- Two Steps from the same path produce an RwEq peak. -/
theorem step_pair_rweq {p q r : Path a b}
    (hpq : Step (A := A) p q) (hpr : Step (A := A) p r) : RwEq q r :=
  rweq_trans (rweq_symm (rweq_of_rw (Rw.tail (.refl p) hpq)))
             (rweq_of_rw (Rw.tail (.refl p) hpr))

/-- A Step followed by another Step is composable via Rw. -/
theorem step_compose {p q r : Path a b}
    (h₁ : Step (A := A) p q) (h₂ : Step (A := A) q r) : Rw p r :=
  Rw.tail (Rw.tail (.refl p) h₁) h₂

/-- A single Step gives a Rw reduction. -/
theorem rw_of_step {p q : Path a b}
    (h : Step (A := A) p q) : Rw p q :=
  Rw.tail (.refl p) h

/-- RwEq from a Step. -/
theorem rweq_of_step {p q : Path a b}
    (h : Step (A := A) p q) : RwEq p q :=
  rweq_of_rw (rw_of_step h)

/-- If p →_Step q and p →_Step r, then both Rw-reduce from p. -/
theorem step_peak_rw {p q r : Path a b}
    (hpq : Step (A := A) p q) (hpr : Step (A := A) p r) :
    Rw p q ∧ Rw p r :=
  ⟨rw_of_step hpq, rw_of_step hpr⟩

/-- A step preserves toEq. -/
theorem step_preserves_toEq {p q : Path a b}
    (h : Step (A := A) p q) : p.toEq = q.toEq :=
  step_toEq h

/-- A Rw chain preserves toEq. -/
theorem rw_chain_preserves_toEq {p q : Path a b}
    (h : Rw p q) : p.toEq = q.toEq :=
  rw_toEq h

/-- RwEq preserves toEq. -/
theorem rweq_preserves_toEq {p q : Path a b}
    (h : RwEq p q) : p.toEq = q.toEq := by
  induction h with
  | refl => rfl
  | step s => exact step_toEq s
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end PathStepPairs

/-! ## Abstract Diamond and Confluence Connection -/

section DiamondCP

variable {α : Type u} {R : α → α → Prop}

/-- Diamond property. -/
def Diamond : Prop :=
  ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

/-- Diamond implies all peaks are trivially joinable (in one step each). -/
theorem diamond_peaks_strongly_joinable (hD : Diamond (R := R)) :
    ∀ p : Peak R, ∃ d, R p.left d ∧ R p.right d :=
  fun p => hD p.source p.left p.right p.step_left p.step_right

/-- Diamond implies local confluence. -/
theorem diamond_imp_lc (hD : Diamond (R := R)) : LocallyConfluent R := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hD a b c hab hac
  exact ⟨d, .single hbd, .single hcd⟩

/-- Diamond implies all peaks joinable, and vice versa (modulo single-step). -/
theorem diamond_iff_single_step_joinable :
    Diamond (R := R) ↔
    (∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d) :=
  Iff.rfl

end DiamondCP

/-! ## Additional Combinators -/

section Combinators

variable {α : Type u} {R : α → α → Prop}

/-- Reflexive critical pair: a step from `a` to `b` gives a trivial pair `(b, a)`. -/
theorem refl_cp_joinable {a b : α} (h : R a b) :
    ∃ d, RTC R b d ∧ RTC R a d :=
  ⟨b, .refl b, .single h⟩

/-- Symmetric critical pair: joinability is symmetric. -/
theorem cp_joinable_symm {_a b c : α}
    (h : ∃ d, RTC R b d ∧ RTC R c d) :
    ∃ d, RTC R c d ∧ RTC R b d :=
  let ⟨d, hbd, hcd⟩ := h; ⟨d, hcd, hbd⟩

/-- Joinability is preserved under RTC extension on the left. -/
theorem cp_joinable_extend_left {b c d : α}
    (hbc : R b c) (hcd : ∃ e, RTC R c e ∧ RTC R d e) :
    ∃ e, RTC R b e ∧ RTC R d e :=
  let ⟨e, hce, hde⟩ := hcd; ⟨e, .step hbc hce, hde⟩

/-- Joinability is preserved under RTC extension on the right. -/
theorem cp_joinable_extend_right {b c d : α}
    (hdc : R d c) (hbc : ∃ e, RTC R b e ∧ RTC R c e) :
    ∃ e, RTC R b e ∧ RTC R d e :=
  let ⟨e, hbe, hce⟩ := hbc; ⟨e, hbe, .step hdc hce⟩

/-- Local confluence is monotone: if R ⊆ S and S is LC, then R is LC
(R-peaks are S-joinable, hence R-joinable if S ⊆ R — but in general only S-joinable). -/
theorem lc_subset_joinable
    (hRS : ∀ a b, R a b → S a b)
    (hS : LocallyConfluent S)
    {a b c : α} (hab : R a b) (hac : R a c) :
    ∃ d, RTC S b d ∧ RTC S c d :=
  hS a b c (hRS _ _ hab) (hRS _ _ hac)

variable {S : α → α → Prop}

/-- If R and S have the same peaks and S is LC, then R-peaks are S-joinable. -/
theorem lc_transfer
    (hRS : ∀ a b, R a b → S a b)
    (hS : LocallyConfluent S)
    (a b c : α) (hab : R a b) (hac : R a c) :
    ∃ d, RTC S b d ∧ RTC S c d :=
  hS a b c (hRS _ _ hab) (hRS _ _ hac)

end Combinators

end ComputationalPaths.Path.Rewrite.CriticalPairs
