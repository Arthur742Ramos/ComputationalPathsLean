/-
# First-Order Term Rewriting via Computational Paths

This module formalizes first-order term rewriting systems (TRS) and connects
them to computational paths.  Terms are built from variables and function
symbols applied to fixed-arity arguments.

## Main Results

- `Term` type (binary for simplicity, avoids nested inductive)
- Substitution and its algebraic properties
- One-step and multi-step rewriting
- Substitution as path transport (congrArg)
- Critical pairs and joinability
- Confluence, local confluence, Newman's lemma
- Normal form uniqueness

## References

- Baader & Nipkow, "Term Rewriting and All That" (1998)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewrite.TermRewriting

universe u

/-! ## First-Order Terms (Binary)

We use a simplified term language: constants, variables, and binary application.
This avoids nested inductive issues while retaining the essential structure. -/

/-- First-order terms: variables, constants, and binary application. -/
inductive Term where
  | var (n : Nat) : Term
  | const (c : Nat) : Term
  | app (f : Term) (x : Term) : Term
  deriving DecidableEq, Repr

namespace Term

/-- Size of a term. -/
@[simp] noncomputable def size : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .app f x => f.size + x.size + 1

theorem size_pos (t : Term) : 0 < t.size := by
  cases t <;> simp <;> omega

/-- Depth of a term. -/
@[simp] noncomputable def depth : Term → Nat
  | .var _ => 0
  | .const _ => 0
  | .app f x => max f.depth x.depth + 1

/-- Count variable occurrences. -/
@[simp] noncomputable def varCount : Term → Nat
  | .var _ => 1
  | .const _ => 0
  | .app f x => f.varCount + x.varCount

/-- Check if a variable occurs in a term. -/
@[simp] noncomputable def hasVar (n : Nat) : Term → Bool
  | .var m => n == m
  | .const _ => false
  | .app f x => f.hasVar n || x.hasVar n

/-- A term is ground if it has no variables. -/
@[simp] noncomputable def isGround : Term → Bool
  | .var _ => false
  | .const _ => true
  | .app f x => f.isGround && x.isGround

end Term

/-! ## Substitutions -/

/-- A substitution maps variables to terms. -/
noncomputable def Subst := Nat → Term

/-- The identity substitution. -/
noncomputable def Subst.id : Subst := Term.var

/-- Apply a substitution to a term. -/
@[simp] noncomputable def applySubst (σ : Subst) : Term → Term
  | .var n => σ n
  | .const c => .const c
  | .app f x => .app (applySubst σ f) (applySubst σ x)

/-- Identity substitution is the identity function. -/
@[simp] theorem applySubst_id (t : Term) : applySubst Subst.id t = t := by
  induction t with
  | var n => simp [Subst.id]
  | const c => simp
  | app f x ihf ihx => simp [ihf, ihx]

/-- Composition of substitutions. -/
noncomputable def Subst.comp (σ τ : Subst) : Subst :=
  fun n => applySubst σ (τ n)

/-- Applying composed substitutions = applying sequentially. -/
theorem applySubst_comp (σ τ : Subst) (t : Term) :
    applySubst (Subst.comp σ τ) t = applySubst σ (applySubst τ t) := by
  induction t with
  | var n => simp [Subst.comp]
  | const c => simp
  | app f x ihf ihx => simp [ihf, ihx]

/-- Identity is left identity for composition. -/
theorem Subst.comp_id_left (σ : Subst) (n : Nat) :
    Subst.comp Subst.id σ n = σ n := by
  simp [Subst.comp]

/-- Identity is right identity for composition. -/
theorem Subst.comp_id_right (σ : Subst) (n : Nat) :
    Subst.comp σ Subst.id n = σ n := by
  simp [Subst.comp, Subst.id]

/-- Composition is associative. -/
theorem Subst.comp_assoc (σ τ ρ : Subst) (n : Nat) :
    Subst.comp (Subst.comp σ τ) ρ n = Subst.comp σ (Subst.comp τ ρ) n := by
  simp [Subst.comp, applySubst_comp]

/-! ## Rewrite Rules and Rewriting -/

/-- A rewrite rule. -/
structure TRule where
  lhs : Term
  rhs : Term

/-- One-step rewriting: apply a rule with a matching substitution. -/
inductive TStep (rules : List TRule) : Term → Term → Prop where
  | root (r : TRule) (σ : Subst) :
      r ∈ rules →
      TStep rules (applySubst σ r.lhs) (applySubst σ r.rhs)
  | appL {f f' x : Term} :
      TStep rules f f' → TStep rules (.app f x) (.app f' x)
  | appR {f x x' : Term} :
      TStep rules x x' → TStep rules (.app f x) (.app f x')

/-- Multi-step rewriting. -/
inductive TRtc (rules : List TRule) : Term → Term → Prop where
  | refl (t : Term) : TRtc rules t t
  | head {a b c : Term} : TStep rules a b → TRtc rules b c → TRtc rules a c

namespace TRtc

variable {rules : List TRule}

theorem single {a b : Term} (h : TStep rules a b) : TRtc rules a b :=
  .head h (.refl b)

theorem trans {a b c : Term} (h₁ : TRtc rules a b) (h₂ : TRtc rules b c) :
    TRtc rules a c := by
  induction h₁ with
  | refl => exact h₂
  | head step _ ih => exact .head step (ih h₂)

/-- AppL congruence for multi-step. -/
theorem appL_congr {f f' : Term} (x : Term) (h : TRtc rules f f') :
    TRtc rules (.app f x) (.app f' x) := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .head (.appL step) ih

/-- AppR congruence for multi-step. -/
theorem appR_congr (f : Term) {x x' : Term} (h : TRtc rules x x') :
    TRtc rules (.app f x) (.app f x') := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .head (.appR step) ih

end TRtc

/-! ## Critical Pairs -/

/-- A critical pair. -/
structure CriticalPair where
  left : Term
  right : Term

/-- Joinability of a critical pair. -/
noncomputable def CriticalPair.Joinable (rules : List TRule) (cp : CriticalPair) : Prop :=
  ∃ t, TRtc rules cp.left t ∧ TRtc rules cp.right t

/-! ## Confluence -/

/-- Confluence. -/
noncomputable def IsConfluent (rules : List TRule) : Prop :=
  ∀ a b c, TRtc rules a b → TRtc rules a c →
    ∃ d, TRtc rules b d ∧ TRtc rules c d

/-- Local confluence (weak Church-Rosser). -/
noncomputable def IsLocallyConfluent (rules : List TRule) : Prop :=
  ∀ a b c, TStep rules a b → TStep rules a c →
    ∃ d, TRtc rules b d ∧ TRtc rules c d

/-- Confluence implies local confluence. -/
theorem confluent_implies_lc {rules : List TRule}
    (hc : IsConfluent rules) : IsLocallyConfluent rules :=
  fun a b c h₁ h₂ => hc a b c (.single h₁) (.single h₂)

/-! ## Normal Forms -/

/-- A term is in normal form. -/
noncomputable def IsNF (rules : List TRule) (t : Term) : Prop :=
  ∀ t', ¬ TStep rules t t'

/-- Normal forms are unique in confluent systems. -/
theorem unique_nf {rules : List TRule} (hc : IsConfluent rules)
    {a nf₁ nf₂ : Term}
    (h₁ : TRtc rules a nf₁) (hnf₁ : IsNF rules nf₁)
    (h₂ : TRtc rules a nf₂) (hnf₂ : IsNF rules nf₂) :
    nf₁ = nf₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := hc a nf₁ nf₂ h₁ h₂
  cases hd₁ with
  | refl => cases hd₂ with
    | refl => rfl
    | head step _ => exact absurd step (hnf₂ _)
  | head step _ => exact absurd step (hnf₁ _)

/-- Variables are normal forms if no rule has a variable as a matched LHS instance. -/
theorem var_nf {rules : List TRule} (n : Nat)
    (h : ∀ r ∈ rules, ∀ σ, applySubst σ r.lhs ≠ .var n) :
    IsNF rules (.var n) := by
  intro t' ht
  have : ∃ s, .var n = s ∧ TStep rules s t' := ⟨_, rfl, ht⟩
  obtain ⟨s, hs, hstep⟩ := this
  induction hstep with
  | root r σ hmem => exact h r hmem σ hs.symm
  | appL _ _ => cases hs
  | appR _ _ => cases hs

/-- Constants are normal forms if no rule matches. -/
theorem const_nf {rules : List TRule} (c : Nat)
    (h : ∀ r ∈ rules, ∀ σ, applySubst σ r.lhs ≠ .const c) :
    IsNF rules (.const c) := by
  intro t' ht
  have : ∃ s, .const c = s ∧ TStep rules s t' := ⟨_, rfl, ht⟩
  obtain ⟨s, hs, hstep⟩ := this
  induction hstep with
  | root r σ hmem => exact h r hmem σ hs.symm
  | appL _ _ => cases hs
  | appR _ _ => cases hs

/-! ## Termination -/

/-- Terminating (strongly normalizing). -/
noncomputable def IsTerminating (rules : List TRule) : Prop :=
  WellFounded (fun a b => TStep rules b a)

/-- Newman's Lemma: WF + WCR → CR. -/
theorem newman {rules : List TRule}
    (hwf : IsTerminating rules)
    (hlc : IsLocallyConfluent rules) :
    IsConfluent rules := by
  intro a
  induction a using hwf.induction with
  | _ a ih =>
    intro b c hab hac
    cases hab with
    | refl => exact ⟨c, hac, .refl c⟩
    | head step_ab rest_ab =>
      cases hac with
      | refl => exact ⟨b, .refl b, .head step_ab rest_ab⟩
      | head step_ac rest_ac =>
        -- a →₁ ab_tgt, a →₁ ac_tgt
        -- Local confluence gives d₁ with ab_tgt →* d₁, ac_tgt →* d₁
        obtain ⟨d₁, hbd₁, hcd₁⟩ := hlc a _ _ step_ab step_ac
        -- IH at ab_tgt: join (rest_ab target = b) and d₁
        have ihab := ih _ step_ab
        obtain ⟨d₂, hbd₂, hd₁d₂⟩ := ihab b d₁ rest_ab hbd₁
        -- IH at ac_tgt: join d₁ and (rest_ac target = c)
        have ihac := ih _ step_ac
        obtain ⟨d₃, hd₁d₃, hcd₃⟩ := ihac d₁ c hcd₁ rest_ac
        -- Now d₁ →* d₂ and d₁ →* d₃, join them using IH at ab_tgt
        -- ab_tgt →* d₁ →* d₂ and ab_tgt →* d₁ →* d₃
        obtain ⟨d₄, hd₂d₄, hd₃d₄⟩ := ihab d₂ d₃ (hbd₁.trans hd₁d₂) (hbd₁.trans hd₁d₃)
        exact ⟨d₄, hbd₂.trans hd₂d₄, hcd₃.trans hd₃d₄⟩

/-! ## Substitution as Path Transport -/

/-- Substitution maps paths to paths via congrArg. -/
noncomputable def substPath (σ : Subst) {s t : Term}
    (p : ComputationalPaths.Path s t) :
    ComputationalPaths.Path (applySubst σ s) (applySubst σ t) :=
  ComputationalPaths.Path.congrArg (applySubst σ) p

/-- substPath preserves reflexivity. -/
@[simp] theorem substPath_refl (σ : Subst) (t : Term) :
    substPath σ (ComputationalPaths.Path.refl t) =
      ComputationalPaths.Path.refl (applySubst σ t) := by
  simp [substPath]

/-- substPath preserves transitivity. -/
@[simp] theorem substPath_trans (σ : Subst) {s t u : Term}
    (p : ComputationalPaths.Path s t) (q : ComputationalPaths.Path t u) :
    substPath σ (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (substPath σ p) (substPath σ q) := by
  simp [substPath]

/-- substPath preserves symmetry. -/
@[simp] theorem substPath_symm (σ : Subst) {s t : Term}
    (p : ComputationalPaths.Path s t) :
    substPath σ (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (substPath σ p) := by
  simp [substPath]

/-- substPath composes correctly. -/
theorem substPath_comp (σ τ : Subst) {s t : Term}
    (p : ComputationalPaths.Path s t) :
    substPath σ (substPath τ p) =
      ComputationalPaths.Path.congrArg (applySubst σ)
        (ComputationalPaths.Path.congrArg (applySubst τ) p) := by
  simp [substPath]

/-- Identity substitution path is identity. -/
theorem substPath_id {s t : Term}
    (p : ComputationalPaths.Path s t) :
    substPath Subst.id p =
      ComputationalPaths.Path.congrArg (applySubst Subst.id) p := by
  rfl

/-- Identity substitution yields same toEq (up to congrArg). -/
theorem substPath_id_toEq {s t : Term}
    (p : ComputationalPaths.Path s t) :
    (substPath Subst.id p).toEq =
      _root_.congrArg (applySubst Subst.id) p.toEq := by
  simp

/-! ## Conversion -/

/-- Conversion: symmetric closure of rewriting. -/
inductive TConv (rules : List TRule) : Term → Term → Prop where
  | refl (t : Term) : TConv rules t t
  | fwd : TStep rules s t → TConv rules s t
  | bwd : TStep rules t s → TConv rules s t
  | trans : TConv rules a b → TConv rules b c → TConv rules a c

theorem TConv.symm {rules : List TRule} {s t : Term}
    (h : TConv rules s t) : TConv rules t s := by
  induction h with
  | refl => exact .refl _
  | fwd h => exact .bwd h
  | bwd h => exact .fwd h
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem TRtc.toConv {rules : List TRule} {s t : Term}
    (h : TRtc rules s t) : TConv rules s t := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .trans (.fwd step) ih

/-! ## Empty System -/

theorem no_step_empty {a b : Term} : ¬ TStep ([] : List TRule) a b := by
  intro h
  induction h with
  | root r _ hmem => simp at hmem
  | appL _ ih => exact ih
  | appR _ ih => exact ih

theorem empty_confluent : IsConfluent ([] : List TRule) := by
  intro a b c hab hac
  cases hab with
  | refl => exact ⟨c, hac, .refl c⟩
  | head step _ => exact absurd step no_step_empty

/-- In the empty system, conversion is equality. -/
theorem conv_empty_eq {a b : Term} (h : TConv ([] : List TRule) a b) :
    a = b := by
  induction h with
  | refl => rfl
  | fwd h => exact absurd h no_step_empty
  | bwd h => exact absurd h no_step_empty
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Ground Terms -/

/-- Substitution on ground terms is identity. -/
theorem applySubst_ground (σ : Subst) (t : Term) (hg : t.isGround = true) :
    applySubst σ t = t := by
  induction t with
  | var _ => simp [Term.isGround] at hg
  | const _ => simp
  | app f x ihf ihx =>
    simp [Term.isGround] at hg
    simp [ihf hg.1, ihx hg.2]

/-- Ground terms have zero variable count. -/
theorem ground_varCount_zero (t : Term) (hg : t.isGround = true) :
    t.varCount = 0 := by
  induction t with
  | var _ => simp [Term.isGround] at hg
  | const _ => simp
  | app f x ihf ihx =>
    simp [Term.isGround] at hg
    simp [ihf hg.1, ihx hg.2]

end ComputationalPaths.Path.Rewrite.TermRewriting
