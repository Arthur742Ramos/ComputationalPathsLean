/-
# Term Rewriting Systems via Structural Computational Paths

This module formalizes term rewriting systems where rewrite sequences
are connected to computational Paths, confluence is path joining,
Church-Rosser is via path construction, and substitution acts
functorially through congrArg.

## Main constructions

- `TRSTerm`: first-order terms (variables, constants, binary application)
- Rewrite rules as path-generating data
- Confluence, Church-Rosser, Newman's lemma
- Substitution as path functoriality (congrArg)
- congrArg-based congruence for application
- Transport of predicates along rewrite paths

## References

- Baader & Nipkow, "Term Rewriting and All That" (1998)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.TermRewritingPaths

open ComputationalPaths.Path

universe u

/-! ## Term Language -/

/-- First-order terms with variables, constants, and binary application. -/
inductive TRSTerm where
  | var (n : Nat) : TRSTerm
  | const (c : Nat) : TRSTerm
  | app (f : TRSTerm) (x : TRSTerm) : TRSTerm
  deriving DecidableEq, Repr

namespace TRSTerm

@[simp] def size : TRSTerm → Nat
  | .var _ => 1
  | .const _ => 1
  | .app f x => f.size + x.size + 1

theorem size_pos (t : TRSTerm) : 0 < t.size := by cases t <;> simp <;> omega

@[simp] def depth : TRSTerm → Nat
  | .var _ => 0
  | .const _ => 0
  | .app f x => max f.depth x.depth + 1

@[simp] def isGround : TRSTerm → Bool
  | .var _ => false
  | .const _ => true
  | .app f x => f.isGround && x.isGround

end TRSTerm

/-! ## Substitutions -/

def TRSSubst := Nat → TRSTerm

def TRSSubst.id : TRSSubst := TRSTerm.var

@[simp] def applySubst (σ : TRSSubst) : TRSTerm → TRSTerm
  | .var n => σ n
  | .const c => .const c
  | .app f x => .app (applySubst σ f) (applySubst σ x)

@[simp] theorem applySubst_id (t : TRSTerm) : applySubst TRSSubst.id t = t := by
  induction t with
  | var n => simp [TRSSubst.id]
  | const c => simp
  | app f x ihf ihx => simp [ihf, ihx]

def TRSSubst.comp (σ τ : TRSSubst) : TRSSubst :=
  fun n => applySubst σ (τ n)

theorem applySubst_comp (σ τ : TRSSubst) (t : TRSTerm) :
    applySubst (TRSSubst.comp σ τ) t = applySubst σ (applySubst τ t) := by
  induction t with
  | var n => simp [TRSSubst.comp]
  | const c => simp
  | app f x ihf ihx => simp [ihf, ihx]

/-! ## Rewrite Rules -/

/-- A rewrite rule. -/
structure RewriteRule where
  lhs : TRSTerm
  rhs : TRSTerm

/-- A term rewriting system. -/
abbrev TRS := List RewriteRule

/-! ## One-step and Multi-step Rewriting -/

inductive OneStep (R : TRS) : TRSTerm → TRSTerm → Prop where
  | root (r : RewriteRule) (σ : TRSSubst) :
      r ∈ R → OneStep R (applySubst σ r.lhs) (applySubst σ r.rhs)
  | appL {f f' x : TRSTerm} :
      OneStep R f f' → OneStep R (.app f x) (.app f' x)
  | appR {f x x' : TRSTerm} :
      OneStep R x x' → OneStep R (.app f x) (.app f x')

inductive MultiStep (R : TRS) : TRSTerm → TRSTerm → Prop where
  | refl (t : TRSTerm) : MultiStep R t t
  | head {a b c : TRSTerm} : OneStep R a b → MultiStep R b c → MultiStep R a c

namespace MultiStep

variable {R : TRS}

theorem single {a b : TRSTerm} (h : OneStep R a b) : MultiStep R a b :=
  .head h (.refl b)

theorem trans {a b c : TRSTerm} (h₁ : MultiStep R a b) (h₂ : MultiStep R b c) :
    MultiStep R a c := by
  induction h₁ with
  | refl => exact h₂
  | head step _ ih => exact .head step (ih h₂)

theorem appL_congr {f f' : TRSTerm} (x : TRSTerm) (h : MultiStep R f f') :
    MultiStep R (.app f x) (.app f' x) := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .head (.appL step) ih

theorem appR_congr (f : TRSTerm) {x x' : TRSTerm} (h : MultiStep R x x') :
    MultiStep R (.app f x) (.app f x') := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .head (.appR step) ih

end MultiStep

/-! ## Confluence and Church-Rosser -/

def IsConfluent (R : TRS) : Prop :=
  ∀ a b c, MultiStep R a b → MultiStep R a c →
    ∃ d, MultiStep R b d ∧ MultiStep R c d

def IsLocallyConfluent (R : TRS) : Prop :=
  ∀ a b c, OneStep R a b → OneStep R a c →
    ∃ d, MultiStep R b d ∧ MultiStep R c d

theorem confluent_implies_local {R : TRS}
    (hc : IsConfluent R) : IsLocallyConfluent R :=
  fun a b c h₁ h₂ => hc a b c (.single h₁) (.single h₂)

/-- Conversion: symmetric closure of rewriting. -/
inductive Conversion (R : TRS) : TRSTerm → TRSTerm → Prop where
  | refl (t : TRSTerm) : Conversion R t t
  | fwd : OneStep R s t → Conversion R s t
  | bwd : OneStep R t s → Conversion R s t
  | trans : Conversion R a b → Conversion R b c → Conversion R a c

theorem Conversion.symm {R : TRS} {s t : TRSTerm}
    (h : Conversion R s t) : Conversion R t s := by
  induction h with
  | refl => exact .refl _
  | fwd h => exact .bwd h
  | bwd h => exact .fwd h
  | trans _ _ ih1 ih2 => exact .trans ih2 ih1

theorem MultiStep.toConversion {R : TRS} {s t : TRSTerm}
    (h : MultiStep R s t) : Conversion R s t := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .trans (.fwd step) ih

/-- Church-Rosser: conversion implies joinability. -/
def ChurchRosser (R : TRS) : Prop :=
  ∀ a b, Conversion R a b → ∃ d, MultiStep R a d ∧ MultiStep R b d

theorem confluent_implies_churchRosser {R : TRS}
    (hc : IsConfluent R) : ChurchRosser R := by
  intro a b hab
  induction hab with
  | refl t => exact ⟨t, .refl t, .refl t⟩
  | fwd h => exact ⟨_, .single h, .refl _⟩
  | bwd h => exact ⟨_, .refl _, .single h⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨d₁, ha_d₁, hb_d₁⟩ := ih1
    obtain ⟨d₂, hb_d₂, hc_d₂⟩ := ih2
    obtain ⟨d₃, hd₁_d₃, hd₂_d₃⟩ := hc _ _ _ hb_d₁ hb_d₂
    exact ⟨d₃, ha_d₁.trans hd₁_d₃, hc_d₂.trans hd₂_d₃⟩

/-! ## Normal Forms -/

def IsNF (R : TRS) (t : TRSTerm) : Prop :=
  ∀ t', ¬ OneStep R t t'

theorem unique_nf {R : TRS} (hc : IsConfluent R)
    {a nf₁ nf₂ : TRSTerm}
    (h₁ : MultiStep R a nf₁) (hnf₁ : IsNF R nf₁)
    (h₂ : MultiStep R a nf₂) (hnf₂ : IsNF R nf₂) :
    nf₁ = nf₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := hc a nf₁ nf₂ h₁ h₂
  cases hd₁ with
  | refl => cases hd₂ with
    | refl => rfl
    | head step _ => exact absurd step (hnf₂ _)
  | head step _ => exact absurd step (hnf₁ _)

/-! ## Termination and Newman's Lemma -/

def IsTerminating (R : TRS) : Prop :=
  WellFounded (fun a b => OneStep R b a)

theorem newman {R : TRS}
    (hwf : IsTerminating R) (hlc : IsLocallyConfluent R) :
    IsConfluent R := by
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
        obtain ⟨d₁, hbd₁, hcd₁⟩ := hlc a _ _ step_ab step_ac
        have ihab := ih _ step_ab
        obtain ⟨d₂, hbd₂, hd₁d₂⟩ := ihab b d₁ rest_ab hbd₁
        have ihac := ih _ step_ac
        obtain ⟨d₃, hd₁d₃, hcd₃⟩ := ihac d₁ c hcd₁ rest_ac
        obtain ⟨d₄, hd₂d₄, hd₃d₄⟩ := ihab d₂ d₃ (hbd₁.trans hd₁d₂) (hbd₁.trans hd₁d₃)
        exact ⟨d₄, hbd₂.trans hd₂d₄, hcd₃.trans hd₃d₄⟩

/-! ## Substitution as Path Functoriality (congrArg) -/

/-- Substitution acts on paths via congrArg. -/
@[simp] def substPathMap (σ : TRSSubst) {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) :
    ComputationalPaths.Path (applySubst σ s) (applySubst σ t) :=
  ComputationalPaths.Path.congrArg (applySubst σ) p

@[simp] theorem substPathMap_refl (σ : TRSSubst) (t : TRSTerm) :
    substPathMap σ (ComputationalPaths.Path.refl t) =
      ComputationalPaths.Path.refl (applySubst σ t) := by
  simp

@[simp] theorem substPathMap_trans (σ : TRSSubst) {s t u : TRSTerm}
    (p : ComputationalPaths.Path s t) (q : ComputationalPaths.Path t u) :
    substPathMap σ (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (substPathMap σ p) (substPathMap σ q) := by
  simp

@[simp] theorem substPathMap_symm (σ : TRSSubst) {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) :
    substPathMap σ (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (substPathMap σ p) := by
  simp

theorem substPathMap_id_toEq {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) :
    (substPathMap TRSSubst.id p).toEq =
      _root_.congrArg (applySubst TRSSubst.id) p.toEq := by
  simp

/-! ## Structural Path Constructions for Substitution -/

/-- Path witnessing identity substitution is a no-op. -/
def idSubstPath (t : TRSTerm) :
    ComputationalPaths.Path (applySubst TRSSubst.id t) t :=
  ComputationalPaths.Path.mk [Step.mk _ _ (applySubst_id t)] (applySubst_id t)

/-- Path witnessing substitution composition. -/
def compSubstPath (σ τ : TRSSubst) (t : TRSTerm) :
    ComputationalPaths.Path
      (applySubst (TRSSubst.comp σ τ) t)
      (applySubst σ (applySubst τ t)) :=
  ComputationalPaths.Path.mk [Step.mk _ _ (applySubst_comp σ τ t)] (applySubst_comp σ τ t)

/-- Symmetry of idSubstPath. -/
def idSubstPathSymm (t : TRSTerm) :
    ComputationalPaths.Path t (applySubst TRSSubst.id t) :=
  ComputationalPaths.Path.symm (idSubstPath t)

/-- Round-trip: idSubstPath ∘ symm is refl (toEq). -/
theorem idSubstPath_roundtrip_toEq (t : TRSTerm) :
    (ComputationalPaths.Path.trans (idSubstPath t) (idSubstPathSymm t)).toEq = rfl := by
  simp

theorem compSubstPath_toEq (σ τ : TRSSubst) (t : TRSTerm) :
    (compSubstPath σ τ t).toEq = applySubst_comp σ τ t := by
  simp

/-! ## Critical Pairs as Path Divergences -/

/-- A critical pair modeled as a path divergence from a common source. -/
structure CriticalPairPaths where
  source : TRSTerm
  left : TRSTerm
  right : TRSTerm
  leftPath : ComputationalPaths.Path source left
  rightPath : ComputationalPaths.Path source right

/-- Joinability of a critical pair. -/
def CriticalPairPaths.Joinable (R : TRS) (cp : CriticalPairPaths) : Prop :=
  ∃ target, MultiStep R cp.left target ∧ MultiStep R cp.right target

/-- Trivial critical pair (both sides same). -/
def trivialCriticalPair (t : TRSTerm) : CriticalPairPaths where
  source := t
  left := t
  right := t
  leftPath := ComputationalPaths.Path.refl t
  rightPath := ComputationalPaths.Path.refl t

theorem trivialCriticalPair_joinable (R : TRS) (t : TRSTerm) :
    (trivialCriticalPair t).Joinable R :=
  ⟨t, .refl t, .refl t⟩

/-! ## Transport of Predicates along Rewrite Paths -/

@[simp] def transportPred (P : TRSTerm → Prop) {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) (h : P s) : P t :=
  ComputationalPaths.Path.transport (D := fun x => P x) p h

@[simp] theorem transportPred_refl (P : TRSTerm → Prop) (t : TRSTerm) (h : P t) :
    transportPred P (ComputationalPaths.Path.refl t) h = h := rfl

@[simp] theorem transportPred_trans (P : TRSTerm → Prop) {s t u : TRSTerm}
    (p : ComputationalPaths.Path s t) (q : ComputationalPaths.Path t u) (h : P s) :
    transportPred P (ComputationalPaths.Path.trans p q) h =
      transportPred P q (transportPred P p h) := by
  simp

/-- Transport along symm inverts transport. -/
theorem transportPred_symm_left (P : TRSTerm → Prop) {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) (h : P s) :
    transportPred P (ComputationalPaths.Path.symm p) (transportPred P p h) = h := by
  simp

/-! ## Ground Term Properties -/

theorem applySubst_ground (σ : TRSSubst) (t : TRSTerm) (hg : t.isGround = true) :
    applySubst σ t = t := by
  induction t with
  | var _ => simp [TRSTerm.isGround] at hg
  | const _ => simp
  | app f x ihf ihx =>
    simp [TRSTerm.isGround] at hg
    simp [ihf hg.1, ihx hg.2]

def groundInvariantPath (σ : TRSSubst) (t : TRSTerm) (hg : t.isGround = true) :
    ComputationalPaths.Path (applySubst σ t) t :=
  ComputationalPaths.Path.mk [Step.mk _ _ (applySubst_ground σ t hg)] (applySubst_ground σ t hg)

/-! ## Empty TRS Properties -/

theorem no_step_empty {a b : TRSTerm} : ¬ OneStep ([] : TRS) a b := by
  intro h
  induction h with
  | root r _ hmem => simp at hmem
  | appL _ ih => exact ih
  | appR _ ih => exact ih

theorem empty_confluent : IsConfluent ([] : TRS) := by
  intro a b c hab hac
  cases hab with
  | refl => exact ⟨c, hac, .refl c⟩
  | head step _ => exact absurd step no_step_empty

theorem empty_churchRosser : ChurchRosser ([] : TRS) :=
  confluent_implies_churchRosser empty_confluent

theorem conv_empty_eq {a b : TRSTerm} (h : Conversion ([] : TRS) a b) :
    a = b := by
  induction h with
  | refl => rfl
  | fwd h => exact absurd h no_step_empty
  | bwd h => exact absurd h no_step_empty
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## congrArg-based Congruence for App -/

/-- Path through app-left via congrArg. -/
def appLeftPath (x : TRSTerm) {f f' : TRSTerm}
    (p : ComputationalPaths.Path f f') :
    ComputationalPaths.Path (TRSTerm.app f x) (TRSTerm.app f' x) :=
  ComputationalPaths.Path.congrArg (fun g => TRSTerm.app g x) p

/-- Path through app-right via congrArg. -/
def appRightPath (f : TRSTerm) {x x' : TRSTerm}
    (p : ComputationalPaths.Path x x') :
    ComputationalPaths.Path (TRSTerm.app f x) (TRSTerm.app f x') :=
  ComputationalPaths.Path.congrArg (fun y => TRSTerm.app f y) p

@[simp] theorem appLeftPath_refl (f x : TRSTerm) :
    appLeftPath x (ComputationalPaths.Path.refl f) =
      ComputationalPaths.Path.refl (TRSTerm.app f x) := by
  simp [appLeftPath]

@[simp] theorem appRightPath_refl (f x : TRSTerm) :
    appRightPath f (ComputationalPaths.Path.refl x) =
      ComputationalPaths.Path.refl (TRSTerm.app f x) := by
  simp [appRightPath]

@[simp] theorem appLeftPath_trans (x : TRSTerm) {f f' f'' : TRSTerm}
    (p : ComputationalPaths.Path f f') (q : ComputationalPaths.Path f' f'') :
    appLeftPath x (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (appLeftPath x p) (appLeftPath x q) := by
  simp [appLeftPath]

@[simp] theorem appRightPath_trans (f : TRSTerm) {x x' x'' : TRSTerm}
    (p : ComputationalPaths.Path x x') (q : ComputationalPaths.Path x' x'') :
    appRightPath f (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (appRightPath f p) (appRightPath f q) := by
  simp [appRightPath]

@[simp] theorem appLeftPath_symm (x : TRSTerm) {f f' : TRSTerm}
    (p : ComputationalPaths.Path f f') :
    appLeftPath x (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (appLeftPath x p) := by
  simp [appLeftPath]

@[simp] theorem appRightPath_symm (f : TRSTerm) {x x' : TRSTerm}
    (p : ComputationalPaths.Path x x') :
    appRightPath f (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (appRightPath f p) := by
  simp [appRightPath]

/-- Composing congrArg paths through both app components. -/
theorem appPath_compose {f f' : TRSTerm} {x x' : TRSTerm}
    (pf : ComputationalPaths.Path f f') (px : ComputationalPaths.Path x x') :
    ComputationalPaths.Path.trans (appLeftPath x pf) (appRightPath f' px) =
      ComputationalPaths.Path.trans
        (ComputationalPaths.Path.congrArg (fun g => TRSTerm.app g x) pf)
        (ComputationalPaths.Path.congrArg (fun y => TRSTerm.app f' y) px) := by
  rfl

/-! ## Step-Path Coherence -/

/-- A Step on TRSTerm from an equality. -/
def stepOfEq (s t : TRSTerm) (h : s = t) : ComputationalPaths.Step TRSTerm :=
  { src := s, tgt := t, proof := h }

theorem stepOfEq_symm_symm (s t : TRSTerm) (h : s = t) :
    (stepOfEq s t h).symm.symm = stepOfEq s t h := by
  simp [stepOfEq]

theorem path_trans_steps {s t u : TRSTerm}
    (p : ComputationalPaths.Path s t) (q : ComputationalPaths.Path t u) :
    (ComputationalPaths.Path.trans p q).steps = p.steps ++ q.steps := rfl

theorem path_symm_steps {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) :
    (ComputationalPaths.Path.symm p).steps =
      p.steps.reverse.map ComputationalPaths.Step.symm := rfl

/-! ## Variables and Constants as Normal Forms -/

theorem var_nf {R : TRS} (n : Nat)
    (h : ∀ r ∈ R, ∀ σ, applySubst σ r.lhs ≠ .var n) :
    IsNF R (.var n) := by
  intro t' ht
  have : ∃ s, TRSTerm.var n = s ∧ OneStep R s t' := ⟨_, rfl, ht⟩
  obtain ⟨s, hs, hstep⟩ := this
  induction hstep with
  | root r σ hmem => exact h r hmem σ hs.symm
  | appL _ _ => cases hs
  | appR _ _ => cases hs

theorem const_nf {R : TRS} (c : Nat)
    (h : ∀ r ∈ R, ∀ σ, applySubst σ r.lhs ≠ .const c) :
    IsNF R (.const c) := by
  intro t' ht
  have : ∃ s, TRSTerm.const c = s ∧ OneStep R s t' := ⟨_, rfl, ht⟩
  obtain ⟨s, hs, hstep⟩ := this
  induction hstep with
  | root r σ hmem => exact h r hmem σ hs.symm
  | appL _ _ => cases hs
  | appR _ _ => cases hs

/-! ## Diamond Property implies Confluence -/

def DiamondProperty (R : TRS) : Prop :=
  ∀ a b c, OneStep R a b → OneStep R a c →
    ∃ d, OneStep R b d ∧ OneStep R c d

theorem diamond_implies_local_confluent {R : TRS}
    (hd : DiamondProperty R) : IsLocallyConfluent R :=
  fun a b c h₁ h₂ =>
    let ⟨d, hbd, hcd⟩ := hd a b c h₁ h₂
    ⟨d, .single hbd, .single hcd⟩

/-! ## Reflexive Path on Terms -/

def termRefl (t : TRSTerm) : ComputationalPaths.Path t t :=
  ComputationalPaths.Path.refl t

@[simp] theorem termRefl_toEq (t : TRSTerm) : (termRefl t).toEq = rfl := by
  simp

@[simp] theorem termRefl_steps (t : TRSTerm) : (termRefl t).steps = [] := by
  simp [termRefl]

/-! ## Substitution Path Composition -/

/-- Composing substPathMaps corresponds to composed substitution path. -/
theorem substPathMap_comp_toEq (σ τ : TRSSubst) {s t : TRSTerm}
    (p : ComputationalPaths.Path s t) :
    (substPathMap σ (substPathMap τ p)).toEq =
      _root_.congrArg (applySubst σ) (_root_.congrArg (applySubst τ) p.toEq) := by
  simp

end ComputationalPaths.Path.Rewriting.TermRewritingPaths
