/-
# Type-Valued Rewriting Framework

This module provides a Type-valued abstract rewriting system framework,
parallel to the Metatheory library but preserving computational content
in Type rather than collapsing to Prop.

## Purpose

This module developed a type-valued confluence pipeline, once aimed at
eliminating `to_canonical`. Contractibility₃ is now derived directly from proof
irrelevance of `RwEq`, but the typed framework remains useful for future work.

## Key Definitions

- `TStar r p q`: Type-valued reflexive-transitive closure
- `TJoinable r p q`: Type-valued joinability with explicit witnesses
- `TDiamond r`: Type-valued diamond property with 3-cells
- `TConfluent r`: Type-valued confluence with 3-cells

## References

- Metatheory library: https://github.com/Arthur742Ramos/Metatheory
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Terese, "Term Rewriting Systems" (2003)
-/

import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.Rewrite.ConfluenceConstructive
import ComputationalPaths.Path.Rewrite.PathExpr

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid
namespace TypedRewriting

universe u v

variable {A : Type u}

/-! ## Type-Valued Reflexive-Transitive Closure

Unlike Prop-valued `Star` in Metatheory, `TStar` preserves the structure
of the derivation as Type-valued data.
-/

/-- Type-valued reflexive-transitive closure.
    The relation `r` maps pairs of paths to `Type v` so that witnesses are
    computationally relevant. -/
inductive TStar {a b : A} (r : Path a b → Path a b → Type v) :
    Path a b → Path a b → Type (max u v) where
  | refl (p : Path a b) : TStar r p p
  | tail {p q s : Path a b} : TStar r p q → r q s → TStar r p s

namespace TStar

/-- Single step implies multi-step -/
noncomputable def single {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} (h : r p q) : TStar r p q :=
  TStar.tail (TStar.refl p) h

/-- Multi-step is transitive -/
noncomputable def trans {a b : A} {r : Path a b → Path a b → Type v}
    {p q s : Path a b} (h1 : TStar r p q) (h2 : TStar r q s) : TStar r p s :=
  match h2 with
  | .refl _ => h1
  | .tail h2' hstep => .tail (trans h1 h2') hstep

/-- Prepend a single step -/
noncomputable def head {a b : A} {r : Path a b → Path a b → Type v}
    {p q s : Path a b} (hpq : r p q) (hqs : TStar r q s) : TStar r p s :=
  trans (single hpq) hqs

/-- Length of a TStar derivation -/
noncomputable def length {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} : TStar r p q → Nat
  | .refl _ => 0
  | .tail h _ => h.length + 1

end TStar

/-! ## Type-Valued Joinability

Two paths are joinable if they can both reach a common path.
We preserve the witnesses (the common path and the derivations to it).
-/

/-- Type-valued joinability: paths can reach a common target. -/
structure TJoinable {a b : A} (r : Path a b → Path a b → Type v)
    (p q : Path a b) : Type (max u v) where
  /-- The common path both can reach -/
  common : Path a b
  /-- Derivation from p to common -/
  left : TStar r p common
  /-- Derivation from q to common -/
  right : TStar r q common

namespace TJoinable

/-- Joinability is reflexive -/
noncomputable def refl {a b : A} {r : Path a b → Path a b → Type v} (p : Path a b) :
    TJoinable r p p :=
  ⟨p, .refl p, .refl p⟩

/-- Joinability is symmetric -/
noncomputable def symm {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} (j : TJoinable r p q) : TJoinable r q p :=
  ⟨j.common, j.right, j.left⟩

/-- From a TStar derivation, paths are joinable -/
noncomputable def of_star {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} (h : TStar r p q) : TJoinable r p q :=
  ⟨q, h, .refl q⟩

end TJoinable

/-! ## Type-Valued Diamond Property

The diamond property says single-step divergences can be closed in one step.
For 3-cells, we additionally require the two closing paths to be 3-equivalent.
-/

/-- Diamond property with 3-cell witness.
    When two single steps diverge, they can close to a common point,
    and the two derivations are 3-equivalent. -/
structure TDiamond {a b : A} (r : Path a b → Path a b → Type v) :
    Type (max (u + 1) v) where
  /-- Embed an `r`-witness as a `Step` so we can form 2-cells (`Derivation₂`)
  and state 3-cell coherences. -/
  step_of : ∀ {p q : Path a b}, r p q → Step p q
  /-- Given two steps from the same source, there exists a common target
      with closing steps. -/
  close : ∀ {p q₁ q₂ : Path a b},
    r p q₁ → r p q₂ →
    Σ (s : Path a b), (r q₁ s) × (r q₂ s)
  /-- The 3-cell witnessing the diamond commutes -/
  coherence : ∀ {p q₁ q₂ : Path a b}
    (h₁ : r p q₁) (h₂ : r p q₂),
    let ⟨_, h₃, h₄⟩ := close h₁ h₂
    Derivation₃
      (.vcomp (.step (step_of h₁)) (.step (step_of h₃)))
      (.vcomp (.step (step_of h₂)) (.step (step_of h₄)))

/-! ## Type-Valued Local Confluence

Local confluence allows multi-step closing of single-step divergences.
-/

/-- Type-valued local confluence with 3-cells. -/
structure TLocalConfluent {a b : A} (r : Path a b → Path a b → Type v) :
    Type (max (u + 1) v) where
  /-- Single-step divergences can be closed with multi-step -/
  close : ∀ {p q₁ q₂ : Path a b},
    r p q₁ → r p q₂ →
    TJoinable r q₁ q₂

/-! ## Type-Valued Confluence

Full confluence: multi-step divergences can be closed.
-/

/-- Type-valued confluence with joining witnesses. -/
structure TConfluent {a b : A} (r : Path a b → Path a b → Type v) :
    Type (max (u + 1) v) where
  /-- Multi-step divergences can be closed -/
  close : ∀ {p q₁ q₂ : Path a b},
    TStar r p q₁ → TStar r p q₂ →
    TJoinable r q₁ q₂

/-! ## Type-Valued Semi-Confluence

Semi-confluence is intermediate between local and full confluence.
-/

/-- Type-valued semi-confluence. -/
structure TSemiConfluent {a b : A} (r : Path a b → Path a b → Type v) :
    Type (max (u + 1) v) where
  /-- Single step vs multi-step can be closed -/
  close : ∀ {p q₁ q₂ : Path a b},
    r p q₁ → TStar r p q₂ →
    TJoinable r q₁ q₂

/-! ## Key Lemmas

These mirror the Metatheory library but preserve Type structure.
-/

section KeyLemmas

variable {a b : A} {r : Path a b → Path a b → Type v}

/-- Diamond implies local confluence -/
noncomputable def localConfluent_of_diamond (hd : TDiamond (a := a) (b := b) r) :
    TLocalConfluent r where
  close := fun h₁ h₂ =>
    let ⟨s, h₃, h₄⟩ := hd.close h₁ h₂
    ⟨s, .single h₃, .single h₄⟩

/-- Semi-confluence implies local confluence -/
noncomputable def localConfluent_of_semiConfluent
    (hsc : TSemiConfluent (a := a) (b := b) r) :
    TLocalConfluent r where
  close := fun h₁ h₂ => hsc.close h₁ (.single h₂)

/-- Confluence implies semi-confluence -/
noncomputable def semiConfluent_of_confluent
    (hc : TConfluent (a := a) (b := b) r) :
    TSemiConfluent r where
  close := fun h₁ h₂ => hc.close (.single h₁) h₂

/-- Confluence implies local confluence -/
noncomputable def localConfluent_of_confluent
    (hc : TConfluent (a := a) (b := b) r) :
    TLocalConfluent r :=
  localConfluent_of_semiConfluent (semiConfluent_of_confluent hc)

end KeyLemmas

/-! ## Strip Lemma (Type-Valued)

The strip lemma is key to proving diamond → confluence.
Given diamond, a single step can be pushed through a multi-step.
-/

section StripLemma

variable {a b : A} {r : Path a b → Path a b → Type v}

/-- Strip lemma helper: push a step through a multi-step,
    yielding multi-step + single step. -/
noncomputable def strip_single (hd : TDiamond (a := a) (b := b) r)
    {p q₁ q₂ : Path a b}
    (h₁ : r p q₁)
    (h₂ : TStar r p q₂) :
    Σ (s : Path a b), TStar r q₁ s × r q₂ s :=
  match h₂ with
  | .refl _ => ⟨q₁, .refl q₁, h₁⟩
  | .tail hstar hstep =>
    let ⟨_, hs', hq₂'s'⟩ := strip_single hd h₁ hstar
    let ⟨s, hs's, hq₂s⟩ := hd.close hq₂'s' hstep
    ⟨s, TStar.tail hs' hs's, hq₂s⟩

/-- Full strip lemma: push a step through a multi-step, get two multi-steps. -/
noncomputable def strip (hd : TDiamond (a := a) (b := b) r)
    {p q₁ q₂ : Path a b}
    (h₁ : r p q₁)
    (h₂ : TStar r p q₂) :
    Σ (s : Path a b), TStar r q₁ s × TStar r q₂ s :=
  match h₂ with
  | .refl _ => ⟨q₁, .refl q₁, .single h₁⟩
  | .tail hstar hstep =>
    let ⟨_, hs', hq₂'s'⟩ := strip hd h₁ hstar
    let ⟨s, hq₂s, hs's⟩ := strip_single hd hstep hq₂'s'
    ⟨s, TStar.tail hs' hs's, hq₂s⟩

end StripLemma

/-! ## Diamond → Confluence (Type-Valued)

The main theorem: diamond property implies confluence.
-/

section DiamondConfluence

variable {a b : A} {r : Path a b → Path a b → Type v}

/-- Diamond implies semi-confluence -/
noncomputable def semiConfluent_of_diamond
    (hd : TDiamond (a := a) (b := b) r) :
    TSemiConfluent r where
  close := fun h₁ h₂ =>
    let ⟨s, hs₁, hs₂⟩ := strip hd h₁ h₂
    ⟨s, hs₁, hs₂⟩

/-- Semi-confluence implies confluence (key lemma!)

    We proceed by structural induction on the first multi-step derivation. -/
noncomputable def confluent_of_semiConfluent
    (hsc : TSemiConfluent (a := a) (b := b) r) :
    TConfluent r where
  close := fun {_ _ _} h₁ h₂ => auxClose hsc h₁ h₂
where
  /-- Auxiliary: structural induction on first derivation. -/
  auxClose (hsc : TSemiConfluent (a := a) (b := b) r)
      {p q₁ q₂ : Path a b}
      (h₁ : TStar r p q₁) (h₂ : TStar r p q₂) : TJoinable r q₁ q₂ :=
    match h₁ with
    | .refl _ => TJoinable.of_star h₂
    | .tail hstar hstep =>
      let ⟨_mid, hq₂mid, hmidmid⟩ := auxClose hsc hstar h₂
      let ⟨t, hq₁t, hmidt⟩ := hsc.close hstep hq₂mid
      ⟨t, hq₁t, TStar.trans hmidmid hmidt⟩

/-- Diamond implies confluence -/
noncomputable def confluent_of_diamond
    (hd : TDiamond (a := a) (b := b) r) :
    TConfluent r :=
  confluent_of_semiConfluent (semiConfluent_of_diamond hd)

end DiamondConfluence

/-! ## Termination and Newman's Lemma

Newman's lemma: termination + local confluence → confluence.
-/

section Newman

variable {a b : A} {r : Path a b → Path a b → Type v}

/-- Type-valued transitive closure (one or more steps). -/
inductive TPlus {a b : A} (r : Path a b → Path a b → Type v) :
    Path a b → Path a b → Type (max u v) where
  | single {p q : Path a b} : r p q → TPlus r p q
  | tail {p q s : Path a b} : TPlus r p q → r q s → TPlus r p s

/-- TPlus implies TStar -/
noncomputable def TStar.of_plus {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} (h : TPlus r p q) : TStar r p q :=
  match h with
  | .single h => .single h
  | .tail h' hstep => .tail (TStar.of_plus h') hstep

/-- Extend a TPlus by a TStar tail -/
noncomputable def TPlus.trans_star {a b : A} {r : Path a b → Path a b → Type v}
    {p q s : Path a b} (hpq : TPlus r p q) (hqs : TStar r q s) : TPlus r p s :=
  match hqs with
  | .refl _ => hpq
  | .tail hqs' hstep => .tail (hpq.trans_star hqs') hstep

/-- Termination: the relation is well-founded on the reverse of TPlus.
    We state this propositionally since `WellFounded` lives in `Prop`. -/
noncomputable def Terminating {a b : A} (r : Path a b → Path a b → Type v) : Prop :=
  WellFounded (fun (p q : Path a b) => Nonempty (TPlus r q p))

/-- Head-based multi-step: built by prepending steps at the front.
    This makes first-step decomposition trivial, which is needed for Newman's lemma. -/
inductive TStarH {a b : A} (r : Path a b → Path a b → Type v) :
    Path a b → Path a b → Type (max u v) where
  | refl (p : Path a b) : TStarH r p p
  | head {p q s : Path a b} : r p q → TStarH r q s → TStarH r p s

/-- Convert tail-based TStar to head-based TStarH -/
noncomputable def TStar.toH {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} (h : TStar r p q) : TStarH r p q :=
  match h with
  | .refl _ => .refl _
  | .tail hstar hstep => appendH (toH hstar) hstep
where
  appendH {p q s : Path a b} (h : TStarH r p q) (hs : r q s) : TStarH r p s :=
    match h with
    | .refl _ => .head hs (.refl _)
    | .head hr rest => .head hr (appendH rest hs)

/-- Convert head-based TStarH to tail-based TStar -/
noncomputable def TStarH.toT {a b : A} {r : Path a b → Path a b → Type v}
    {p q : Path a b} (h : TStarH r p q) : TStar r p q :=
  match h with
  | .refl _ => .refl _
  | .head hr rest => TStar.head hr rest.toT

/-- Newman's Lemma (Type-Valued): Termination + Local Confluence → Confluence

    The proof uses well-founded induction on the termination order and
    head-based multi-step decomposition. -/
noncomputable def newman
    (hterm : Terminating (a := a) (b := b) r)
    (hlc : TLocalConfluent (a := a) (b := b) r) :
    TConfluent r where
  close := fun {p _ _} h₁ h₂ =>
    newmanAux hterm hlc p h₁.toH h₂.toH
where
  /-- The core of Newman's lemma, using head-based derivations for
      clean first-step decomposition. -/
  newmanAux (hterm : Terminating (a := a) (b := b) r)
      (hlc : TLocalConfluent (a := a) (b := b) r)
      (p : Path a b) {q₁ q₂ : Path a b}
      (h₁ : TStarH r p q₁) (h₂ : TStarH r p q₂) : TJoinable r q₁ q₂ :=
    hterm.fix (C := fun p => ∀ {q₁ q₂ : Path a b},
      TStarH r p q₁ → TStarH r p q₂ → TJoinable r q₁ q₂)
      (fun p ih {q₁ q₂} h₁ h₂ =>
        match h₁, h₂ with
        | .refl _, h₂ => TJoinable.of_star h₂.toT
        | h₁, .refl _ => TJoinable.symm (TJoinable.of_star h₁.toT)
        | .head hstep₁ rest₁, .head hstep₂ rest₂ =>
          -- hstep₁ : r p a₁, rest₁ : TStarH r a₁ q₁
          -- hstep₂ : r p a₂, rest₂ : TStarH r a₂ q₂
          -- By local confluence: a₁ and a₂ can be joined
          let ⟨c, ha₁c, ha₂c⟩ := hlc.close hstep₁ hstep₂
          -- IH at a₁ (p →₁ a₁, so a₁ is strictly smaller):
          -- join rest₁ (a₁ →* q₁) with ha₁c (a₁ →* c)
          let j₁ := ih _ ⟨.single hstep₁⟩ rest₁ ha₁c.toH
          -- j₁ : TJoinable r q₁ j₁.common with q₁ →* j₁.common and c →* j₁.common

          -- IH at a₂ (p →₁ a₂, so a₂ is strictly smaller):
          -- join rest₂ (a₂ →* q₂) with ha₂c (a₂ →* c)
          let j₂ := ih _ ⟨.single hstep₂⟩ rest₂ ha₂c.toH
          -- j₂ : TJoinable r q₂ j₂.common with q₂ →* j₂.common and c →* j₂.common

          -- Now join j₁.common and j₂.common through c.
          -- c →* j₁.common and c →* j₂.common
          -- IH at c (p →₁ a₁ →* c, so c is strictly smaller...
          -- we need p →⁺ c, which is (.single hstep₁).trans_star ha₁c)
          let p_plus_c : TPlus r p c := TPlus.trans_star (.single hstep₁) ha₁c
          let jc := ih _ ⟨p_plus_c⟩ j₁.right.toH j₂.right.toH
          -- jc : TJoinable r j₁.common j₂.common

          -- Assemble: q₁ →* j₁.common →* jc.common and q₂ →* j₂.common →* jc.common
          ⟨jc.common,
           TStar.trans j₁.left jc.left,
           TStar.trans j₂.left jc.right⟩)
      p h₁ h₂

end Newman

/-! ## Typed Instances for `Step`

We lift `Step : Path a b → Path a b → Prop` into the Type-valued framework
via `PLift`. -/

section StepInstances

open Path Rewrite

/-- Lift the Prop-valued `Step` relation into `Type` via `PLift`.
    Note: `Step` lives at `Type 0` (Prop), so `StepT` lives at `Type 0`.
    We fix the universe to 0 for this section. -/
abbrev StepT {A : Type} {a b : A} (p q : Path a b) : Type := PLift (Step p q)

variable {A₀ : Type} {a₀ b₀ : A₀}

private noncomputable def TStar.of_rw_prop {p q : Path a₀ b₀} (h : Rw p q) :
    Nonempty (TStar StepT p q) := by
  induction h with
  | refl => exact ⟨.refl _⟩
  | tail _ step ih => exact ih.elim fun d => ⟨.tail d ⟨step⟩⟩

noncomputable def TStar.of_rw {p q : Path a₀ b₀} (h : Rw p q) :
    TStar StepT p q :=
  Classical.choice (TStar.of_rw_prop h)

/-- `Step` is type-level locally confluent using the Prop-level proof. -/
noncomputable def localConfluent_step
    [Rewrite.ConfluenceConstructive.HasLocalConfluenceProp.{0}] :
    TLocalConfluent (a := a₀) (b := b₀) StepT where
  close := fun {_p _q₁ _q₂} h₁ h₂ =>
    have hjoin :=
      (ConfluenceConstructive.local_confluence_prop
        (A := A₀) (a := a₀) (b := b₀) h₁.down h₂.down)
    Classical.choice (hjoin.elim fun s hs =>
      hs.elim fun hq₁s hq₂s =>
        ⟨⟨s, TStar.of_rw hq₁s, TStar.of_rw hq₂s⟩⟩)

/-- `Step` is type-level confluent, using termination + local confluence. -/
noncomputable def confluent_step
    [Rewrite.ConfluenceConstructive.HasLocalConfluenceProp.{0}]
    (hterm : Terminating (a := a₀) (b := b₀) StepT) :
    TConfluent (a := a₀) (b := b₀) StepT :=
  newman hterm (localConfluent_step (a₀ := a₀) (b₀ := b₀))

end StepInstances

/-! ## Deeper structural properties -/

section DeepProperties

variable {A : Type u} {a b : A}

end DeepProperties

end TypedRewriting
end OmegaGroupoid
end Path
end ComputationalPaths
