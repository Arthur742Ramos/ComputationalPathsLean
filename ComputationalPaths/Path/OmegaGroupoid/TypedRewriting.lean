/-
# Type-Valued Rewriting Framework

This module provides a Type-valued abstract rewriting system framework,
parallel to the Metatheory library but preserving computational content
in Type rather than collapsing to Prop.

## Purpose

To eliminate `to_canonical`, we need confluence at the TYPE level with 3-cells.
The Metatheory library proves confluence in Prop; here we lift those structures
to Type, adding 3-cell witnesses throughout.

## Key Definitions

- `TStar r a b`: Type-valued reflexive-transitive closure
- `TJoinable r a b`: Type-valued joinability with explicit witnesses
- `TDiamond r`: Type-valued diamond property with 3-cells
- `TConfluent r`: Type-valued confluence with 3-cells

## References

- Metatheory library: https://github.com/Arthur742Ramos/Metatheory
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
- Terese, "Term Rewriting Systems" (2003)
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid
namespace TypedRewriting

universe u

variable {A : Type u}

/-! ## Type-Valued Reflexive-Transitive Closure

Unlike Prop-valued `Star` in Metatheory, `TStar` preserves the structure
of the derivation as Type-valued data.
-/

/-- Type-valued reflexive-transitive closure.
    This is isomorphic to `Derivation₂` but defined inductively
    to match the Metatheory structure for easier lifting. -/
inductive TStar {a b : A} (r : ∀ {p q : Path a b}, Prop) :
    Path a b → Path a b → Type u where
  | refl (p : Path a b) : TStar r p p
  | tail {p q s : Path a b} : TStar r p q → r (p := q) (q := s) → TStar r p s

namespace TStar

/-- Single step implies multi-step -/
def single {a b : A} {r : ∀ {p q : Path a b}, Prop}
    {p q : Path a b} (h : r (p := p) (q := q)) : TStar r p q :=
  TStar.tail (TStar.refl p) h

/-- Multi-step is transitive -/
def trans {a b : A} {r : ∀ {p q : Path a b}, Prop}
    {p q s : Path a b} (h1 : TStar r p q) (h2 : TStar r q s) : TStar r p s := by
  induction h2 with
  | refl => exact h1
  | tail _ hstep ih => exact TStar.tail ih hstep

/-- Prepend a single step -/
def head {a b : A} {r : ∀ {p q : Path a b}, Prop}
    {p q s : Path a b} (hpq : r (p := p) (q := q)) (hqs : TStar r q s) : TStar r p s :=
  trans (single hpq) hqs

/-- Length of a TStar derivation -/
def length {a b : A} {r : ∀ {p q : Path a b}, Prop}
    {p q : Path a b} : TStar r p q → Nat
  | .refl _ => 0
  | .tail h _ => h.length + 1

/-- Decompose a `TStar` derivation into its first step (if any) together with
the remaining derivation.

`uncons h` is `none` exactly when `h` is reflexive. When it is `some`, it returns
the first one-step reduction `p ⟶ q₁` and the remaining tail `q₁ ⟶* q`. -/
def uncons {a b : A} {r : forall {p q : Path a b}, Prop}
    {p q : Path a b} (h : TStar r p q) :
    Option (Sigma fun q1 : Path a b =>
      r (p := p) (q := q1) × TStar r q1 q) := by
  induction h with
  | refl =>
      exact none
  | tail hstar hstep ih =>
      cases ih with
      | none =>
          exact some ⟨_, hstep, .refl _⟩
      | some data =>
          rcases data with ⟨q1, hpq1, hq1q⟩
          exact some ⟨q1, hpq1, .tail hq1q hstep⟩

/-- `uncons` always succeeds on a non-empty derivation. -/
theorem uncons_tail_some {a b : A} {r : forall {p q : Path a b}, Prop}
    {p q s : Path a b} (hstar : TStar r p q) (hstep : r (p := q) (q := s)) :
    ∃ data, uncons (r := r) (.tail hstar hstep) = some data := by
  cases hu : uncons (r := r) hstar with
  | none =>
      refine ⟨⟨_, hstep, .refl _⟩, ?_⟩
      simp [uncons, hu]
  | some data =>
      rcases data with ⟨q1, hpq1, hq1q⟩
      refine ⟨⟨q1, hpq1, .tail hq1q hstep⟩, ?_⟩
      simp [uncons, hu]

end TStar

/-! ## Type-Valued Joinability

Two paths are joinable if they can both reach a common path.
We preserve the witnesses (the common path and the derivations to it).
-/

/-- Type-valued joinability: paths can reach a common target. -/
structure TJoinable {a b : A} (r : ∀ {p q : Path a b}, Prop)
    (p q : Path a b) : Type u where
  /-- The common path both can reach -/
  common : Path a b
  /-- Derivation from p to common -/
  left : TStar r p common
  /-- Derivation from q to common -/
  right : TStar r q common

namespace TJoinable

/-- Joinability is reflexive -/
def refl {a b : A} {r : ∀ {p q : Path a b}, Prop} (p : Path a b) :
    TJoinable r p p :=
  ⟨p, .refl p, .refl p⟩

/-- Joinability is symmetric -/
def symm {a b : A} {r : ∀ {p q : Path a b}, Prop}
    {p q : Path a b} (j : TJoinable r p q) : TJoinable r q p :=
  ⟨j.common, j.right, j.left⟩

/-- From a TStar derivation, paths are joinable -/
def of_star {a b : A} {r : ∀ {p q : Path a b}, Prop}
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
structure TDiamond {a b : A} (r : ∀ {p q : Path a b}, Prop) : Type (u + 1) where
  /-- Embed an `r`-witness as a `Step` so we can form 2-cells (`Derivation₂`)
  and state 3-cell coherences. -/
  step_of : ∀ {p q : Path a b}, r (p := p) (q := q) → Step p q
  /-- Given two steps from the same source... -/
  close : ∀ {p q₁ q₂ : Path a b},
    r (p := p) (q := q₁) → r (p := p) (q := q₂) →
    /-- ...there exists a common target with closing steps... -/
    Σ (s : Path a b),
      (r (p := q₁) (q := s)) ×
      (r (p := q₂) (q := s))
  /-- ...and the 3-cell witnessing the diamond commutes -/
  coherence : ∀ {p q₁ q₂ : Path a b}
    (h₁ : r (p := p) (q := q₁)) (h₂ : r (p := p) (q := q₂)),
    let ⟨s, h₃, h₄⟩ := close h₁ h₂
    -- The two derivations p → q₁ → s and p → q₂ → s are 3-equivalent
    Derivation₃
      (.vcomp (.step (step_of h₁)) (.step (step_of h₃)))
      (.vcomp (.step (step_of h₂)) (.step (step_of h₄)))

/-! ## Type-Valued Local Confluence

Local confluence allows multi-step closing of single-step divergences.
-/

/-- Type-valued local confluence with 3-cells. -/
structure TLocalConfluent {a b : A} (r : ∀ {p q : Path a b}, Prop) : Type (u + 1) where
  /-- Single-step divergences can be closed with multi-step -/
  close : ∀ {p q₁ q₂ : Path a b},
    r (p := p) (q := q₁) → r (p := p) (q := q₂) →
    TJoinable r q₁ q₂

/-! ## Type-Valued Confluence

Full confluence: multi-step divergences can be closed.
-/

/-- Type-valued confluence with joining witnesses. -/
structure TConfluent {a b : A} (r : ∀ {p q : Path a b}, Prop) : Type (u + 1) where
  /-- Multi-step divergences can be closed -/
  close : ∀ {p q₁ q₂ : Path a b},
    TStar r p q₁ → TStar r p q₂ →
    TJoinable r q₁ q₂

/-! ## Type-Valued Semi-Confluence

Semi-confluence is intermediate between local and full confluence.
-/

/-- Type-valued semi-confluence. -/
structure TSemiConfluent {a b : A} (r : ∀ {p q : Path a b}, Prop) : Type (u + 1) where
  /-- Single step vs multi-step can be closed -/
  close : ∀ {p q₁ q₂ : Path a b},
    r (p := p) (q := q₁) → TStar r p q₂ →
    TJoinable r q₁ q₂

/-! ## Key Lemmas

These mirror the Metatheory library but preserve Type structure.
-/

section KeyLemmas

variable {a b : A} {r : ∀ {p q : Path a b}, Prop}

/-- Diamond implies local confluence -/
def localConfluent_of_diamond (hd : TDiamond (a := a) (b := b) r) :
    TLocalConfluent r where
  close := fun {_ q₁ q₂} h₁ h₂ =>
    let ⟨s, h₃, h₄⟩ := hd.close h₁ h₂
    ⟨s, .single h₃, .single h₄⟩

/-- Semi-confluence implies local confluence -/
def localConfluent_of_semiConfluent (hsc : TSemiConfluent (a := a) (b := b) r) :
    TLocalConfluent r where
  close := fun h₁ h₂ => hsc.close h₁ (.single h₂)

/-- Confluence implies semi-confluence -/
def semiConfluent_of_confluent (hc : TConfluent (a := a) (b := b) r) :
    TSemiConfluent r where
  close := fun h₁ h₂ => hc.close (.single h₁) h₂

/-- Confluence implies local confluence -/
def localConfluent_of_confluent (hc : TConfluent (a := a) (b := b) r) :
    TLocalConfluent r :=
  localConfluent_of_semiConfluent (semiConfluent_of_confluent hc)

end KeyLemmas

/-! ## Strip Lemma (Type-Valued)

The strip lemma is key to proving diamond → confluence.
Given diamond, a single step can be pushed through a multi-step.
-/

section StripLemma

variable {a b : A} {r : ∀ {p q : Path a b}, Prop}

/-- Strip lemma helper: push a step through a multi-step, get multi-step + single step. -/
def strip_single (hd : TDiamond (a := a) (b := b) r)
    {p q₁ q₂ : Path a b}
    (h₁ : r (p := p) (q := q₁))
    (h₂ : TStar r p q₂) :
    Σ (s : Path a b), TStar r q₁ s × r (p := q₂) (q := s) := by
  induction h₂ generalizing q₁ with
  | refl =>
    -- q₂ = p, so r p q₁ gives us r q₂ q₁
    exact ⟨q₁, .refl q₁, h₁⟩
  | tail hstar hstep ih =>
    -- hstar : TStar r p q₂', hstep : r q₂' q₂
    -- ih : ∀ q₁, r p q₁ → Σ s, TStar r q₁ s × r q₂' s
    obtain ⟨s', hs', hq₂'s'⟩ := ih h₁
    -- Apply diamond to hq₂'s' : r q₂' s' and hstep : r q₂' q₂
    obtain ⟨s, hs's, hq₂s⟩ := hd.close hq₂'s' hstep
    exact ⟨s, TStar.tail hs' hs's, hq₂s⟩

/-- Full strip lemma: push a step through a multi-step, get two multi-steps. -/
def strip (hd : TDiamond (a := a) (b := b) r)
    {p q₁ q₂ : Path a b}
    (h₁ : r (p := p) (q := q₁))
    (h₂ : TStar r p q₂) :
    Σ (s : Path a b), TStar r q₁ s × TStar r q₂ s := by
  induction h₂ generalizing q₁ with
  | refl =>
    -- q₂ = p
    exact ⟨q₁, .refl q₁, .single h₁⟩
  | tail hstar hstep ih =>
    -- hstar : TStar r p q₂', hstep : r q₂' q₂
    obtain ⟨s', hs', hq₂'s'⟩ := ih h₁
    -- Push hstep through hq₂'s' using strip_single
    obtain ⟨s, hq₂s, hs's⟩ := strip_single hd hstep hq₂'s'
    exact ⟨s, TStar.tail hs' hs's, hq₂s⟩

end StripLemma

/-! ## Diamond → Confluence (Type-Valued)

The main theorem: diamond property implies confluence.
-/

section DiamondConfluence

variable {a b : A} {r : ∀ {p q : Path a b}, Prop}

/-- Diamond implies semi-confluence -/
def semiConfluent_of_diamond (hd : TDiamond (a := a) (b := b) r) :
    TSemiConfluent r where
  close := fun h₁ h₂ =>
    let ⟨s, hs₁, hs₂⟩ := strip hd h₁ h₂
    ⟨s, hs₁, hs₂⟩

/-- Semi-confluence implies confluence (key lemma!) -/
def confluent_of_semiConfluent (hsc : TSemiConfluent (a := a) (b := b) r) :
    TConfluent r where
  close := fun {p q₁ q₂} h₁ h₂ => by
    -- Induction on h₁
    induction h₁ generalizing q₂ with
    | refl => exact TJoinable.of_star h₂
    | tail hstar hstep ih =>
      -- hstar : TStar r p q₁', hstep : r q₁' q₁
      -- ih : TStar r p q₂ → TJoinable r q₁' q₂
      obtain ⟨s, hs₁', hs₂⟩ := ih h₂
      -- By semi-confluence on hstep and hs₁'
      obtain ⟨t, hs₁t, hst⟩ := hsc.close hstep hs₁'
      exact ⟨t, hs₁t, TStar.trans hs₂ hst⟩

/-- Diamond implies confluence -/
def confluent_of_diamond (hd : TDiamond (a := a) (b := b) r) :
    TConfluent r :=
  confluent_of_semiConfluent (semiConfluent_of_diamond hd)

end DiamondConfluence

/-! ## Termination and Newman's Lemma

Newman's lemma: termination + local confluence → confluence.
-/

section Newman

variable {a b : A} {r : ∀ {p q : Path a b}, Prop}

/-- Type-valued transitive closure (one or more steps). -/
inductive TPlus {a b : A} (r : ∀ {p q : Path a b}, Prop) :
    Path a b → Path a b → Type u where
  | single {p q : Path a b} : r (p := p) (q := q) → TPlus r p q
  | tail {p q s : Path a b} : TPlus r p q → r (p := q) (q := s) → TPlus r p s

/-- TPlus implies TStar -/
def TStar.of_plus {a b : A} {r : ∀ {p q : Path a b}, Prop}
    {p q : Path a b} : TPlus r p q → TStar r p q
  | .single h => .single h
  | .tail h hstep => .tail (TStar.of_plus h) hstep

/-- Termination: the relation is well-founded on the reverse of TPlus. -/
def Terminating {a b : A} (r : ∀ {p q : Path a b}, Prop) : Prop :=
  WellFounded (fun p q => TPlus r q p)

/-- Newman's Lemma (Type-Valued): Termination + Local Confluence → Confluence

    The proof follows the standard structure but preserves Type-valued witnesses.
    We use well-founded induction on the termination order. -/
def newman (hterm : Terminating (a := a) (b := b) r)
    (hlc : TLocalConfluent (a := a) (b := b) r) :
    TConfluent r where
  close := fun {p q₁ q₂} h₁ h₂ => by
    -- Well-founded induction on p
    induction p using hterm.induction generalizing q₁ q₂ with
    | h p ih =>
      -- Case split on h₁
      cases h₁ with
      | refl => exact TJoinable.of_star h₂
      | tail h₁' hstep₁ =>
        -- h₁' : TStar r p p', hstep₁ : r p' q₁
        -- Case split on h₂
        cases h₂ with
        | refl =>
          exact TJoinable.symm (TJoinable.of_star (.tail h₁' hstep₁))
        | tail h₂' hstep₂ =>
          -- h₂' : TStar r p p'', hstep₂ : r p'' q₂
          -- Get p' from h₁'
          -- Reconstruct the full derivations and split off their *first* steps.
          -- (Our `TStar` is defined by appending steps, so we use `TStar.uncons`.)
          let h1full : TStar r p q₁ := .tail h₁' hstep₁
          let h2full : TStar r p q₂ := .tail h₂' hstep₂

          -- Helper: extend a `TPlus` derivation by a `TStar` tail.
          have transPlusStar :
              ∀ {x y z : Path a b}, TPlus r x y → TStar r y z → TPlus r x z := by
            intro x y z hxy hyz
            induction hyz generalizing x with
            | refl =>
                exact hxy
            | tail hstar hstep ih =>
                exact TPlus.tail (ih hxy) hstep

          -- Extract the head step p ⟶ p₁ and the remainder p₁ ⟶* q₁ (and likewise for q₂).
          rcases TStar.uncons_tail_some (r := r) h₁' hstep₁ with ⟨data1, _h1u⟩
          rcases data1 with ⟨p₁, hp₁, h₁rest⟩
          rcases TStar.uncons_tail_some (r := r) h₂' hstep₂ with ⟨data2, _h2u⟩
          rcases data2 with ⟨p₂, hp₂, h₂rest⟩

          -- Local confluence closes the one-step divergence.
          obtain ⟨s, hp₁s, hp₂s⟩ := hlc.close (p := p) (q1 := p₁) (q2 := p₂) hp₁ hp₂

          -- Apply IH at `p₁` and `p₂` to join the endpoints with `s`.
          have jq₁s : TJoinable r q₁ s :=
            ih p₁ (.single hp₁) h₁rest hp₁s
          have jq₂s : TJoinable r q₂ s :=
            ih p₂ (.single hp₂) h₂rest hp₂s

          -- `s` is reachable from `p` by at least one step, so IH applies at `s`.
          have p_to_s : TPlus r p s :=
            transPlusStar (.single hp₁) hp₁s

          -- Use IH at `s` to join the two common points coming from `q₁` and `q₂`.
          have jCommon : TJoinable r jq₁s.common jq₂s.common :=
            ih s p_to_s jq₁s.right jq₂s.right

          -- Assemble the final joinability witness for `q₁` and `q₂`.
          refine ⟨jCommon.common, ?_, ?_⟩
          · exact TStar.trans jq₁s.left jCommon.left
          · exact TStar.trans jq₂s.left jCommon.right

end Newman

end TypedRewriting
end OmegaGroupoid
end Path
end ComputationalPaths
