/-
# String Rewriting Systems via Structural Computational Paths

This module formalizes string rewriting systems (Thue systems) where
word equalities are witnessed by computational Paths, monoid structure
uses path algebra, and rewriting properties connect to path operations
via congrArg, transport, trans, and symm.

## Main constructions

- `SRWord`: words over an alphabet (lists)
- `SRRule`: string rewrite rules
- `SRStep` / `SRRtc`: one-step and multi-step rewriting
- `ThueEquiv`: Thue congruence (equivalence closure)
- Church-Rosser and confluence via path joining
- Length-based termination
- Monoid structure with path witnesses (associativity, identity)
- Transport of word properties along rewrite paths

## References

- Book & Otto, "String-Rewriting Systems" (1993)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Rewriting.StringRewritingPaths

open ComputationalPaths.Path
open List

universe u

/-! ## Words and Rewrite Rules -/

abbrev SRWord (α : Type u) := List α

structure SRRule (α : Type u) where
  lhs : SRWord α
  rhs : SRWord α

/-! ## One-step and Multi-step Rewriting -/

inductive SRStep {α : Type u} (rules : List (SRRule α)) :
    SRWord α → SRWord α → Prop where
  | apply (r : SRRule α) (u v : SRWord α) :
      r ∈ rules → SRStep rules (u ++ r.lhs ++ v) (u ++ r.rhs ++ v)

inductive SRRtc {α : Type u} (rules : List (SRRule α)) :
    SRWord α → SRWord α → Prop where
  | refl (w : SRWord α) : SRRtc rules w w
  | head {a b c : SRWord α} : SRStep rules a b → SRRtc rules b c → SRRtc rules a c

namespace SRRtc

variable {α : Type u} {rules : List (SRRule α)}

theorem single {a b : SRWord α} (h : SRStep rules a b) : SRRtc rules a b :=
  .head h (.refl b)

theorem trans {a b c : SRWord α} (h₁ : SRRtc rules a b) (h₂ : SRRtc rules b c) :
    SRRtc rules a c := by
  induction h₁ with
  | refl => exact h₂
  | head step _ ih => exact .head step (ih h₂)

end SRRtc

/-! ## Thue Congruence (Symmetric Closure) -/

inductive ThueEquiv {α : Type u} (rules : List (SRRule α)) :
    SRWord α → SRWord α → Prop where
  | refl (w : SRWord α) : ThueEquiv rules w w
  | fwd (r : SRRule α) (u v : SRWord α) :
      r ∈ rules → ThueEquiv rules (u ++ r.lhs ++ v) (u ++ r.rhs ++ v)
  | bwd (r : SRRule α) (u v : SRWord α) :
      r ∈ rules → ThueEquiv rules (u ++ r.rhs ++ v) (u ++ r.lhs ++ v)
  | symm {a b : SRWord α} : ThueEquiv rules a b → ThueEquiv rules b a
  | trans {a b c : SRWord α} : ThueEquiv rules a b → ThueEquiv rules b c → ThueEquiv rules a c

/-- Forward step implies Thue equivalence. -/
theorem SRStep.toThueEquiv {α : Type u} {rules : List (SRRule α)}
    {a b : SRWord α} (h : SRStep rules a b) : ThueEquiv rules a b := by
  cases h with
  | apply r u v hmem => exact .fwd r u v hmem

/-- Multi-step implies Thue equivalence. -/
theorem SRRtc.toThueEquiv {α : Type u} {rules : List (SRRule α)}
    {a b : SRWord α} (h : SRRtc rules a b) : ThueEquiv rules a b := by
  induction h with
  | refl => exact .refl _
  | head step _ ih => exact .trans (step.toThueEquiv) ih

/-! ## Monoid Structure via Paths -/

/-- Path witnessing associativity of word concatenation. -/
def wordAssocPath {α : Type u} (u v w : SRWord α) :
    ComputationalPaths.Path (u ++ v ++ w) (u ++ (v ++ w)) :=
  ComputationalPaths.Path.mk [Step.mk _ _ (List.append_assoc u v w)]
    (List.append_assoc u v w)

/-- Path witnessing left identity. -/
def wordNilLeftPath {α : Type u} (w : SRWord α) :
    ComputationalPaths.Path ([] ++ w) w :=
  ComputationalPaths.Path.mk [Step.mk _ _ (List.nil_append w)] (List.nil_append w)

/-- Path witnessing right identity. -/
def wordNilRightPath {α : Type u} (w : SRWord α) :
    ComputationalPaths.Path (w ++ []) w :=
  ComputationalPaths.Path.mk [Step.mk _ _ (List.append_nil w)] (List.append_nil w)

@[simp] theorem wordNilLeftPath_toEq {α : Type u} (w : SRWord α) :
    (wordNilLeftPath w).toEq = List.nil_append w := by simp

@[simp] theorem wordNilRightPath_toEq {α : Type u} (w : SRWord α) :
    (wordNilRightPath w).toEq = List.append_nil w := by simp

@[simp] theorem wordAssocPath_toEq {α : Type u} (u v w : SRWord α) :
    (wordAssocPath u v w).toEq = List.append_assoc u v w := by simp

/-- Symmetry of associativity path. -/
def wordAssocPathSymm {α : Type u} (u v w : SRWord α) :
    ComputationalPaths.Path (u ++ (v ++ w)) (u ++ v ++ w) :=
  ComputationalPaths.Path.symm (wordAssocPath u v w)

/-- Round-trip: assoc path composed with its inverse yields refl (toEq). -/
theorem wordAssocPath_roundtrip_toEq {α : Type u} (u v w : SRWord α) :
    (ComputationalPaths.Path.trans (wordAssocPath u v w) (wordAssocPathSymm u v w)).toEq = rfl := by
  simp

/-! ## Church-Rosser and Confluence -/

def SRConfluent {α : Type u} (rules : List (SRRule α)) : Prop :=
  ∀ a b c : SRWord α, SRRtc rules a b → SRRtc rules a c →
    ∃ d, SRRtc rules b d ∧ SRRtc rules c d

def SRChurchRosser {α : Type u} (rules : List (SRRule α)) : Prop :=
  ∀ a b : SRWord α, ThueEquiv rules a b →
    ∃ c, SRRtc rules a c ∧ SRRtc rules b c

theorem confluent_implies_churchRosser {α : Type u} {rules : List (SRRule α)}
    (hconf : SRConfluent rules) : SRChurchRosser rules := by
  intro a b hab
  induction hab with
  | refl w => exact ⟨w, .refl w, .refl w⟩
  | fwd r u v hmem =>
    exact ⟨u ++ r.rhs ++ v, .single (.apply r u v hmem), .refl _⟩
  | bwd r u v hmem =>
    exact ⟨u ++ r.rhs ++ v, .refl _, .single (.apply r u v hmem)⟩
  | symm _ ih =>
    obtain ⟨c, hac, hbc⟩ := ih
    exact ⟨c, hbc, hac⟩
  | trans _ _ ih1 ih2 =>
    obtain ⟨c₁, hac₁, hbc₁⟩ := ih1
    obtain ⟨c₂, hbc₂, hcc₂⟩ := ih2
    obtain ⟨d, hc₁d, hc₂d⟩ := hconf _ _ _ hbc₁ hbc₂
    exact ⟨d, hac₁.trans hc₁d, hcc₂.trans hc₂d⟩

/-! ## Normal Forms -/

def SRIsNF {α : Type u} (rules : List (SRRule α)) (w : SRWord α) : Prop :=
  ∀ w', ¬ SRStep rules w w'

theorem unique_normal_form {α : Type u} {rules : List (SRRule α)}
    (hconf : SRConfluent rules)
    {a nf₁ nf₂ : SRWord α}
    (h₁ : SRRtc rules a nf₁) (hnf₁ : SRIsNF rules nf₁)
    (h₂ : SRRtc rules a nf₂) (hnf₂ : SRIsNF rules nf₂) :
    nf₁ = nf₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := hconf a nf₁ nf₂ h₁ h₂
  cases hd₁ with
  | refl => cases hd₂ with
    | refl => rfl
    | head step _ => exact absurd step (hnf₂ _)
  | head step _ => exact absurd step (hnf₁ _)

/-! ## Length-Based Termination -/

def SRRule.isLengthReducing {α : Type u} (r : SRRule α) : Prop :=
  r.rhs.length < r.lhs.length

def isAllLengthReducing {α : Type u} (rules : List (SRRule α)) : Prop :=
  ∀ r ∈ rules, SRRule.isLengthReducing r

theorem length_reducing_step {α : Type u} {rules : List (SRRule α)}
    (hlr : isAllLengthReducing rules) {a b : SRWord α}
    (h : SRStep rules a b) : b.length < a.length := by
  cases h with
  | apply r u v hmem =>
    simp [List.length_append]
    have := hlr r hmem
    unfold SRRule.isLengthReducing at this
    omega

theorem length_reducing_rtc {α : Type u} {rules : List (SRRule α)}
    (hlr : isAllLengthReducing rules) {a b : SRWord α}
    (h : SRRtc rules a b) : b.length ≤ a.length := by
  induction h with
  | refl => omega
  | head step _ ih =>
    have := length_reducing_step hlr step
    omega

theorem length_reducing_wf {α : Type u} {rules : List (SRRule α)}
    (hlr : isAllLengthReducing rules) :
    WellFounded (fun a b => SRStep rules b a) :=
  Subrelation.wf
    (fun {a b} (h : SRStep rules b a) => length_reducing_step hlr h)
    (InvImage.wf (fun (w : SRWord α) => w.length) Nat.lt_wfRel.wf)

/-! ## Empty System Properties -/

theorem no_step_empty {α : Type u} {a b : SRWord α} :
    ¬ SRStep ([] : List (SRRule α)) a b := by
  intro h; cases h; rename_i hmem; simp at hmem

theorem empty_confluent {α : Type u} :
    SRConfluent ([] : List (SRRule α)) := by
  intro a b c h₁ h₂
  cases h₁ with
  | refl => exact ⟨c, h₂, .refl c⟩
  | head step _ => exact absurd step no_step_empty

theorem thueEquiv_empty_iff_eq {α : Type u} {a b : SRWord α} :
    ThueEquiv ([] : List (SRRule α)) a b → a = b := by
  intro h
  induction h with
  | refl => rfl
  | fwd r _ _ hmem => simp at hmem
  | bwd r _ _ hmem => simp at hmem
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-! ## Single-Rule Systems -/

theorem single_rule_step {α : Type u} (l r : SRWord α)
    {a b : SRWord α} (h : SRStep [SRRule.mk l r] a b) :
    ∃ u v, a = u ++ l ++ v ∧ b = u ++ r ++ v := by
  cases h with
  | apply rule u v hmem =>
    simp at hmem
    subst hmem
    exact ⟨u, v, rfl, rfl⟩

theorem single_rule_terminates {α : Type u} (l r : SRWord α)
    (hlr : r.length < l.length) :
    WellFounded (fun a b => SRStep [SRRule.mk l r] b a) :=
  length_reducing_wf (fun rule hmem => by simp at hmem; subst hmem; exact hlr)

/-! ## Path Representation of Word Operations -/

/-- congrArg lifts word concatenation through paths. -/
def appendLeftPath {α : Type u} (prefix_ : SRWord α) {w w' : SRWord α}
    (p : ComputationalPaths.Path w w') :
    ComputationalPaths.Path (prefix_ ++ w) (prefix_ ++ w') :=
  ComputationalPaths.Path.congrArg (prefix_ ++ ·) p

def appendRightPath {α : Type u} (suffix_ : SRWord α) {w w' : SRWord α}
    (p : ComputationalPaths.Path w w') :
    ComputationalPaths.Path (w ++ suffix_) (w' ++ suffix_) :=
  ComputationalPaths.Path.congrArg (· ++ suffix_) p

@[simp] theorem appendLeftPath_refl {α : Type u} (prefix_ : SRWord α) (w : SRWord α) :
    appendLeftPath prefix_ (ComputationalPaths.Path.refl w) =
      ComputationalPaths.Path.refl (prefix_ ++ w) := by
  simp [appendLeftPath]

@[simp] theorem appendRightPath_refl {α : Type u} (suffix_ : SRWord α) (w : SRWord α) :
    appendRightPath suffix_ (ComputationalPaths.Path.refl w) =
      ComputationalPaths.Path.refl (w ++ suffix_) := by
  simp [appendRightPath]

@[simp] theorem appendLeftPath_trans {α : Type u} (prefix_ : SRWord α)
    {w w' w'' : SRWord α}
    (p : ComputationalPaths.Path w w') (q : ComputationalPaths.Path w' w'') :
    appendLeftPath prefix_ (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (appendLeftPath prefix_ p) (appendLeftPath prefix_ q) := by
  simp [appendLeftPath]

@[simp] theorem appendRightPath_trans {α : Type u} (suffix_ : SRWord α)
    {w w' w'' : SRWord α}
    (p : ComputationalPaths.Path w w') (q : ComputationalPaths.Path w' w'') :
    appendRightPath suffix_ (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (appendRightPath suffix_ p) (appendRightPath suffix_ q) := by
  simp [appendRightPath]

@[simp] theorem appendLeftPath_symm {α : Type u} (prefix_ : SRWord α)
    {w w' : SRWord α} (p : ComputationalPaths.Path w w') :
    appendLeftPath prefix_ (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (appendLeftPath prefix_ p) := by
  simp [appendLeftPath]

@[simp] theorem appendRightPath_symm {α : Type u} (suffix_ : SRWord α)
    {w w' : SRWord α} (p : ComputationalPaths.Path w w') :
    appendRightPath suffix_ (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (appendRightPath suffix_ p) := by
  simp [appendRightPath]

/-! ## Transport of Word Properties -/

/-- Transport a predicate on words along a path. -/
def transportWordProp {α : Type u} (P : SRWord α → Prop) {w w' : SRWord α}
    (p : ComputationalPaths.Path w w') (h : P w) : P w' :=
  ComputationalPaths.Path.transport (D := fun x => P x) p h

@[simp] theorem transportWordProp_refl {α : Type u} (P : SRWord α → Prop)
    (w : SRWord α) (h : P w) :
    transportWordProp P (ComputationalPaths.Path.refl w) h = h := rfl

/-- congrArg for word length along paths. -/
def lengthPath {α : Type u} {w w' : SRWord α}
    (p : ComputationalPaths.Path w w') :
    ComputationalPaths.Path w.length w'.length :=
  ComputationalPaths.Path.congrArg List.length p

@[simp] theorem lengthPath_refl {α : Type u} (w : SRWord α) :
    lengthPath (ComputationalPaths.Path.refl w) =
      ComputationalPaths.Path.refl w.length := by
  simp [lengthPath]

@[simp] theorem lengthPath_trans {α : Type u} {w w' w'' : SRWord α}
    (p : ComputationalPaths.Path w w') (q : ComputationalPaths.Path w' w'') :
    lengthPath (ComputationalPaths.Path.trans p q) =
      ComputationalPaths.Path.trans (lengthPath p) (lengthPath q) := by
  simp [lengthPath]

@[simp] theorem lengthPath_symm {α : Type u} {w w' : SRWord α}
    (p : ComputationalPaths.Path w w') :
    lengthPath (ComputationalPaths.Path.symm p) =
      ComputationalPaths.Path.symm (lengthPath p) := by
  simp [lengthPath]

/-! ## Rewriting Preserves Thue Classes -/

theorem sstep_same_class {α : Type u} {rules : List (SRRule α)}
    {a b : SRWord α} (h : SRStep rules a b) :
    ThueEquiv rules a b := h.toThueEquiv

theorem srtc_same_class {α : Type u} {rules : List (SRRule α)}
    {a b : SRWord α} (h : SRRtc rules a b) :
    ThueEquiv rules a b := h.toThueEquiv

/-! ## ThueEquiv is an Equivalence -/

theorem ThueEquiv.rfl' {α : Type u} {rules : List (SRRule α)} {w : SRWord α} :
    ThueEquiv rules w w := .refl w

theorem ThueEquiv.equiv {α : Type u} {rules : List (SRRule α)}
    {a b c : SRWord α}
    (hab : ThueEquiv rules a b) (hbc : ThueEquiv rules b c) :
    ThueEquiv rules a c := .trans hab hbc

end ComputationalPaths.Path.Rewriting.StringRewritingPaths
