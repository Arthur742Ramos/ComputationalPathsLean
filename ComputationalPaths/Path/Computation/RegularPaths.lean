/-
# Regular Expressions and Paths

This module formalizes regular expressions and their path-theoretic
interpretation: regex as path patterns, Kleene algebra of paths,
star-free paths, pumping lemma aspects, and path language operations.

## References

- Kozen, "A completeness theorem for Kleene algebras"
- Sipser, "Introduction to the Theory of Computation"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace RegularPaths

universe u

/-! ## Regular Expression Definition -/

/-- Regular expressions over alphabet Alpha. -/
inductive Regex (Alpha : Type u) : Type u
  | empty : Regex Alpha
  | epsilon : Regex Alpha
  | char : Alpha → Regex Alpha
  | union : Regex Alpha → Regex Alpha → Regex Alpha
  | concat : Regex Alpha → Regex Alpha → Regex Alpha
  | star : Regex Alpha → Regex Alpha

/-- Language of a regex: set of words matched. -/
inductive regexMatch {Alpha : Type u} : Regex Alpha → List Alpha → Prop
  | epsilon : regexMatch .epsilon []
  | char (a : Alpha) : regexMatch (.char a) [a]
  | unionL {r₁ r₂ : Regex Alpha} {w : List Alpha}
      (h : regexMatch r₁ w) : regexMatch (.union r₁ r₂) w
  | unionR {r₁ r₂ : Regex Alpha} {w : List Alpha}
      (h : regexMatch r₂ w) : regexMatch (.union r₁ r₂) w
  | concat {r₁ r₂ : Regex Alpha} {w₁ w₂ : List Alpha}
      (h₁ : regexMatch r₁ w₁) (h₂ : regexMatch r₂ w₂) :
      regexMatch (.concat r₁ r₂) (w₁ ++ w₂)
  | starEmpty {r : Regex Alpha} : regexMatch (.star r) []
  | starStep {r : Regex Alpha} {w₁ w₂ : List Alpha}
      (h₁ : regexMatch r w₁) (h₂ : regexMatch (.star r) w₂) :
      regexMatch (.star r) (w₁ ++ w₂)

/-! ## Path Language -/

/-- A path language is a set of words (lists over Alpha). -/
noncomputable def PathLang (Alpha : Type u) := List Alpha → Prop

/-- Language of a regex as a PathLang. -/
noncomputable def regexLang {Alpha : Type u} (r : Regex Alpha) : PathLang Alpha :=
  fun w => regexMatch r w

/-- Empty language. -/
noncomputable def emptyLang (Alpha : Type u) : PathLang Alpha := fun _ => False

/-- Epsilon language (contains only the empty word). -/
noncomputable def epsilonLang (Alpha : Type u) : PathLang Alpha := fun w => w = []

/-- Singleton language. -/
noncomputable def singletonLang {Alpha : Type u} (a : Alpha) : PathLang Alpha := fun w => w = [a]

/-- Union of two languages. -/
noncomputable def langUnion {Alpha : Type u} (L₁ L₂ : PathLang Alpha) : PathLang Alpha :=
  fun w => L₁ w ∨ L₂ w

/-- Concatenation of two languages. -/
noncomputable def langConcat {Alpha : Type u} (L₁ L₂ : PathLang Alpha) : PathLang Alpha :=
  fun w => ∃ w₁ w₂, L₁ w₁ ∧ L₂ w₂ ∧ w = w₁ ++ w₂

/-- Kleene star of a language. -/
inductive langStar {Alpha : Type u} (L : PathLang Alpha) : List Alpha → Prop
  | nil : langStar L []
  | cons {w₁ w₂ : List Alpha} (h₁ : L w₁) (h₂ : langStar L w₂) :
      langStar L (w₁ ++ w₂)

/-! ## Path Witnesses for Language Operations -/

/-- Empty regex matches nothing. -/
theorem empty_matches_nothing {Alpha : Type u} (w : List Alpha) :
    ¬ regexMatch (Regex.empty : Regex Alpha) w := by
  intro h; cases h

/-- Epsilon regex matches only empty word. -/
theorem epsilon_matches_nil {Alpha : Type u} :
    regexMatch (Regex.epsilon : Regex Alpha) [] :=
  regexMatch.epsilon

/-- Char regex matches singleton. -/
theorem char_matches_singleton {Alpha : Type u} (a : Alpha) :
    regexMatch (Regex.char a) [a] :=
  regexMatch.char a

/-- Star of any regex matches empty word. -/
theorem star_matches_nil {Alpha : Type u} (r : Regex Alpha) :
    regexMatch (Regex.star r) [] :=
  regexMatch.starEmpty

/-- Union is commutative in terms of language membership. -/
theorem union_comm {Alpha : Type u} (L₁ L₂ : PathLang Alpha) (w : List Alpha) :
    langUnion L₁ L₂ w ↔ langUnion L₂ L₁ w := by
  constructor <;> intro h <;> cases h with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- Union is associative. -/
theorem union_assoc {Alpha : Type u} (L₁ L₂ L₃ : PathLang Alpha) (w : List Alpha) :
    langUnion (langUnion L₁ L₂) L₃ w ↔ langUnion L₁ (langUnion L₂ L₃) w := by
  constructor <;> intro h
  · cases h with
    | inl h => cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)
  · cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h => cases h with
      | inl h => exact Or.inl (Or.inr h)
      | inr h => exact Or.inr h

/-- Union with empty is identity. -/
theorem union_empty_left {Alpha : Type u} (L : PathLang Alpha) (w : List Alpha) :
    langUnion (emptyLang Alpha) L w ↔ L w := by
  constructor
  · intro h; cases h with
    | inl h => exact absurd h (by intro hf; exact hf)
    | inr h => exact h
  · intro h; exact Or.inr h

/-- Concatenation with epsilon on left. -/
theorem concat_epsilon_left {Alpha : Type u} (L : PathLang Alpha) (w : List Alpha) :
    langConcat (epsilonLang Alpha) L w ↔ L w := by
  constructor
  · intro ⟨w₁, w₂, hw₁, hw₂, heq⟩
    simp [epsilonLang] at hw₁
    subst hw₁; simp at heq; subst heq; exact hw₂
  · intro h; exact ⟨[], w, rfl, h, by simp⟩

/-- Concatenation with epsilon on right. -/
theorem concat_epsilon_right {Alpha : Type u} (L : PathLang Alpha) (w : List Alpha) :
    langConcat L (epsilonLang Alpha) w ↔ L w := by
  constructor
  · intro ⟨w₁, w₂, hw₁, hw₂, heq⟩
    simp [epsilonLang] at hw₂
    subst hw₂; simp at heq; subst heq; exact hw₁
  · intro h; exact ⟨w, [], h, rfl, by simp⟩

/-- Star includes the base language. -/
theorem star_includes_base {Alpha : Type u} (L : PathLang Alpha) (w : List Alpha)
    (h : L w) : langStar L w := by
  have := langStar.cons h (langStar.nil)
  simp at this; exact this

/-! ## Kleene Algebra Path Structure -/

/-- Regex size for structural arguments. -/
noncomputable def regexSize {Alpha : Type u} : Regex Alpha → Nat
  | .empty => 1
  | .epsilon => 1
  | .char _ => 1
  | .union r₁ r₂ => 1 + regexSize r₁ + regexSize r₂
  | .concat r₁ r₂ => 1 + regexSize r₁ + regexSize r₂
  | .star r => 1 + regexSize r

/-- Regex size is always positive. -/
theorem regexSize_pos {Alpha : Type u} (r : Regex Alpha) : 0 < regexSize r := by
  cases r <;> simp [regexSize] <;> omega

/-- Path: union of r with itself is equivalent. -/
theorem union_idempotent {Alpha : Type u} (r : Regex Alpha) (w : List Alpha) :
    regexMatch (.union r r) w ↔ regexMatch r w := by
  constructor
  · intro h; cases h with
    | unionL h => exact h
    | unionR h => exact h
  · intro h; exact regexMatch.unionL h

/-- Concatenation with empty annihilates. -/
theorem concat_empty_left {Alpha : Type u} (r : Regex Alpha) (w : List Alpha) :
    ¬ regexMatch (.concat .empty r) w := by
  intro h; cases h with
  | concat h₁ _ => cases h₁

/-- Concatenation with empty on right annihilates. -/
theorem concat_empty_right {Alpha : Type u} (r : Regex Alpha) (w : List Alpha) :
    ¬ regexMatch (.concat r .empty) w := by
  intro h; cases h with
  | concat _ h₂ => cases h₂

/-- Star of empty matches only nil. -/
theorem star_empty_nil {Alpha : Type u} (w : List Alpha) :
    regexMatch (.star (Regex.empty : Regex Alpha)) w → w = [] := by
  intro h
  cases h with
  | starEmpty => rfl
  | starStep h₁ _ => cases h₁

/-! ## Path-based Pumping -/

/-- Word length predicate for pumping. -/
noncomputable def wordLongEnough {Alpha : Type u} (w : List Alpha) (n : Nat) : Prop :=
  w.length ≥ n

/-- Pumping decomposition structure. -/
structure PumpDecomp (Alpha : Type u) (w : List Alpha) where
  x : List Alpha
  y : List Alpha
  z : List Alpha
  split_eq : w = x ++ y ++ z
  y_nonempty : y ≠ []
  xy_bound : (x ++ y).length ≤ w.length

/-- If y is nonempty, pumping once gives a longer word. -/
theorem pump_once_longer {Alpha : Type u} (x y z : List Alpha) (hy : y ≠ []) :
    (x ++ y ++ y ++ z).length > (x ++ y ++ z).length := by
  simp only [List.length_append]
  have : y.length > 0 := by
    cases y with
    | nil => exact absurd rfl hy
    | cons _ _ => simp [List.length]
  omega

/-! ## Star-Free Paths -/

/-- Star-free regex: no star operator. -/
inductive StarFree (Alpha : Type u) : Type u
  | empty : StarFree Alpha
  | epsilon : StarFree Alpha
  | char : Alpha → StarFree Alpha
  | union : StarFree Alpha → StarFree Alpha → StarFree Alpha
  | concat : StarFree Alpha → StarFree Alpha → StarFree Alpha
  | complement : StarFree Alpha → StarFree Alpha

/-- Embedding star-free into regex (without complement). -/
noncomputable def starFreeToRegexPartial {Alpha : Type u} : StarFree Alpha → Regex Alpha
  | .empty => .empty
  | .epsilon => .epsilon
  | .char a => .char a
  | .union r₁ r₂ => .union (starFreeToRegexPartial r₁) (starFreeToRegexPartial r₂)
  | .concat r₁ r₂ => .concat (starFreeToRegexPartial r₁) (starFreeToRegexPartial r₂)
  | .complement r => starFreeToRegexPartial r  -- complement not expressible, keep inner

/-- StarFree size. -/
noncomputable def starFreeSize {Alpha : Type u} : StarFree Alpha → Nat
  | .empty => 1
  | .epsilon => 1
  | .char _ => 1
  | .union r₁ r₂ => 1 + starFreeSize r₁ + starFreeSize r₂
  | .concat r₁ r₂ => 1 + starFreeSize r₁ + starFreeSize r₂
  | .complement r => 1 + starFreeSize r

/-- StarFree size is positive. -/
theorem starFreeSize_pos {Alpha : Type u} (r : StarFree Alpha) : 0 < starFreeSize r := by
  cases r <;> simp [starFreeSize] <;> omega

/-! ## RegularStep Rewrite Rules -/

/-- Rewrite steps for regular expression computations. -/
inductive RegularStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Union idempotency reduction. -/
  | union_idem {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : RegularStep p q
  /-- Concatenation associativity. -/
  | concat_assoc {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : RegularStep p q
  /-- Star unrolling. -/
  | star_unroll {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : RegularStep p q
  /-- Empty elimination. -/
  | empty_elim {A : Type u} {a : A} (p : Path a a) :
      RegularStep p (Path.refl a)

/-- RegularStep is sound. -/
theorem regularStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : RegularStep p q) : p.proof = q.proof := by
  cases h with
  | union_idem _ _ h => exact h
  | concat_assoc _ _ h => exact h
  | star_unroll _ _ h => exact h
  | empty_elim _ => rfl

/-! ## RwEq Instances -/

/-- RwEq: epsilon match path is stable. -/
noncomputable def rwEq_epsilon {Alpha : Type u} :
    RwEq (Path.refl (regexMatch (Regex.epsilon : Regex Alpha) []))
         (Path.refl (regexMatch (Regex.epsilon : Regex Alpha) [])) :=
  RwEq.refl _

/-- Path: regex language union corresponds to langUnion. -/
theorem regex_union_lang {Alpha : Type u} (r₁ r₂ : Regex Alpha) (w : List Alpha) :
    regexLang (.union r₁ r₂) w ↔ langUnion (regexLang r₁) (regexLang r₂) w := by
  constructor
  · intro h; cases h with
    | unionL h => exact Or.inl h
    | unionR h => exact Or.inr h
  · intro h; cases h with
    | inl h => exact regexMatch.unionL h
    | inr h => exact regexMatch.unionR h

/-- symm ∘ symm for regex paths. -/
theorem symm_symm_regex {Alpha : Type u} (r : Regex Alpha) :
    Path.toEq (Path.symm (Path.symm (Path.refl (regexSize r)))) =
    Path.toEq (Path.refl (regexSize r)) := by simp

/-- congrArg for regex size under union. -/
noncomputable def congrArg_regex_union {Alpha : Type u} (r₁ r₂ r₃ : Regex Alpha)
    (h : Path r₂ r₃) :
    Path (Regex.union r₁ r₂) (Regex.union r₁ r₃) :=
  Path.congrArg (Regex.union r₁) h

/-- transport for regex language membership. -/
theorem transport_regex_lang {Alpha : Type u} (r₁ r₂ : Regex Alpha)
    (h : Path r₁ r₂) (w : List Alpha) :
    regexLang r₁ w ↔ regexLang r₂ w := by
  cases h with
  | mk steps proof => cases proof; exact Iff.rfl

/-- Language star is monotone: if L₁ ⊆ L₂ then L₁* ⊆ L₂*. -/
theorem langStar_mono {Alpha : Type u} (L₁ L₂ : PathLang Alpha)
    (hsub : ∀ w, L₁ w → L₂ w) (w : List Alpha) (h : langStar L₁ w) :
    langStar L₂ w := by
  induction h with
  | nil => exact langStar.nil
  | cons h₁ _ ih => exact langStar.cons (hsub _ h₁) ih

/-- Concatenation of two star words is in star. -/
theorem star_concat_star {Alpha : Type u} (L : PathLang Alpha)
    (u₁ u₂ : List Alpha) (h₁ : langStar L u₁) (h₂ : langStar L u₂) :
    langStar L (u₁ ++ u₂) := by
  induction h₁ generalizing u₂ with
  | nil => simpa
  | @cons v₁ v₂ hv _ ihv =>
    rw [show v₁ ++ v₂ ++ u₂ = v₁ ++ (v₂ ++ u₂) from List.append_assoc v₁ v₂ u₂]
    exact langStar.cons hv (ihv u₂ h₂)

/-- Star of star is star (one direction): langStar (langStar L) ⊆ langStar L. -/
theorem star_star_sub {Alpha : Type u} (L : PathLang Alpha) (w : List Alpha)
    (h : langStar (langStar L) w) : langStar L w := by
  induction h with
  | nil => exact langStar.nil
  | @cons w₁ w₂ h₁ _ ih => exact star_concat_star L w₁ w₂ h₁ ih

end RegularPaths
end Computation
end Path
end ComputationalPaths
