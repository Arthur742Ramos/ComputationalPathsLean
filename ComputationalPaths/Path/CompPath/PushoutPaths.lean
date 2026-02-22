/-
# Path Characterization for Pushouts

This module characterizes paths in pushouts as "zig-zag" sequences.
A path in Pushout A B C f g can be decomposed into a sequence of:
- Paths within A (via inl)
- Paths within B (via inr)
- Glue paths crossing between A and B

This is the core machinery needed for the Seifert-Van Kampen theorem.

## The Zig-Zag Representation

A path from inl(a) to inl(a') can be represented as:
  inl(a) → inl(f(c₁)) → inr(g(c₁)) → inr(b₁) → ... → inl(a')

where:
- Each → within inl/inr is a path in A or B
- Transitions inl(f(c)) → inr(g(c)) are glue paths
- Transitions inr(g(c)) → inl(f(c)) are inverse glue paths

## References

- Favonia & Shulman, "The Seifert-van Kampen Theorem in HoTT"
- HoTT Book, Chapter 8.7
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace CompPath

open Pushout
open Wedge

universe u v

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}

/-! ## Side Indicator

Paths in a pushout alternate between the "left" (A) and "right" (B) sides.
-/

/-- Indicates which side of the pushout we're on. -/
inductive Side : Type where
  | left : Side   -- In A (via inl)
  | right : Side  -- In B (via inr)
deriving DecidableEq, Repr

namespace Side

noncomputable def flip : Side → Side
  | left => right
  | right => left

@[simp] theorem flip_flip (s : Side) : flip (flip s) = s := by
  cases s <;> rfl

@[simp] theorem flip_left : flip left = right := rfl
@[simp] theorem flip_right : flip right = left := rfl

end Side

/-! ## Word Representation for Free Products

For the special case of wedge sums (and for the general SVK theorem),
we represent loops as words in a free product.
-/

/-- A word in the free product G₁ * G₂.
Elements alternate between G₁ and G₂ (no adjacent elements from same group). -/
inductive FreeProductWord (G₁ : Type u) (G₂ : Type u) : Type u where
  /-- Empty word (identity). -/
  | nil : FreeProductWord G₁ G₂
  /-- Cons an element from G₁. -/
  | consLeft (x : G₁) (rest : FreeProductWord G₁ G₂) : FreeProductWord G₁ G₂
  /-- Cons an element from G₂. -/
  | consRight (y : G₂) (rest : FreeProductWord G₁ G₂) : FreeProductWord G₁ G₂

namespace FreeProductWord

variable {G₁ : Type u} {G₂ : Type u}

/-- Concatenate two words. -/
noncomputable def concat : FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
  | nil, w₂ => w₂
  | consLeft x rest, w₂ => consLeft x (concat rest w₂)
  | consRight y rest, w₂ => consRight y (concat rest w₂)

/-- Length of a word. -/
noncomputable def length : FreeProductWord G₁ G₂ → Nat
  | nil => 0
  | consLeft _ rest => 1 + length rest
  | consRight _ rest => 1 + length rest

/-- Singleton word from G₁. -/
noncomputable def singleLeft (x : G₁) : FreeProductWord G₁ G₂ := consLeft x nil

/-- Singleton word from G₂. -/
noncomputable def singleRight (y : G₂) : FreeProductWord G₁ G₂ := consRight y nil

/-- Reverse a word. -/
noncomputable def reverse : FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
  | nil => nil
  | consLeft x rest => concat (reverse rest) (singleLeft x)
  | consRight y rest => concat (reverse rest) (singleRight y)

/-- Map a word by mapping each letter on its side. -/
noncomputable def map {H₁ H₂ : Type u}
    (f : G₁ → H₁) (g : G₂ → H₂) :
    FreeProductWord G₁ G₂ → FreeProductWord H₁ H₂
  | nil => nil
  | consLeft x rest => consLeft (f x) (map f g rest)
  | consRight y rest => consRight (g y) (map f g rest)

@[simp] theorem map_nil {H₁ H₂ : Type u}
    (f : G₁ → H₁) (g : G₂ → H₂) :
    map f g (nil : FreeProductWord G₁ G₂) = nil := rfl

@[simp] theorem map_consLeft {H₁ H₂ : Type u}
    (f : G₁ → H₁) (g : G₂ → H₂) (x : G₁) (rest : FreeProductWord G₁ G₂) :
    map f g (consLeft x rest) = consLeft (f x) (map f g rest) := rfl

@[simp] theorem map_consRight {H₁ H₂ : Type u}
    (f : G₁ → H₁) (g : G₂ → H₂) (y : G₂) (rest : FreeProductWord G₁ G₂) :
    map f g (consRight y rest) = consRight (g y) (map f g rest) := rfl

/-- Equivalence on free-product words induced by equivalences on each side. -/
noncomputable def equiv {H₁ H₂ : Type u}
    (e₁ : SimpleEquiv G₁ H₁) (e₂ : SimpleEquiv G₂ H₂) :
    SimpleEquiv (FreeProductWord G₁ G₂) (FreeProductWord H₁ H₂) where
  toFun := map e₁.toFun e₂.toFun
  invFun := map e₁.invFun e₂.invFun
  left_inv := by
    intro w
    induction w with
    | nil => simp [map]
    | consLeft x rest ih =>
        simp [map, ih, e₁.left_inv]
    | consRight y rest ih =>
        simp [map, ih, e₂.left_inv]
  right_inv := by
    intro w
    induction w with
    | nil => simp [map]
    | consLeft x rest ih =>
        simp [map, ih, e₁.right_inv]
    | consRight y rest ih =>
        simp [map, ih, e₂.right_inv]

/-- Inverse of a word in a free product: reverse and negate each element.
This requires `Neg` instances on the component types (e.g., for ℤ). -/
noncomputable def inverse [Neg G₁] [Neg G₂] : FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
  | nil => nil
  | consLeft x rest => concat (inverse rest) (singleLeft (-x))
  | consRight y rest => concat (inverse rest) (singleRight (-y))

@[simp] theorem inverse_nil [Neg G₁] [Neg G₂] :
    inverse (nil : FreeProductWord G₁ G₂) = nil := rfl

@[simp] theorem concat_nil_left (w : FreeProductWord G₁ G₂) : concat nil w = w := rfl

@[simp] theorem singleLeft_concat (x : G₁) (w : FreeProductWord G₁ G₂) :
    concat (singleLeft x) w = consLeft x w := rfl

@[simp] theorem singleRight_concat (y : G₂) (w : FreeProductWord G₁ G₂) :
    concat (singleRight y) w = consRight y w := rfl

@[simp] theorem concat_nil_right (w : FreeProductWord G₁ G₂) : concat w nil = w := by
  induction w with
  | nil => rfl
  | consLeft x rest ih => simp [concat, ih]
  | consRight y rest ih => simp [concat, ih]

@[simp] theorem concat_assoc (w₁ w₂ w₃ : FreeProductWord G₁ G₂) :
    concat (concat w₁ w₂) w₃ = concat w₁ (concat w₂ w₃) := by
  induction w₁ with
  | nil => rfl
  | consLeft x rest ih => simp [concat, ih]
  | consRight y rest ih => simp [concat, ih]

/-! ### Inverse Properties -/

/-- Inverse distributes over concatenation (in reverse order). -/
theorem inverse_concat [Neg G₁] [Neg G₂] (w₁ w₂ : FreeProductWord G₁ G₂) :
    inverse (concat w₁ w₂) = concat (inverse w₂) (inverse w₁) := by
  induction w₁ with
  | nil => simp [concat, inverse]
  | consLeft x rest ih =>
      simp only [concat, inverse]
      rw [ih]
      simp only [concat_assoc]
  | consRight y rest ih =>
      simp only [concat, inverse]
      rw [ih]
      simp only [concat_assoc]

/-- Double inverse is identity (requires double negation to be identity). -/
theorem inverse_inverse [Neg G₁] [Neg G₂]
    (hG₁ : ∀ x : G₁, -(-x) = x) (hG₂ : ∀ y : G₂, -(-y) = y)
    (w : FreeProductWord G₁ G₂) : inverse (inverse w) = w := by
  induction w with
  | nil => rfl
  | consLeft x rest ih =>
      simp only [inverse, singleLeft]
      rw [inverse_concat, ih]
      simp only [inverse, hG₁, concat_nil_left, singleLeft_concat]
  | consRight y rest ih =>
      simp only [inverse, singleRight]
      rw [inverse_concat, ih]
      simp only [inverse, hG₂, concat_nil_left, singleRight_concat]

/-- Inverse of a singleton left element. -/
@[simp] theorem inverse_singleLeft [Neg G₁] [Neg G₂] (x : G₁) :
    inverse (singleLeft x : FreeProductWord G₁ G₂) = singleLeft (-x) := by
  simp [inverse, singleLeft]

/-- Inverse of a singleton right element. -/
@[simp] theorem inverse_singleRight [Neg G₁] [Neg G₂] (y : G₂) :
    inverse (singleRight y : FreeProductWord G₁ G₂) = singleRight (-y) := by
  simp [inverse, singleRight]

/-! ### Reduced Words

A reduced word has no adjacent elements from the same side. This is important
for normal forms in free products. -/

/-- A word is reduced if no two adjacent elements are from the same side. -/
noncomputable def isReduced : FreeProductWord G₁ G₂ → Bool
  | nil => true
  | consLeft _ nil => true
  | consLeft _ (consLeft _ _) => false
  | consLeft _ rest@(consRight _ _) => isReduced rest
  | consRight _ nil => true
  | consRight _ (consRight _ _) => false
  | consRight _ rest@(consLeft _ _) => isReduced rest

/-- The empty word is reduced. -/
theorem isReduced_nil : isReduced (nil : FreeProductWord G₁ G₂) = true := by
  unfold isReduced
  rfl

/-- A singleton left word is reduced. -/
theorem isReduced_singleLeft (x : G₁) :
    isReduced (singleLeft x : FreeProductWord G₁ G₂) = true := by
  unfold singleLeft isReduced
  rfl

/-- A singleton right word is reduced. -/
theorem isReduced_singleRight (y : G₂) :
    isReduced (singleRight y : FreeProductWord G₁ G₂) = true := by
  unfold singleRight isReduced
  rfl

/-- Inductive characterization of reduced words. -/
inductive IsReducedInd : FreeProductWord G₁ G₂ → Prop where
  | nil : IsReducedInd nil
  | singleLeft (x : G₁) : IsReducedInd (singleLeft x)
  | singleRight (y : G₂) : IsReducedInd (singleRight y)
  | consLeftRight (x : G₁) (y : G₂) (rest : FreeProductWord G₁ G₂)
      (h : IsReducedInd (consRight y rest)) :
      IsReducedInd (consLeft x (consRight y rest))
  | consRightLeft (y : G₂) (x : G₁) (rest : FreeProductWord G₁ G₂)
      (h : IsReducedInd (consLeft x rest)) :
      IsReducedInd (consRight y (consLeft x rest))

/-- Boolean `isReduced` implies `IsReducedInd`. -/
theorem isReducedInd_of_isReduced {w : FreeProductWord G₁ G₂} (h : isReduced w = true) :
    IsReducedInd w := by
  induction w with
  | nil => exact IsReducedInd.nil
  | consLeft x rest ih =>
      cases rest with
      | nil => exact IsReducedInd.singleLeft x
      | consLeft x' rest' =>
          unfold isReduced at h
          exact False.elim (Bool.false_ne_true h)
      | consRight y rest' =>
          unfold isReduced at h
          exact IsReducedInd.consLeftRight x y rest' (ih h)
  | consRight y rest ih =>
      cases rest with
      | nil => exact IsReducedInd.singleRight y
      | consRight y' rest' =>
          unfold isReduced at h
          exact False.elim (Bool.false_ne_true h)
      | consLeft x rest' =>
          unfold isReduced at h
          exact IsReducedInd.consRightLeft y x rest' (ih h)

/-! ### Free Group Reduction Relation

For free products of groups (not just sets), we need a reduction relation that:
1. Combines adjacent elements from the same side: `consLeft x (consLeft y rest) ≈ consLeft (x + y) rest`
2. Removes identity elements: `consLeft 0 rest ≈ rest`

This allows proving that `w * inverse(w) = nil` (the group cancellation law). -/

/-- Single-step reduction in a free product word.
This captures both adjacent element combination and identity removal. -/
inductive FreeGroupStep [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → Prop where
  /-- Combine adjacent left elements: consLeft x (consLeft y rest) → consLeft (x + y) rest -/
  | combineLeft (x y : G₁) (rest : FreeProductWord G₁ G₂) :
      FreeGroupStep (consLeft x (consLeft y rest)) (consLeft (x + y) rest)
  /-- Combine adjacent right elements: consRight x (consRight y rest) → consRight (x + y) rest -/
  | combineRight (x y : G₂) (rest : FreeProductWord G₁ G₂) :
      FreeGroupStep (consRight x (consRight y rest)) (consRight (x + y) rest)
  /-- Remove left identity: consLeft 0 rest → rest -/
  | removeLeftZero (rest : FreeProductWord G₁ G₂) :
      FreeGroupStep (consLeft 0 rest) rest
  /-- Remove right identity: consRight 0 rest → rest -/
  | removeRightZero (rest : FreeProductWord G₁ G₂) :
      FreeGroupStep (consRight 0 rest) rest
  /-- Congruence: reduce inside consLeft -/
  | congrLeft (x : G₁) {w w' : FreeProductWord G₁ G₂} :
      FreeGroupStep w w' → FreeGroupStep (consLeft x w) (consLeft x w')
  /-- Congruence: reduce inside consRight -/
  | congrRight (y : G₂) {w w' : FreeProductWord G₁ G₂} :
      FreeGroupStep w w' → FreeGroupStep (consRight y w) (consRight y w')

/-- Multi-step reduction (reflexive-transitive closure). -/
inductive FreeGroupRw [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → Prop where
  | refl (w : FreeProductWord G₁ G₂) : FreeGroupRw w w
  | step {w₁ w₂ : FreeProductWord G₁ G₂} :
      FreeGroupStep w₁ w₂ → FreeGroupRw w₁ w₂
  | trans {w₁ w₂ w₃ : FreeProductWord G₁ G₂} :
      FreeGroupRw w₁ w₂ → FreeGroupRw w₂ w₃ → FreeGroupRw w₁ w₃

/-- Free group equivalence (symmetric-transitive closure of FreeGroupRw). -/
inductive FreeGroupEq [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → Prop where
  | refl (w : FreeProductWord G₁ G₂) : FreeGroupEq w w
  | step {w₁ w₂ : FreeProductWord G₁ G₂} :
      FreeGroupStep w₁ w₂ → FreeGroupEq w₁ w₂
  | symm {w₁ w₂ : FreeProductWord G₁ G₂} :
      FreeGroupEq w₁ w₂ → FreeGroupEq w₂ w₁
  | trans {w₁ w₂ w₃ : FreeProductWord G₁ G₂} :
      FreeGroupEq w₁ w₂ → FreeGroupEq w₂ w₃ → FreeGroupEq w₁ w₃

namespace FreeGroupEq

variable [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]

/-- FreeGroupRw implies FreeGroupEq. -/
theorem of_rw {w₁ w₂ : FreeProductWord G₁ G₂} (h : FreeGroupRw w₁ w₂) :
    FreeGroupEq w₁ w₂ := by
  induction h with
  | refl w => exact FreeGroupEq.refl w
  | step hs => exact FreeGroupEq.step hs
  | trans _ _ ih1 ih2 => exact FreeGroupEq.trans ih1 ih2

/-- Congruence for consLeft. -/
theorem consLeft_congr (x : G₁) {w w' : FreeProductWord G₁ G₂}
    (h : FreeGroupEq w w') : FreeGroupEq (consLeft x w) (consLeft x w') := by
  induction h with
  | refl _ => exact FreeGroupEq.refl _
  | step hs => exact FreeGroupEq.step (FreeGroupStep.congrLeft x hs)
  | symm _ ih => exact FreeGroupEq.symm ih
  | trans _ _ ih1 ih2 => exact FreeGroupEq.trans ih1 ih2

/-- Congruence for consRight. -/
theorem consRight_congr (y : G₂) {w w' : FreeProductWord G₁ G₂}
    (h : FreeGroupEq w w') : FreeGroupEq (consRight y w) (consRight y w') := by
  induction h with
  | refl _ => exact FreeGroupEq.refl _
  | step hs => exact FreeGroupEq.step (FreeGroupStep.congrRight y hs)
  | symm _ ih => exact FreeGroupEq.symm ih
  | trans _ _ ih1 ih2 => exact FreeGroupEq.trans ih1 ih2

/-- Adjacent left elements can be combined. -/
theorem combineLeft (x y : G₁) (rest : FreeProductWord G₁ G₂) :
    FreeGroupEq (consLeft x (consLeft y rest)) (consLeft (x + y) rest) :=
  FreeGroupEq.step (FreeGroupStep.combineLeft x y rest)

/-- Adjacent right elements can be combined. -/
theorem combineRight (x y : G₂) (rest : FreeProductWord G₁ G₂) :
    FreeGroupEq (consRight x (consRight y rest)) (consRight (x + y) rest) :=
  FreeGroupEq.step (FreeGroupStep.combineRight x y rest)

/-- Left zero can be removed. -/
theorem removeLeftZero (rest : FreeProductWord G₁ G₂) :
    FreeGroupEq (consLeft 0 rest) rest :=
  FreeGroupEq.step (FreeGroupStep.removeLeftZero rest)

/-- Right zero can be removed. -/
theorem removeRightZero (rest : FreeProductWord G₁ G₂) :
    FreeGroupEq (consRight 0 rest) rest :=
  FreeGroupEq.step (FreeGroupStep.removeRightZero rest)

end FreeGroupEq

/-! ### Key Lemma: Cancellation

The key property we need: `concat w (inverse w) ≈ nil` (in FreeGroupEq).
This requires that addition and negation satisfy group laws. -/

/-- FreeGroupStep lifts through concat on the left. -/
theorem freeGroupStep_concat_left [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    (w₂ : FreeProductWord G₁ G₂) {w₁ w₁' : FreeProductWord G₁ G₂}
    (h : FreeGroupStep w₁ w₁') :
    FreeGroupEq (concat w₁ w₂) (concat w₁' w₂) := by
  induction h with
  | combineLeft x y rest =>
      simp only [concat]
      exact FreeGroupEq.step (FreeGroupStep.combineLeft x y (concat rest w₂))
  | combineRight x y rest =>
      simp only [concat]
      exact FreeGroupEq.step (FreeGroupStep.combineRight x y (concat rest w₂))
  | removeLeftZero rest =>
      simp only [concat]
      exact FreeGroupEq.step (FreeGroupStep.removeLeftZero _)
  | removeRightZero rest =>
      simp only [concat]
      exact FreeGroupEq.step (FreeGroupStep.removeRightZero _)
  | congrLeft x _ ih =>
      simp only [concat]
      exact FreeGroupEq.consLeft_congr x ih
  | congrRight y _ ih =>
      simp only [concat]
      exact FreeGroupEq.consRight_congr y ih

/-- Concatenation respects FreeGroupEq on the left. -/
theorem concat_freeGroupEq_left [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    (w₂ : FreeProductWord G₁ G₂) {w₁ w₁' : FreeProductWord G₁ G₂}
    (h : FreeGroupEq w₁ w₁') :
    FreeGroupEq (concat w₁ w₂) (concat w₁' w₂) := by
  induction h with
  | refl _ => exact FreeGroupEq.refl _
  | step hs => exact freeGroupStep_concat_left w₂ hs
  | symm _ ih => exact FreeGroupEq.symm ih
  | trans _ _ ih1 ih2 => exact FreeGroupEq.trans ih1 ih2

/-- Concatenation respects FreeGroupEq on the right. -/
theorem concat_freeGroupEq_right [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    (w₁ : FreeProductWord G₁ G₂) {w₂ w₂' : FreeProductWord G₁ G₂}
    (h : FreeGroupEq w₂ w₂') :
    FreeGroupEq (concat w₁ w₂) (concat w₁ w₂') := by
  induction w₁ with
  | nil => exact h
  | consLeft x rest ih =>
      simp only [concat]
      exact FreeGroupEq.consLeft_congr x ih
  | consRight y rest ih =>
      simp only [concat]
      exact FreeGroupEq.consRight_congr y ih

/-- Key cancellation lemma: `concat (singleLeft x) (singleLeft (-x)) ≈ nil`
when `x + (-x) = 0`. -/
theorem singleLeft_cancel [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] [Neg G₁]
    (hadd : ∀ x : G₁, x + (-x) = 0) (x : G₁) :
    FreeGroupEq (concat (singleLeft x) (singleLeft (-x)))
                (nil : FreeProductWord G₁ G₂) := by
  simp only [singleLeft, concat]
  -- consLeft x (consLeft (-x) nil) → consLeft (x + (-x)) nil → consLeft 0 nil → nil
  apply FreeGroupEq.trans (FreeGroupEq.combineLeft x (-x) nil)
  rw [hadd]
  exact FreeGroupEq.removeLeftZero nil

/-- Key cancellation lemma: `concat (singleRight y) (singleRight (-y)) ≈ nil`
when `y + (-y) = 0`. -/
theorem singleRight_cancel [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] [Neg G₂]
    (hadd : ∀ y : G₂, y + (-y) = 0) (y : G₂) :
    FreeGroupEq (concat (singleRight y) (singleRight (-y)))
                (nil : FreeProductWord G₁ G₂) := by
  simp only [singleRight, concat]
  apply FreeGroupEq.trans (FreeGroupEq.combineRight y (-y) nil)
  rw [hadd]
  exact FreeGroupEq.removeRightZero nil

/-- The main cancellation theorem: `concat w (inverse w) ≈ nil`.
This is the key property making free products into groups. -/
theorem concat_inverse_nil [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] [Neg G₁] [Neg G₂]
    (haddG₁ : ∀ x : G₁, x + (-x) = 0)
    (haddG₂ : ∀ y : G₂, y + (-y) = 0)
    (w : FreeProductWord G₁ G₂) :
    FreeGroupEq (concat w (inverse w)) nil := by
  induction w with
  | nil =>
      simp only [inverse, concat]
      exact FreeGroupEq.refl nil
  | consLeft x rest ih =>
      -- inverse (consLeft x rest) = concat (inverse rest) (singleLeft (-x))
      -- concat (consLeft x rest) (concat (inverse rest) (singleLeft (-x)))
      -- = consLeft x (concat rest (concat (inverse rest) (singleLeft (-x))))
      -- By associativity: = consLeft x (concat (concat rest (inverse rest)) (singleLeft (-x)))
      -- By ih: ≈ consLeft x (concat nil (singleLeft (-x)))
      --       = consLeft x (singleLeft (-x))
      --       = consLeft x (consLeft (-x) nil)
      -- By combine + remove: ≈ nil
      simp only [inverse, concat]
      -- Goal: FreeGroupEq (consLeft x (concat rest (concat (inverse rest) (singleLeft (-x))))) nil
      have h1 : FreeGroupEq
          (consLeft x (concat rest (concat (inverse rest) (singleLeft (-x)))))
          (consLeft x (concat (concat rest (inverse rest)) (singleLeft (-x)))) := by
        apply FreeGroupEq.consLeft_congr
        rw [concat_assoc]
        exact FreeGroupEq.refl _
      apply FreeGroupEq.trans h1
      have h2 : FreeGroupEq
          (consLeft x (concat (concat rest (inverse rest)) (singleLeft (-x))))
          (consLeft x (concat nil (singleLeft (-x)))) := by
        apply FreeGroupEq.consLeft_congr
        exact concat_freeGroupEq_left _ ih
      apply FreeGroupEq.trans h2
      simp only [concat]
      -- consLeft x (consLeft (-x) nil) ≈ nil
      apply FreeGroupEq.trans (FreeGroupEq.combineLeft x (-x) nil)
      rw [haddG₁]
      exact FreeGroupEq.removeLeftZero nil
  | consRight y rest ih =>
      simp only [inverse, concat]
      have h1 : FreeGroupEq
          (consRight y (concat rest (concat (inverse rest) (singleRight (-y)))))
          (consRight y (concat (concat rest (inverse rest)) (singleRight (-y)))) := by
        apply FreeGroupEq.consRight_congr
        rw [concat_assoc]
        exact FreeGroupEq.refl _
      apply FreeGroupEq.trans h1
      have h2 : FreeGroupEq
          (consRight y (concat (concat rest (inverse rest)) (singleRight (-y))))
          (consRight y (concat nil (singleRight (-y)))) := by
        apply FreeGroupEq.consRight_congr
        exact concat_freeGroupEq_left _ ih
      apply FreeGroupEq.trans h2
      simp only [concat]
      apply FreeGroupEq.trans (FreeGroupEq.combineRight y (-y) nil)
      rw [haddG₂]
      exact FreeGroupEq.removeRightZero nil

/-- Inverse respects FreeGroupStep.
This requires the group anti-homomorphism property: -(x + y) = (-y) + (-x). -/
theorem inverse_freeGroupStep [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] [Neg G₁] [Neg G₂]
    (hnegG₁ : ∀ x y : G₁, -(x + y) = (-y) + (-x))
    (hnegG₂ : ∀ x y : G₂, -(x + y) = (-y) + (-x))
    (hnegZeroG₁ : -(0 : G₁) = 0)
    (hnegZeroG₂ : -(0 : G₂) = 0)
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : FreeGroupStep w₁ w₂) :
    FreeGroupEq (inverse w₁) (inverse w₂) := by
  induction h with
  | combineLeft x y rest =>
      -- inverse (consLeft x (consLeft y rest)) = concat (concat (inverse rest) (singleLeft (-y))) (singleLeft (-x))
      -- inverse (consLeft (x+y) rest) = concat (inverse rest) (singleLeft (-(x+y)))
      simp only [inverse]
      -- Need: concat (concat (inverse rest) (singleLeft (-y))) (singleLeft (-x)) ≈
      --       concat (inverse rest) (singleLeft (-(x+y)))
      -- Use associativity and combine
      rw [concat_assoc]
      apply concat_freeGroupEq_right
      -- Need: concat (singleLeft (-y)) (singleLeft (-x)) ≈ singleLeft (-(x+y))
      simp only [singleLeft, concat]
      -- consLeft (-y) (consLeft (-x) nil) ≈ consLeft (-(x+y)) nil
      apply FreeGroupEq.trans (FreeGroupEq.combineLeft (-y) (-x) nil)
      rw [← hnegG₁]
      exact FreeGroupEq.refl _
  | combineRight x y rest =>
      simp only [inverse]
      rw [concat_assoc]
      apply concat_freeGroupEq_right
      simp only [singleRight, concat]
      apply FreeGroupEq.trans (FreeGroupEq.combineRight (-y) (-x) nil)
      rw [← hnegG₂]
      exact FreeGroupEq.refl _
  | removeLeftZero rest =>
      -- inverse (consLeft 0 rest) = concat (inverse rest) (singleLeft (-0))
      -- inverse rest
      simp only [inverse]
      -- concat (inverse rest) (singleLeft (-0)) ≈ inverse rest
      rw [hnegZeroG₁]
      simp only [singleLeft]
      -- Goal: FreeGroupEq (concat (inverse rest) (consLeft 0 nil)) (inverse rest)
      -- Use: concat (inverse rest) (consLeft 0 nil) ≈ concat (inverse rest) nil ≈ inverse rest
      apply FreeGroupEq.trans (concat_freeGroupEq_right (inverse rest) (FreeGroupEq.removeLeftZero nil))
      simp only [concat_nil_right]
      exact FreeGroupEq.refl _
  | removeRightZero rest =>
      simp only [inverse]
      rw [hnegZeroG₂]
      simp only [singleRight]
      -- Goal: FreeGroupEq (concat (inverse rest) (consRight 0 nil)) (inverse rest)
      apply FreeGroupEq.trans (concat_freeGroupEq_right (inverse rest) (FreeGroupEq.removeRightZero nil))
      simp only [concat_nil_right]
      exact FreeGroupEq.refl _
  | congrLeft x _ ih =>
      simp only [inverse]
      exact concat_freeGroupEq_left _ ih
  | congrRight y _ ih =>
      simp only [inverse]
      exact concat_freeGroupEq_left _ ih

/-- Right cancellation: `concat (inverse w) w ≈ nil`. -/
theorem inverse_concat_nil [Add G₁] [Add G₂] [Zero G₁] [Zero G₂] [Neg G₁] [Neg G₂]
    (haddG₁ : ∀ x : G₁, (-x) + x = 0)
    (haddG₂ : ∀ y : G₂, (-y) + y = 0)
    (w : FreeProductWord G₁ G₂) :
    FreeGroupEq (concat (inverse w) w) nil := by
  induction w with
  | nil =>
      simp only [inverse, concat]
      exact FreeGroupEq.refl nil
  | consLeft x rest ih =>
      -- inverse (consLeft x rest) = concat (inverse rest) (singleLeft (-x))
      -- concat (concat (inverse rest) (singleLeft (-x))) (consLeft x rest)
      -- By assoc: = concat (inverse rest) (concat (singleLeft (-x)) (consLeft x rest))
      --          = concat (inverse rest) (consLeft (-x) (consLeft x rest))
      -- By combine: ≈ concat (inverse rest) (consLeft ((-x) + x) rest)
      --            = concat (inverse rest) (consLeft 0 rest)
      -- By remove: ≈ concat (inverse rest) rest
      -- By ih: ≈ nil
      simp only [inverse]
      rw [concat_assoc]
      simp only [singleLeft, concat]
      -- Goal: FreeGroupEq (concat (inverse rest) (consLeft (-x) (consLeft x rest))) nil
      have h1 : FreeGroupEq (consLeft (-x) (consLeft x rest)) (consLeft ((-x) + x) rest) :=
        FreeGroupEq.combineLeft (-x) x rest
      have h2 : FreeGroupEq (concat (inverse rest) (consLeft (-x) (consLeft x rest)))
                            (concat (inverse rest) (consLeft ((-x) + x) rest)) :=
        concat_freeGroupEq_right _ h1
      apply FreeGroupEq.trans h2
      rw [haddG₁]
      have h3 : FreeGroupEq (consLeft 0 rest) rest := FreeGroupEq.removeLeftZero rest
      have h4 : FreeGroupEq (concat (inverse rest) (consLeft 0 rest))
                            (concat (inverse rest) rest) :=
        concat_freeGroupEq_right _ h3
      apply FreeGroupEq.trans h4
      exact ih
  | consRight y rest ih =>
      simp only [inverse]
      rw [concat_assoc]
      simp only [singleRight, concat]
      have h1 : FreeGroupEq (consRight (-y) (consRight y rest)) (consRight ((-y) + y) rest) :=
        FreeGroupEq.combineRight (-y) y rest
      have h2 : FreeGroupEq (concat (inverse rest) (consRight (-y) (consRight y rest)))
                            (concat (inverse rest) (consRight ((-y) + y) rest)) :=
        concat_freeGroupEq_right _ h1
      apply FreeGroupEq.trans h2
      rw [haddG₂]
      have h3 : FreeGroupEq (consRight 0 rest) rest := FreeGroupEq.removeRightZero rest
      have h4 : FreeGroupEq (concat (inverse rest) (consRight 0 rest))
                            (concat (inverse rest) rest) :=
        concat_freeGroupEq_right _ h3
      apply FreeGroupEq.trans h4
      exact ih

end FreeProductWord

/-! ## The Amalgamated Free Product

For the full SVK theorem, we need the amalgamated free product G₁ *_H G₂
where H maps into both G₁ and G₂.
-/

/-- Relations in the amalgamated free product.
Two words are related if they differ by the amalgamation relation:
for h : H, i₁(h) in G₁ equals i₂(h) in G₂. -/
inductive AmalgRelation {G₁ G₂ H : Type u}
    (i₁ : H → G₁) (i₂ : H → G₂) :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → Prop where
  /-- i₁(h) can be replaced by i₂(h). -/
  | amalgLeftToRight (h : H) (pre suf : FreeProductWord G₁ G₂) :
      AmalgRelation i₁ i₂
        (FreeProductWord.concat pre
          (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ h)) suf))
        (FreeProductWord.concat pre
          (FreeProductWord.concat (FreeProductWord.singleRight (i₂ h)) suf))
  /-- i₂(h) can be replaced by i₁(h). -/
  | amalgRightToLeft (h : H) (pre suf : FreeProductWord G₁ G₂) :
      AmalgRelation i₁ i₂
        (FreeProductWord.concat pre
          (FreeProductWord.concat (FreeProductWord.singleRight (i₂ h)) suf))
        (FreeProductWord.concat pre
          (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ h)) suf))

/-- The equivalence relation generated by amalgamation. -/
inductive AmalgEquiv {G₁ G₂ H : Type u} (i₁ : H → G₁) (i₂ : H → G₂) :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → Prop where
  | refl (w : FreeProductWord G₁ G₂) : AmalgEquiv i₁ i₂ w w
  | step {w₁ w₂ : FreeProductWord G₁ G₂} :
      AmalgRelation i₁ i₂ w₁ w₂ → AmalgEquiv i₁ i₂ w₁ w₂
  | symm {w₁ w₂ : FreeProductWord G₁ G₂} :
      AmalgEquiv i₁ i₂ w₁ w₂ → AmalgEquiv i₁ i₂ w₂ w₁
  | trans {w₁ w₂ w₃ : FreeProductWord G₁ G₂} :
      AmalgEquiv i₁ i₂ w₁ w₂ → AmalgEquiv i₁ i₂ w₂ w₃ → AmalgEquiv i₁ i₂ w₁ w₃

/-- The amalgamated free product G₁ *_H G₂ as a quotient. -/
noncomputable def AmalgamatedFreeProduct (G₁ G₂ H : Type u) (i₁ : H → G₁) (i₂ : H → G₂) : Type u :=
  Quot (AmalgEquiv i₁ i₂)

namespace AmalgamatedFreeProduct

variable {G₁ G₂ H : Type u} {i₁ : H → G₁} {i₂ : H → G₂}

/-- Embed a word into the amalgamated free product. -/
noncomputable def ofWord (w : FreeProductWord G₁ G₂) : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.mk _ w

/-- Identity element (empty word). -/
noncomputable def one : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ := ofWord .nil

/-- Embed an element of G₁. -/
noncomputable def inl (x : G₁) : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  ofWord (FreeProductWord.singleLeft x)

/-- Embed an element of G₂. -/
noncomputable def inr (y : G₂) : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  ofWord (FreeProductWord.singleRight y)

/-- The amalgamation: i₁(h) = i₂(h) in the product. -/
theorem amalgamate (h : H) :
    inl (i₁ h) = inr (i₂ h) (G₁ := G₁) (G₂ := G₂) (H := H) (i₁ := i₁) (i₂ := i₂) := by
  unfold inl inr ofWord
  apply Quot.sound
  apply AmalgEquiv.step
  have h1 : FreeProductWord.singleLeft (G₂ := G₂) (i₁ h) =
      FreeProductWord.concat (G₁ := G₁) (G₂ := G₂) .nil
        (FreeProductWord.concat (FreeProductWord.singleLeft (G₂ := G₂) (i₁ h))
          (FreeProductWord.nil (G₁ := G₁) (G₂ := G₂))) := by
    simp [FreeProductWord.concat, FreeProductWord.singleLeft]
  have h2 : FreeProductWord.singleRight (G₁ := G₁) (i₂ h) =
      FreeProductWord.concat (G₁ := G₁) (G₂ := G₂) .nil
        (FreeProductWord.concat (FreeProductWord.singleRight (G₁ := G₁) (i₂ h))
          (FreeProductWord.nil (G₁ := G₁) (G₂ := G₂))) := by
    simp [FreeProductWord.concat, FreeProductWord.singleRight]
  rw [h1, h2]
  exact AmalgRelation.amalgLeftToRight h
    (FreeProductWord.nil (G₁ := G₁) (G₂ := G₂))
    (FreeProductWord.nil (G₁ := G₁) (G₂ := G₂))

/-- Multiplication helper on words. -/
noncomputable def mulWord (w₁ w₂ : FreeProductWord G₁ G₂) : FreeProductWord G₁ G₂ :=
  FreeProductWord.concat w₁ w₂

/-- Concatenation respects the equivalence relation on the left. -/
theorem concat_respects_left (w₂ : FreeProductWord G₁ G₂) {w₁ w₁' : FreeProductWord G₁ G₂}
    (h : AmalgEquiv i₁ i₂ w₁ w₁') :
    AmalgEquiv i₁ i₂ (FreeProductWord.concat w₁ w₂) (FreeProductWord.concat w₁' w₂) := by
  induction h with
  | refl w => exact AmalgEquiv.refl _
  | step hr =>
      cases hr with
      | amalgLeftToRight h pre suf =>
          apply AmalgEquiv.step
          simp only [FreeProductWord.concat_assoc]
          exact AmalgRelation.amalgLeftToRight h pre (FreeProductWord.concat suf w₂)
      | amalgRightToLeft h pre suf =>
          apply AmalgEquiv.step
          simp only [FreeProductWord.concat_assoc]
          exact AmalgRelation.amalgRightToLeft h pre (FreeProductWord.concat suf w₂)
  | symm _ ih => exact AmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact AmalgEquiv.trans ih1 ih2

/-- Concatenation respects the equivalence relation on the right. -/
theorem concat_respects_right (w₁ : FreeProductWord G₁ G₂) {w₂ w₂' : FreeProductWord G₁ G₂}
    (h : AmalgEquiv i₁ i₂ w₂ w₂') :
    AmalgEquiv i₁ i₂ (FreeProductWord.concat w₁ w₂) (FreeProductWord.concat w₁ w₂') := by
  induction h with
  | refl w => exact AmalgEquiv.refl _
  | step hr =>
      cases hr with
      | amalgLeftToRight hh pre suf =>
          apply AmalgEquiv.step
          have : FreeProductWord.concat w₁ (FreeProductWord.concat pre
              (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ hh)) suf)) =
            FreeProductWord.concat (FreeProductWord.concat w₁ pre)
              (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ hh)) suf) := by
            simp [FreeProductWord.concat_assoc]
          have h2 : FreeProductWord.concat w₁ (FreeProductWord.concat pre
              (FreeProductWord.concat (FreeProductWord.singleRight (i₂ hh)) suf)) =
            FreeProductWord.concat (FreeProductWord.concat w₁ pre)
              (FreeProductWord.concat (FreeProductWord.singleRight (i₂ hh)) suf) := by
            simp [FreeProductWord.concat_assoc]
          rw [this, h2]
          exact AmalgRelation.amalgLeftToRight hh (FreeProductWord.concat w₁ pre) suf
      | amalgRightToLeft hh pre suf =>
          apply AmalgEquiv.step
          have : FreeProductWord.concat w₁ (FreeProductWord.concat pre
              (FreeProductWord.concat (FreeProductWord.singleRight (i₂ hh)) suf)) =
            FreeProductWord.concat (FreeProductWord.concat w₁ pre)
              (FreeProductWord.concat (FreeProductWord.singleRight (i₂ hh)) suf) := by
            simp [FreeProductWord.concat_assoc]
          have h2 : FreeProductWord.concat w₁ (FreeProductWord.concat pre
              (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ hh)) suf)) =
            FreeProductWord.concat (FreeProductWord.concat w₁ pre)
              (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ hh)) suf) := by
            simp [FreeProductWord.concat_assoc]
          rw [this, h2]
          exact AmalgRelation.amalgRightToLeft hh (FreeProductWord.concat w₁ pre) suf
  | symm _ ih => exact AmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact AmalgEquiv.trans ih1 ih2

/-- Multiplication helper: multiply a word on the right. -/
noncomputable def mulWordRight (w₂ : FreeProductWord G₁ G₂) :
    AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ → AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w₁ => ofWord (FreeProductWord.concat w₁ w₂))
    (fun _ _ h => Quot.sound (concat_respects_left w₂ h))

/-- Multiplication in the amalgamated free product. -/
noncomputable def mul (x y : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w₂ => mulWordRight w₂ x)
    (fun w₂ w₂' h => by
      induction x using Quot.ind with
      | _ w₁ =>
        unfold mulWordRight
        apply Quot.sound
        exact concat_respects_right w₁ h)
    y

noncomputable instance : Mul (AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨mul⟩
noncomputable instance : One (AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨one⟩

@[simp] theorem one_mul' (x : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) : mul one x = x := by
  induction x using Quot.ind with
  | _ w =>
    show mul one (Quot.mk _ w) = Quot.mk _ w
    rfl

@[simp] theorem mul_one' (x : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) : mul x one = x := by
  induction x using Quot.ind with
  | _ w =>
    show mul (Quot.mk _ w) one = Quot.mk _ w
    simp only [mul, one, ofWord, mulWordRight, FreeProductWord.concat_nil_right]

theorem mul_assoc' (x y z : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    mul (mul x y) z = mul x (mul y z) := by
  induction x using Quot.ind with
  | _ w₁ =>
    induction y using Quot.ind with
    | _ w₂ =>
      induction z using Quot.ind with
      | _ w₃ =>
        show mul (mul (Quot.mk _ w₁) (Quot.mk _ w₂)) (Quot.mk _ w₃) =
             mul (Quot.mk _ w₁) (mul (Quot.mk _ w₂) (Quot.mk _ w₃))
        simp only [mul, ofWord, mulWordRight, FreeProductWord.concat_assoc]

/-! ### Inverse Operation -/

/-- Inverse respects the amalgamation relation.
If `w₁ ≈ w₂` via amalgamation, then `inverse w₁ ≈ inverse w₂`.

This requires that the amalgamation maps commute with negation:
`-i₁(h) = i₁(-h)` and `-i₂(h) = i₂(-h)`. This is automatic for group homomorphisms. -/
theorem inverse_respects_amalg [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))  -- i₁ commutes with negation
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h))  -- i₂ commutes with negation
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : AmalgEquiv i₁ i₂ w₁ w₂) :
    AmalgEquiv i₁ i₂ (FreeProductWord.inverse w₁) (FreeProductWord.inverse w₂) := by
  induction h with
  | refl _ => exact AmalgEquiv.refl _
  | step hr =>
      cases hr with
      | amalgLeftToRight hh pre suf =>
          -- inverse (concat pre (concat (singleLeft (i₁ hh)) suf))
          -- = concat (concat (inverse suf) (singleLeft (-(i₁ hh)))) (inverse pre)
          -- We need to show this ≈ concat (concat (inverse suf) (singleRight (-(i₂ hh)))) (inverse pre)
          simp only [FreeProductWord.inverse_concat]
          -- Use associativity to restructure: (A · B) · C = A · (B · C)
          have assoc1 : FreeProductWord.concat
              (FreeProductWord.concat (FreeProductWord.inverse suf)
                (FreeProductWord.inverse (FreeProductWord.singleLeft (i₁ hh))))
              (FreeProductWord.inverse pre) =
            FreeProductWord.concat (FreeProductWord.inverse suf)
              (FreeProductWord.concat
                (FreeProductWord.inverse (FreeProductWord.singleLeft (i₁ hh)))
                (FreeProductWord.inverse pre)) := by
            simp [FreeProductWord.concat_assoc]
          have assoc2 : FreeProductWord.concat
              (FreeProductWord.concat (FreeProductWord.inverse suf)
                (FreeProductWord.inverse (FreeProductWord.singleRight (i₂ hh))))
              (FreeProductWord.inverse pre) =
            FreeProductWord.concat (FreeProductWord.inverse suf)
              (FreeProductWord.concat
                (FreeProductWord.inverse (FreeProductWord.singleRight (i₂ hh)))
                (FreeProductWord.inverse pre)) := by
            simp [FreeProductWord.concat_assoc]
          rw [assoc1, assoc2]
          apply concat_respects_right
          apply concat_respects_left
          simp only [FreeProductWord.inverse_singleLeft, FreeProductWord.inverse_singleRight]
          rw [hi₁ hh, hi₂ hh]
          apply AmalgEquiv.step
          -- Goal: AmalgRelation ... (singleLeft (i₁ (-hh))) (singleRight (i₂ (-hh)))
          have h1 : (FreeProductWord.singleLeft (i₁ (-hh)) : FreeProductWord G₁ G₂) =
              FreeProductWord.concat (FreeProductWord.nil : FreeProductWord G₁ G₂)
                (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ (-hh)))
                  (FreeProductWord.nil : FreeProductWord G₁ G₂)) := rfl
          have h2 : (FreeProductWord.singleRight (i₂ (-hh)) : FreeProductWord G₁ G₂) =
              FreeProductWord.concat (FreeProductWord.nil : FreeProductWord G₁ G₂)
                (FreeProductWord.concat (FreeProductWord.singleRight (i₂ (-hh)))
                  (FreeProductWord.nil : FreeProductWord G₁ G₂)) := rfl
          rw [h1, h2]
          exact AmalgRelation.amalgLeftToRight (-hh)
            (FreeProductWord.nil : FreeProductWord G₁ G₂)
            (FreeProductWord.nil : FreeProductWord G₁ G₂)
      | amalgRightToLeft hh pre suf =>
          simp only [FreeProductWord.inverse_concat]
          have assoc1 : FreeProductWord.concat
              (FreeProductWord.concat (FreeProductWord.inverse suf)
                (FreeProductWord.inverse (FreeProductWord.singleRight (i₂ hh))))
              (FreeProductWord.inverse pre) =
            FreeProductWord.concat (FreeProductWord.inverse suf)
              (FreeProductWord.concat
                (FreeProductWord.inverse (FreeProductWord.singleRight (i₂ hh)))
                (FreeProductWord.inverse pre)) := by
            simp [FreeProductWord.concat_assoc]
          have assoc2 : FreeProductWord.concat
              (FreeProductWord.concat (FreeProductWord.inverse suf)
                (FreeProductWord.inverse (FreeProductWord.singleLeft (i₁ hh))))
              (FreeProductWord.inverse pre) =
            FreeProductWord.concat (FreeProductWord.inverse suf)
              (FreeProductWord.concat
                (FreeProductWord.inverse (FreeProductWord.singleLeft (i₁ hh)))
                (FreeProductWord.inverse pre)) := by
            simp [FreeProductWord.concat_assoc]
          rw [assoc1, assoc2]
          apply concat_respects_right
          apply concat_respects_left
          simp only [FreeProductWord.inverse_singleLeft, FreeProductWord.inverse_singleRight]
          rw [hi₁ hh, hi₂ hh]
          apply AmalgEquiv.step
          have h1 : (FreeProductWord.singleRight (i₂ (-hh)) : FreeProductWord G₁ G₂) =
              FreeProductWord.concat (FreeProductWord.nil : FreeProductWord G₁ G₂)
                (FreeProductWord.concat (FreeProductWord.singleRight (i₂ (-hh)))
                  (FreeProductWord.nil : FreeProductWord G₁ G₂)) := rfl
          have h2 : (FreeProductWord.singleLeft (i₁ (-hh)) : FreeProductWord G₁ G₂) =
              FreeProductWord.concat (FreeProductWord.nil : FreeProductWord G₁ G₂)
                (FreeProductWord.concat (FreeProductWord.singleLeft (i₁ (-hh)))
                  (FreeProductWord.nil : FreeProductWord G₁ G₂)) := rfl
          rw [h1, h2]
          exact AmalgRelation.amalgRightToLeft (-hh)
            (FreeProductWord.nil : FreeProductWord G₁ G₂)
            (FreeProductWord.nil : FreeProductWord G₁ G₂)
  | symm _ ih => exact AmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact AmalgEquiv.trans ih1 ih2

/-- Inverse operation on the amalgamated free product.
Requires that the amalgamation maps commute with negation. -/
noncomputable def inv [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h))
    (x : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w => ofWord (FreeProductWord.inverse w))
    (fun _ _ h => Quot.sound (inverse_respects_amalg hi₁ hi₂ h))
    x

/-- Inverse of identity is identity. -/
@[simp] theorem inv_one [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h)) :
    inv hi₁ hi₂ (one : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) = one := by
  simp only [inv, one, ofWord, FreeProductWord.inverse_nil]

/-- Inverse distributes over multiplication (in reverse order). -/
theorem inv_mul [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h))
    (x y : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    inv hi₁ hi₂ (mul x y) = mul (inv hi₁ hi₂ y) (inv hi₁ hi₂ x) := by
  induction x using Quot.ind with
  | _ _w₁ =>
    induction y using Quot.ind with
    | _ _w₂ =>
      simp only [inv, mul, ofWord, mulWordRight, FreeProductWord.inverse_concat]

end AmalgamatedFreeProduct

/-! ## Full Amalgamated Free Product with Group Laws

For the group laws (mul_inv_cancel, inv_mul_cancel) to hold, we need to
quotient by both the amalgamation relation AND the free group reduction relation.
-/

/-- Combined equivalence relation including both amalgamation and free group reduction.
This is the proper equivalence for free products of groups. -/
inductive FullAmalgEquiv {G₁ G₂ H : Type u} [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    (i₁ : H → G₁) (i₂ : H → G₂) :
    FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → Prop where
  | refl (w : FreeProductWord G₁ G₂) : FullAmalgEquiv i₁ i₂ w w
  | amalg {w₁ w₂ : FreeProductWord G₁ G₂} :
      AmalgRelation i₁ i₂ w₁ w₂ → FullAmalgEquiv i₁ i₂ w₁ w₂
  | freeGroup {w₁ w₂ : FreeProductWord G₁ G₂} :
      FreeProductWord.FreeGroupStep w₁ w₂ → FullAmalgEquiv i₁ i₂ w₁ w₂
  | symm {w₁ w₂ : FreeProductWord G₁ G₂} :
      FullAmalgEquiv i₁ i₂ w₁ w₂ → FullAmalgEquiv i₁ i₂ w₂ w₁
  | trans {w₁ w₂ w₃ : FreeProductWord G₁ G₂} :
      FullAmalgEquiv i₁ i₂ w₁ w₂ → FullAmalgEquiv i₁ i₂ w₂ w₃ → FullAmalgEquiv i₁ i₂ w₁ w₃

namespace FullAmalgEquiv

variable {G₁ G₂ H : Type u} [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
variable {i₁ : H → G₁} {i₂ : H → G₂}

/-- AmalgEquiv implies FullAmalgEquiv. -/
theorem of_amalgEquiv {w₁ w₂ : FreeProductWord G₁ G₂} (h : AmalgEquiv i₁ i₂ w₁ w₂) :
    FullAmalgEquiv i₁ i₂ w₁ w₂ := by
  induction h with
  | refl _ => exact FullAmalgEquiv.refl _
  | step hr => exact FullAmalgEquiv.amalg hr
  | symm _ ih => exact FullAmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FullAmalgEquiv.trans ih1 ih2

/-- FreeGroupEq implies FullAmalgEquiv. -/
theorem of_freeGroupEq {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : FreeProductWord.FreeGroupEq w₁ w₂) :
    FullAmalgEquiv i₁ i₂ w₁ w₂ := by
  induction h with
  | refl _ => exact FullAmalgEquiv.refl _
  | step hs => exact FullAmalgEquiv.freeGroup hs
  | symm _ ih => exact FullAmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FullAmalgEquiv.trans ih1 ih2

end FullAmalgEquiv

/-- The full amalgamated free product with group structure.
Quotiented by both amalgamation and free group reduction. -/
noncomputable def FullAmalgamatedFreeProduct (G₁ G₂ H : Type u) [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    (i₁ : H → G₁) (i₂ : H → G₂) : Type u :=
  Quot (FullAmalgEquiv i₁ i₂)

namespace FullAmalgamatedFreeProduct

variable {G₁ G₂ H : Type u} [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
variable {i₁ : H → G₁} {i₂ : H → G₂}

/-- Embed a word into the full amalgamated free product. -/
noncomputable def ofWord (w : FreeProductWord G₁ G₂) : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.mk _ w

/-- Identity element (empty word). -/
noncomputable def one : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ := ofWord .nil

/-- Concatenation respects the full equivalence relation on the left. -/
theorem concat_respects_left (w₂ : FreeProductWord G₁ G₂) {w₁ w₁' : FreeProductWord G₁ G₂}
    (h : FullAmalgEquiv i₁ i₂ w₁ w₁') :
    FullAmalgEquiv i₁ i₂ (FreeProductWord.concat w₁ w₂) (FreeProductWord.concat w₁' w₂) := by
  induction h with
  | refl _ => exact FullAmalgEquiv.refl _
  | amalg hr =>
      cases hr with
      | amalgLeftToRight hh pre suf =>
          apply FullAmalgEquiv.amalg
          simp only [FreeProductWord.concat_assoc]
          exact AmalgRelation.amalgLeftToRight hh pre (FreeProductWord.concat suf w₂)
      | amalgRightToLeft hh pre suf =>
          apply FullAmalgEquiv.amalg
          simp only [FreeProductWord.concat_assoc]
          exact AmalgRelation.amalgRightToLeft hh pre (FreeProductWord.concat suf w₂)
  | freeGroup hs =>
      exact FullAmalgEquiv.of_freeGroupEq (FreeProductWord.freeGroupStep_concat_left w₂ hs)
  | symm _ ih => exact FullAmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FullAmalgEquiv.trans ih1 ih2

/-- Concatenation respects the full equivalence relation on the right. -/
theorem concat_respects_right (w₁ : FreeProductWord G₁ G₂) {w₂ w₂' : FreeProductWord G₁ G₂}
    (h : FullAmalgEquiv i₁ i₂ w₂ w₂') :
    FullAmalgEquiv i₁ i₂ (FreeProductWord.concat w₁ w₂) (FreeProductWord.concat w₁ w₂') := by
  induction h with
  | refl _ => exact FullAmalgEquiv.refl _
  | amalg hr =>
      cases hr with
      | amalgLeftToRight hh pre suf =>
          apply FullAmalgEquiv.amalg
          -- Goal: concat w₁ (concat pre (concat (singleLeft ..) suf)) ≈
          --       concat w₁ (concat pre (concat (singleRight ..) suf))
          -- Use associativity: concat w₁ (concat pre x) = concat (concat w₁ pre) x
          rw [← FreeProductWord.concat_assoc w₁ pre, ← FreeProductWord.concat_assoc w₁ pre]
          exact AmalgRelation.amalgLeftToRight hh (FreeProductWord.concat w₁ pre) suf
      | amalgRightToLeft hh pre suf =>
          apply FullAmalgEquiv.amalg
          rw [← FreeProductWord.concat_assoc w₁ pre, ← FreeProductWord.concat_assoc w₁ pre]
          exact AmalgRelation.amalgRightToLeft hh (FreeProductWord.concat w₁ pre) suf
  | freeGroup hs =>
      -- Use the existing concat_freeGroupEq_right lemma
      exact FullAmalgEquiv.of_freeGroupEq (FreeProductWord.concat_freeGroupEq_right w₁ (FreeProductWord.FreeGroupEq.step hs))
  | symm _ ih => exact FullAmalgEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FullAmalgEquiv.trans ih1 ih2

/-- Multiplication helper: multiply a word on the right. -/
noncomputable def mulWordRight (w₂ : FreeProductWord G₁ G₂) :
    FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ → FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w₁ => ofWord (FreeProductWord.concat w₁ w₂))
    (fun _ _ h => Quot.sound (concat_respects_left w₂ h))

/-- Multiplication in the full amalgamated free product. -/
noncomputable def mul (x y : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w₂ => mulWordRight w₂ x)
    (fun w₂ w₂' h => by
      induction x using Quot.ind with
      | _ w₁ =>
        unfold mulWordRight
        apply Quot.sound
        exact concat_respects_right w₁ h)
    y

noncomputable instance : Mul (FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨mul⟩
noncomputable instance : One (FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨one⟩

@[simp] theorem one_mul' (x : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) : mul one x = x := by
  induction x using Quot.ind with
  | _ w => rfl

@[simp] theorem mul_one' (x : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) : mul x one = x := by
  induction x using Quot.ind with
  | _ w =>
    simp only [mul, one, ofWord, mulWordRight, FreeProductWord.concat_nil_right]

theorem mul_assoc' (x y z : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    mul (mul x y) z = mul x (mul y z) := by
  induction x using Quot.ind with
  | _ w₁ =>
    induction y using Quot.ind with
    | _ w₂ =>
      induction z using Quot.ind with
      | _ w₃ =>
        simp only [mul, ofWord, mulWordRight, FreeProductWord.concat_assoc]

/-- Inverse operation on the full amalgamated free product.
Requires group laws for negation:
- Negation commutes with i₁, i₂
- Negation anti-distributes over addition: -(x + y) = (-y) + (-x)
- Negation of zero is zero -/
noncomputable def inv [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h))
    (hnegG₁ : ∀ x y : G₁, -(x + y) = (-y) + (-x))
    (hnegG₂ : ∀ x y : G₂, -(x + y) = (-y) + (-x))
    (hnegZeroG₁ : -(0 : G₁) = 0)
    (hnegZeroG₂ : -(0 : G₂) = 0)
    (x : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w => ofWord (FreeProductWord.inverse w))
    (fun w₁ w₂ h => by
      apply Quot.sound
      induction h with
      | refl _ => exact FullAmalgEquiv.refl _
      | amalg hr =>
          exact FullAmalgEquiv.of_amalgEquiv (AmalgamatedFreeProduct.inverse_respects_amalg hi₁ hi₂ (AmalgEquiv.step hr))
      | freeGroup hs =>
          exact FullAmalgEquiv.of_freeGroupEq (FreeProductWord.inverse_freeGroupStep hnegG₁ hnegG₂ hnegZeroG₁ hnegZeroG₂ hs)
      | symm _ ih => exact FullAmalgEquiv.symm ih
      | trans _ _ ih1 ih2 => exact FullAmalgEquiv.trans ih1 ih2)
    x

/-! ### Group Laws -/

/-- **Left cancellation law**: x * inv(x) = one.
This is the key group law showing that inverse is a right inverse. -/
theorem mul_inv_cancel [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h))
    (hnegG₁ : ∀ x y : G₁, -(x + y) = (-y) + (-x))
    (hnegG₂ : ∀ x y : G₂, -(x + y) = (-y) + (-x))
    (hnegZeroG₁ : -(0 : G₁) = 0)
    (hnegZeroG₂ : -(0 : G₂) = 0)
    (haddG₁ : ∀ x : G₁, x + (-x) = 0)
    (haddG₂ : ∀ y : G₂, y + (-y) = 0)
    (x : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    mul x (inv hi₁ hi₂ hnegG₁ hnegG₂ hnegZeroG₁ hnegZeroG₂ x) = one := by
  induction x using Quot.ind with
  | _ w =>
    simp only [mul, inv, one, ofWord, mulWordRight]
    apply Quot.sound
    exact FullAmalgEquiv.of_freeGroupEq (FreeProductWord.concat_inverse_nil haddG₁ haddG₂ w)

/-- **Right cancellation law**: inv(x) * x = one.
This is the key group law showing that inverse is a left inverse. -/
theorem inv_mul_cancel [Neg G₁] [Neg G₂] [Neg H]
    (hi₁ : ∀ h : H, -(i₁ h) = i₁ (-h))
    (hi₂ : ∀ h : H, -(i₂ h) = i₂ (-h))
    (hnegG₁ : ∀ x y : G₁, -(x + y) = (-y) + (-x))
    (hnegG₂ : ∀ x y : G₂, -(x + y) = (-y) + (-x))
    (hnegZeroG₁ : -(0 : G₁) = 0)
    (hnegZeroG₂ : -(0 : G₂) = 0)
    (haddG₁ : ∀ x : G₁, (-x) + x = 0)
    (haddG₂ : ∀ y : G₂, (-y) + y = 0)
    (x : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
    mul (inv hi₁ hi₂ hnegG₁ hnegG₂ hnegZeroG₁ hnegZeroG₂ x) x = one := by
  induction x using Quot.ind with
  | _ w =>
    simp only [mul, inv, one, ofWord, mulWordRight]
    apply Quot.sound
    exact FullAmalgEquiv.of_freeGroupEq (FreeProductWord.inverse_concat_nil haddG₁ haddG₂ w)

end FullAmalgamatedFreeProduct

/-! ## Universal Property of Free Products

The free product G₁ * G₂ satisfies a universal property: for any group H with
homomorphisms φ₁ : G₁ → H and φ₂ : G₂ → H, there exists a unique homomorphism
φ : G₁ * G₂ → H such that φ ∘ inl = φ₁ and φ ∘ inr = φ₂.

We formalize this using FreeProductWord with the appropriate quotient.
-/

namespace FreeProductUniversal

variable {G₁ G₂ H : Type u}

/-- Lift a pair of functions to a function on free product words.
This is the "word extension" that applies φ₁ to left letters and φ₂ to right letters,
then combines the results using the group operation in H. -/
noncomputable def wordLift [One H] [Mul H] (φ₁ : G₁ → H) (φ₂ : G₂ → H) :
    FreeProductWord G₁ G₂ → H
  | .nil => 1
  | .consLeft x rest => φ₁ x * wordLift φ₁ φ₂ rest
  | .consRight y rest => φ₂ y * wordLift φ₁ φ₂ rest

/-- wordLift on nil gives the identity. -/
@[simp] theorem wordLift_nil [One H] [Mul H] (φ₁ : G₁ → H) (φ₂ : G₂ → H) :
    wordLift φ₁ φ₂ .nil = 1 := rfl

/-- wordLift on consLeft. -/
@[simp] theorem wordLift_consLeft [One H] [Mul H] (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (x : G₁) (rest : FreeProductWord G₁ G₂) :
    wordLift φ₁ φ₂ (.consLeft x rest) = φ₁ x * wordLift φ₁ φ₂ rest := rfl

/-- wordLift on consRight. -/
@[simp] theorem wordLift_consRight [One H] [Mul H] (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (y : G₂) (rest : FreeProductWord G₁ G₂) :
    wordLift φ₁ φ₂ (.consRight y rest) = φ₂ y * wordLift φ₁ φ₂ rest := rfl

/-- wordLift respects concatenation when H has One and associative Mul with left identity. -/
theorem wordLift_concat [One H] [Mul H]
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (w₁ w₂ : FreeProductWord G₁ G₂) :
    wordLift φ₁ φ₂ (FreeProductWord.concat w₁ w₂) =
    wordLift φ₁ φ₂ w₁ * wordLift φ₁ φ₂ w₂ := by
  induction w₁ with
  | nil =>
      simp only [FreeProductWord.concat, wordLift_nil]
      exact (hone_mul _).symm
  | consLeft x rest ih =>
      simp only [FreeProductWord.concat, wordLift_consLeft, ih]
      exact (hmul_assoc _ _ _).symm
  | consRight y rest ih =>
      simp only [FreeProductWord.concat, wordLift_consRight, ih]
      exact (hmul_assoc _ _ _).symm

/-- wordLift sends singleLeft to φ₁. -/
@[simp] theorem wordLift_singleLeft [One H] [Mul H]
    (hmul_one : ∀ x : H, x * 1 = x)
    (φ₁ : G₁ → H) (φ₂ : G₂ → H) (x : G₁) :
    wordLift φ₁ φ₂ (FreeProductWord.singleLeft x) = φ₁ x := by
  simp only [FreeProductWord.singleLeft, wordLift_consLeft, wordLift_nil]
  exact hmul_one _

/-- wordLift sends singleRight to φ₂. -/
@[simp] theorem wordLift_singleRight [One H] [Mul H]
    (hmul_one : ∀ x : H, x * 1 = x)
    (φ₁ : G₁ → H) (φ₂ : G₂ → H) (y : G₂) :
    wordLift φ₁ φ₂ (FreeProductWord.singleRight y) = φ₂ y := by
  simp only [FreeProductWord.singleRight, wordLift_consRight, wordLift_nil]
  exact hmul_one _

/-- wordLift respects FreeGroupStep when φ₁, φ₂ preserve additive structure.
This requires that φ₁(x + y) = φ₁(x) * φ₁(y) and φ₁(0) = 1, etc. -/
theorem wordLift_respects_freeGroupStep [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    [One H] [Mul H]
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : FreeProductWord.FreeGroupStep w₁ w₂) :
    wordLift φ₁ φ₂ w₁ = wordLift φ₁ φ₂ w₂ := by
  induction h with
  | combineLeft x y rest =>
      simp only [wordLift_consLeft, hφ₁_add]
      exact (hmul_assoc _ _ _).symm
  | combineRight x y rest =>
      simp only [wordLift_consRight, hφ₂_add]
      exact (hmul_assoc _ _ _).symm
  | removeLeftZero rest =>
      simp only [wordLift_consLeft, hφ₁_zero]
      exact hone_mul _
  | removeRightZero rest =>
      simp only [wordLift_consRight, hφ₂_zero]
      exact hone_mul _
  | congrLeft x _ ih =>
      simp only [wordLift_consLeft, ih]
  | congrRight y _ ih =>
      simp only [wordLift_consRight, ih]

/-- wordLift respects FreeGroupEq when φ₁, φ₂ preserve additive structure. -/
theorem wordLift_respects_freeGroupEq [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    [One H] [Mul H]
    (hone_mul : ∀ x : H, 1 * x = x)
    (hmul_assoc : ∀ x y z : H, (x * y) * z = x * (y * z))
    (φ₁ : G₁ → H) (φ₂ : G₂ → H)
    (hφ₁_add : ∀ x y, φ₁ (x + y) = φ₁ x * φ₁ y)
    (hφ₂_add : ∀ x y, φ₂ (x + y) = φ₂ x * φ₂ y)
    (hφ₁_zero : φ₁ 0 = 1)
    (hφ₂_zero : φ₂ 0 = 1)
    {w₁ w₂ : FreeProductWord G₁ G₂}
    (h : FreeProductWord.FreeGroupEq w₁ w₂) :
    wordLift φ₁ φ₂ w₁ = wordLift φ₁ φ₂ w₂ := by
  induction h with
  | refl _ => rfl
  | step hs =>
      exact wordLift_respects_freeGroupStep hone_mul hmul_assoc φ₁ φ₂
        hφ₁_add hφ₂_add hφ₁_zero hφ₂_zero hs
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

end FreeProductUniversal

/-! ## Free Group on Generators (via Free Products)

The free group F_n on n generators can be represented as a special case
of free products. F₁ ≃ ℤ, and F₂ = ℤ * ℤ.

For a general free group on a type of generators, we use words where
each generator and its inverse can appear. This is distinct from the
surface-specific free-group encodings used in older developments.
-/

/-- The free group on a type of generators α, as a free product.
Elements are represented as words with positive (Left) and inverse (Right) generators.
This is an alias for FreeProductWord α α. -/
noncomputable def GeneratorWord (α : Type u) : Type u := FreeProductWord α α

namespace GeneratorWord

variable {α : Type u}

/-- Empty word (identity element). -/
noncomputable def nil : GeneratorWord α := FreeProductWord.nil

/-- A positive generator (g⁺). -/
noncomputable def gen (a : α) : GeneratorWord α := FreeProductWord.singleLeft a

/-- An inverse generator (g⁻¹). -/
noncomputable def genInv (a : α) : GeneratorWord α := FreeProductWord.singleRight a

/-- Concatenation of free group words. -/
noncomputable def mul (w₁ w₂ : GeneratorWord α) : GeneratorWord α :=
  FreeProductWord.concat w₁ w₂

/-- Length of a word. -/
noncomputable def length : GeneratorWord α → Nat := FreeProductWord.length

/-- The word for a⁺ ⋅ a⁻¹. -/
noncomputable def genTimesGenInv (a : α) : GeneratorWord α :=
  mul (gen a) (genInv a)

/-- The word for a⁻¹ ⋅ a⁺. -/
noncomputable def genInvTimesGen (a : α) : GeneratorWord α :=
  mul (genInv a) (gen a)

noncomputable instance : One (GeneratorWord α) := ⟨nil⟩
noncomputable instance : Mul (GeneratorWord α) := ⟨mul⟩

@[simp] theorem one_def : (1 : GeneratorWord α) = nil := rfl
@[simp] theorem mul_def (w₁ w₂ : GeneratorWord α) : w₁ * w₂ = mul w₁ w₂ := rfl

@[simp] theorem one_mul (w : GeneratorWord α) : 1 * w = w := rfl

@[simp] theorem mul_one (w : GeneratorWord α) : w * 1 = w :=
  FreeProductWord.concat_nil_right w

theorem mul_assoc (w₁ w₂ w₃ : GeneratorWord α) : (w₁ * w₂) * w₃ = w₁ * (w₂ * w₃) := by
  simp only [mul_def, mul, FreeProductWord.concat_assoc]

/-- The free group on one generator is isomorphic to ℤ.
We represent this via GeneratorWord Unit. -/
abbrev FreeGroupOne := GeneratorWord Unit

/-- The free group on two generators.
We represent this via GeneratorWord Bool. -/
abbrev FreeGroupTwo := GeneratorWord Bool

/-- Generator a in F₂. -/
noncomputable def genA : FreeGroupTwo := gen false

/-- Generator b in F₂. -/
noncomputable def genB : FreeGroupTwo := gen true

/-- Inverse of generator a in F₂. -/
noncomputable def genAInv : FreeGroupTwo := genInv false

/-- Inverse of generator b in F₂. -/
noncomputable def genBInv : FreeGroupTwo := genInv true

/-- The word aba⁻¹b⁻¹ (commutator) in F₂. -/
noncomputable def commutator : FreeGroupTwo :=
  genA * genB * genAInv * genBInv

/-- The commutator has length 4. -/
theorem commutator_length : commutator.length = 4 := rfl

end GeneratorWord

/-! ## Free Group F₁ ≃ ℤ

The free group on one generator is isomorphic to the integers.
A word in F₁ can be "evaluated" to an integer by summing:
- +1 for each positive occurrence of the generator
- -1 for each inverse occurrence
-/

namespace FreeGroupOne

/-- Evaluate a word in F₁ to an integer (winding number). -/
noncomputable def toInt : GeneratorWord.FreeGroupOne → Int
  | .nil => 0
  | .consLeft () rest => 1 + toInt rest
  | .consRight () rest => -1 + toInt rest

/-- Convert a natural number to a word in F₁ (positive powers of the generator). -/
noncomputable def ofNat : Nat → GeneratorWord.FreeGroupOne
  | 0 => .nil
  | n + 1 => .consLeft () (ofNat n)

/-- ofInt for negative integers. -/
noncomputable def ofNegNat : Nat → GeneratorWord.FreeGroupOne
  | 0 => .nil
  | n + 1 => .consRight () (ofNegNat n)

/-- toInt of the generator is 1. -/
@[simp] theorem toInt_gen : toInt (GeneratorWord.gen ()) = 1 := by
  simp [GeneratorWord.gen, FreeProductWord.singleLeft, toInt]

/-- toInt of the inverse generator is -1. -/
@[simp] theorem toInt_genInv : toInt (GeneratorWord.genInv ()) = -1 := by
  simp [GeneratorWord.genInv, FreeProductWord.singleRight, toInt]

/-- Helper: toInt is additive with respect to FreeProductWord.concat. -/
theorem toInt_concat (w₁ w₂ : GeneratorWord.FreeGroupOne) :
    toInt (FreeProductWord.concat w₁ w₂) = toInt w₁ + toInt w₂ := by
  induction w₁ with
  | nil => simp [FreeProductWord.concat, toInt]
  | consLeft x rest ih =>
      simp only [FreeProductWord.concat, toInt]
      rw [ih, Int.add_assoc]
  | consRight y rest ih =>
      simp only [FreeProductWord.concat, toInt]
      rw [ih, Int.add_assoc]

/-- toInt is additive with respect to multiplication. -/
theorem toInt_mul (w₁ w₂ : GeneratorWord.FreeGroupOne) :
    toInt (w₁ * w₂) = toInt w₁ + toInt w₂ :=
  toInt_concat w₁ w₂

/-- toInt of ofNat n is n. -/
theorem toInt_ofNat (n : Nat) : toInt (ofNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ofNat, toInt]
      rw [ih]
      -- 1 + n = n + 1
      exact Int.add_comm 1 n

/-- toInt of ofNegNat n is -n. -/
theorem toInt_ofNegNat (n : Nat) : toInt (ofNegNat n) = -n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [ofNegNat, toInt]
      rw [ih]
      -- -1 + -n = -(n + 1)
      rw [← Int.neg_add, Int.add_comm]
      rfl

end FreeGroupOne

/-! ## Wedge Sum Loops

For the wedge sum A ∨ B (pushout of A ← pt → B), the fundamental group
is the free product π₁(A) * π₁(B) (no amalgamation since π₁(pt) is trivial).
-/

section WedgeLoops

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

/-- Loop code for the wedge sum: words in the free product of loop spaces. -/
abbrev WedgeLoopCode : Type u :=
  FreeProductWord (LoopSpace A a₀) (LoopSpace B b₀)

/-- The decode function: convert a word to a loop in the wedge.
Each letter becomes a loop, composed in sequence. -/
noncomputable def wedgeDecode :
    WedgeLoopCode a₀ b₀ → LoopSpace (Wedge A B a₀ b₀) (Wedge.basepoint)
  | .nil => Path.refl _
  | .consLeft p rest =>
      -- p is a loop in A at a₀
      Path.trans (Pushout.inlPath (A := A) (B := B) (C := PUnit')
        (f := fun _ => a₀) (g := fun _ => b₀) p)
        (wedgeDecode rest)
  | .consRight q rest =>
      -- q is a loop in B at b₀
      -- Go to inr b₀ via glue, do the loop, come back
      Path.trans
        (Path.trans
          (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
          (Path.trans (Pushout.inrPath (A := A) (B := B) (C := PUnit')
            (f := fun _ => a₀) (g := fun _ => b₀) q)
            (Path.symm (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)))))
        (wedgeDecode rest)

/-- Decode respects word concatenation. -/
noncomputable def wedgeDecode_concat (w₁ w₂ : WedgeLoopCode a₀ b₀) :
    RwEq (wedgeDecode a₀ b₀ (FreeProductWord.concat w₁ w₂))
         (Path.trans (wedgeDecode a₀ b₀ w₁) (wedgeDecode a₀ b₀ w₂)) := by
  induction w₁ with
  | nil =>
      -- concat nil w₂ = w₂, wedgeDecode nil = refl
      -- Need: RwEq (wedgeDecode w₂) (Path.trans (Path.refl _) (wedgeDecode w₂))
      simp only [FreeProductWord.concat, wedgeDecode]
      exact rweq_symm (rweq_cmpA_refl_left _)
  | consLeft p rest ih =>
      -- concat (consLeft p rest) w₂ = consLeft p (concat rest w₂)
      -- wedgeDecode (consLeft p (concat rest w₂)) = trans (inlPath p) (wedgeDecode (concat rest w₂))
      simp only [FreeProductWord.concat, wedgeDecode]
      -- By ih: RwEq (wedgeDecode (concat rest w₂)) (trans (wedgeDecode rest) (wedgeDecode w₂))
      -- We have: trans (inlPath p) (wedgeDecode (concat rest w₂))
      -- Want:    trans (trans (inlPath p) (wedgeDecode rest)) (wedgeDecode w₂)
      apply rweq_trans
        (rweq_trans_congr_right
          (Pushout.inlPath (A := A) (B := B) (C := PUnit')
            (f := fun _ => a₀) (g := fun _ => b₀) p) ih)
      exact rweq_symm (rweq_tt _ _ _)
  | consRight q rest ih =>
      simp only [FreeProductWord.concat, wedgeDecode]
      -- Similar: use ih and associativity
      apply rweq_trans (rweq_trans_congr_right _ ih)
      exact rweq_symm (rweq_tt _ _ _)

end WedgeLoops

/-! ## Fundamental Group Multiplication Helper

Helper for multiplying fundamental group elements. This is used throughout
the encode-decode machinery for both the general SVK theorem and the wedge sum case.
-/

/-- Helper: multiply two fundamental group elements (via Path.trans). -/
noncomputable def piOneMul {X : Type u} {x₀ : X} (α β : π₁(X, x₀)) : π₁(X, x₀) :=
  Quot.lift
    (fun p =>
      Quot.lift
        (fun q => Quot.mk _ (Path.trans p q))
        (fun _ _ hq =>
          Quot.sound (rweqProp_of_rweq (rweq_trans_congr_right p (rweq_of_rweqProp hq))))
        β)
    (fun p p' hp => by
      -- Need to show: lift (trans p _) β = lift (trans p' _) β when p ~_rw p'
      induction β using Quot.ind with
      | _ q =>
          exact Quot.sound (rweqProp_of_rweq (rweq_trans_congr_left q (rweq_of_rweqProp hp))))
    α

/-- Associativity of piOneMul: (α ⋅ β) ⋅ γ = α ⋅ (β ⋅ γ). -/
theorem piOneMul_assoc {X : Type u} {x₀ : X}
    (α β γ : π₁(X, x₀)) :
    piOneMul (piOneMul α β) γ = piOneMul α (piOneMul β γ) := by
  induction α using Quot.ind with
  | _ p =>
    induction β using Quot.ind with
    | _ q =>
      induction γ using Quot.ind with
      | _ r =>
        show Quot.mk (rwEqRel X x₀ x₀) (Path.trans (Path.trans p q) r) =
             Quot.mk (rwEqRel X x₀ x₀) (Path.trans p (Path.trans q r))
        exact Quot.sound (rweqProp_of_rweq (rweq_tt p q r))

/-- Right identity for piOneMul: α ⋅ refl = α. -/
theorem piOneMul_refl_right {X : Type u} {x₀ : X} (α : π₁(X, x₀)) :
    piOneMul α (Quot.mk _ (Path.refl x₀)) = α := by
  induction α using Quot.ind with
  | _ p =>
    show Quot.mk (rwEqRel X x₀ x₀) (Path.trans p (Path.refl x₀)) =
         Quot.mk (rwEqRel X x₀ x₀) p
    exact Quot.sound (rweqProp_of_rweq (rweq_cmpA_refl_right p))

/-- Left identity for piOneMul: refl ⋅ α = α. -/
theorem piOneMul_refl_left {X : Type u} {x₀ : X} (α : π₁(X, x₀)) :
    piOneMul (Quot.mk _ (Path.refl x₀)) α = α := by
  induction α using Quot.ind with
  | _ p =>
    show Quot.mk (rwEqRel X x₀ x₀) (Path.trans (Path.refl x₀) p) =
         Quot.mk (rwEqRel X x₀ x₀) p
    exact Quot.sound (rweqProp_of_rweq (rweq_cmpA_refl_left p))

/-- piOneMul at concrete representatives. -/
theorem piOneMul_mk_mk {X : Type u} {x₀ : X} (p q : LoopSpace X x₀) :
    piOneMul (Quot.mk _ p) (Quot.mk _ q) = Quot.mk _ (Path.trans p q) := rfl

/-! ## The Seifert-Van Kampen Theorem (Statement)

For a pushout of connected, pointed types where the intersection is connected,
the fundamental group of the pushout is the amalgamated free product.
-/

section SVK

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}
variable (a₀ : A) (b₀ : B) (c₀ : C)
variable (hf : Path (f c₀) a₀) (hg : Path (g c₀) b₀)

-- Assume all spaces are path-connected
variable (hA : CompPath.IsPathConnected A)
variable (hB : CompPath.IsPathConnected B)
variable (hC : CompPath.IsPathConnected C)

/-- The induced map on fundamental groups: π₁(A) → π₁(Pushout). -/
noncomputable def piOneInl :
    π₁(A, a₀) → π₁(Pushout A B C f g, Pushout.inl a₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Pushout.inlPath p))
    (by
      intro p q hpq
      -- If p ~_rw q in A, then inlPath p ~_rw inlPath q in Pushout
      apply Quot.sound
      unfold Pushout.inlPath
      exact rweqProp_of_rweq (rweq_congrArg_of_rweq Pushout.inl (rweq_of_rweqProp hpq)))

/-- The induced map on fundamental groups: π₁(B) → π₁(Pushout). -/
noncomputable def piOneInr :
    π₁(B, b₀) → π₁(Pushout A B C f g, Pushout.inr b₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Pushout.inrPath p))
    (by
      intro p q hpq
      apply Quot.sound
      unfold Pushout.inrPath
      exact rweqProp_of_rweq (rweq_congrArg_of_rweq Pushout.inr (rweq_of_rweqProp hpq)))

/-- The induced map from π₁(C): via f. -/
noncomputable def piOneFmap :
    π₁(C, c₀) → π₁(A, f c₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Path.congrArg f p))
    (by
      intro p q hpq
      apply Quot.sound
      exact rweqProp_of_rweq (rweq_congrArg_of_rweq f (rweq_of_rweqProp hpq)))

/-- The induced map from π₁(C): via g. -/
noncomputable def piOneGmap :
    π₁(C, c₀) → π₁(B, g c₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Path.congrArg g p))
    (by
      intro p q hpq
      apply Quot.sound
      exact rweqProp_of_rweq (rweq_congrArg_of_rweq g (rweq_of_rweqProp hpq)))

/-! ### Seifert-Van Kampen Theorem

For a pushout of connected types with connected intersection:
```
      C ---g---> B
      |         |
      f         inr
      v         v
      A --inl-> Pushout
```

The fundamental group π₁(Pushout, inl(f c₀)) is isomorphic to
the amalgamated free product π₁(A, f c₀) *_{π₁(C, c₀)} π₁(B, g c₀).

The isomorphism is induced by:
- π₁(A) → π₁(Pushout) via inl
- π₁(B) → π₁(Pushout) via inr (with transport to match basepoints)
with the amalgamation relation: f*(γ) = g*(γ) for γ : π₁(C).

**Proof outline** (following Favonia & Shulman):

1. **Decode**: Define a map from AmalgamatedFreeProduct to π₁(Pushout)
   - Elements of π₁(A) map via `piOneInl`
   - Elements of π₁(B) map via `piOneInr` (with basepoint transport)
   - The amalgamation relation is respected because the glue path
     witnesses `inl(f(c)) = inr(g(c))`

2. **Encode**: Define a map from π₁(Pushout) to AmalgamatedFreeProduct
   - Uses the "code family" approach with `Pushout.ind`
   - Each path segment is classified as coming from A or B
   - Glue paths switch between the two sides

3. **Round-trip**: Show encode ∘ decode = id and decode ∘ encode = id
   - Uses the computation rules for `rec` and `ind`
   - Path associativity and identity laws from RwEq
-/

/-! ### Encode/Decode for General Pushouts -/

/-- The code type for general pushouts.
For a point x in Pushout, Code(x) represents "words ending at x".
At the basepoint inl(f c₀), this is the amalgamated free product. -/
abbrev PushoutCode (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) : Type u :=
  FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀))

/-! ### Encoding provenance-aware pushout paths -/

namespace PushoutCompPath

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B}
variable {a₀ : A} {b₀ : B}

/-- Encode a provenance-aware pushout path by mapping `inl`/`inr` steps to letters.
Glue steps are ignored, serving only to switch sides in a path representation. -/
noncomputable def encodeWith
    (encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀))
    (encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀))
    {x y : PushoutCompPath A B C f g} :
    PushoutPath A B C f g x y → FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))
  | PushoutPath.refl _ => FreeProductWord.nil
  | PushoutPath.cons (PushoutStep.inlStep p) rest =>
      FreeProductWord.consLeft (encodeInl p) (encodeWith encodeInl encodeInr rest)
  | PushoutPath.cons (PushoutStep.inrStep p) rest =>
      FreeProductWord.consRight (encodeInr p) (encodeWith encodeInl encodeInr rest)
  | PushoutPath.cons (PushoutStep.glueStep _) rest =>
      encodeWith encodeInl encodeInr rest
  | PushoutPath.cons (PushoutStep.glueStepInv _) rest =>
      encodeWith encodeInl encodeInr rest

/-- Encoding of a reflexive provenance path is the empty word. -/
@[simp] theorem encodeWith_refl
    (encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀))
    (encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀))
    (x : PushoutCompPath A B C f g) :
    encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr)
        (PushoutPath.refl x) = FreeProductWord.nil := rfl

/-- Encoding of an `inl` step prepends a left letter. -/
@[simp] theorem encodeWith_cons_inl
    (encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀))
    (encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀))
    {a a' : A} {y : PushoutCompPath A B C f g}
    (p : Path a a')
    (rest : PushoutPath A B C f g (PushoutCompPath.inl a') y) :
    encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr)
        (PushoutPath.cons (PushoutStep.inlStep p) rest) =
      FreeProductWord.consLeft (encodeInl p)
        (encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
          (encodeInl := encodeInl) (encodeInr := encodeInr) rest) := rfl

/-- Encoding of an `inr` step prepends a right letter. -/
@[simp] theorem encodeWith_cons_inr
    (encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀))
    (encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀))
    {b b' : B} {y : PushoutCompPath A B C f g}
    (p : Path b b')
    (rest : PushoutPath A B C f g (PushoutCompPath.inr b') y) :
    encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr)
        (PushoutPath.cons (PushoutStep.inrStep p) rest) =
      FreeProductWord.consRight (encodeInr p)
        (encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
          (encodeInl := encodeInl) (encodeInr := encodeInr) rest) := rfl

/-- Encoding ignores a glue step. -/
@[simp] theorem encodeWith_cons_glue
    (encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀))
    (encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀))
    (c : C) {y : PushoutCompPath A B C f g}
    (rest : PushoutPath A B C f g (PushoutCompPath.inr (g c)) y) :
    encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr)
        (PushoutPath.cons (PushoutStep.glueStep c) rest) =
      encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr) rest := rfl

/-- Encoding ignores an inverse glue step. -/
@[simp] theorem encodeWith_cons_glueInv
    (encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀))
    (encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀))
    (c : C) {y : PushoutCompPath A B C f g}
    (rest : PushoutPath A B C f g (PushoutCompPath.inl (f c)) y) :
    encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr)
        (PushoutPath.cons (PushoutStep.glueStepInv c) rest) =
      encodeWith (A := A) (B := B) (C := C) (f := f) (g := g)
        (encodeInl := encodeInl) (encodeInr := encodeInr) rest := rfl

end PushoutCompPath

/-! ## Provenance-Based Wedge Loop Quotient

We define a wedge-loop quotient that keeps explicit provenance (left/right steps)
and quotients only by equality of the encoded word. This avoids assumptions by
building encode/decode directly on provenance paths.
-/

namespace WedgeProvenance

open PushoutCompPath

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

/-- Provenance loops in a wedge sum, as chains of pushout steps at the basepoint. -/
abbrev WedgeProvenanceLoop : Type u :=
  PushoutCompPath.PushoutPath A B PUnit'
    (fun _ => a₀) (fun _ => b₀)
    (Wedge.basepoint (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
    (Wedge.basepoint (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))

/-- Encoding primitives for provenance loops in wedge sums. -/
class HasWedgeProvenanceEncode (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) : Type u where
  /-- Encode a left-side path as a loop class in `π₁(A, a₀)`. -/
  encodeInl : ∀ {a a' : A}, Path a a' → π₁(A, a₀)
  /-- Encode a right-side path as a loop class in `π₁(B, b₀)`. -/
  encodeInr : ∀ {b b' : B}, Path b b' → π₁(B, b₀)
  /-- On loops at `a₀`, `encodeInl` is the quotient map. -/
  encodeInl_loop : ∀ p : LoopSpace A a₀, encodeInl p = Quot.mk _ p
  /-- On loops at `b₀`, `encodeInr` is the quotient map. -/
  encodeInr_loop : ∀ p : LoopSpace B b₀, encodeInr p = Quot.mk _ p

/-- Encode a provenance loop as a word in the free product of `π₁(A)` and `π₁(B)`. -/
noncomputable def wedgeProvenanceEncode
    [HasWedgeProvenanceEncode A B a₀ b₀] :
    WedgeProvenanceLoop (A := A) (B := B) a₀ b₀ →
      FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
  PushoutCompPath.encodeWith
    (A := A) (B := B) (C := PUnit')
    (f := fun _ => a₀) (g := fun _ => b₀)
    (encodeInl :=
      HasWedgeProvenanceEncode.encodeInl (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
    (encodeInr :=
      HasWedgeProvenanceEncode.encodeInr (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))

/-- Two provenance loops are equivalent if their encoded words coincide. -/
noncomputable def wedgeProvenanceRel
    [HasWedgeProvenanceEncode A B a₀ b₀]
    (p q : WedgeProvenanceLoop (A := A) (B := B) a₀ b₀) : Prop :=
  wedgeProvenanceEncode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) p =
    wedgeProvenanceEncode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) q

/-- Setoid on provenance loops by encoded-word equality. -/
noncomputable def wedgeProvenanceSetoid
    [HasWedgeProvenanceEncode A B a₀ b₀] :
    Setoid (WedgeProvenanceLoop (A := A) (B := B) a₀ b₀) where
  r := wedgeProvenanceRel (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
  iseqv := by
    refine ⟨?refl, ?symm, ?trans⟩
    · intro p
      rfl
    · intro p q h
      exact h.symm
    · intro p q r h₁ h₂
      exact h₁.trans h₂

/-- Provenance-based loop quotient for wedge sums. -/
abbrev WedgeProvenanceQuot
    [HasWedgeProvenanceEncode A B a₀ b₀] : Type u :=
  Quot (wedgeProvenanceSetoid (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).r

/-- Encode at the quotient level. -/
noncomputable def wedgeProvenanceEncodeQuot
    [HasWedgeProvenanceEncode A B a₀ b₀] :
    WedgeProvenanceQuot (A := A) (B := B) a₀ b₀ →
      FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
  Quot.lift
    (wedgeProvenanceEncode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
    (by
      intro p q h
      exact h)

/-- Choose a representative loop in `A` for a `π₁(A)` element. -/
noncomputable def loopRepInl
    (α : π₁(A, a₀)) : LoopSpace A a₀ := by
  classical
  exact Classical.choose (Quot.exists_rep α)

/-- Representative lemma for `loopRepInl`. -/
@[simp] theorem loopRepInl_spec (α : π₁(A, a₀)) :
    Quot.mk _ (loopRepInl (A := A) (a₀ := a₀) α) = α := by
  classical
  exact Classical.choose_spec (Quot.exists_rep α)

/-- Choose a representative loop in `B` for a `π₁(B)` element. -/
noncomputable def loopRepInr
    (β : π₁(B, b₀)) : LoopSpace B b₀ := by
  classical
  exact Classical.choose (Quot.exists_rep β)

/-- Representative lemma for `loopRepInr`. -/
@[simp] theorem loopRepInr_spec (β : π₁(B, b₀)) :
    Quot.mk _ (loopRepInr (B := B) (b₀ := b₀) β) = β := by
  classical
  exact Classical.choose_spec (Quot.exists_rep β)

/-- Decode a word into a provenance loop (before quotienting). -/
noncomputable def wedgeProvenanceDecodeLoop
    [HasWedgeProvenanceEncode A B a₀ b₀] :
    FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) →
      WedgeProvenanceLoop (A := A) (B := B) a₀ b₀
  | .nil => PushoutPath.refl (Wedge.basepoint (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
  | .consLeft α rest =>
      PushoutPath.cons
        (PushoutStep.inlStep (loopRepInl (A := A) (a₀ := a₀) α))
        (wedgeProvenanceDecodeLoop rest)
  | .consRight β rest =>
      PushoutPath.cons
        (PushoutStep.glueStep (A := A) (B := B) (C := PUnit')
          (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit)
        (PushoutPath.cons
          (PushoutStep.inrStep (loopRepInr (B := B) (b₀ := b₀) β))
          (PushoutPath.cons
            (PushoutStep.glueStepInv (A := A) (B := B) (C := PUnit')
              (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit)
            (wedgeProvenanceDecodeLoop rest)))

/-- Decode a word into the provenance quotient. -/
noncomputable def wedgeProvenanceDecodeQuot
    [HasWedgeProvenanceEncode A B a₀ b₀] :
    FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) →
      WedgeProvenanceQuot (A := A) (B := B) a₀ b₀ :=
  fun w => Quot.mk _ (wedgeProvenanceDecodeLoop (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) w)

/-- Encode after decode is the identity on words. -/
theorem wedgeProvenanceEncodeDecode
    [HasWedgeProvenanceEncode A B a₀ b₀]
    (w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    wedgeProvenanceEncodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
        (wedgeProvenanceDecodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) w) = w := by
  induction w with
  | nil =>
      simp [wedgeProvenanceDecodeQuot, wedgeProvenanceDecodeLoop,
        wedgeProvenanceEncodeQuot, wedgeProvenanceEncode]
  | consLeft α rest ih =>
      have hrest :
          PushoutCompPath.encodeWith
              (A := A) (B := B) (C := PUnit')
              (f := fun _ => a₀) (g := fun _ => b₀)
              (encodeInl :=
                HasWedgeProvenanceEncode.encodeInl
                  (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
              (encodeInr :=
                HasWedgeProvenanceEncode.encodeInr
                  (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
              (wedgeProvenanceDecodeLoop (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) rest) =
            rest := by
        simpa [wedgeProvenanceEncode, wedgeProvenanceEncodeQuot, wedgeProvenanceDecodeQuot]
          using ih
      have hα :
          HasWedgeProvenanceEncode.encodeInl (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
              (loopRepInl (A := A) (a₀ := a₀) α) = α := by
        simpa [HasWedgeProvenanceEncode.encodeInl_loop]
          using (loopRepInl_spec (A := A) (a₀ := a₀) α)
      simp [wedgeProvenanceDecodeQuot, wedgeProvenanceDecodeLoop,
        wedgeProvenanceEncodeQuot, wedgeProvenanceEncode, hα, hrest]
  | consRight β rest ih =>
      have hrest :
          PushoutCompPath.encodeWith
              (A := A) (B := B) (C := PUnit')
              (f := fun _ => a₀) (g := fun _ => b₀)
              (encodeInl :=
                HasWedgeProvenanceEncode.encodeInl
                  (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
              (encodeInr :=
                HasWedgeProvenanceEncode.encodeInr
                  (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
              (wedgeProvenanceDecodeLoop (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) rest) =
            rest := by
        simpa [wedgeProvenanceEncode, wedgeProvenanceEncodeQuot, wedgeProvenanceDecodeQuot]
          using ih
      have hβ :
          HasWedgeProvenanceEncode.encodeInr (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
              (loopRepInr (B := B) (b₀ := b₀) β) = β := by
        simpa [HasWedgeProvenanceEncode.encodeInr_loop]
          using (loopRepInr_spec (B := B) (b₀ := b₀) β)
      simp [wedgeProvenanceDecodeQuot, wedgeProvenanceDecodeLoop,
        wedgeProvenanceEncodeQuot, wedgeProvenanceEncode, hβ, hrest]

/-- Decode after encode is the identity in the provenance quotient. -/
theorem wedgeProvenanceDecodeEncode
    [HasWedgeProvenanceEncode A B a₀ b₀]
    (x : WedgeProvenanceQuot (A := A) (B := B) a₀ b₀) :
    wedgeProvenanceDecodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
        (wedgeProvenanceEncodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) x) = x := by
  refine Quot.inductionOn x ?_
  intro p
  apply Quot.sound
  simpa [wedgeProvenanceEncodeQuot, wedgeProvenanceDecodeQuot] using
    (wedgeProvenanceEncodeDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
      (wedgeProvenanceEncode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) p))

/-- Provenance-based SVK equivalence for wedge sums. -/
noncomputable def wedgeProvenanceEquiv
    [HasWedgeProvenanceEncode A B a₀ b₀] :
    SimpleEquiv
      (WedgeProvenanceQuot (A := A) (B := B) a₀ b₀)
      (FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) where
  toFun := wedgeProvenanceEncodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
  invFun := wedgeProvenanceDecodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
  left_inv := wedgeProvenanceDecodeEncode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)
  right_inv := wedgeProvenanceEncodeDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

end WedgeProvenance

/-- Decode for general pushouts: Convert a word to a loop in Pushout.
Similar to wedge decode, but needs to handle basepoint transport. -/
noncomputable def pushoutDecode
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B}
    (c₀ : C) :
    PushoutCode A B C f g c₀ → π₁(Pushout A B C f g, Pushout.inl (f c₀))
  | .nil => Quot.mk _ (Path.refl _)
  | .consLeft α rest =>
      -- α : π₁(A, f c₀), map to π₁(Pushout) via inl
      let αInPushout : π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
        Quot.lift
          (fun p => Quot.mk _ (Pushout.inlPath p))
          (fun _ _ hp =>
            Quot.sound (rweqProp_of_rweq (rweq_congrArg_of_rweq Pushout.inl (rweq_of_rweqProp hp))))
          α
      piOneMul αInPushout (pushoutDecode c₀ rest)
  | .consRight β rest =>
      -- β : π₁(B, g c₀), needs transport via glue
      -- Path from inl(f c₀) to inr(g c₀) is glue(c₀)
      let βInPushout : π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
        Quot.lift
          (fun q => Quot.mk _ (Path.trans
              (Pushout.glue c₀)
              (Path.trans (Pushout.inrPath q)
                (Path.symm (Pushout.glue c₀)))))
          (fun _ _ hq => Quot.sound (rweqProp_of_rweq (
            rweq_trans_congr_right _ (rweq_trans_congr_left _
              (rweq_congrArg_of_rweq Pushout.inr (rweq_of_rweqProp hq))))))
          β
      piOneMul βInPushout (pushoutDecode c₀ rest)

/-- pushoutDecode respects concatenation. -/
theorem pushoutDecode_concat
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B}
    (c₀ : C) (w₁ w₂ : PushoutCode A B C f g c₀) :
    pushoutDecode c₀ (FreeProductWord.concat w₁ w₂) =
    piOneMul (pushoutDecode c₀ w₁) (pushoutDecode c₀ w₂) := by
  induction w₁ with
  | nil =>
      simp only [FreeProductWord.concat, pushoutDecode]
      exact (piOneMul_refl_left _).symm
  | consLeft α rest ih =>
      simp only [FreeProductWord.concat, pushoutDecode]
      rw [ih]
      exact (piOneMul_assoc _ _ _).symm
  | consRight β rest ih =>
      simp only [FreeProductWord.concat, pushoutDecode]
      rw [ih]
      exact (piOneMul_assoc _ _ _).symm

/-- Decode respects the amalgamation relation.
This is the key property: for γ : π₁(C, c₀), the paths
  inl(f*(γ)) and glue ⋅ inr(g*(γ)) ⋅ glue⁻¹
are homotopic in the pushout. -/
theorem pushoutDecode_respects_amalg
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B}
    (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    (γ : π₁(C, c₀))
    (rest : PushoutCode A B C f g c₀) :
    pushoutDecode c₀ (.consLeft (piOneFmap c₀ γ) rest) =
    pushoutDecode c₀ (.consRight (piOneGmap c₀ γ) rest) := by
  -- Both decode to paths that are RwEq-equivalent
  -- The key is that inl(f(p)) and glue ⋅ inr(g(p)) ⋅ glue⁻¹ are homotopic
  -- via the naturality of glue
  induction γ using Quot.ind with
  | _ p =>
    -- p : Loop in C at c₀
    -- f*(p) = congrArg f p, g*(p) = congrArg g p
    simp only [pushoutDecode, piOneFmap, piOneGmap]
    -- Need to show that the two loop representations are equal in π₁
    -- This follows from the glue naturality square
    apply _root_.congrArg (piOneMul · (pushoutDecode c₀ rest))
    let path : Path (PushoutCompPath.inl (f c₀)) (PushoutCompPath.inl (f c₀)) :=
      (inlPath (congrArg f p)).symm.trans ((Pushout.glue c₀).trans (inrPath (congrArg g p) |>.trans (Pushout.glue c₀).symm))

    -- The naturality lemma is: symm(f*p) . glue c₀ . g*p ≈ glue c₀
    -- But `p` here is a loop at c₀, so `c = c₀` and `glue c = glue c₀`.
    -- `HasGlueNaturalLoopRwEq.eq` gives:
    -- RwEq (symm (f*p) . glue c₀ . g*p) (glue c₀)

    have h : RwEq ((inlPath (congrArg f p)).symm.trans ((Pushout.glue c₀).trans (inrPath (congrArg g p)))) (Pushout.glue c₀) :=
      HasGlueNaturalLoopRwEq.eq (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀) c₀ p

    have h' : RwEq path (Path.refl (PushoutCompPath.inl (f c₀))) := by
      -- Goal: symm(f*p) . glue c₀ . g*p . symm(glue c₀) ≈ refl
      -- We know: symm(f*p) . glue c₀ . g*p ≈ glue c₀
      -- So LHS ≈ glue c₀ . symm(glue c₀) ≈ refl

      -- We need to associate the LHS to expose the subterm that matches `h`.
      -- path is: symm(f*p) . (glue . (g*p . symm(glue)))
      -- We want: (symm(f*p) . (glue . g*p)) . symm(glue)

      -- Let L = symm(f*p), M = glue, R = g*p, S = symm(glue)
      -- path = L . (M . (R . S))
      -- h says: L . (M . R) ≈ M

      -- Assoc: L . (M . (R . S)) ≈ L . ((M . R) . S)
      -- Using rweq_tt backwards (rweq_tt.symm)
      -- rweq_tt: trans (trans a b) c ≈ trans a (trans b c)
      -- symm: trans a (trans b c) ≈ trans (trans a b) c

      -- Current term structure: trans L (trans M (trans R S))
      -- We want: trans (trans L (trans M R)) S

      -- First, associate M . (R . S) to (M . R) . S inside
      -- trans L (trans M (trans R S)) ≈ trans L (trans (trans M R) S)
      apply rweq_trans (rweq_trans_congr_right _ (rweq_tt _ _ _).symm)

      -- Now associate L . (K . S) to (L . K) . S
      -- trans L (trans (trans M R) S) ≈ trans (trans L (trans M R)) S
      apply rweq_trans (rweq_tt _ _ _).symm

      -- Now use `h` on `trans L (trans M R)`
      -- trans (trans L (trans M R)) S ≈ trans M S
      apply rweq_trans (rweq_trans_congr_left _ h)

      -- M . S ≈ refl
      apply rweq_cmpA_inv_right _

    -- The goal of Quot.sound is: Setoid.r (inlPath (congrArg f p)) (...)
    -- This is `inlPath (congrArg f p) ≈ ...`
    -- But `h'` is `path ≈ refl`.
    -- path = symm(inlPath ...) . (...)
    -- So `symm(A) . B ≈ refl` implies `A ≈ B`.

    -- We can use `rweq_of_trans_symm_refl_left` if it exists, or just manipulate `h'`.
    -- Or better, show `inlPath ...` is `symm (symm (inlPath ...))` then use congruences.

    -- Let A = inlPath (congrArg f p)
    -- Let B = (glue . (g*p . symm(glue)))
    -- We have `symm A . B ≈ refl`.
    -- We want `A ≈ B`.

    have h_final : RwEq (inlPath (congrArg f p)) ((Pushout.glue c₀).trans ((inrPath (congrArg g p)).trans (Pushout.glue c₀).symm)) := by
      -- A ≈ A . refl
      apply rweq_trans (rweq_cmpA_refl_right (inlPath (congrArg f p))).symm
      -- ≈ A . (symm A . B)  (using h'.symm)
      apply rweq_trans (rweq_trans_congr_right _ (rweq_symm h'))
      -- ≈ (A . symm A) . B
      apply rweq_trans (rweq_tt _ _ _).symm
      -- ≈ refl . B
      apply rweq_trans (rweq_trans_congr_left _ (rweq_cmpA_inv_right _))
      -- ≈ B
      apply rweq_cmpA_refl_left

    apply Quot.sound
    exact h_final

/-- Encode map for general pushouts (at the quotient level). -/
class HasPushoutSVKEncodeQuot (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) where
  encodeQuot :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
      FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀))

noncomputable def pushoutEncodeQuotAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
    FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀)) :=
  HasPushoutSVKEncodeQuot.encodeQuot

/-- Round-trip law: `decode ∘ encode = id` (at π₁ level). -/
class HasPushoutSVKDecodeEncode (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] : Prop where
  decode_encode :
    ∀ p : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀)),
      pushoutDecode c₀ (pushoutEncodeQuotAxiom A B C f g c₀ (Quot.mk _ p)) = Quot.mk _ p

/-- Round-trip law: `encode ∘ decode` gives an amalgamation-equivalent word.

**DEPRECATED**: This class is provably unsatisfiable for all types.
`AmalgEquiv` preserves word length (it only swaps `singleLeft(i₁ h)` ↔
`singleRight(i₂ h)`), while `pushoutDecode` maps words of different lengths
to the same π₁ element (e.g. `nil` and `consLeft 0 nil` both decode to the
identity). Therefore no `encodeQuot` function can satisfy
`AmalgEquiv (encodeQuot (pushoutDecode w)) w` for all `w`.

Use `HasPushoutSVKEncodeDecodeFull` instead, which quotients by
`FullAmalgEquiv` (amalgamation + free group reduction).

See `PushoutSVKInstances.hasPushoutSVKEncodeDecode_impossible_PUnit` for the
formal impossibility proof. -/
-- DEPRECATED: Provably unsatisfiable — nil vs consLeft(0,nil) obstruction.
class HasPushoutSVKEncodeDecode (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] : Prop where
  encode_decode :
    ∀ w : PushoutCode A B C f g c₀,
      AmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
        (pushoutEncodeQuotAxiom A B C f g c₀ (pushoutDecode c₀ w)) w

/-- Full encode/decode data for general pushouts (both round-trip laws). -/
class HasPushoutSVKEncodeData (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) extends HasPushoutSVKEncodeQuot A B C f g c₀ where
  decode_encode :
    ∀ p : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀)),
      pushoutDecode c₀ (encodeQuot (Quot.mk _ p)) = Quot.mk _ p
  encode_decode :
    ∀ w : PushoutCode A B C f g c₀,
      AmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
        (encodeQuot (pushoutDecode c₀ w)) w

noncomputable instance (priority := 100) hasPushoutSVKDecodeEncode_of_encodeData (A : Type u) (B : Type u)
    (C : Type u) (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀] :
    HasPushoutSVKDecodeEncode A B C f g c₀ where
  decode_encode := HasPushoutSVKEncodeData.decode_encode (A := A) (B := B) (C := C) (f := f)
    (g := g) (c₀ := c₀)

noncomputable instance (priority := 100) hasPushoutSVKEncodeDecode_of_encodeData (A : Type u) (B : Type u)
    (C : Type u) (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀] :
    HasPushoutSVKEncodeDecode A B C f g c₀ where
  encode_decode := HasPushoutSVKEncodeData.encode_decode (A := A) (B := B) (C := C) (f := f)
    (g := g) (c₀ := c₀)

/-- Encode on loop representatives. -/
noncomputable def pushoutEncodeAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] :
    LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀)) →
    FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀)) :=
  fun p => pushoutEncodeQuotAxiom A B C f g c₀ (Quot.mk _ p)

/-- Encode respects RwEq. -/
noncomputable def pushoutEncodeAxiom_respects_rweq (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀]
    {p q : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀))}
    (h : RwEq p q) :
    pushoutEncodeAxiom A B C f g c₀ p = pushoutEncodeAxiom A B C f g c₀ q := by
  unfold pushoutEncodeAxiom
  exact _root_.congrArg (pushoutEncodeQuotAxiom A B C f g c₀) (Quot.sound h)

/-- Encode at quotient level. -/
noncomputable def pushoutEncodeQuot
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B} (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
    PushoutCode A B C f g c₀ :=
  pushoutEncodeQuotAxiom A B C f g c₀

/-- The encoding produces an amalgamation-equivalence class. -/
noncomputable def pushoutEncodeAmalg
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B} (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
    AmalgamatedFreeProduct (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
      (piOneFmap c₀) (piOneGmap c₀) :=
  fun α => AmalgamatedFreeProduct.ofWord (pushoutEncodeQuot c₀ α)

set_option maxHeartbeats 400000 in
/-- Decode at the amalgamated free product level respects amalgamation. -/
noncomputable def pushoutDecodeAmalg
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B} (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀] :
    AmalgamatedFreeProduct (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
      (piOneFmap c₀) (piOneGmap c₀) →
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
  Quot.lift (pushoutDecode c₀) (by
    intro w₁ w₂ h
    -- Need: if w₁ ≃_amalg w₂, then decode w₁ = decode w₂
    induction h with
    | refl _ => rfl
    | step hr =>
        cases hr with
        | amalgLeftToRight hh pre suf =>
            -- Replacing i₁(hh) with i₂(hh) in: concat pre (concat (singleLeft (i₁ hh)) suf)
            -- concat (consLeft x nil) suf = consLeft x suf
            have hl : FreeProductWord.concat (FreeProductWord.consLeft (piOneFmap c₀ hh) .nil) suf =
                      FreeProductWord.consLeft (piOneFmap c₀ hh) suf := rfl
            have hr' : FreeProductWord.concat (FreeProductWord.consRight (piOneGmap c₀ hh) .nil) suf =
                       FreeProductWord.consRight (piOneGmap c₀ hh) suf := rfl
            simp only [FreeProductWord.singleLeft, FreeProductWord.singleRight, hl, hr']
            -- Now use pushoutDecode_concat to split
            rw [pushoutDecode_concat, pushoutDecode_concat]
            -- decode(consLeft (i₁ hh) suf) = decode(consRight (i₂ hh) suf)
            -- follows from pushoutDecode_respects_amalg
            apply _root_.congrArg (piOneMul (pushoutDecode c₀ pre))
            exact pushoutDecode_respects_amalg c₀ hh suf
        | amalgRightToLeft hh pre suf =>
            -- Symmetric case: i₂(hh) → i₁(hh)
            have hl : FreeProductWord.concat (FreeProductWord.consRight (piOneGmap c₀ hh) .nil) suf =
                      FreeProductWord.consRight (piOneGmap c₀ hh) suf := rfl
            have hr' : FreeProductWord.concat (FreeProductWord.consLeft (piOneFmap c₀ hh) .nil) suf =
                       FreeProductWord.consLeft (piOneFmap c₀ hh) suf := rfl
            simp only [FreeProductWord.singleLeft, FreeProductWord.singleRight, hl, hr']
            rw [pushoutDecode_concat, pushoutDecode_concat]
            apply _root_.congrArg (piOneMul (pushoutDecode c₀ pre))
            exact (pushoutDecode_respects_amalg c₀ hh suf).symm
    | symm _ ih => exact ih.symm
    | trans _ _ ih1 ih2 => exact ih1.trans ih2)

/-- Round-trip: decode ∘ encode = id. -/
theorem pushoutDecodeEncodeAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKDecodeEncode A B C f g c₀]
    (p : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀))) :
    pushoutDecode c₀ (pushoutEncodeAxiom A B C f g c₀ p) = Quot.mk _ p := by
  unfold pushoutEncodeAxiom
  unfold pushoutEncodeQuotAxiom
  exact HasPushoutSVKDecodeEncode.decode_encode (A := A) (B := B) (C := C) (f := f) (g := g)
    (c₀ := c₀) p

/-- Round-trip: encode ∘ decode gives an amalgamation-equivalent word. -/
theorem pushoutEncodeDecodeAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKEncodeDecode A B C f g c₀]
    (w : PushoutCode A B C f g c₀) :
    AmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
      (pushoutEncodeQuot c₀ (pushoutDecode c₀ w)) w := by
  unfold pushoutEncodeQuot
  unfold pushoutEncodeQuotAxiom
  exact HasPushoutSVKEncodeDecode.encode_decode (A := A) (B := B) (C := C) (f := f) (g := g)
    (c₀ := c₀) w

/-! ## Full (Free-Group-Reduced) SVK Target

`AmalgamatedFreeProduct` quotients only by the amalgamation relation. For many
SVK applications it is more natural to additionally quotient by *free group
reduction* (combine adjacent same-side letters, remove identity letters). This
is packaged by `FullAmalgamatedFreeProduct`, which quotients by `FullAmalgEquiv`
(amalgamation + free-group reduction).
-/

section FullSVK

variable {A : Type u} {B : Type u} {C : Type u}
variable {f : C → A} {g : C → B} (c₀ : C)

-- Provide additive structure on π₁ used by `FreeGroupStep`/`FullAmalgEquiv`.
-- This is local to this section to avoid polluting global instance search.
noncomputable local instance : Add (π₁(A, f c₀)) := ⟨piOneMul⟩
noncomputable local instance : Zero (π₁(A, f c₀)) := ⟨Quot.mk _ (Path.refl (f c₀))⟩
noncomputable local instance : Add (π₁(B, g c₀)) := ⟨piOneMul⟩
noncomputable local instance : Zero (π₁(B, g c₀)) := ⟨Quot.mk _ (Path.refl (g c₀))⟩

/-- The full SVK target type for this pushout: amalgamation + free reduction. -/
abbrev PushoutFullAmalgamatedFreeProduct : Type u :=
  FullAmalgamatedFreeProduct (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
    (piOneFmap c₀) (piOneGmap c₀)

/-- Left injection of π₁(A) into π₁(Pushout) (at basepoint `inl (f c₀)`). -/
noncomputable def pushoutPiOneInl :
    π₁(A, f c₀) → π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
  Quot.lift
    (fun p => Quot.mk _ (Pushout.inlPath p))
    (fun _ _ hp =>
      Quot.sound (rweqProp_of_rweq (rweq_congrArg_of_rweq Pushout.inl (rweq_of_rweqProp hp))))

/-- Right injection of π₁(B) into π₁(Pushout), conjugated by `glue` to match basepoint `inl (f c₀)`. -/
noncomputable def pushoutPiOneInr :
    π₁(B, g c₀) → π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
  Quot.lift
    (fun q => Quot.mk _ (Path.trans
        (Pushout.glue c₀)
        (Path.trans (Pushout.inrPath q)
          (Path.symm (Pushout.glue c₀)))))
    (fun _ _ hq => Quot.sound (rweqProp_of_rweq (
      rweq_trans_congr_right _ (rweq_trans_congr_left _
        (rweq_congrArg_of_rweq Pushout.inr (rweq_of_rweqProp hq))))))

theorem pushoutPiOneInl_mul (α β : π₁(A, f c₀)) :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (piOneMul α β) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β) := by
  induction α using Quot.ind with
  | _ p =>
    induction β using Quot.ind with
    | _ q =>
      change Quot.mk _ (Pushout.inlPath (Path.trans p q)) =
        Quot.mk _ (Path.trans (Pushout.inlPath p) (Pushout.inlPath q))
      apply Quot.sound
      simp [Pushout.inlPath]

theorem pushoutPiOneInl_zero :
    pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (0 : π₁(A, f c₀)) =
      Quot.mk _ (Path.refl (Pushout.inl (f c₀))) := by
  change Quot.mk _ (Pushout.inlPath (Path.refl (f c₀))) =
    Quot.mk _ (Path.refl (Pushout.inl (f c₀)))
  apply Quot.sound
  simp [Pushout.inlPath]

theorem pushoutPiOneInr_mul (β₁ β₂ : π₁(B, g c₀)) :
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (piOneMul β₁ β₂) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₁)
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β₂) := by
  induction β₁ using Quot.ind with
  | _ p =>
    induction β₂ using Quot.ind with
    | _ q =>
      let glue₀ := Pushout.glue (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      change Quot.mk _ (Path.trans glue₀
        (Path.trans
          (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) (Path.trans p q))
          (Path.symm glue₀))) =
        Quot.mk _ (Path.trans
          (Path.trans glue₀
            (Path.trans
              (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
              (Path.symm glue₀)))
          (Path.trans glue₀
            (Path.trans
              (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
              (Path.symm glue₀))))
      apply Quot.sound
      -- Expand conjugation and reassociate/cancel to match the conjugate of `p ⋅ q`.
      -- This is standard: (g p g⁻¹) ⋅ (g q g⁻¹) = g (p ⋅ q) g⁻¹.
      -- Use congrArg on trans plus associativity and inverse cancellation.
      -- First, rewrite `inrPath (p ⋅ q)` to `inrPath p ⋅ inrPath q`.
      have hinr :
          RwEq
            (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) (Path.trans p q))
            (Path.trans
              (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
              (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)) := by
        simp [Pushout.inrPath]

      -- Now compare the two conjugation composites up to RwEq.
      -- Right side is:
      -- (glue ⋅ inrPath p ⋅ glue⁻¹) ⋅ (glue ⋅ inrPath q ⋅ glue⁻¹)
      -- = glue ⋅ inrPath p ⋅ (glue⁻¹ ⋅ glue) ⋅ inrPath q ⋅ glue⁻¹
      -- = glue ⋅ (inrPath p ⋅ inrPath q) ⋅ glue⁻¹
      -- = glue ⋅ inrPath (p ⋅ q) ⋅ glue⁻¹
      -- by `hinr`.
      -- We prove this with associativity + inverse cancellation.
      have hcancel :
          RwEq
            (Path.trans (Path.symm glue₀) glue₀)
            (Path.refl (Pushout.inr (A := A) (B := B) (C := C) (f := f) (g := g) (g c₀))) := by
        simpa using rweq_cmpA_inv_left glue₀

      -- Start from the RHS composite and rewrite to the LHS form.
      -- We'll build the chain in the direction needed by `Quot.sound`.
      -- (Since `RwEq` is symmetric/transitive, direction is flexible.)
      -- Target:
      -- glue ⋅ inrPath (p ⋅ q) ⋅ glue⁻¹
      -- ≈ (glue ⋅ inrPath p ⋅ glue⁻¹) ⋅ (glue ⋅ inrPath q ⋅ glue⁻¹)
      -- We show the latter rewrites to the former.
      -- Note: `rweq_tt` is associativity of `Path.trans`.
      have hassoc1 :
          RwEq
            (Path.trans
              (Path.trans glue₀
                (Path.trans (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                  (Path.symm glue₀)))
              (Path.trans glue₀
                (Path.trans (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                  (Path.symm glue₀))))
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans (Path.symm glue₀)
                  (Path.trans glue₀
                    (Path.trans
                      (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                      (Path.symm glue₀)))))) := by
        -- pull out the leading `glue₀`, then reassociate inside
        have h₁ :=
          (rweq_tt
            glue₀
            (Path.trans (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p) (Path.symm glue₀))
            (Path.trans glue₀
              (Path.trans (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                (Path.symm glue₀))))
        have h₂ :=
          (rweq_tt
            (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
            (Path.symm glue₀)
            (Path.trans glue₀
              (Path.trans (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                (Path.symm glue₀))))
        exact RwEq.trans h₁ (rweq_trans_congr_right glue₀ h₂)

      have hassoc2 :
          RwEq
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans (Path.symm glue₀)
                  (Path.trans glue₀
                    (Path.trans
                      (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                      (Path.symm glue₀))))))
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans
                  (Path.trans (Path.symm glue₀) glue₀)
                  (Path.trans
                    (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                    (Path.symm glue₀))))) := by
        -- reassociate the middle `symm glue₀ ⋅ (glue₀ ⋅ ...)`
        have h :=
          (rweq_tt
            (Path.symm glue₀)
            glue₀
            (Path.trans
              (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
              (Path.symm glue₀))).symm
        exact rweq_trans_congr_right glue₀ (rweq_trans_congr_right
          (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p) h)

      have hmid :
          RwEq
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans
                  (Path.trans (Path.symm glue₀) glue₀)
                  (Path.trans
                    (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                    (Path.symm glue₀)))))
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans
                  (Path.refl _)
                  (Path.trans
                    (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                    (Path.symm glue₀))))) := by
        -- replace `(symm glue₀ ⋅ glue₀)` by `refl` inside the composite
        have h₁ :
            RwEq
              (Path.trans
                (Path.trans (Path.symm glue₀) glue₀)
                (Path.trans
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                  (Path.symm glue₀)))
              (Path.trans
                (Path.refl _)
                (Path.trans
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                  (Path.symm glue₀))) :=
          rweq_trans_congr_left _ hcancel
        exact rweq_trans_congr_right glue₀ (rweq_trans_congr_right
          (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p) h₁)

      have hmid2 :
          RwEq
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans
                  (Path.refl _)
                  (Path.trans
                    (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                    (Path.symm glue₀)))))
            (Path.trans glue₀
              (Path.trans
                (Path.trans
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q))
                (Path.symm glue₀))) := by
        -- remove the middle `refl`, then reassociate
        have h₁ :
            RwEq
              (Path.trans
                (Path.refl _)
                (Path.trans
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                  (Path.symm glue₀)))
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                (Path.symm glue₀)) :=
          rweq_cmpA_refl_left _
        have h₁' :
            RwEq
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans
                  (Path.refl _)
                  (Path.trans
                    (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                    (Path.symm glue₀))))
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                (Path.trans
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
                  (Path.symm glue₀))) :=
          rweq_trans_congr_right _ h₁
        have h₂ :=
          (rweq_tt
            (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
            (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q)
            (Path.symm glue₀)).symm
        exact RwEq.trans (rweq_trans_congr_right glue₀ h₁') (rweq_trans_congr_right glue₀ h₂)

      -- Finally replace `inrPath p ⋅ inrPath q` by `inrPath (p ⋅ q)`.
      have hfin :
          RwEq
            (Path.trans glue₀
              (Path.trans
                (Path.trans
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) p)
                  (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) q))
                (Path.symm glue₀)))
            (Path.trans glue₀
              (Path.trans
                (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) (Path.trans p q))
                (Path.symm glue₀))) := by
        exact rweq_trans_congr_right glue₀ (rweq_trans_congr_left _ (rweq_symm hinr))
      -- Chain everything together.
      -- The chain above rewrites the product of conjugates into the conjugate of `p ⋅ q`,
      -- so we take `symm` to match the goal's direction.
      exact rweqProp_of_rweq <|
        (RwEq.trans hassoc1
            (RwEq.trans hassoc2
              (RwEq.trans hmid (RwEq.trans hmid2 hfin)))).symm

theorem pushoutDecode_consLeft (α : π₁(A, f c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consLeft α rest) =
      piOneMul
        (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) := by
  simp [pushoutDecode, pushoutPiOneInl]

theorem pushoutDecode_consRight (β : π₁(B, g c₀)) (rest : PushoutCode A B C f g c₀) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (.consRight β rest) =
      piOneMul
        (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ β)
        (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ rest) := by
  simp [pushoutDecode, pushoutPiOneInr]

theorem pushoutPiOneInr_zero :
    pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (0 : π₁(B, g c₀)) =
      Quot.mk _ (Path.refl (Pushout.inl (f c₀))) := by
  change Quot.mk _ (Path.trans
      (Pushout.glue (A := A) (B := B) (C := C) (f := f) (g := g) c₀)
      (Path.trans
        (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) (Path.refl (g c₀)))
        (Path.symm (Pushout.glue (A := A) (B := B) (C := C) (f := f) (g := g) c₀)))) =
    Quot.mk _ (Path.refl (Pushout.inl (f c₀)))
  -- Conjugation of the identity loop is the identity.
  apply Quot.sound
  let glue₀ := Pushout.glue (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  have hinr :
      RwEq
        (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) (Path.refl (g c₀)))
        (Path.refl (Pushout.inr (A := A) (B := B) (C := C) (f := f) (g := g) (g c₀))) := by
    simp [Pushout.inrPath]
  -- Reduce glue ⋅ refl ⋅ glue⁻¹ to refl.
  have hstep :
      RwEq
        (Path.trans glue₀
          (Path.trans
            (Pushout.inrPath (A := A) (B := B) (C := C) (f := f) (g := g) (Path.refl (g c₀)))
            (Path.symm glue₀)))
        (Path.trans glue₀ (Path.symm glue₀)) := by
    exact rweq_trans_congr_right _ (rweq_trans_congr_left _ hinr)
  exact rweqProp_of_rweq (RwEq.trans hstep (rweq_cmpA_inv_right glue₀))

theorem pushoutDecode_respects_freeGroupStep
    {w₁ w₂ : PushoutCode A B C f g c₀}
    (h : FreeProductWord.FreeGroupStep w₁ w₂) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ w₁ =
      pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ w₂ := by
  induction h with
  | combineLeft x y rest =>
      -- decode(x · (y · rest)) = decode((x+y) · rest)
      rw [pushoutDecode_consLeft (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x (.consLeft y rest)]
      rw [pushoutDecode_consLeft (A := A) (B := B) (C := C) (f := f) (g := g) c₀ y rest]
      rw [pushoutDecode_consLeft (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (x + y) rest]
      have hx :
          pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (x + y) =
            piOneMul
              (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x)
              (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ y) := by
        -- `x + y` is `piOneMul x y` by the local `Add` instance.
        simpa using (pushoutPiOneInl_mul (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x y)
      rw [hx]
      exact (piOneMul_assoc _ _ _).symm
  | combineRight x y rest =>
      rw [pushoutDecode_consRight (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x (.consRight y rest)]
      rw [pushoutDecode_consRight (A := A) (B := B) (C := C) (f := f) (g := g) c₀ y rest]
      rw [pushoutDecode_consRight (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (x + y) rest]
      have hx :
          pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (x + y) =
            piOneMul
              (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x)
              (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ y) := by
        simpa using (pushoutPiOneInr_mul (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x y)
      rw [hx]
      exact (piOneMul_assoc _ _ _).symm
  | removeLeftZero rest =>
      rw [pushoutDecode_consLeft (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (0 : π₁(A, f c₀)) rest]
      have hz :
          pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (0 : π₁(A, f c₀)) =
            Quot.mk _ (Path.refl (Pushout.inl (f c₀))) :=
        pushoutPiOneInl_zero (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      rw [hz]
      exact piOneMul_refl_left _
  | removeRightZero rest =>
      rw [pushoutDecode_consRight (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (0 : π₁(B, g c₀)) rest]
      have hz :
          pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (0 : π₁(B, g c₀)) =
            Quot.mk _ (Path.refl (Pushout.inl (f c₀))) :=
        pushoutPiOneInr_zero (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      rw [hz]
      exact piOneMul_refl_left _
  | congrLeft x _ ih =>
      simpa [pushoutDecode_consLeft] using
        _root_.congrArg
          (piOneMul (pushoutPiOneInl (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x)) ih
  | congrRight y _ ih =>
      simpa [pushoutDecode_consRight] using
        _root_.congrArg
          (piOneMul (pushoutPiOneInr (A := A) (B := B) (C := C) (f := f) (g := g) c₀ y)) ih

set_option maxHeartbeats 400000 in
/-- Decode at the *full* amalgamated free product level (amalgamation + free group reduction). -/
noncomputable def pushoutDecodeFullAmalg
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀] :
    FullAmalgamatedFreeProduct (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
      (piOneFmap c₀) (piOneGmap c₀) →
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
  Quot.lift (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀) (by
    intro w₁ w₂ h
    induction h with
    | refl _ => rfl
    | amalg hr =>
        cases hr with
        | amalgLeftToRight hh pre suf =>
            have hl : FreeProductWord.concat (FreeProductWord.consLeft (piOneFmap c₀ hh) .nil) suf =
                      FreeProductWord.consLeft (piOneFmap c₀ hh) suf := rfl
            have hr' : FreeProductWord.concat (FreeProductWord.consRight (piOneGmap c₀ hh) .nil) suf =
                       FreeProductWord.consRight (piOneGmap c₀ hh) suf := rfl
            simp only [FreeProductWord.singleLeft, FreeProductWord.singleRight, hl, hr']
            rw [pushoutDecode_concat, pushoutDecode_concat]
            apply _root_.congrArg (piOneMul (pushoutDecode c₀ pre))
            exact pushoutDecode_respects_amalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ hh suf
        | amalgRightToLeft hh pre suf =>
            have hl : FreeProductWord.concat (FreeProductWord.consRight (piOneGmap c₀ hh) .nil) suf =
                      FreeProductWord.consRight (piOneGmap c₀ hh) suf := rfl
            have hr' : FreeProductWord.concat (FreeProductWord.consLeft (piOneFmap c₀ hh) .nil) suf =
                       FreeProductWord.consLeft (piOneFmap c₀ hh) suf := rfl
            simp only [FreeProductWord.singleLeft, FreeProductWord.singleRight, hl, hr']
            rw [pushoutDecode_concat, pushoutDecode_concat]
            apply _root_.congrArg (piOneMul (pushoutDecode c₀ pre))
            exact (pushoutDecode_respects_amalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ hh suf).symm
    | freeGroup hs =>
        exact pushoutDecode_respects_freeGroupStep (A := A) (B := B) (C := C) (f := f) (g := g) c₀ hs
    | symm _ ih => exact ih.symm
    | trans _ _ ih1 ih2 => exact ih1.trans ih2)

/-- Encode into the full amalgamated free product by quotienting the word-level encode. -/
noncomputable def pushoutEncodeFullAmalg
    [HasPushoutSVKEncodeQuot A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
      PushoutFullAmalgamatedFreeProduct (A := A) (B := B) (C := C) (f := f) (g := g) c₀ :=
  fun α => FullAmalgamatedFreeProduct.ofWord (pushoutEncodeQuot (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α)

/-- Round-trip law: `encode ∘ decode` gives a *full-amalgamation-equivalent* word. -/
class HasPushoutSVKEncodeDecodeFull (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeQuot A B C f g c₀] : Prop where
  encode_decode_full :
    ∀ w : PushoutCode A B C f g c₀,
      FullAmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
        (pushoutEncodeQuotAxiom A B C f g c₀ (pushoutDecode c₀ w)) w

noncomputable instance (priority := 100) hasPushoutSVKEncodeDecodeFull_of_encodeDecode
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKEncodeDecode A B C f g c₀] :
    HasPushoutSVKEncodeDecodeFull A B C f g c₀ where
  encode_decode_full := by
    intro w
    exact FullAmalgEquiv.of_amalgEquiv (pushoutEncodeDecodeAxiom (A := A) (B := B) (C := C) (f := f) (g := g) c₀ w)

/-- Full SVK equivalence: π₁(Pushout) ≃ FullAmalgamatedFreeProduct (amalgamation + free reduction). -/
noncomputable def seifertVanKampenFullEquiv
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀]
    [HasPushoutSVKDecodeEncode A B C f g c₀]
    [HasPushoutSVKEncodeDecodeFull A B C f g c₀] :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (PushoutFullAmalgamatedFreeProduct (A := A) (B := B) (C := C) (f := f) (g := g) c₀) where
  toFun := pushoutEncodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  invFun := pushoutDecodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  left_inv := by
    intro α
    induction α using Quot.ind with
    | _ p =>
      simp only [pushoutEncodeFullAmalg, pushoutEncodeQuot, pushoutDecodeFullAmalg,
        FullAmalgamatedFreeProduct.ofWord]
      exact pushoutDecodeEncodeAxiom A B C f g c₀ p
  right_inv := by
    intro x
    induction x using Quot.ind with
    | _ w =>
      simp only [pushoutDecodeFullAmalg, pushoutEncodeFullAmalg, pushoutEncodeQuot,
        FullAmalgamatedFreeProduct.ofWord]
      apply Quot.sound
      exact HasPushoutSVKEncodeDecodeFull.encode_decode_full (A := A) (B := B) (C := C) (f := f) (g := g)
        (c₀ := c₀) w

end FullSVK

/-- Prop-level SVK interface: the *full* decode map (amalgamation + free reduction) is bijective.

This is an "encode-free" assumption: given bijectivity of `pushoutDecodeFullAmalg`,
we can construct an `encode` map by classical choice and recover the full SVK equivalence. -/
class HasPushoutSVKDecodeFullAmalgBijective (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀] : Prop where
  bijective :
    Function.Injective
        (pushoutDecodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) ∧
      Function.Surjective
      (pushoutDecodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀)

noncomputable instance (priority := 200) hasPushoutSVKDecodeFullAmalgBijective_of_encode
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀]
    [HasPushoutSVKDecodeEncode A B C f g c₀]
    [HasPushoutSVKEncodeDecodeFull A B C f g c₀] :
    HasPushoutSVKDecodeFullAmalgBijective A B C f g c₀ where
  bijective := by
    refine ⟨?_, ?_⟩
    · intro x₁ x₂ h
      let e :=
        seifertVanKampenFullEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      calc
        x₁ = e.toFun (e.invFun x₁) := (e.right_inv x₁).symm
        _ = e.toFun (e.invFun x₂) := _root_.congrArg e.toFun h
        _ = x₂ := e.right_inv x₂
    · intro α
      let e :=
        seifertVanKampenFullEquiv (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      refine ⟨e.toFun α, e.left_inv α⟩

/-- Choice-based full SVK equivalence: requires only Prop-level bijectivity of full decode. -/
noncomputable def seifertVanKampenFullEquiv_of_decodeFullAmalg_bijective
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeFullAmalgBijective A B C f g c₀] :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (PushoutFullAmalgamatedFreeProduct (A := A) (B := B) (C := C) (f := f) (g := g) c₀) where
  toFun := by
    classical
    intro α
    exact
      Classical.choose
        ((HasPushoutSVKDecodeFullAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
              (g := g) (c₀ := c₀)).2
          α)
  invFun := pushoutDecodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  left_inv := by
    classical
    intro α
    simpa using
      Classical.choose_spec
        ((HasPushoutSVKDecodeFullAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
              (g := g) (c₀ := c₀)).2
          α)
  right_inv := by
    classical
    intro x
    have hinj :
        Function.Injective
          (pushoutDecodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) :=
      (HasPushoutSVKDecodeFullAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f) (g := g)
            (c₀ := c₀)).1
    apply hinj
    simpa using
      Classical.choose_spec
        ((HasPushoutSVKDecodeFullAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
              (g := g) (c₀ := c₀)).2
          (pushoutDecodeFullAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x))

/-- Left-inverse at the amalgamated free product level:
`pushoutDecodeAmalg c₀ (pushoutEncodeAmalg c₀ α) = α`. -/
theorem pushoutDecodeAmalg_encodeAmalg (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKDecodeEncode A B C f g c₀]
    (α : π₁(Pushout A B C f g, Pushout.inl (f c₀))) :
    pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
      (pushoutEncodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α) = α := by
  induction α using Quot.ind with
  | _ p =>
    simp only [pushoutEncodeAmalg, pushoutEncodeQuot, pushoutDecodeAmalg,
      AmalgamatedFreeProduct.ofWord]
    exact pushoutDecodeEncodeAxiom A B C f g c₀ p

/-- `pushoutDecodeAmalg` is surjective assuming only the `decode ∘ encode` law. -/
theorem pushoutDecodeAmalg_surjective (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKDecodeEncode A B C f g c₀] :
    Function.Surjective
      (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) := by
  intro α
  refine ⟨pushoutEncodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ α, ?_⟩
  exact pushoutDecodeAmalg_encodeAmalg A B C f g c₀ α

/-- `pushoutEncodeAmalg` is injective assuming only the `decode ∘ encode` law. -/
theorem pushoutEncodeAmalg_injective (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKDecodeEncode A B C f g c₀] :
    Function.Injective
      (pushoutEncodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) := by
  -- `decode` is a left inverse of `encode`.
  refine (fun α₁ α₂ h => ?_)
  have h' :=
    _root_.congrArg
      (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) h
  simpa [pushoutDecodeAmalg_encodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀)]
    using h'

/-- Right-inverse at the amalgamated free product level:
`pushoutEncodeAmalg c₀ (pushoutDecodeAmalg c₀ x) = x`. -/
theorem pushoutEncodeAmalg_decodeAmalg (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKEncodeDecode A B C f g c₀]
    (x :
      AmalgamatedFreeProduct (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
        (piOneFmap c₀) (piOneGmap c₀)) :
    pushoutEncodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x) =
      x := by
  induction x using Quot.ind with
  | _ w =>
    simp only [pushoutDecodeAmalg, pushoutEncodeAmalg, pushoutEncodeQuot,
      AmalgamatedFreeProduct.ofWord]
    apply Quot.sound
    exact pushoutEncodeDecodeAxiom A B C f g c₀ w

/-- `pushoutEncodeAmalg` is surjective assuming only the `encode ∘ decode` law. -/
theorem pushoutEncodeAmalg_surjective (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKEncodeDecode A B C f g c₀] :
    Function.Surjective
      (pushoutEncodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) := by
  intro x
  refine ⟨pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x, ?_⟩
  exact pushoutEncodeAmalg_decodeAmalg A B C f g c₀ x

/-- `pushoutDecodeAmalg` is injective assuming only the `encode ∘ decode` law. -/
theorem pushoutDecodeAmalg_injective (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀] [HasPushoutSVKEncodeDecode A B C f g c₀] :
    Function.Injective
      (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) := by
  refine (fun x₁ x₂ h => ?_)
  have h' :=
    _root_.congrArg
      (pushoutEncodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) h
  simpa [pushoutEncodeAmalg_decodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀)]
    using h'

/-- Prop-level SVK interface: the *decode* map at the amalgamated free product level is bijective.

**DEPRECATED**: This class is provably unsatisfiable for all types.
`AmalgEquiv` preserves word length, so `Quot.mk nil` and
`Quot.mk (consLeft 0 nil)` are distinct amalgam classes (word lengths 0 vs 1),
yet both decode to the identity in π₁. Therefore `pushoutDecodeAmalg` is never
injective and the bijectivity requirement cannot be satisfied.

Use `HasPushoutSVKDecodeFullAmalgBijective` instead, which quotients by
`FullAmalgEquiv` (amalgamation + free group reduction), collapsing
`consLeft 0 nil` to `nil`.

See `PushoutSVKInstances.hasPushoutSVKDecodeAmalgBijective_impossible_PUnit`
for the formal impossibility proof. -/
-- DEPRECATED: Provably unsatisfiable — AmalgEquiv preserves word length.
class HasPushoutSVKDecodeAmalgBijective (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀] : Prop where
  bijective :
    Function.Injective
        (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) ∧
      Function.Surjective
      (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀)

noncomputable instance (priority := 200) hasPushoutSVKDecodeAmalgBijective_of_encode
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀]
    [HasPushoutSVKDecodeEncode A B C f g c₀]
    [HasPushoutSVKEncodeDecode A B C f g c₀] :
    HasPushoutSVKDecodeAmalgBijective A B C f g c₀ where
  bijective :=
    ⟨pushoutDecodeAmalg_injective (A := A) (B := B) (C := C) (f := f) (g := g) c₀,
      pushoutDecodeAmalg_surjective (A := A) (B := B) (C := C) (f := f) (g := g) c₀⟩

/-- Choice-based SVK equivalence: requires only Prop-level bijectivity of decode (no explicit encode map). -/
noncomputable def seifertVanKampenEquiv_of_decodeAmalg_bijective
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀] :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀)) where
  toFun := by
    classical
    intro α
    exact
      Classical.choose
        ((HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
              (g := g) (c₀ := c₀)).2
          α)
  invFun := pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
  left_inv := by
    classical
    intro α
    simpa using
      Classical.choose_spec
        ((HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
              (g := g) (c₀ := c₀)).2
          α)
  right_inv := by
    classical
    intro x
    -- Use injectivity of decode and the chosen preimage equation.
    have hinj :
        Function.Injective
          (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) :=
      (HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f) (g := g)
            (c₀ := c₀)).1
    apply hinj
    simpa using
      Classical.choose_spec
        ((HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
              (g := g) (c₀ := c₀)).2
          (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x))

private noncomputable def quotRel {α : Sort u} (r : α → α → Prop) (hr : Equivalence r) : Quot r → Quot r → Prop :=
  fun q₁ q₂ =>
    Quot.liftOn q₁
      (fun a₁ =>
        Quot.liftOn q₂
          (fun a₂ => r a₁ a₂)
          (fun a₂ b₂ hab =>
            propext
              ⟨fun ha => Equivalence.trans hr ha hab,
               fun hb => Equivalence.trans hr hb (Equivalence.symm hr hab)⟩))
      (fun a₁ b₁ hab => by
        induction q₂ using Quot.inductionOn with
        | _ a₂ =>
            apply propext
            constructor
            · intro ha
              exact Equivalence.trans hr (Equivalence.symm hr hab) ha
            · intro hb
              exact Equivalence.trans hr hab hb)


private theorem rel_of_quot_mk_eq {α : Sort u} {r : α → α → Prop} (hr : Equivalence r) {a b : α} :
    Quot.mk r a = Quot.mk r b → r a b := by
  intro h
  have hrefl : quotRel r hr (Quot.mk r a) (Quot.mk r a) := by
    simpa [quotRel] using Equivalence.refl hr a
  have hab : quotRel r hr (Quot.mk r a) (Quot.mk r b) := by
    simpa [h] using hrefl
  simpa [quotRel] using hab

private theorem amalgEquiv_equivalence {G₁ G₂ H : Type u} (i₁ : H → G₁) (i₂ : H → G₂) :
    Equivalence (AmalgEquiv i₁ i₂) := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    exact AmalgEquiv.refl w
  · intro w₁ w₂ h
    exact AmalgEquiv.symm h
  · intro w₁ w₂ w₃ h₁ h₂
    exact AmalgEquiv.trans h₁ h₂

/-- Choice-based encode into the amalgamated free product, derived from bijectivity of decode. -/
noncomputable def pushoutEncodeAmalg_of_decodeAmalg_bijective
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
      AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀) := by
  classical
  intro α
  exact
    Classical.choose
      ((HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
            (g := g) (c₀ := c₀)).2
        α)

/-- Round-trip: decode after the choice-based encode (at amalgam level) gives back the original. -/
theorem pushoutDecodeAmalg_encodeAmalg_of_decodeAmalg_bijective
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀]
    (α : π₁(Pushout A B C f g, Pushout.inl (f c₀))) :
    pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (pushoutEncodeAmalg_of_decodeAmalg_bijective A B C f g c₀ α) =
      α := by
  classical
  simpa [pushoutEncodeAmalg_of_decodeAmalg_bijective] using
    Classical.choose_spec
      ((HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f)
            (g := g) (c₀ := c₀)).2
        α)

/-- Choice-based encode at word level, derived from bijectivity of `pushoutDecodeAmalg`. -/
noncomputable def pushoutEncodeQuot_of_decodeAmalg_bijective
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
      PushoutCode A B C f g c₀ := by
  classical
  intro α
  exact
    Classical.choose
      (Quot.exists_rep
        (pushoutEncodeAmalg_of_decodeAmalg_bijective A B C f g c₀ α))

/-- Round-trip: decode after the choice-based word-level encode gives back the original. -/
theorem pushoutDecode_encodeQuot_of_decodeAmalg_bijective
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀]
    (α : π₁(Pushout A B C f g, Pushout.inl (f c₀))) :
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀
        (pushoutEncodeQuot_of_decodeAmalg_bijective A B C f g c₀ α) =
      α := by
  classical
  let x :
      AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀) :=
    pushoutEncodeAmalg_of_decodeAmalg_bijective A B C f g c₀ α
  have hx :
      pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x = α :=
    pushoutDecodeAmalg_encodeAmalg_of_decodeAmalg_bijective A B C f g c₀ α
  have hw :
      (Quot.mk _ (pushoutEncodeQuot_of_decodeAmalg_bijective A B C f g c₀ α) :
          AmalgamatedFreeProduct
            (π₁(A, f c₀))
            (π₁(B, g c₀))
            (π₁(C, c₀))
            (piOneFmap c₀)
            (piOneGmap c₀)) =
        x := by
    simpa [pushoutEncodeQuot_of_decodeAmalg_bijective, x] using
      (Classical.choose_spec (Quot.exists_rep x))
  have h := hx
  rw [← hw] at h
  simpa [pushoutDecodeAmalg] using h

/-- Round-trip: the choice-based word-level encode is an amalgamation representative. -/
theorem pushoutEncodeQuot_decode_of_decodeAmalg_bijective
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀]
    (w : PushoutCode A B C f g c₀) :
    AmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
      (pushoutEncodeQuot_of_decodeAmalg_bijective A B C f g c₀
          (pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ w))
      w := by
  classical
  let α : π₁(Pushout A B C f g, Pushout.inl (f c₀)) :=
    pushoutDecode (A := A) (B := B) (C := C) (f := f) (g := g) c₀ w
  let x :
      AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀) :=
    pushoutEncodeAmalg_of_decodeAmalg_bijective A B C f g c₀ α
  let w' : PushoutCode A B C f g c₀ :=
    pushoutEncodeQuot_of_decodeAmalg_bijective A B C f g c₀ α
  have hw' :
      (Quot.mk _ w' :
          AmalgamatedFreeProduct
            (π₁(A, f c₀))
            (π₁(B, g c₀))
            (π₁(C, c₀))
            (piOneFmap c₀)
            (piOneGmap c₀)) =
        x := by
    simpa [pushoutEncodeQuot_of_decodeAmalg_bijective, w', x] using
      (Classical.choose_spec (Quot.exists_rep x))
  have hx :
      pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ x = α :=
    pushoutDecodeAmalg_encodeAmalg_of_decodeAmalg_bijective A B C f g c₀ α
  have hx0 :
      pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀ (Quot.mk _ w) = α := by
    simp [pushoutDecodeAmalg, α]
  have hinj :
      Function.Injective
        (pushoutDecodeAmalg (A := A) (B := B) (C := C) (f := f) (g := g) c₀) :=
    (HasPushoutSVKDecodeAmalgBijective.bijective (A := A) (B := B) (C := C) (f := f) (g := g)
          (c₀ := c₀)).1
  have hxEq :
      x =
        (Quot.mk _ w :
          AmalgamatedFreeProduct
            (π₁(A, f c₀))
            (π₁(B, g c₀))
            (π₁(C, c₀))
            (piOneFmap c₀)
            (piOneGmap c₀)) := by
    apply hinj
    exact hx.trans hx0.symm
  have hquot :
      (Quot.mk _ w' :
          AmalgamatedFreeProduct
            (π₁(A, f c₀))
            (π₁(B, g c₀))
            (π₁(C, c₀))
            (piOneFmap c₀)
            (piOneGmap c₀)) =
        Quot.mk _ w := by
    calc
      (Quot.mk _ w' :
          AmalgamatedFreeProduct
            (π₁(A, f c₀))
            (π₁(B, g c₀))
            (π₁(C, c₀))
            (piOneFmap c₀)
            (piOneGmap c₀)) =
          x := hw'
      _ = Quot.mk _ w := hxEq
  exact
    rel_of_quot_mk_eq
      (r := AmalgEquiv (piOneFmap c₀) (piOneGmap c₀))
      (hr := amalgEquiv_equivalence (piOneFmap c₀) (piOneGmap c₀))
      hquot

/-- Recover the full SVK encode/decode package from Prop-level bijectivity of decode. -/
noncomputable def hasPushoutSVKEncodeData_of_decodeAmalg_bijective
    (A : Type u) (B : Type u) (C : Type u) (f : C → A) (g : C → B) (c₀ : C)
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKDecodeAmalgBijective A B C f g c₀] :
    HasPushoutSVKEncodeData A B C f g c₀ where
  encodeQuot := pushoutEncodeQuot_of_decodeAmalg_bijective A B C f g c₀
  decode_encode := by
    intro p
    simpa using
      pushoutDecode_encodeQuot_of_decodeAmalg_bijective A B C f g c₀ (Quot.mk _ p)
  encode_decode := by
    intro w
    simpa using pushoutEncodeQuot_decode_of_decodeAmalg_bijective A B C f g c₀ w

noncomputable def seifertVanKampenEquiv
    [HasGlueNaturalLoopRwEq (A := A) (B := B) (C := C) (f := f) (g := g) c₀]
    [HasPushoutSVKEncodeQuot A B C f g c₀]
    [HasPushoutSVKDecodeEncode A B C f g c₀]
    [HasPushoutSVKEncodeDecode A B C f g c₀] :
    SimpleEquiv
      (π₁(Pushout A B C f g, Pushout.inl (f c₀)))
      (AmalgamatedFreeProduct
        (π₁(A, f c₀))
        (π₁(B, g c₀))
        (π₁(C, c₀))
        (piOneFmap c₀)
        (piOneGmap c₀)) where
  toFun := pushoutEncodeAmalg c₀
  invFun := pushoutDecodeAmalg c₀
  left_inv := by
    intro α
    induction α using Quot.ind with
    | _ p =>
      simp only [pushoutEncodeAmalg, pushoutEncodeQuot, pushoutDecodeAmalg,
                 AmalgamatedFreeProduct.ofWord]
      exact pushoutDecodeEncodeAxiom A B C f g c₀ p
  right_inv := by
    intro x
    induction x using Quot.ind with
    | _ w =>
      simp only [pushoutDecodeAmalg, pushoutEncodeAmalg, pushoutEncodeQuot,
                 AmalgamatedFreeProduct.ofWord]
      apply Quot.sound
      exact pushoutEncodeDecodeAxiom A B C f g c₀ w

end SVK

/-! ## Special Case: Wedge Sum (Free Product)

When C = Unit (a single point), the amalgamated free product reduces
to the ordinary free product, since π₁(pt) is trivial.
-/

section WedgeSVK

variable {A : Type u} {B : Type u}
variable (a₀ : A) (b₀ : B)

/-! ### Wedge Sum Fundamental Group

For the wedge sum A ∨ B, the fundamental group is the free product π₁(A) * π₁(B).
We construct this via the encode-decode method:

1. **Decode**: Convert a word in π₁(A) * π₁(B) to a loop in A ∨ B
2. **Encode**: Extract the word structure from a loop in A ∨ B
3. **Round-trip**: Show encode ∘ decode and decode ∘ encode are identity

The key insight is that paths in a wedge sum decompose uniquely into
alternating segments from A and B, connected by the glue path.
-/

/-- The free product code type for wedge loops at the π₁ level.
Words are sequences of fundamental group elements (equivalence classes of loops). -/
abbrev WedgeFreeProductCode : Type u :=
  FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))

/-- Decode: Map a word to a fundamental group element of the wedge.
Each π₁ element is sent to its image in π₁(Wedge). -/
noncomputable def wedgeFreeProductDecode :
    WedgeFreeProductCode a₀ b₀ → π₁(Wedge A B a₀ b₀, Wedge.basepoint)
  | .nil => Quot.mk _ (Path.refl _)
  | .consLeft α rest =>
      -- α : π₁(A, a₀), map α to π₁(Wedge) via inl, then multiply with rest
       let αInWedge : π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
         Quot.lift
          (fun p => Quot.mk _ (Pushout.inlPath p))
          (fun _ _ hp =>
            Quot.sound (rweqProp_of_rweq (rweq_congrArg_of_rweq Pushout.inl (rweq_of_rweqProp hp))))
          α
       piOneMul αInWedge (wedgeFreeProductDecode rest)
  | .consRight β rest =>
      -- β : π₁(B, b₀), wrap with glue path: glue ⋅ inrPath ⋅ glue⁻¹ ⋅ rest
        let βInWedge : π₁(Wedge A B a₀ b₀, Wedge.basepoint) :=
          Quot.lift
           (fun p => Quot.mk _ (Path.trans
               (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
               (Path.trans (Pushout.inrPath p)
                 (Path.symm (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))))))
          (fun _ _ hp => Quot.sound (rweqProp_of_rweq (
            rweq_trans_congr_right _ (rweq_trans_congr_left _
              (rweq_congrArg_of_rweq Pushout.inr (rweq_of_rweqProp hp))))))
           β
       piOneMul βInWedge (wedgeFreeProductDecode rest)

/-- Prop-level wedge interface: the *decode* map from free product words is bijective.

This allows constructing an `encode` map by classical choice, without assuming
any explicit wedge encode data. -/
class HasWedgeSVKDecodeBijective (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) : Prop where
  bijective :
    Function.Injective (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀) ∧
      Function.Surjective (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀)

/-- Choice-based wedge equivalence: requires only Prop-level bijectivity of decode. -/
noncomputable def wedgeFundamentalGroupEquiv_of_decode_bijective
    [HasWedgeSVKDecodeBijective A B a₀ b₀] :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode (A := A) (B := B) a₀ b₀) where
  toFun := by
    classical
    intro α
    exact
      Classical.choose
        ((HasWedgeSVKDecodeBijective.bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).2
          α)
  invFun := wedgeFreeProductDecode (A := A) (B := B) a₀ b₀
  left_inv := by
    classical
    intro α
    simpa using
      Classical.choose_spec
        ((HasWedgeSVKDecodeBijective.bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).2
          α)
  right_inv := by
    classical
    intro w
    have hinj :
        Function.Injective (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀) :=
      (HasWedgeSVKDecodeBijective.bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).1
    apply hinj
    simpa using
      Classical.choose_spec
        ((HasWedgeSVKDecodeBijective.bijective (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)).2
          (wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ w))

/-- The decode map respects concatenation of words.
This follows from the associativity of path composition (rweq_tt) and the
identity law (rweq_cmpA_refl_left). -/
theorem wedgeFreeProductDecode_concat (w₁ w₂ : WedgeFreeProductCode a₀ b₀) :
    wedgeFreeProductDecode a₀ b₀ (FreeProductWord.concat w₁ w₂) =
    piOneMul (wedgeFreeProductDecode a₀ b₀ w₁) (wedgeFreeProductDecode a₀ b₀ w₂) := by
  induction w₁ with
  | nil =>
      -- concat nil w₂ = w₂, decode nil = Quot.mk _ (refl _)
      -- Need: decode w₂ = piOneMul (Quot.mk _ refl) (decode w₂)
      simp only [FreeProductWord.concat, wedgeFreeProductDecode]
      exact (piOneMul_refl_left _).symm
  | consLeft α rest ih =>
      -- concat (consLeft α rest) w₂ = consLeft α (concat rest w₂)
      -- decode(consLeft α (concat rest w₂)) = piOneMul αInWedge (decode(concat rest w₂))
      -- By ih: decode(concat rest w₂) = piOneMul (decode rest) (decode w₂)
      -- So decode(consLeft α (concat rest w₂)) = piOneMul αInWedge (piOneMul (decode rest) (decode w₂))
      -- By associativity: = piOneMul (piOneMul αInWedge (decode rest)) (decode w₂)
      --                  = piOneMul (decode(consLeft α rest)) (decode w₂)
      simp only [FreeProductWord.concat, wedgeFreeProductDecode]
      rw [ih]
      exact (piOneMul_assoc _ _ _).symm
  | consRight β rest ih =>
      -- Same pattern: use ih and associativity
      simp only [FreeProductWord.concat, wedgeFreeProductDecode]
      rw [ih]
      exact (piOneMul_assoc _ _ _).symm

/-! Encode function for wedge loops.

The encode function extracts word structure from a loop. The key insight is that
any loop at the basepoint is RwEq-equivalent to one built from:
- Paths within inl(A) → left letters
- Glue-inrPath-glue⁻¹ sequences → right letters

Since we work with π₁ (quotient by RwEq), encode only needs to be well-defined
on equivalence classes, which follows from RwEq implying equal underlying equality.

**Implementation**: We define encode directly using the property that RwEq-equivalent
paths have equal underlying equality (p.toEq = q.toEq), so any reasonable encoding
function is well-defined on the quotient.

 The actual word extraction would normally use a code family. In this codebase we
 expose the missing encode direction for wedge sums via the explicit typeclass
`WedgeSVKInstances.HasWedgeSVKEncodeData` (see the `WedgeEncodeAPI` re-export near
the end of this file). -/

/-- `wedgeFreeProductDecode` is `pushoutDecode` specialised to `PUnit'`. -/
theorem wedgeFreeProductDecode_eq_pushoutDecode (a₀ : A) (b₀ : B) :
    wedgeFreeProductDecode (A := A) (B := B) a₀ b₀ =
      pushoutDecode (A := A) (B := B) (C := PUnit')
        (f := fun _ : PUnit' => a₀)
        (g := fun _ : PUnit' => b₀)
        PUnit'.unit := by
  funext w
  induction w with
  | nil => rfl
  | consLeft α rest ih =>
      simp only [wedgeFreeProductDecode, pushoutDecode_consLeft, pushoutPiOneInl, ih]
  | consRight β rest ih =>
      simp only [wedgeFreeProductDecode, pushoutDecode_consRight, pushoutPiOneInr, ih, Wedge.glue]

/-! Decode after encode gives back the original loop (at π₁ level).

This is the key round-trip property: encoding a loop extracts its word structure,
and decoding that word reconstructs a loop in the same equivalence class.

In the code family approach, this follows from:
1. Transport along refl is identity
2. Transport along inlPath α corresponds to prepending a left letter
3. Transport along glue sequences corresponds to prepending a right letter
4. decode reverses these operations exactly -/
-- (The round-trip property is re-stated later as `wedgeDecodeEncodeAxiom`,
-- now under the minimal wedge-specific assumptions.)

/-! The fundamental group of a wedge sum is the free product.

This is the simplest case of SVK where the gluing space is a point.
Use `wedgeFundamentalGroupEquiv_of_decode_bijective` with
`HasWedgeSVKDecodeBijective` instead of a bespoke wrapper assumption. -/

end WedgeSVK


/-! ## Concrete SVK Instances for Wedge Sums

For wedge sums A ∨ B (where C = PUnit'), we can provide concrete instances
of the SVK typeclasses. The encode direction depends on additional structure
captured by typeclasses, while the key properties follow from path analysis
in wedge sums.
-/

namespace WedgeSVKInstances

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

/-- Encode/decode data for wedge sums (explicit assumption).

This packages the missing encode direction for wedge sums as a typeclass,
so no kernel assumptions are introduced by importing `PushoutPaths.lean`.

It is intentionally stronger than `HasPushoutSVKEncodeData` for the wedge case:
we assume `encode ∘ decode = id` as an equality on words (not just `AmalgEquiv`). -/
class HasWedgeSVKEncodeQuot (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) : Type u where
  /-- Encode at the quotient level: π₁(Wedge) → FreeProductWord. -/
  encodeQuot :
      π₁(Wedge A B a₀ b₀, Wedge.basepoint) →
      FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))

/-- Encode at the quotient level (from `HasWedgeSVKEncodeQuot`). -/
noncomputable def wedgeEncodeQuotPrim [HasWedgeSVKEncodeQuot A B a₀ b₀] :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) →
    FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
  HasWedgeSVKEncodeQuot.encodeQuot (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

/-- Round-trip law: `decode ∘ encode = id` (at π₁ level). -/
class HasWedgeSVKDecodeEncode (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [HasWedgeSVKEncodeQuot A B a₀ b₀] : Prop where
  decode_encode :
    ∀ p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint,
      pushoutDecode (A := A) (B := B) (C := PUnit')
          (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit
          (wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀ (Quot.mk _ p)) = Quot.mk _ p

/-- Round-trip law: `encode ∘ decode = id` on words (wedge case).

**DEPRECATED**: This class is provably unsatisfiable for all types.
The strict word-level round-trip `encodeQuot (pushoutDecode w) = w` requires
`pushoutDecode` to be injective on raw `FreeProductWord`s, but `nil` and
`consLeft 0 nil` both decode to the identity in π₁ while being structurally
distinct words. Therefore no `encodeQuot` can return `nil` for one and
`consLeft 0 nil` for the other.

Use `HasPushoutSVKEncodeDecodeFull` (or `HasWedgeSVKEncodeDataFull` from
`PushoutSVKInstances.lean`) instead, which uses `FullAmalgEquiv`.

See `WedgeSVKCircleInstances.not_hasWedgeSVKEncodeDecode_Circle` and
`PushoutSVKInstances.hasWedgeSVKEncodeData_impossible_PUnit` for the
formal impossibility proofs. -/
-- DEPRECATED: Provably unsatisfiable — nil vs consLeft(0,nil) obstruction.
class HasWedgeSVKEncodeDecode (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [HasWedgeSVKEncodeQuot A B a₀ b₀] : Prop where
  encode_decode :
    ∀ w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)),
      wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀
          (pushoutDecode (A := A) (B := B) (C := PUnit')
            (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit w) = w

/-- Full encode/decode data for wedge sums (both round-trip laws). -/
-- DEPRECATED: Contains impossible field (encode_decode); see HasWedgeSVKEncodeDecode.
class HasWedgeSVKEncodeData (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) : Type u extends
    HasWedgeSVKEncodeQuot A B a₀ b₀ where
  /-- `decode ∘ encode = id` on loop representatives (hence on π₁). -/
  decode_encode :
      ∀ p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint,
        pushoutDecode (A := A) (B := B) (C := PUnit')
          (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit
          (encodeQuot (Quot.mk _ p)) = Quot.mk _ p

  /-- `encode ∘ decode = id` as an equality on words (wedge case). -/
  encode_decode :
      ∀ w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)),
        encodeQuot
          (pushoutDecode (A := A) (B := B) (C := PUnit')
            (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit w) = w

noncomputable instance (priority := 100) hasWedgeSVKDecodeEncode_of_encodeData
    (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) [HasWedgeSVKEncodeData A B a₀ b₀] :
    HasWedgeSVKDecodeEncode A B a₀ b₀ where
  decode_encode :=
    HasWedgeSVKEncodeData.decode_encode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

noncomputable instance (priority := 100) hasWedgeSVKEncodeDecode_of_encodeData
    (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) [HasWedgeSVKEncodeData A B a₀ b₀] :
    HasWedgeSVKEncodeDecode A B a₀ b₀ where
  encode_decode :=
    HasWedgeSVKEncodeData.encode_decode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)

/-- `decode ∘ encode = id` on loop representatives (from `HasWedgeSVKEncodeData`). -/
theorem wedgeDecodeEncodePrim
    [HasWedgeSVKEncodeQuot A B a₀ b₀] [HasWedgeSVKDecodeEncode A B a₀ b₀]
    (p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint) :
    pushoutDecode (A := A) (B := B) (C := PUnit')
      (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit
      (wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀ (Quot.mk _ p)) = Quot.mk _ p :=
  HasWedgeSVKDecodeEncode.decode_encode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) p

/-- `encode ∘ decode = id` on words (from `HasWedgeSVKEncodeData`). -/
theorem wedgeEncodeDecodeQuotPrim
    [HasWedgeSVKEncodeQuot A B a₀ b₀] [HasWedgeSVKEncodeDecode A B a₀ b₀]
    (w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀
      (pushoutDecode (A := A) (B := B) (C := PUnit')
        (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit w) = w :=
  HasWedgeSVKEncodeDecode.encode_decode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) w

/-- Wedge decode is bijective, derived from the explicit wedge encode/decode assumptions. -/
noncomputable instance (priority := 200) instHasWedgeSVKDecodeBijective_of_encode
    [HasWedgeSVKEncodeQuot A B a₀ b₀]
    [HasWedgeSVKDecodeEncode A B a₀ b₀]
    [HasWedgeSVKEncodeDecode A B a₀ b₀] :
    HasWedgeSVKDecodeBijective A B a₀ b₀ where
  bijective := by
    refine ⟨?_, ?_⟩
    · intro w₁ w₂ h
      have h' :=
        _root_.congrArg (wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀) h
      have hw₁ :
          wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀ (wedgeFreeProductDecode a₀ b₀ w₁) = w₁ := by
        simpa [wedgeFreeProductDecode_eq_pushoutDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)]
          using wedgeEncodeDecodeQuotPrim (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) w₁
      have hw₂ :
          wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀ (wedgeFreeProductDecode a₀ b₀ w₂) = w₂ := by
        simpa [wedgeFreeProductDecode_eq_pushoutDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)]
          using wedgeEncodeDecodeQuotPrim (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) w₂
      simpa [hw₁, hw₂] using h'
    · intro α
      induction α using Quot.ind with
      | _ p =>
        refine ⟨wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀ (Quot.mk _ p), ?_⟩
        simpa [wedgeFreeProductDecode_eq_pushoutDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)]
          using wedgeDecodeEncodePrim (A := A) (B := B) (a₀ := a₀) (b₀ := b₀) p

/-- AmalgEquiv version of wedgeEncodeDecodeQuotPrim for HasPushoutSVKEncodeData. -/
theorem wedgeEncodeDecodeQuotPrim_amalg
    [HasWedgeSVKEncodeQuot A B a₀ b₀] [HasWedgeSVKEncodeDecode A B a₀ b₀]
    (w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    AmalgEquiv
      (piOneFmap (A := A) (C := PUnit') (f := fun _ => a₀) PUnit'.unit)
      (piOneGmap (B := B) (C := PUnit') (g := fun _ => b₀) PUnit'.unit)
      (wedgeEncodeQuotPrim a₀ b₀
        (pushoutDecode (A := A) (B := B) (C := PUnit')
          (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit w))
      w := by
  rw [wedgeEncodeDecodeQuotPrim]
  exact AmalgEquiv.refl w

/-- Instance: HasPushoutSVKEncodeData for Wedge sums.

This provides the encode-decode infrastructure needed for SVK. -/
noncomputable instance hasPushoutSVKEncodeData [HasWedgeSVKEncodeData A B a₀ b₀] :
    HasPushoutSVKEncodeData A B PUnit'
      (fun _ => a₀) (fun _ => b₀) PUnit'.unit where
  encodeQuot := wedgeEncodeQuotPrim a₀ b₀
  decode_encode := fun p => by
    simp only [wedgeEncodeQuotPrim]
    exact wedgeDecodeEncodePrim a₀ b₀ p
  encode_decode := fun w => wedgeEncodeDecodeQuotPrim_amalg a₀ b₀ w

/- The wedge equivalence is obtained directly from
`wedgeFundamentalGroupEquiv_of_decode_bijective` or the wedge encode/decode
assumptions; no wrapper instance is needed. -/
end WedgeSVKInstances

/-! ## Wedge Encode API (minimal assumptions)

The legacy wedge-encode helpers in the `WedgeSVK` section used the generic
`HasPushoutSVKEncodeData` specialization to `PUnit'`. Now that wedge encoding is
packaged explicitly as `WedgeSVKInstances.HasWedgeSVKEncodeData`, we provide a
small API that depends only on this wedge-specific class.
-/

section WedgeEncodeAPI

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

/-- Encode on loop representatives, using the wedge-specific encode data. -/
noncomputable def wedgeEncodeAxiom (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [WedgeSVKInstances.HasWedgeSVKEncodeData A B a₀ b₀] :
    LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint →
      FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
  fun p =>
    WedgeSVKInstances.wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀ (Quot.mk _ p)

/-- Encode respects RwEq (as it factors through π₁). -/
noncomputable def wedgeEncodeAxiom_respects_rweq (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [WedgeSVKInstances.HasWedgeSVKEncodeData A B a₀ b₀]
    {p q : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint}
    (h : RwEq p q) :
    wedgeEncodeAxiom A B a₀ b₀ p = wedgeEncodeAxiom A B a₀ b₀ q := by
  unfold wedgeEncodeAxiom
  exact
    _root_.congrArg (WedgeSVKInstances.wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀)
      (Quot.sound h)

/-- Encode at the quotient level: π₁(Wedge) → FreeProductWord. -/
noncomputable def wedgeEncodeQuot
    [WedgeSVKInstances.HasWedgeSVKEncodeData A B a₀ b₀] :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) → WedgeFreeProductCode a₀ b₀ :=
  WedgeSVKInstances.wedgeEncodeQuotPrim (A := A) (B := B) a₀ b₀

/-- Computation rule for `wedgeEncodeQuot` on representatives. -/
@[simp] theorem wedgeEncodeQuot_mk
    [WedgeSVKInstances.HasWedgeSVKEncodeData A B a₀ b₀]
    (p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint) :
    wedgeEncodeQuot (A := A) (B := B) a₀ b₀ (Quot.mk _ p) =
      wedgeEncodeAxiom A B a₀ b₀ p :=
  rfl

/-- Decode after encode gives back the original loop (at π₁ level). -/
theorem wedgeDecodeEncodeAxiom (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [WedgeSVKInstances.HasWedgeSVKEncodeData A B a₀ b₀]
    (p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint) :
    wedgeFreeProductDecode a₀ b₀ (wedgeEncodeAxiom A B a₀ b₀ p) = Quot.mk _ p := by
  -- Reduce to the corresponding statement phrased with `pushoutDecode`.
  rw [wedgeFreeProductDecode_eq_pushoutDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)]
  simpa [wedgeEncodeAxiom] using
    WedgeSVKInstances.wedgeDecodeEncodePrim (A := A) (B := B) a₀ b₀ p

end WedgeEncodeAPI

/-! ## Summary

This module establishes:

1. **Free Product Words** (`FreeProductWord`): The representation of elements
   in a free product as alternating sequences.
   - `concat`: Concatenation of words
   - `inverse`: Word inverse (with `Neg` constraint)
   - `isReduced`: Predicate for reduced words (no adjacent same-side elements)

2. **Amalgamated Free Product** (`AmalgamatedFreeProduct`): The quotient of
   the free product by the amalgamation relation i₁(h) = i₂(h).
   - `mul`, `one`: Monoid structure
   - `inv`: Group inverse (requires amalgamation maps to commute with negation)
   - `mul_assoc'`, `one_mul'`, `mul_one'`: Monoid laws
   - `inv_one`, `inv_mul`: Inverse properties

3. **Wedge Decode** (`wedgeDecode`): Converts a word in π₁(A) * π₁(B) to
   an actual loop in the wedge sum A ∨ B.

4. **Induced Maps** (`piOneInl`, `piOneInr`): The functorial action of
   the pushout injections on fundamental groups.

5. **Seifert-Van Kampen** (`seifertVanKampenEquiv`): The statement that
   π₁(Pushout) ≃ π₁(A) *_{π₁(C)} π₁(B).

6. **Provenance Wedge Quotient** (`WedgeProvenance`): A provenance-based loop
   quotient for wedge sums together with `wedgeProvenanceEquiv`, giving a
   constructive SVK-style equivalence without assumptions.

The proofs use the computational paths framework where:
- Loops are computational paths (with explicit step structure)
- Path equality is rewrite equality (`RwEq`)
- The fundamental group is the quotient by rewrite equality
-/

end CompPath
end Path
end ComputationalPaths
