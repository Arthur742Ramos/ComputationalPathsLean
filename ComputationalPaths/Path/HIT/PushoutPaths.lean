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

import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

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

def flip : Side → Side
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
def concat : FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
  | nil, w₂ => w₂
  | consLeft x rest, w₂ => consLeft x (concat rest w₂)
  | consRight y rest, w₂ => consRight y (concat rest w₂)

/-- Length of a word. -/
def length : FreeProductWord G₁ G₂ → Nat
  | nil => 0
  | consLeft _ rest => 1 + length rest
  | consRight _ rest => 1 + length rest

/-- Singleton word from G₁. -/
def singleLeft (x : G₁) : FreeProductWord G₁ G₂ := consLeft x nil

/-- Singleton word from G₂. -/
def singleRight (y : G₂) : FreeProductWord G₁ G₂ := consRight y nil

/-- Reverse a word. -/
def reverse : FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
  | nil => nil
  | consLeft x rest => concat (reverse rest) (singleLeft x)
  | consRight y rest => concat (reverse rest) (singleRight y)

/-- Inverse of a word in a free product: reverse and negate each element.
This requires `Neg` instances on the component types (e.g., for ℤ). -/
def inverse [Neg G₁] [Neg G₂] : FreeProductWord G₁ G₂ → FreeProductWord G₁ G₂
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
def isReduced : FreeProductWord G₁ G₂ → Bool
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
def AmalgamatedFreeProduct (G₁ G₂ H : Type u) (i₁ : H → G₁) (i₂ : H → G₂) : Type u :=
  Quot (AmalgEquiv i₁ i₂)

namespace AmalgamatedFreeProduct

variable {G₁ G₂ H : Type u} {i₁ : H → G₁} {i₂ : H → G₂}

/-- Embed a word into the amalgamated free product. -/
def ofWord (w : FreeProductWord G₁ G₂) : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.mk _ w

/-- Identity element (empty word). -/
def one : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ := ofWord .nil

/-- Embed an element of G₁. -/
def inl (x : G₁) : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  ofWord (FreeProductWord.singleLeft x)

/-- Embed an element of G₂. -/
def inr (y : G₂) : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
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
def mulWord (w₁ w₂ : FreeProductWord G₁ G₂) : FreeProductWord G₁ G₂ :=
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
def mulWordRight (w₂ : FreeProductWord G₁ G₂) :
    AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ → AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w₁ => ofWord (FreeProductWord.concat w₁ w₂))
    (fun _ _ h => Quot.sound (concat_respects_left w₂ h))

/-- Multiplication in the amalgamated free product. -/
def mul (x y : AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
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

instance : Mul (AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨mul⟩
instance : One (AmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨one⟩

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
def inv [Neg G₁] [Neg G₂] [Neg H]
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
def FullAmalgamatedFreeProduct (G₁ G₂ H : Type u) [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
    (i₁ : H → G₁) (i₂ : H → G₂) : Type u :=
  Quot (FullAmalgEquiv i₁ i₂)

namespace FullAmalgamatedFreeProduct

variable {G₁ G₂ H : Type u} [Add G₁] [Add G₂] [Zero G₁] [Zero G₂]
variable {i₁ : H → G₁} {i₂ : H → G₂}

/-- Embed a word into the full amalgamated free product. -/
def ofWord (w : FreeProductWord G₁ G₂) : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.mk _ w

/-- Identity element (empty word). -/
def one : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ := ofWord .nil

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
def mulWordRight (w₂ : FreeProductWord G₁ G₂) :
    FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ → FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂ :=
  Quot.lift
    (fun w₁ => ofWord (FreeProductWord.concat w₁ w₂))
    (fun _ _ h => Quot.sound (concat_respects_left w₂ h))

/-- Multiplication in the full amalgamated free product. -/
def mul (x y : FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) :
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

instance : Mul (FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨mul⟩
instance : One (FullAmalgamatedFreeProduct G₁ G₂ H i₁ i₂) := ⟨one⟩

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
Requires group axioms for negation:
- Negation commutes with i₁, i₂
- Negation anti-distributes over addition: -(x + y) = (-y) + (-x)
- Negation of zero is zero -/
def inv [Neg G₁] [Neg G₂] [Neg H]
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
This is the key group axiom showing that inverse is a right inverse. -/
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
This is the key group axiom showing that inverse is a left inverse. -/
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
      -- We need: loop at Wedge.basepoint = Wedge.inl a₀
      Path.trans (Pushout.inlPath p) (wedgeDecode rest)
  | .consRight q rest =>
      -- q is a loop in B at b₀
      -- Go to inr b₀ via glue, do the loop, come back
      Path.trans
        (Path.trans
          (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀))
          (Path.trans (Pushout.inrPath q)
            (Path.symm (Wedge.glue (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)))))
        (wedgeDecode rest)

/-- Decode respects word concatenation. -/
theorem wedgeDecode_concat (w₁ w₂ : WedgeLoopCode a₀ b₀) :
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
      apply rweq_trans (rweq_trans_congr_right (Pushout.inlPath p) ih)
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
        (fun q => Quot.mk RwEq (Path.trans p q))
        (fun _ _ hq => Quot.sound (rweq_trans_congr_right p hq))
        β)
    (fun p p' hp => by
      -- Need to show: lift (trans p _) β = lift (trans p' _) β when p ~_rw p'
      induction β using Quot.ind with
      | _ q => exact Quot.sound (rweq_trans_congr_left q hp))
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
        show Quot.mk RwEq (Path.trans (Path.trans p q) r) =
             Quot.mk RwEq (Path.trans p (Path.trans q r))
        exact Quot.sound (rweq_tt p q r)

/-- Right identity for piOneMul: α ⋅ refl = α. -/
theorem piOneMul_refl_right {X : Type u} {x₀ : X} (α : π₁(X, x₀)) :
    piOneMul α (Quot.mk _ (Path.refl x₀)) = α := by
  induction α using Quot.ind with
  | _ p =>
    show Quot.mk RwEq (Path.trans p (Path.refl x₀)) = Quot.mk RwEq p
    exact Quot.sound (rweq_cmpA_refl_right p)

/-- Left identity for piOneMul: refl ⋅ α = α. -/
theorem piOneMul_refl_left {X : Type u} {x₀ : X} (α : π₁(X, x₀)) :
    piOneMul (Quot.mk _ (Path.refl x₀)) α = α := by
  induction α using Quot.ind with
  | _ p =>
    show Quot.mk RwEq (Path.trans (Path.refl x₀) p) = Quot.mk RwEq p
    exact Quot.sound (rweq_cmpA_refl_left p)

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
variable (hf : f c₀ = a₀) (hg : g c₀ = b₀)

-- Assume all spaces are path-connected
variable (hA : IsPathConnected A)
variable (hB : IsPathConnected B)
variable (hC : IsPathConnected C)

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
      exact rweq_congrArg_of_rweq Pushout.inl hpq)

/-- The induced map on fundamental groups: π₁(B) → π₁(Pushout). -/
noncomputable def piOneInr :
    π₁(B, b₀) → π₁(Pushout A B C f g, Pushout.inr b₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Pushout.inrPath p))
    (by
      intro p q hpq
      apply Quot.sound
      unfold Pushout.inrPath
      exact rweq_congrArg_of_rweq Pushout.inr hpq)

/-- The induced map from π₁(C): via f. -/
noncomputable def piOneFmap :
    π₁(C, c₀) → π₁(A, f c₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Path.congrArg f p))
    (by
      intro p q hpq
      apply Quot.sound
      exact rweq_congrArg_of_rweq f hpq)

/-- The induced map from π₁(C): via g. -/
noncomputable def piOneGmap :
    π₁(C, c₀) → π₁(B, g c₀) :=
  Quot.lift
    (fun p => Quot.mk _ (Path.congrArg g p))
    (by
      intro p q hpq
      apply Quot.sound
      exact rweq_congrArg_of_rweq g hpq)

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
          (fun _ _ hp => Quot.sound (rweq_congrArg_of_rweq Pushout.inl hp))
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
          (fun _ _ hq => Quot.sound (
            rweq_trans_congr_right _ (rweq_trans_congr_left _
              (rweq_congrArg_of_rweq Pushout.inr hq))))
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
    [Pushout.HasGlueNaturalRwEq (A := A) (B := B) (C := C) (f := f) (g := g)]
    (c₀ : C)
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
    apply Quot.sound
    -- Apply the glue naturality theorem
    exact Pushout.glue_natural_loop_rweq c₀ p

/-- Encode axiom for general pushouts (at the quotient level). -/
class HasPushoutSVKEncodeData (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) where
  encodeQuot :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
      FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀))
  decode_encode :
    ∀ p : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀)),
      pushoutDecode c₀ (encodeQuot (Quot.mk _ p)) = Quot.mk _ p
  encode_decode :
    ∀ w : PushoutCode A B C f g c₀,
      AmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
        (encodeQuot (pushoutDecode c₀ w)) w

noncomputable def pushoutEncodeQuotAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
    FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀)) :=
  HasPushoutSVKEncodeData.encodeQuot

/-- Encode on loop representatives. -/
noncomputable def pushoutEncodeAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀] :
    LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀)) →
    FreeProductWord (π₁(A, f c₀)) (π₁(B, g c₀)) :=
  fun p => pushoutEncodeQuotAxiom A B C f g c₀ (Quot.mk _ p)

/-- Encode respects RwEq. -/
theorem pushoutEncodeAxiom_respects_rweq (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀]
    {p q : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀))}
    (h : RwEq p q) :
    pushoutEncodeAxiom A B C f g c₀ p = pushoutEncodeAxiom A B C f g c₀ q := by
  unfold pushoutEncodeAxiom
  exact _root_.congrArg (pushoutEncodeQuotAxiom A B C f g c₀) (Quot.sound h)

/-- Encode at quotient level. -/
noncomputable def pushoutEncodeQuot
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B} (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
    PushoutCode A B C f g c₀ :=
  pushoutEncodeQuotAxiom A B C f g c₀

/-- The encoding produces an amalgamation-equivalence class. -/
noncomputable def pushoutEncodeAmalg
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B} (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀] :
    π₁(Pushout A B C f g, Pushout.inl (f c₀)) →
    AmalgamatedFreeProduct (π₁(A, f c₀)) (π₁(B, g c₀)) (π₁(C, c₀))
      (piOneFmap c₀) (piOneGmap c₀) :=
  fun α => AmalgamatedFreeProduct.ofWord (pushoutEncodeQuot c₀ α)

set_option maxHeartbeats 400000 in
/-- Decode at the amalgamated free product level respects amalgamation. -/
noncomputable def pushoutDecodeAmalg
    {A : Type u} {B : Type u} {C : Type u}
    {f : C → A} {g : C → B} (c₀ : C)
    [Pushout.HasGlueNaturalRwEq (A := A) (B := B) (C := C) (f := f) (g := g)] :
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
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀]
    (p : LoopSpace (Pushout A B C f g) (Pushout.inl (f c₀))) :
    pushoutDecode c₀ (pushoutEncodeAxiom A B C f g c₀ p) = Quot.mk _ p := by
  unfold pushoutEncodeAxiom
  unfold pushoutEncodeQuotAxiom
  exact HasPushoutSVKEncodeData.decode_encode (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀) p

/-- Round-trip: encode ∘ decode gives an amalgamation-equivalent word. -/
theorem pushoutEncodeDecodeAxiom (A : Type u) (B : Type u) (C : Type u)
    (f : C → A) (g : C → B) (c₀ : C) [HasPushoutSVKEncodeData A B C f g c₀]
    (w : PushoutCode A B C f g c₀) :
    AmalgEquiv (piOneFmap c₀) (piOneGmap c₀)
      (pushoutEncodeQuot c₀ (pushoutDecode c₀ w)) w := by
  unfold pushoutEncodeQuot
  unfold pushoutEncodeQuotAxiom
  exact HasPushoutSVKEncodeData.encode_decode (A := A) (B := B) (C := C) (f := f) (g := g) (c₀ := c₀) w

noncomputable def seifertVanKampenEquiv [Pushout.HasGlueNaturalRwEq (A := A) (B := B) (C := C) (f := f) (g := g)]
    [HasPushoutSVKEncodeData A B C f g c₀] :
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
          (fun _ _ hp => Quot.sound (rweq_congrArg_of_rweq Pushout.inl hp))
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
          (fun _ _ hp => Quot.sound (
            rweq_trans_congr_right _ (rweq_trans_congr_left _
              (rweq_congrArg_of_rweq Pushout.inr hp))))
          β
      piOneMul βInWedge (wedgeFreeProductDecode rest)

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

/-- Encode function for wedge loops.

The encode function extracts word structure from a loop. The key insight is that
any loop at the basepoint is RwEq-equivalent to one built from:
- Paths within inl(A) → left letters
- Glue-inrPath-glue⁻¹ sequences → right letters

Since we work with π₁ (quotient by RwEq), encode only needs to be well-defined
on equivalence classes, which follows from RwEq implying equal underlying equality.

**Implementation**: We define encode directly using the property that RwEq-equivalent
paths have equal underlying equality (p.toEq = q.toEq), so any reasonable encoding
function is well-defined on the quotient.

The actual word extraction would normally use a code family; for now we define
wedge encoding by specialising the general pushout encoding interface. -/
noncomputable def wedgeEncodeAxiom (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [HasPushoutSVKEncodeData A B PUnit'
      (fun _ : PUnit' => a₀) (fun _ : PUnit' => b₀) PUnit'.unit] :
    LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint → FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
  pushoutEncodeAxiom A B PUnit'
    (fun _ : PUnit' => a₀)
    (fun _ : PUnit' => b₀)
    PUnit'.unit

/-- Encode respects RwEq. -/
theorem wedgeEncodeAxiom_respects_rweq (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [HasPushoutSVKEncodeData A B PUnit'
      (fun _ : PUnit' => a₀) (fun _ : PUnit' => b₀) PUnit'.unit]
    {p q : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint}
    (h : RwEq p q) :
    wedgeEncodeAxiom A B a₀ b₀ p = wedgeEncodeAxiom A B a₀ b₀ q := by
  simpa [wedgeEncodeAxiom] using
    pushoutEncodeAxiom_respects_rweq A B PUnit'
      (fun _ : PUnit' => a₀)
      (fun _ : PUnit' => b₀)
      PUnit'.unit
      (p := p) (q := q) h

/-- Encode at the quotient level: π₁(Wedge) → FreeProductWord. -/
noncomputable def wedgeEncodeQuot
    [HasPushoutSVKEncodeData A B PUnit'
      (fun _ : PUnit' => a₀) (fun _ : PUnit' => b₀) PUnit'.unit] :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) → WedgeFreeProductCode a₀ b₀ :=
  Quot.lift (wedgeEncodeAxiom A B a₀ b₀)
    (fun _ _ h => wedgeEncodeAxiom_respects_rweq A B a₀ b₀ h)

/-- Computation rule for `wedgeEncodeQuot` on representatives. -/
@[simp] theorem wedgeEncodeQuot_mk
    [HasPushoutSVKEncodeData A B PUnit'
      (fun _ : PUnit' => a₀) (fun _ : PUnit' => b₀) PUnit'.unit]
    (p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint) :
    wedgeEncodeQuot (A := A) (B := B) a₀ b₀ (Quot.mk _ p) = wedgeEncodeAxiom A B a₀ b₀ p :=
  rfl

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
      simp only [wedgeFreeProductDecode, pushoutDecode, ih]
  | consRight β rest ih =>
      simp only [wedgeFreeProductDecode, pushoutDecode, ih, Wedge.glue]

/-- Decode after encode gives back the original loop (at π₁ level).

This is the key round-trip property: encoding a loop extracts its word structure,
and decoding that word reconstructs a loop in the same equivalence class.

In the code family approach, this follows from:
1. Transport along refl is identity
2. Transport along inlPath α corresponds to prepending a left letter
3. Transport along glue sequences corresponds to prepending a right letter
4. decode reverses these operations exactly -/
theorem wedgeDecodeEncodeAxiom (A : Type u) (B : Type u) (a₀ : A) (b₀ : B)
    [HasPushoutSVKEncodeData A B PUnit'
      (fun _ : PUnit' => a₀) (fun _ : PUnit' => b₀) PUnit'.unit]
    (p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint) :
    wedgeFreeProductDecode a₀ b₀ (wedgeEncodeAxiom A B a₀ b₀ p) = Quot.mk _ p := by
  -- Expand the wedge-specific definitions into the general pushout statements.
  -- `simp` turns `wedgeEncodeAxiom` into the specialised `pushoutEncodeAxiom`.
  simp only [wedgeEncodeAxiom]
  rw [wedgeFreeProductDecode_eq_pushoutDecode (A := A) (B := B) (a₀ := a₀) (b₀ := b₀)]
  exact
    pushoutDecodeEncodeAxiom A B PUnit'
      (fun _ : PUnit' => a₀)
      (fun _ : PUnit' => b₀)
      PUnit'.unit
      p

/-- The fundamental group of a wedge sum is the free product.

This is the simplest case of SVK where the gluing space is a point.
The full encode/decode proof is not yet formalized here, so we record the
equivalence as a packaged axiom. -/
class HasWedgeFundamentalGroupEquiv (A : Type u) (B : Type u) (a₀ : A) (b₀ : B) where
  equiv :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode a₀ b₀)

noncomputable def wedgeFundamentalGroupEquiv [HasWedgeFundamentalGroupEquiv A B a₀ b₀] :
    SimpleEquiv
      (π₁(Wedge A B a₀ b₀, Wedge.basepoint))
      (WedgeFreeProductCode a₀ b₀) :=
  HasWedgeFundamentalGroupEquiv.equiv

end WedgeSVK

/-! ## Concrete SVK Instances for Wedge Sums

For wedge sums A ∨ B (where C = PUnit'), we can provide concrete instances
of the SVK typeclasses. The encode direction requires HIT recursion, which
we axiomatize. The key properties follow from path analysis in wedge sums.
-/

namespace WedgeSVKInstances

variable {A : Type u} {B : Type u} (a₀ : A) (b₀ : B)

/-- Axiom: Primitive encode function for paths in a wedge sum.

This axiom states that every loop at the basepoint of a wedge sum
can be analyzed to extract a word in π₁(A) * π₁(B).

The encode function is characterized by:
- encode(refl) = nil
- encode(inlPath p ⋅ rest) = consLeft [p] (encode rest)
- encode(glue ⋅ inrPath q ⋅ glue⁻¹ ⋅ rest) = consRight [q] (encode rest)

These computation rules are captured by the round-trip properties. -/
axiom wedgeEncodePrim :
    LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint →
    FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))

/-- Axiom: The primitive encode respects RwEq. -/
axiom wedgeEncodePrim_respects_rweq
    {p q : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint}
    (h : RwEq p q) :
    wedgeEncodePrim a₀ b₀ p = wedgeEncodePrim a₀ b₀ q

/-- Encode at the quotient level. -/
noncomputable def wedgeEncodeQuotPrim :
    π₁(Wedge A B a₀ b₀, Wedge.basepoint) →
    FreeProductWord (π₁(A, a₀)) (π₁(B, b₀)) :=
  Quot.lift (wedgeEncodePrim a₀ b₀) (fun _ _ h => wedgeEncodePrim_respects_rweq a₀ b₀ h)

/-- Axiom: decode ∘ encode = id on loop representatives.

This axiom states that encoding a loop and then decoding gives back the
same loop (up to RwEq, hence equal in the quotient). -/
axiom wedgeDecodeEncodePrim
    (p : LoopSpace (Wedge A B a₀ b₀) Wedge.basepoint) :
    pushoutDecode (A := A) (B := B) (C := PUnit')
      (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit
      (wedgeEncodePrim a₀ b₀ p) = Quot.mk _ p

/-- Axiom: encode ∘ decode = id on words at the quotient level.

For wedge sums, the amalgamation is trivial since C = PUnit' has trivial π₁. -/
axiom wedgeEncodeDecodeQuotPrim
    (w : FreeProductWord (π₁(A, a₀)) (π₁(B, b₀))) :
    wedgeEncodeQuotPrim a₀ b₀
      (pushoutDecode (A := A) (B := B) (C := PUnit')
        (f := fun _ => a₀) (g := fun _ => b₀) PUnit'.unit w) = w

/-- AmalgEquiv version of wedgeEncodeDecodeQuotPrim for HasPushoutSVKEncodeData. -/
theorem wedgeEncodeDecodeQuotPrim_amalg
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
noncomputable instance hasPushoutSVKEncodeData :
    HasPushoutSVKEncodeData A B PUnit'
      (fun _ => a₀) (fun _ => b₀) PUnit'.unit where
  encodeQuot := wedgeEncodeQuotPrim a₀ b₀
  decode_encode := fun p => by
    simp only [wedgeEncodeQuotPrim]
    exact wedgeDecodeEncodePrim a₀ b₀ p
  encode_decode := fun w => wedgeEncodeDecodeQuotPrim_amalg a₀ b₀ w

/-- Instance: HasWedgeFundamentalGroupEquiv for Wedge sums.

This packages the encode-decode equivalence. -/
noncomputable instance hasWedgeFundamentalGroupEquiv :
    HasWedgeFundamentalGroupEquiv A B a₀ b₀ where
  equiv := {
    toFun := wedgeEncodeQuotPrim a₀ b₀
    invFun := wedgeFreeProductDecode a₀ b₀
    left_inv := by
      intro α
      induction α using Quot.ind with
      | _ p =>
        simp only [wedgeEncodeQuotPrim, wedgeFreeProductDecode_eq_pushoutDecode]
        exact wedgeDecodeEncodePrim a₀ b₀ p
    right_inv := by
      intro w
      simp only [wedgeEncodeQuotPrim, wedgeFreeProductDecode_eq_pushoutDecode]
      exact wedgeEncodeDecodeQuotPrim a₀ b₀ w
  }

end WedgeSVKInstances

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

The proofs use the computational paths framework where:
- Loops are computational paths (with explicit step structure)
- Path equality is rewrite equality (`RwEq`)
- The fundamental group is the quotient by rewrite equality
-/

end Path
end ComputationalPaths
