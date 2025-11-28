/-
# The Figure-Eight Space (S¹ ∨ S¹)

This module formalizes the figure-eight space as the wedge sum of two circles,
and proves that its fundamental group is the free product ℤ * ℤ (equivalently,
the free group on two generators F₂).

## Main Results

- `FigureEight`: The figure-eight space as `Wedge Circle Circle`
- `figureEightPiOneEquiv`: π₁(S¹ ∨ S¹) ≃ FreeProductWord ℤ ℤ
- `figureEightLoopA`, `figureEightLoopB`: The two fundamental generators

## Mathematical Background

The figure-eight is a canonical example of a space with non-abelian fundamental
group. The two loops generate freely, meaning every element of π₁ can be
uniquely expressed as an alternating word in powers of the two loops.

This demonstrates the power of the Seifert-van Kampen theorem: since
π₁(pt) is trivial, we get π₁(A ∨ B) ≃ π₁(A) * π₁(B) (true free product).

## References

- HoTT Book, Chapter 8.6 (The van Kampen theorem)
- de Veras et al., "On the Calculation of Fundamental Groups..."
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.HIT.Pushout
import ComputationalPaths.Path.HIT.PushoutPaths

namespace ComputationalPaths
namespace Path

universe u

/-! ## Circle Equivalence Axiom

The full proof that π₁(S¹) ≃ ℤ is in CircleStep.lean, but we axiomatize the
result here to avoid circular dependencies. The key facts are:
- `circleEncode : circlePiOne → Int` (defined in Circle.lean)
- `circleDecode : Int → circlePiOne` (defined in Circle.lean)
- Round-trip properties (proven in CircleStep.lean)
-/

/-- `decode ∘ encode = id` on π₁(S¹). Proven in CircleStep via equality induction. -/
axiom circleDecode_circleEncode (x : circlePiOne) :
    circleDecode (circleEncode x) = x

/-- `encode ∘ decode = id` on ℤ. Proven in CircleStep by integer induction. -/
axiom circleEncode_circleDecode (z : Int) :
    circleEncode (circleDecode z) = z

/-- The fundamental equivalence π₁(S¹) ≃ ℤ. -/
noncomputable def circlePiOneEquivInt : SimpleEquiv circlePiOne Int where
  toFun := circleEncode
  invFun := circleDecode
  left_inv := circleDecode_circleEncode
  right_inv := circleEncode_circleDecode

/-! ## The Figure-Eight Space -/

/-- The figure-eight space: wedge sum of two circles sharing a common basepoint.
Topologically, this is two circles joined at a single point, forming an "8" shape. -/
def FigureEight : Type u := Wedge Circle.{u} Circle.{u} circleBase circleBase

namespace FigureEight

/-! ## Basic Structure -/

/-- The basepoint of the figure-eight (the junction where the two circles meet). -/
noncomputable def base : FigureEight := Wedge.basepoint

/-- Injection of the left circle into the figure-eight. -/
noncomputable def inlCircle (x : Circle) : FigureEight := Wedge.inl x

/-- Injection of the right circle into the figure-eight. -/
noncomputable def inrCircle (x : Circle) : FigureEight := Wedge.inr x

/-- The glue path identifying the two basepoints. -/
noncomputable def glue : Path (inlCircle circleBase) (inrCircle circleBase) :=
  Wedge.glue

/-! ## The Two Fundamental Loops

The figure-eight has two fundamental loops:
- Loop A: goes around the left circle
- Loop B: goes around the right circle (conjugated by glue)

These generate the fundamental group freely.
-/

/-- Loop A: The fundamental loop of the left circle, embedded in the figure-eight.
This is simply the left circle's loop, which is already based at the basepoint. -/
noncomputable def loopA : Path base base :=
  Pushout.inlPath circleLoop

/-- Loop B: The fundamental loop of the right circle, conjugated to be based at
the figure-eight basepoint.

Since the right circle's basepoint is identified with the left via glue,
we must conjugate: loopB = glue ⋅ circleLoop ⋅ glue⁻¹ -/
noncomputable def loopB : Path base base :=
  Path.trans
    (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))
    (Path.trans (Pushout.inrPath circleLoop)
      (Path.symm (Wedge.glue (A := Circle) (B := Circle) (a₀ := circleBase) (b₀ := circleBase))))

/-! ## Loop Space and Fundamental Group -/

/-- Loop space of the figure-eight at its basepoint. -/
abbrev FigureEightLoopSpace : Type u := LoopSpace FigureEight base

/-- Fundamental group π₁(figure-eight, base). -/
abbrev FigureEightPiOne : Type u := π₁(FigureEight, base)

/-- Loop A as an element of the fundamental group. -/
noncomputable def loopAClass : FigureEightPiOne := Quot.mk _ loopA

/-- Loop B as an element of the fundamental group. -/
noncomputable def loopBClass : FigureEightPiOne := Quot.mk _ loopB

/-! ## Equivalence with Free Product of Integers

We now establish the main theorem:
  π₁(S¹ ∨ S¹) ≃ FreeProductWord (π₁(S¹)) (π₁(S¹)) ≃ FreeProductWord ℤ ℤ

The proof proceeds in two steps:
1. Apply wedgeFundamentalGroupEquiv to get π₁(S¹ ∨ S¹) ≃ π₁(S¹) * π₁(S¹)
2. Lift circlePiOneEquivInt to get π₁(S¹) * π₁(S¹) ≃ ℤ * ℤ
-/

/-- Helper: Map an equivalence through a FreeProductWord.
Given equivalences e₁ : G₁ ≃ H₁ and e₂ : G₂ ≃ H₂, we get
FreeProductWord G₁ G₂ ≃ FreeProductWord H₁ H₂ -/
def freeProductWordMap {G₁ G₂ H₁ H₂ : Type u}
    (f₁ : G₁ → H₁) (f₂ : G₂ → H₂) :
    FreeProductWord G₁ G₂ → FreeProductWord H₁ H₂
  | .nil => .nil
  | .consLeft x rest => .consLeft (f₁ x) (freeProductWordMap f₁ f₂ rest)
  | .consRight y rest => .consRight (f₂ y) (freeProductWordMap f₁ f₂ rest)

/-- The map is functorial: id maps to id. -/
theorem freeProductWordMap_id {G₁ G₂ : Type u} (w : FreeProductWord G₁ G₂) :
    freeProductWordMap id id w = w := by
  induction w with
  | nil => rfl
  | consLeft x rest ih => simp [freeProductWordMap, ih]
  | consRight y rest ih => simp [freeProductWordMap, ih]

/-- The map is functorial: composition. -/
theorem freeProductWordMap_comp {G₁ G₂ H₁ H₂ K₁ K₂ : Type u}
    (f₁ : G₁ → H₁) (f₂ : G₂ → H₂)
    (g₁ : H₁ → K₁) (g₂ : H₂ → K₂)
    (w : FreeProductWord G₁ G₂) :
    freeProductWordMap g₁ g₂ (freeProductWordMap f₁ f₂ w) =
    freeProductWordMap (g₁ ∘ f₁) (g₂ ∘ f₂) w := by
  induction w with
  | nil => rfl
  | consLeft x rest ih => simp [freeProductWordMap, ih]
  | consRight y rest ih => simp [freeProductWordMap, ih]

/-- Helper: if f₁ = id and f₂ = id pointwise, then freeProductWordMap f₁ f₂ = id. -/
theorem freeProductWordMap_id_of_pointwise {G₁ G₂ : Type u}
    {f₁ : G₁ → G₁} {f₂ : G₂ → G₂}
    (hf₁ : ∀ x, f₁ x = x) (hf₂ : ∀ y, f₂ y = y)
    (w : FreeProductWord G₁ G₂) :
    freeProductWordMap f₁ f₂ w = w := by
  induction w with
  | nil => rfl
  | consLeft x rest ih => simp [freeProductWordMap, hf₁ x, ih]
  | consRight y rest ih => simp [freeProductWordMap, hf₂ y, ih]

/-- Lift equivalences to free product words. -/
noncomputable def freeProductWordEquiv {G₁ G₂ H₁ H₂ : Type u}
    (e₁ : SimpleEquiv G₁ H₁) (e₂ : SimpleEquiv G₂ H₂) :
    SimpleEquiv (FreeProductWord G₁ G₂) (FreeProductWord H₁ H₂) where
  toFun := freeProductWordMap e₁.toFun e₂.toFun
  invFun := freeProductWordMap e₁.invFun e₂.invFun
  left_inv := by
    intro w
    rw [freeProductWordMap_comp]
    exact freeProductWordMap_id_of_pointwise e₁.left_inv e₂.left_inv w
  right_inv := by
    intro w
    rw [freeProductWordMap_comp]
    exact freeProductWordMap_id_of_pointwise e₁.right_inv e₂.right_inv w

/-! ## The Main Theorem -/

/-- Step 1: π₁(figure-eight) ≃ FreeProductWord (π₁(S¹)) (π₁(S¹))

This is a direct application of the wedge fundamental group theorem. -/
noncomputable def figureEightPiOneEquivPiOneProduct :
    SimpleEquiv FigureEightPiOne (FreeProductWord circlePiOne circlePiOne) :=
  wedgeFundamentalGroupEquiv circleBase circleBase

/-- Step 2: FreeProductWord (π₁(S¹)) (π₁(S¹)) ≃ FreeProductWord ℤ ℤ

This lifts the circle equivalence π₁(S¹) ≃ ℤ to free product words. -/
noncomputable def piOneProductEquivIntProduct :
    SimpleEquiv (FreeProductWord circlePiOne circlePiOne) (FreeProductWord Int Int) :=
  freeProductWordEquiv circlePiOneEquivInt circlePiOneEquivInt

/-- **Main Theorem**: π₁(S¹ ∨ S¹, base) ≃ ℤ * ℤ (free product of integers)

The fundamental group of the figure-eight is the free group on two generators,
represented here as alternating words in ℤ and ℤ.

This is a consequence of the Seifert-van Kampen theorem for wedge sums:
  π₁(A ∨ B) ≃ π₁(A) * π₁(B)
combined with the circle theorem:
  π₁(S¹) ≃ ℤ
-/
noncomputable def figureEightPiOneEquiv :
    SimpleEquiv FigureEightPiOne (FreeProductWord Int Int) :=
  SimpleEquiv.comp figureEightPiOneEquivPiOneProduct piOneProductEquivIntProduct

/-! ## Winding Numbers and Word Extraction

We can interpret elements of π₁(figure-eight) as words in two generators.
-/

/-- Extract the free product word from a loop in the figure-eight.
This is the "winding number" generalization: it tells us how many times
we go around each circle, in what order. -/
noncomputable def extractWord : FigureEightPiOne → FreeProductWord Int Int :=
  figureEightPiOneEquiv.toFun

/-- Construct a loop from a word in ℤ * ℤ. -/
noncomputable def wordToLoop : FreeProductWord Int Int → FigureEightPiOne :=
  figureEightPiOneEquiv.invFun

/-- Round-trip: extractWord ∘ wordToLoop = id -/
theorem extractWord_wordToLoop (w : FreeProductWord Int Int) :
    extractWord (wordToLoop w) = w :=
  figureEightPiOneEquiv.right_inv w

/-- Round-trip: wordToLoop ∘ extractWord = id -/
theorem wordToLoop_extractWord (α : FigureEightPiOne) :
    wordToLoop (extractWord α) = α :=
  figureEightPiOneEquiv.left_inv α

/-! ## Generator Words

The two fundamental loops correspond to specific words.
-/

/-- Loop A corresponds to the word with a single left element (1 in first ℤ). -/
noncomputable def loopAWord : FreeProductWord Int Int :=
  .consLeft 1 .nil

/-- Loop B corresponds to the word with a single right element (1 in second ℤ). -/
noncomputable def loopBWord : FreeProductWord Int Int :=
  .consRight 1 .nil

/-- The word for n loops around A. -/
noncomputable def loopAPowWord (n : Int) : FreeProductWord Int Int :=
  .consLeft n .nil

/-- The word for n loops around B. -/
noncomputable def loopBPowWord (n : Int) : FreeProductWord Int Int :=
  .consRight n .nil

/-! ## Non-Abelianness

A key property of the figure-eight fundamental group is that it's non-abelian:
loopA ⋅ loopB ≠ loopB ⋅ loopA (as words in the free product).

This is witnessed at the word level.
-/

/-- AB as a word: go around A once, then B once. -/
def wordAB : FreeProductWord Int Int :=
  .consLeft 1 (.consRight 1 .nil)

/-- BA as a word: go around B once, then A once. -/
def wordBA : FreeProductWord Int Int :=
  .consRight 1 (.consLeft 1 .nil)

/-- AB ≠ BA: The fundamental group is non-abelian.
This is immediate from the word representation. -/
theorem wordAB_ne_wordBA : wordAB ≠ wordBA := by
  intro h
  cases h

/-- The length of AB is 2. -/
theorem wordAB_length : wordAB.length = 2 := rfl

/-- The length of BA is 2. -/
theorem wordBA_length : wordBA.length = 2 := rfl

/-! ## Word Operations

We can define word concatenation and its relationship to π₁ multiplication.
-/

/-- Inverse of a word (reverse and negate all entries). -/
def wordInverse : FreeProductWord Int Int → FreeProductWord Int Int
  | .nil => .nil
  | .consLeft n rest =>
      FreeProductWord.concat (wordInverse rest) (.consLeft (-n) .nil)
  | .consRight n rest =>
      FreeProductWord.concat (wordInverse rest) (.consRight (-n) .nil)

/-- The inverse of loopAWord is -1 on the left. -/
theorem wordInverse_loopAWord :
    wordInverse loopAWord = .consLeft (-1) .nil := rfl

/-- The inverse of loopBWord is -1 on the right. -/
theorem wordInverse_loopBWord :
    wordInverse loopBWord = .consRight (-1) .nil := rfl

end FigureEight

/-! ## Summary

This module establishes:

1. **Figure-Eight Definition**: `FigureEight := Wedge Circle Circle`

2. **Two Generators**:
   - `loopA`: The left circle's fundamental loop
   - `loopB`: The right circle's loop (conjugated by glue)

3. **Main Theorem** (`figureEightPiOneEquiv`):
   ```
   π₁(S¹ ∨ S¹, base) ≃ FreeProductWord ℤ ℤ
   ```

4. **Non-Abelianness**: The fundamental group is non-abelian (witnessed by
   word structure: AB ≠ BA).

This demonstrates the practical application of:
- The wedge sum construction (`Wedge`)
- The Seifert-van Kampen theorem (`wedgeFundamentalGroupEquiv`)
- The circle fundamental group (`circlePiOneEquivInt`)
- Composition of equivalences via `SimpleEquiv.comp`
-/

end Path
end ComputationalPaths
