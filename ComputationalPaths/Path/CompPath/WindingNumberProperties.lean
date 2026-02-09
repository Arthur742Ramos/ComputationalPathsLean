/-
# Winding Number Properties for the Computational Circle

This module extends `CircleCompPath` with algebraic properties of the winding
number on `π₁(S¹)`. We define loop multiplication on the quotient of loop
expressions and show additivity, homomorphism behavior, injectivity,
surjectivity, and the constant-loop value.

## Key Results

- `circlePiOneMul`: multiplication on circle π₁ by concatenating expressions
- `winding_number_add`: winding number is additive under multiplication
- `winding_number_injective`/`winding_number_surjective`: bijectivity facts
- `winding_number_constant`: constant loop maps to zero

## References

- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.CompPath.CircleCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Multiplication on circle π₁ -/

private theorem circleCompPathRel_trans_right
    (p : CircleCompPathExpr circleCompPathBase circleCompPathBase)
    {q q' : CircleCompPathExpr circleCompPathBase circleCompPathBase}
    (h : circleCompPathRel q q') :
    circleCompPathRel (CircleCompPathExpr.trans p q)
      (CircleCompPathExpr.trans p q') := by
  dsimp [circleCompPathRel] at h ⊢
  simp [h]

private theorem circleCompPathRel_trans_left
    (q : CircleCompPathExpr circleCompPathBase circleCompPathBase)
    {p p' : CircleCompPathExpr circleCompPathBase circleCompPathBase}
    (h : circleCompPathRel p p') :
    circleCompPathRel (CircleCompPathExpr.trans p q)
      (CircleCompPathExpr.trans p' q) := by
  dsimp [circleCompPathRel] at h ⊢
  simp [h]

/-- Multiply by a fixed right loop expression. -/
noncomputable def circleCompPathMulExprRight
    (q : CircleCompPathExpr circleCompPathBase circleCompPathBase) :
    circlePiOne → circlePiOne :=
  Quot.lift
    (fun p => Quot.mk _ (CircleCompPathExpr.trans p q))
    (fun _ _ h => Quot.sound (circleCompPathRel_trans_left q h))

/-- Multiplication on `circlePiOne` induced by loop concatenation. -/
noncomputable def circlePiOneMul (x y : circlePiOne) : circlePiOne :=
  Quot.lift
    (fun q => circleCompPathMulExprRight q x)
    (fun _ _ h => by
      induction x using Quot.ind with
      | _ p =>
          unfold circleCompPathMulExprRight
          apply Quot.sound
          exact circleCompPathRel_trans_right p h)
    y

/-- Multiplication by a fixed right expression on representatives. -/
@[simp] theorem circleCompPathMulExprRight_mk
    (q : CircleCompPathExpr circleCompPathBase circleCompPathBase)
    (p : CircleCompPathExpr circleCompPathBase circleCompPathBase) :
    circleCompPathMulExprRight q (Quot.mk _ p) =
      Quot.mk _ (CircleCompPathExpr.trans p q) := rfl

/-- Multiplication on representatives. -/
@[simp] theorem circlePiOneMul_mk_mk
    (p q : CircleCompPathExpr circleCompPathBase circleCompPathBase) :
    circlePiOneMul (Quot.mk _ p) (Quot.mk _ q) =
      Quot.mk _ (CircleCompPathExpr.trans p q) := rfl

/-- Identity element of `circlePiOne` (constant loop). -/
def circlePiOneOne : circlePiOne :=
  circleDecode 0

/-- The winding-number map on `circlePiOne`. -/
@[simp] noncomputable def windingNumber : circlePiOne → Int :=
  circlePiOneEncode

/-! ## Winding number laws -/

/-- Additivity of winding number under loop multiplication. -/
theorem winding_number_add (x y : circlePiOne) :
    windingNumber (circlePiOneMul x y) = windingNumber x + windingNumber y := by
  refine Quot.inductionOn x ?_
  intro p
  refine Quot.inductionOn y ?_
  intro q
  simp [circlePiOneMul, circleCompPathMulExprRight, windingNumber]

/-- Winding number sends the constant loop to zero. -/
theorem winding_number_constant : windingNumber circlePiOneOne = 0 := by
  simp [windingNumber, circlePiOneOne]

/-- Winding number is a group homomorphism with respect to multiplication. -/
theorem winding_number_hom (x y : circlePiOne) :
    windingNumber (circlePiOneMul x y) = windingNumber x + windingNumber y :=
  winding_number_add x y

/-- Injectivity of the winding number on `circlePiOne`. -/
theorem winding_number_injective {x y : circlePiOne}
    (h : windingNumber x = windingNumber y) : x = y := by
  have hx : circleDecode (windingNumber x) = x := by
    simpa [windingNumber] using (circleDecode_circlePiOneEncode x)
  have hy : circleDecode (windingNumber y) = y := by
    simpa [windingNumber] using (circleDecode_circlePiOneEncode y)
  calc
    x = circleDecode (windingNumber x) := by
          simpa using hx.symm
    _ = circleDecode (windingNumber y) := by
          rw [h]
    _ = y := by
          simpa using hy

/-- Surjectivity of the winding number on `circlePiOne`. -/
theorem winding_number_surjective (z : Int) :
    ∃ x : circlePiOne, windingNumber x = z := by
  refine ⟨circleDecode z, ?_⟩
  simpa [windingNumber] using (circlePiOneEncode_circleDecode z)

/-! ## Summary -/

/-!
We define loop multiplication on the circle π₁ quotient, prove the winding
number is additive and a homomorphism, and record explicit injectivity,
surjectivity, and the constant-loop value.
-/

end CompPath
end Path
end ComputationalPaths
