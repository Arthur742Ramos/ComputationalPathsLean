/-
# Circle Step Laws and π₁(S¹) ≃ ℤ

This module completes the proof that π₁(S¹) ≃ ℤ by proving the round-trip
properties encode ∘ decode = id and decode ∘ encode = id.

The step laws (circleEncode_circleDecode_add_one, etc.) are defined in Circle.lean.
This module uses them to prove the full equivalence.
-/

import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Quot

set_option maxHeartbeats 1000000

namespace ComputationalPaths
namespace Path

open SimpleEquiv

universe u

variable [HasUnivalence.{0}]

/-- Encode∘decode identity on negative integers by Nat induction. -/
theorem circleEncode_circleDecode_of_negNat (k : Nat) :
  circleEncode (circleDecode (-(k : Int))) = -(k : Int) := by
  induction k with
  | zero =>
      -- -0 = 0, so this is the same as circleEncode_circleDecode_ofNat 0
      have h0 : (-(0 : Nat) : Int) = 0 := by decide
      rw [h0]
      exact circleEncode_circleDecode_ofNat 0
  | succ k ih =>
      have step := circleEncode_circleDecode_add_neg_one (z := - (k : Int))
      -- -(succ k) = -k + (-1)
      have heq : -((Nat.succ k : Nat) : Int) = - (k : Int) + (-1) := by omega
      rw [heq]
      -- Now use the step law
      rw [step]
      -- ih : circleEncode (circleDecode (-k)) = -k
      rw [ih]
      -- -k - 1 = -(k+1)
      omega

@[simp] theorem circleEncode_circleDecode (z : Int) :
  circleEncode (circleDecode z) = z := by
  cases z with
  | ofNat n =>
      exact circleEncode_circleDecode_ofNat n
  | negSucc n =>
      exact circleEncode_circleDecode_of_negNat (Nat.succ n)

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
 private theorem circleDecodeEq_circleEncodeEq.{v}
     (e : circleBase.{v} = circleBase.{v}) :
     (circleLoopPathZPow.{v} (circleEncodePath.{v} (Path.ofEq e))).toEq = e := by
  cases e with
  | refl =>
      -- encodeEq rfl = 0 and decodeEq 0 = rfl
      -- Path.ofEq rfl = refl, and circleEncodePath refl = 0
      show (circleLoopPathZPow.{v} (circleEncodePath.{v} (Path.refl circleBase.{v}))).toEq = rfl
      rw [circleEncodePath_refl.{v}]

/-- `decode ∘ encode = id` on π₁(S¹).

This proof uses `circleLoop_rweq_decode`, a circle-specific axiom stating that
every loop on S¹ is RwEq to the decoded form of its winding number. This captures
  the geometric fact that loops on the circle are classified by winding number,
  without collapsing all paths globally (as the removed `Step.canon` would have). -/
 theorem circleDecode_circleEncode [HasCircleLoopDecode.{u}] (x : circlePiOne.{u}) :
     circleDecode (circleEncode x) = x := by
  -- Induct on the quotient
  refine Quot.inductionOn x ?h
  intro p
  -- circleEncode (Quot.mk _ p) = circleEncodePath p by definition
  show circleDecode (circleEncode (Quot.mk _ p)) = Quot.mk _ p
  -- Unfold: circleEncode (Quot.mk _ p) = circleEncodeLift (Quot.mk _ p) = circleEncodePath p
  have henc : circleEncode (Quot.mk _ p) = circleEncodePath p := rfl
  rw [henc]
  -- By circleLoop_rweq_decode: RwEq p (circleLoopPathZPow (circleEncodePath p))
  have hrweq := circleLoop_rweq_decode p
  -- This gives: Quot.mk _ p = Quot.mk _ (circleLoopPathZPow (circleEncodePath p))
  have heq : Quot.mk RwEq p = Quot.mk RwEq (circleLoopPathZPow (circleEncodePath p)) :=
    Quot.sound hrweq
  -- By circleLoopZPow_eq_ofLoop: circleDecode z = LoopQuot.ofLoop (circleLoopPathZPow z)
  have hdec : circleDecode (circleEncodePath p) =
      LoopQuot.ofLoop (A := Circle) (a := circleBase)
        (circleLoopPathZPow (circleEncodePath p)) :=
    circleLoopZPow_eq_ofLoop (circleEncodePath p)
  -- LoopQuot.ofLoop = Quot.mk _ by definition
  rw [hdec]
  -- Now goal is: LoopQuot.ofLoop (circleLoopPathZPow (circleEncodePath p)) = Quot.mk _ p
  -- Which is: Quot.mk _ (circleLoopPathZPow (circleEncodePath p)) = Quot.mk _ p
  exact heq.symm

 noncomputable def circlePiOneEquivInt [HasCircleLoopDecode.{u}] : SimpleEquiv (circlePiOne.{u}) Int where
  toFun := circleWindingNumber
  invFun := circleDecode
  left_inv := by
    intro x
    change circleDecode (circleEncode x) = x
    exact circleDecode_circleEncode (x := x)
  right_inv := by
    intro z
    change circleEncode (circleDecode z) = z
    exact circleEncode_circleDecode (z := z)

@[simp] theorem circleWindingNumber_decode (z : Int) :
    circleWindingNumber (circleDecode z) = z := by
  change circleEncode (circleDecode z) = z
  exact circleEncode_circleDecode (z := z)

end Path
end ComputationalPaths
