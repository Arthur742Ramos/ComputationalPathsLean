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
private theorem circleDecodeEq_circleEncodeEq.{u}
    (e : circleBase.{u} = circleBase.{u}) :
    (circleLoopPathZPow.{u} (circleEncodePath.{u} (Path.ofEq e))).toEq = e := by
  cases e with
  | refl =>
      -- encodeEq rfl = 0 and decodeEq 0 = rfl
      -- Path.ofEq rfl = refl, and circleEncodePath refl = 0
      show (circleLoopPathZPow.{u} (circleEncodePath.{u} (Path.refl circleBase.{u}))).toEq = rfl
      rw [circleEncodePath_refl.{u}]

/-- `decode ∘ encode = id` on π₁(S¹). -/
theorem circleDecode_circleEncode (x : circlePiOne) :
    circleDecode (circleEncode x) = x := by
  -- Compare via propositional equality using `toEq`.
  apply PathRwQuot.eq_of_toEq_eq (A := Circle) (a := circleBase) (b := circleBase)
  -- Work with a path representative of `x`.
  refine Quot.inductionOn x (fun p => ?_)
  -- Reduce `decode (encode (ofLoop p))` to an equality on raw z-powers.
  have hzpow :
      PathRwQuot.toEq (A := Circle)
        (circleDecode (circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = (circleLoopPathZPow (circleEncodePath p)).toEq := by
    -- `toEq (decode z)` calculates to the raw `circleLoopPathZPow`.
    change PathRwQuot.toEq (A := Circle)
        (circleLoopZPow (circleEncodePath p))
        = (circleLoopPathZPow (circleEncodePath p)).toEq
    exact circleLoopZPow_toEq (z := circleEncodePath p)
  -- Replace the integer by the canonicalised version built from `p.toEq`.
  have hcanon :
      circleEncodePath (Path.ofEq p.toEq) = circleEncodePath p := by
    have hcanonRw : RwEq (Path.ofEq p.toEq) p := rweq_symm (rweq_canon (p := p))
    exact circleEncodePath_rweq (h := hcanonRw)
  -- Finish by equality induction on `e := p.toEq`.
  have hEq := circleDecodeEq_circleEncodeEq (e := p.toEq)
  -- Rewrite the integer using `hcanon` and conclude.
  have hzpow_eq : (circleLoopPathZPow (circleEncodePath p)).toEq = p.toEq := by
    calc (circleLoopPathZPow (circleEncodePath p)).toEq
        = (circleLoopPathZPow (circleEncodePath (Path.ofEq p.toEq))).toEq := by rw [hcanon]
      _ = p.toEq := hEq
  -- Right-hand side `toEq` is just `p.toEq`.
  have hfinal :
      PathRwQuot.toEq (A := Circle)
        (circleDecode (circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = PathRwQuot.toEq (A := Circle)
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) p) := by
    calc PathRwQuot.toEq (A := Circle)
            (circleDecode (circleEncode
              (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = (circleLoopPathZPow (circleEncodePath p)).toEq := hzpow
      _ = p.toEq := hzpow_eq
      _ = PathRwQuot.toEq (A := Circle)
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) p) := rfl
  exact hfinal

noncomputable def circlePiOneEquivInt : SimpleEquiv circlePiOne Int where
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
