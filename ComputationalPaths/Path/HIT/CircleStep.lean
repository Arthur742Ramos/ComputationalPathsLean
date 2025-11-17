import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths
namespace Path

open SimpleEquiv

@[simp] theorem circleEncode_circleDecode_add_one (z : Int) :
  circleEncode (circleDecode (z + 1)) = circleEncode (circleDecode z) + 1 := by
  change circleEncode (circleLoopZPow (z + 1))
      = circleEncode (circleLoopZPow z) + 1
  rw [circleLoopZPow_add (m := z) (n := 1), circleLoopZPow_one]
  have hx := circleEncode_comp_loop (x := circleLoopZPow z)
  exact hx

@[simp] theorem circleEncode_circleDecode_add_neg_one (z : Int) :
  circleEncode (circleDecode (z + (-1))) = circleEncode (circleDecode z) - 1 := by
  change circleEncode (circleLoopZPow (z + (-1)))
      = circleEncode (circleLoopZPow z) - 1
  rw [circleLoopZPow_add (m := z) (n := -1), circleLoopZPow_neg_one]
  have hx := circleEncode_comp_inv_loop (x := circleLoopZPow z)
  exact hx

/-- Encode∘decode identity on negative integers by Nat induction. -/
theorem circleEncode_circleDecode_of_negNat (k : Nat) :
  circleEncode (circleDecode (-(k : Int))) = -(k : Int) := by
  induction k with
  | zero =>
      simpa using circleEncode_circleDecode_ofNat 0
  | succ k ih =>
      have step := circleEncode_circleDecode_add_neg_one (z := - (k : Int))
      have hk := (Int.natCast_succ k)
      have hneg := _root_.congrArg (fun t => -t) hk
      have : -((Nat.succ k : Nat) : Int) = - (k : Int) + (-1) := by
        simpa [Int.sub_eq_add_neg, Int.add_comm, Int.add_left_comm, Int.add_assoc] using hneg
      calc
        circleEncode (circleDecode (-(Nat.succ k : Int)))
            = circleEncode (circleDecode (- (k : Int) + (-1))) := by simpa [this]
        _ = circleEncode (circleDecode (-(k : Int))) - 1 := step
        _ = -(k : Int) - 1 := by simpa using ih
        _ = -((Nat.succ k : Nat) : Int) := by simpa [Int.sub_eq_add_neg] using this.symm

@[simp] theorem circleEncode_circleDecode (z : Int) :
  circleEncode (circleDecode z) = z := by
  cases z with
  | ofNat n =>
      exact circleEncode_circleDecode_ofNat n
  | negSucc n =>
      exact circleEncode_circleDecode_of_negNat (Nat.succ n)

-- Equality-level helper: `decodeEq ∘ encodeEq = id` on `(=)`.
private theorem circleDecodeEq_circleEncodeEq
    (e : circleBase = circleBase) :
    (circleLoopPathZPow (circleEncodePath (Path.ofEq e))).toEq = e := by
  cases e with
  | rfl =>
      -- encodeEq rfl = 0 and decodeEq 0 = rfl
      simpa using (by
        have : circleEncodePath (Path.refl circleBase) = (0 : Int) :=
          circleEncodePath_refl
        simpa [this])

/-- `decode ∘ encode = id` on π₁(S¹). -/
theorem circleDecode_circleEncode (x : circlePiOne) :
    circleDecode (circleEncode x) = x := by
  -- Compare via propositional equality using `toEq`.
  apply eq_of_toEq_eq (A := Circle) (a := circleBase) (b := circleBase)
  -- Work with a path representative of `x`.
  refine Quot.inductionOn x (fun p => ?_)
  -- Reduce `decode (encode (ofLoop p))` to an equality on raw z-powers.
  have :
      PathRwQuot.toEq (A := Circle)
        (circleDecode (circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = (circleLoopPathZPow (circleEncodePath p)).toEq := by
    -- `toEq (decode z)` calculates to the raw `circleLoopPathZPow`.
    change PathRwQuot.toEq (A := Circle)
        (circleLoopZPow (circleEncodePath p))
        = (circleLoopPathZPow (circleEncodePath p)).toEq
    simpa using circleLoopZPow_toEq (z := circleEncodePath p)
  -- Replace the integer by the canonicalised version built from `p.toEq`.
  have hcanon :
      circleEncodePath (Path.ofEq p.toEq) = circleEncodePath p := by
    have hcanonRw : RwEq (Path.ofEq p.toEq) p := rweq_canon (p := p)
    exact circleEncodePath_rweq (h := hcanonRw)
  -- Finish by equality induction on `e := p.toEq`.
  have hEq := circleDecodeEq_circleEncodeEq (e := p.toEq)
  -- Rewrite the integer using `hcanon` and conclude.
  have :
      (circleLoopPathZPow (circleEncodePath p)).toEq = p.toEq := by
    simpa [hcanon] using hEq
  -- Right-hand side `toEq` is just `p.toEq`.
  have :
      PathRwQuot.toEq (A := Circle)
        (circleDecode (circleEncode
          (LoopQuot.ofLoop (A := Circle) (a := circleBase) p)))
        = PathRwQuot.toEq (A := Circle)
            (LoopQuot.ofLoop (A := Circle) (a := circleBase) p) :=
    this
  simpa using this

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
