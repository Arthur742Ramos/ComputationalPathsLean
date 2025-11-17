import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

open SimpleEquiv

-- Precise zpow addition specializations avoiding universe issues.
theorem circleLoopZPow_add_one (z : Int) :
    circleLoopZPow (z + 1)
      = LoopQuot.comp (circleLoopZPow z) circleLoopClass := by
  simpa [circleLoopZPow_one] using
    (circleLoopZPow_add (m := z) (n := 1))

theorem circleLoopZPow_add_neg_one (z : Int) :
    circleLoopZPow (z + (-1))
      = LoopQuot.comp (circleLoopZPow z) (LoopQuot.inv circleLoopClass) := by
  simpa [circleLoopZPow_neg_one] using
    (circleLoopZPow_add (m := z) (n := -1))

@[simp] theorem circleEncode_circleDecode_add_one (z : Int) :
    circleEncode (circleDecode (z + 1))
      = circleEncode (circleDecode z) + 1 := by
  -- Work with `circleEncodeLift` to avoid universe mismatch, then fold back.
  change circleEncodeLift (circleLoopZPow (z + 1))
      = circleEncodeLift (circleLoopZPow z) + 1
  have hz := circleLoopZPow_add_one z
  have eqA := _root_.congrArg circleEncodeLift hz
  exact eqA.trans (circleEncodeLift_comp_loop (x := circleLoopZPow z))

@[simp] theorem circleEncode_circleDecode_add_neg_one (z : Int) :
    circleEncode (circleDecode (z + (-1)))
      = circleEncode (circleDecode z) - 1 := by
  change circleEncodeLift (circleLoopZPow (z + (-1)))
      = circleEncodeLift (circleLoopZPow z) - 1
  have hz := circleLoopZPow_add_neg_one z
  have eqA := _root_.congrArg circleEncodeLift hz
  exact eqA.trans (circleEncodeLift_comp_inv_loop (x := circleLoopZPow z))

/-- Encode∘decode identity on negative integers by Nat induction. -/
theorem circleEncode_circleDecode_of_negNat (k : Nat) :
    circleEncode (circleDecode (-(k : Int))) = -(k : Int) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Step: use the -1 step lemma at z = -k
      have step := circleEncode_circleDecode_add_neg_one (z := - (k : Int))
      -- Rewrite the target integer -((k+1)) as (-k) + (-1)
      have hneg : -((Nat.succ k : Nat) : Int) = - (k : Int) + (-1) := by
        have hk := (Int.natCast_succ k)
        -- ((k+1) : Int) = (k : Int) + 1; negate both sides and normalise
        have := congrArg (fun t => -t) hk
        -- -((k:ℤ)+1) = -(k:ℤ) + (-1)
        simpa [Int.sub_eq_add_neg, Int.add_comm, Int.add_left_comm, Int.add_assoc]
          using this
      -- Apply the step lemma and the induction hypothesis, then normalise -k - 1 to -(k+1)
      calc
        circleEncode (circleDecode (-(Nat.succ k : Int)))
            = circleEncode (circleDecode (- (k : Int) + (-1))) := by
                simpa [hneg]
        _ = circleEncode (circleDecode (-(k : Int))) - 1 := step
        _ = -(k : Int) - 1 := by simpa using ih
        _ = -((Nat.succ k : Nat) : Int) := by
                -- -(k) - 1 = -(k) + (-1) = -(k + 1)
                simpa [Int.natCast_succ, Int.sub_eq_add_neg,
                  Int.add_comm, Int.add_left_comm, Int.add_assoc]
                  using rfl

@[simp] theorem circleEncode_circleDecode (z : Int) :
    circleEncode (circleDecode z) = z := by
  cases z with
  | ofNat n =>
      exact circleEncode_circleDecode_ofNat n
  | negSucc n =>
      -- z = -(n.succ)
      exact circleEncode_circleDecode_of_negNat (Nat.succ n)

/-- Subtype for the image (range) of `circleDecode`. -/
def circleDecodeRangeSubtype : Type _ :=
  { x : CircleLoopQuot // ∃ z : Int, x = circleDecode z }

/-- Equivalence between Z and the range of `circleDecode` in π₁(S¹).
This packages the already established `encode ∘ decode = id` into a two-sided
inverse on the image; the other direction holds by construction of the range. -/
def circlePiOneEquivIntRange : SimpleEquiv Int circleDecodeRangeSubtype where
  toFun := fun z => ⟨circleDecode z, ⟨z, rfl⟩⟩
  invFun := fun s => circleEncode s.val
  left_inv := by
    intro z; exact circleEncode_circleDecode (z := z)
  right_inv := by
    intro s
    rcases s with ⟨x, ⟨z, hz⟩⟩
    -- decode (encode x) = x for x in the range of decode
    have : circleDecode (circleEncode x) = x := by
      -- Use that x = decode z and the established encode∘decode identity
      have h := _root_.congrArg circleDecode (circleEncode_circleDecode (z := z))
      -- h : circleDecode (circleEncode (circleDecode z)) = circleDecode z
      -- rewrite by x = decode z
      simpa [hz]
      -- Equality in the subtype reduces to equality of values
    apply Subtype.eq
    simpa using this

/-- On the image of `circleDecode`, we have `decode ∘ encode = id`. -/
@[simp] theorem circleDecode_circleEncode_of_memRange
    {x : CircleLoopQuot} (hx : ∃ z : Int, x = circleDecode z) :
    circleDecode (circleEncode x) = x := by
  rcases hx with ⟨z, hz⟩
  have h := _root_.congrArg circleDecode (circleEncode_circleDecode (z := z))
  -- h : circleDecode (circleEncode (circleDecode z)) = circleDecode z
  -- rewrite using x = circleDecode z
  simpa [hz]

@[simp] theorem circleWindingNumber_decode (z : Int) :
    circleWindingNumber (circleDecode z) = z := by
  change circleEncode (circleDecode z) = z
  exact circleEncode_circleDecode (z := z)

end Path
end ComputationalPaths
