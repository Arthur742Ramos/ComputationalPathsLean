import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

open SimpleEquiv

@[simp] theorem int_add_sub_add_right (a b c : Int) :
    (a + c) - (b + c) = a - b := by
  have hb : -(b + c) = (-b) + (-c) := by simp
  simp [Int.sub_eq_add_neg, hb, Int.add_assoc, Int.add_comm, Int.add_left_comm]

@[simp] theorem circleEncode_circleDecode_add_one (z : Int) :
    circleEncode (circleDecode (z + 1))
      = circleEncode (circleDecode z) + 1 := by
  change circleEncodeLift (circleLoopZPow (z + 1))
      = circleEncodeLift (circleLoopZPow z) + 1
  rw [circleLoopZPow_add (m := z) (n := 1), circleLoopZPow_one]
  exact circleEncodeLift_comp_loop (x := circleLoopZPow z)

@[simp] theorem circleEncode_circleDecode_add_neg_one (z : Int) :
    circleEncode (circleDecode (z + (-1)))
      = circleEncode (circleDecode z) - 1 := by
  change circleEncodeLift (circleLoopZPow (z + (-1)))
      = circleEncodeLift (circleLoopZPow z) - 1
  rw [circleLoopZPow_add (m := z) (n := -1), circleLoopZPow_neg_one]
  exact circleEncodeLift_comp_inv_loop (x := circleLoopZPow z)

/-- Encode∘decode identity on negative integers by Nat induction. -/
theorem circleEncode_circleDecode_of_negNat (k : Nat) :
    circleEncode (circleDecode (-(k : Int))) = -(k : Int) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      -- Step: use the −1 step lemma at z = −k
      have step := circleEncode_circleDecode_add_neg_one (z := - (k : Int))
      -- Rewrite the target integer -((k+1)) as (-k) + (-1)
      have hneg : -((Nat.succ k : Nat) : Int) = - (k : Int) + (-1) := by
        have := (Int.natCast_succ k)
        -- ((k+1) : Int) = (k : Int) + 1, so negate both sides
        simpa [Int.add_comm, Int.add_left_comm, Int.add_assoc, Int.sub_eq_add_neg]
          using congrArg (fun t => -t) this
      -- Apply the step lemma and the induction hypothesis, then normalise −k − 1 to −(k+1)
      calc
        circleEncode (circleDecode (-(Nat.succ k : Int)))
            = circleEncode (circleDecode (- (k : Int) + (-1))) := by
                simpa [hneg]
        _ = circleEncode (circleDecode (-(k : Int))) - 1 := step
        _ = -(k : Int) - 1 := by simpa using congrArg (fun t => t) ih
        _ = -((Nat.succ k : Nat) : Int) := by
                -- -(k) - 1 = -(k) + (-1) = -(k + 1)
                simpa [Int.natCast_succ, Int.sub_eq_add_neg,
                  Int.add_comm, Int.add_left_comm, Int.add_assoc]
                  using rfl

@[simp] theorem circleEncode_circleDecode (z : Int) :
    circleEncode (circleDecode z) = z := by
  cases z with
  | ofNat n =>
      simpa using circleEncode_circleDecode_ofNat n
  | negSucc n =>
      -- z = -(n.succ)
      simpa using circleEncode_circleDecode_of_negNat (Nat.succ n)

/-- Subtype for the image (range) of `circleDecode`. -/
def circleDecodeRangeSubtype : Type _ :=
  { x : CircleLoopQuot // ∃ z : Int, x = circleDecode z }

/-- Equivalence between ℤ and the range of `circleDecode` in π₁(S¹).
This packages the already established `encode ∘ decode = id` into a two-sided
inverse on the image; the other direction holds by construction of the range. -/
def circlePiOneEquivIntRange : SimpleEquiv Int circleDecodeRangeSubtype where
  toFun := fun z => ⟨circleDecode z, ⟨z, rfl⟩⟩
  invFun := fun s => circleEncode s.val
  left_inv := by
    intro z; simp [circleEncode_circleDecode]
  right_inv := by
    intro s
    rcases s with ⟨x, ⟨z, hz⟩⟩
    -- decode (encode x) = x for x in the range of decode
    have : circleDecode (circleEncode x) = circleDecode z := by
      simpa [hz] using congrArg circleDecode (circleEncode_circleDecode (z := z)).symm
    -- Wrap back into the subtype
    -- toFun (invFun ⟨x,⟨z,hz⟩⟩) = ⟨decode (encode x), ⟨_, rfl⟩⟩
    -- Use the above equality to rewrite to ⟨decode z, ⟨z, rfl⟩⟩ = ⟨x, ⟨z, hz⟩⟩
    apply Subtype.eq
    simpa [hz] using this

end Path
end ComputationalPaths
