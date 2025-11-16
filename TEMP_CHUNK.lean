theorem circleLoopZPow_add_one (z : Int) :
    circleLoopZPow (z + 1)
      = LoopQuot.comp (circleLoopZPow z) circleLoopClass := by
  have h := circleLoopZPow_add (m := z) (n := 1)
  have h1 :
      LoopQuot.comp (circleLoopZPow z) (circleLoopZPow 1)
        = LoopQuot.comp (circleLoopZPow z) circleLoopClass := by
    cases circleLoopZPow_one; rfl
  exact h.trans h1
@[simp] theorem circleEncode_circleDecode_add_one (z : Int) :
    circleEncode (circleDecode (z + 1))
      = circleEncode (circleDecode z) + 1 := by
  -- Work with `circleEncodeLift` to avoid universe inference issues, then fold back.
  change circleEncodeLift (circleLoopZPow (z + 1))
      = circleEncodeLift (circleLoopZPow z) + 1
  have hz := circleLoopZPow_add_one z
  have eqA := _root_.congrArg circleEncodeLift hz
  exact eqA.trans (circleEncodeLift_comp_loop (x := circleLoopZPow z))
-- Step lemma sketch (commented out to avoid universe friction in Eq.trans):
-- @[simp] theorem circleEncode_circleDecode_add_one (z : Int) :
--     circleEncode (circleDecode (z + 1))
--       = circleEncode (circleDecode z) + 1 := by
--   have h := circleDecode_add_one_rw z
--   have e := circleEncode_comp_loop (x := circleDecode z)
--   exact (_root_.congrArg circleEncode h).trans e

-- Step law: encoding `decode (z + (-1))` decreases by one.
theorem circleLoopZPow_add_neg_one (z : Int) :
    circleLoopZPow (z + (-1))
      = LoopQuot.comp (circleLoopZPow z) (LoopQuot.inv circleLoopClass) := by
  have h := circleLoopZPow_add (m := z) (n := -1)
  have h1 :
      LoopQuot.comp (circleLoopZPow z) (circleLoopZPow (-1))
        = LoopQuot.comp (circleLoopZPow z) (LoopQuot.inv circleLoopClass) := by
    cases circleLoopZPow_neg_one; rfl
  exact h.trans h1
@[simp] theorem circleEncode_circleDecode_add_neg_one (z : Int) :
    circleEncode (circleDecode (z + (-1)))
      = circleEncode (circleDecode z) - 1 := by
  change circleEncodeLift (circleLoopZPow (z + (-1)))
      = circleEncodeLift (circleLoopZPow z) - 1
  have hz := circleLoopZPow_add_neg_one z
  have eqA := _root_.congrArg circleEncodeLift hz
  exact eqA.trans (circleEncodeLift_comp_inv_loop (x := circleLoopZPow z))
-- @[simp] theorem circleEncode_circleDecode_add_neg_one (z : Int) :
--     circleEncode (circleDecode (z + (-1)))
--       = circleEncode (circleDecode z) - 1 := by
--   have h := circleDecode_add_neg_one_rw z
--   have e := circleEncode_comp_inv_loop (x := circleDecode z)
--   exact (_root_.congrArg circleEncode h).trans e

end
end Path
end ComputationalPaths



