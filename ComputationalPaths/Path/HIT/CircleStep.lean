import ComputationalPaths.Path.HIT.Circle

namespace ComputationalPaths
namespace Path

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

end Path
end ComputationalPaths

