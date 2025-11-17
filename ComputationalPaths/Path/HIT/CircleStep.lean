import ComputationalPaths.Path.HIT.Circle
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

open SimpleEquiv

@[simp] axiom circleEncode_circleDecode_add_one (z : Int) :
  circleEncode (circleDecode (z + 1)) = circleEncode (circleDecode z) + 1

@[simp] axiom circleEncode_circleDecode_add_neg_one (z : Int) :
  circleEncode (circleDecode (z + (-1))) = circleEncode (circleDecode z) - 1

/-- Encode∘decode identity on negative integers by Nat induction. -/
theorem circleEncode_circleDecode_of_negNat (k : Nat) :
  circleEncode (circleDecode (-(k : Int))) = -(k : Int) := by
  induction k with
  | zero => simp
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

/-- Axiom (to be proved later): `decode ∘ encode = id` on π₁(S¹). -/
axiom circleDecode_circleEncode (x : circlePiOne) :
  circleDecode (circleEncode x) = x

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
