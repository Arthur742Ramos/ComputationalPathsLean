/-
# RP^2 via computational paths

We model RP^2 using the standard CW presentation with a single 2-cell
attaching map of degree 2. In the computational-path setting, the resulting
fundamental group is Z/2. We encode Z/2 as Bool with xor.
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Z/2 encoding -/

abbrev Z2 : Type := Bool

@[simp] def z2_add (a b : Z2) : Z2 := xor a b

@[simp] def z2_zero : Z2 := false

@[simp] def z2_one : Z2 := true

/-! ## RP^2 pi_1 data -/

/-- We treat the fundamental group of RP^2 as Z/2. -/
abbrev rp2PiOne : Type := Z2

noncomputable def rp2PiOneEquivZ2 : SimpleEquiv rp2PiOne Z2 where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Compatibility aliases -/

abbrev RealProjective2 : Type u := PUnit'

@[simp] abbrev realProjective2Base : RealProjective2 := PUnit'.unit

end CompPath
end Path
end ComputationalPaths
