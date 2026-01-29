/-
# The Mobius band via computational paths

The Mobius band deformation retracts onto its core circle, so its fundamental
group is the same as the circle. We model it as a compatibility alias of the
computational-path circle and reuse the existing pi_1 encoding.
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## The Mobius band as a computational-path circle -/

/-- The Mobius band is modeled by its deformation retract onto the circle. -/
abbrev MobiusBandCompPath : Type u := CircleCompPath.{u}

@[simp] abbrev mobiusBandBase : MobiusBandCompPath := circleCompPathBase

/-! ## Fundamental group -/

abbrev mobiusBandPiOne : Type u := circleCompPathPiOne

noncomputable def mobiusBandPiOneEquivInt :
    SimpleEquiv mobiusBandPiOne Int :=
  circleCompPathPiOneEquivInt

/-! ## Compatibility aliases -/

abbrev MobiusBand : Type u := MobiusBandCompPath.{u}

@[simp] abbrev mobiusBandBasepoint : MobiusBand := mobiusBandBase

end CompPath
end Path
end ComputationalPaths
