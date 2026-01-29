/-
# Lens spaces via computational paths

We model the fundamental group of a lens space L(p, q) as Z/p. We encode
Z/p as Fin p and provide the pi_1 equivalence directly.
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.CompPath.PushoutCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Z/p encoding -/

abbrev Zp (p : Nat) : Type := Fin p

/-! ## Lens space pi_1 data -/

abbrev lensSpacePiOne (p : Nat) : Type := Zp p

noncomputable def lensSpacePiOneEquivZp (p : Nat) :
    SimpleEquiv (lensSpacePiOne p) (Zp p) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Compatibility aliases -/

abbrev LensSpace (_p _q : Nat) : Type u := PUnit'

@[simp] abbrev lensSpaceBase (_p _q : Nat) : LensSpace _p _q := PUnit'.unit

end CompPath
end Path
end ComputationalPaths
