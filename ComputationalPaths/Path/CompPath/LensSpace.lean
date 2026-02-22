/-
# Lens spaces via computational paths

We model the fundamental group of a lens space L(p, q) as Z/p and provide
Path-level loop data for compatibility with the computational-path interface.

## Key Results

- `lensSpacePiOneEquivZp`: identity equivalence for the Z/p model.
- `lensSpaceLoop`, `lensSpaceLoopPow`: loop generator and iterates as Paths.
- `lensSpaceDecodePath`: interpret Z/p elements as loop paths.
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Z/p encoding -/

/-- `Z/p` modeled as `Fin p`. -/
abbrev Zp (p : Nat) : Type := Fin p

/-! ## Lens space pi_1 data -/

/-- Model for `π₁(L(p,q))` as `Z/p`. -/
abbrev lensSpacePiOne (p : Nat) : Type := Zp p

/-- Identity equivalence between the model and `Z/p`. -/
noncomputable def lensSpacePiOneEquivZp (p : Nat) :
    SimpleEquiv (lensSpacePiOne p) (Zp p) where
  toFun := id
  invFun := id
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-! ## Compatibility aliases -/

/-- Placeholder lens space type. -/
abbrev LensSpace (_p _q : Nat) : Type u := PUnit'

/-- Basepoint of the lens space. -/
@[simp] abbrev lensSpaceBase (_p _q : Nat) : LensSpace _p _q := PUnit'.unit

/-! ## Path-level loops -/

/-- Loop space at the lens space basepoint. -/
abbrev lensSpaceLoopSpace (p q : Nat) : Type u :=
  Path (A := LensSpace p q) (lensSpaceBase p q) (lensSpaceBase p q)

/-- Fundamental loop at the basepoint. -/
@[simp] noncomputable def lensSpaceLoop (p q : Nat) : lensSpaceLoopSpace p q :=
  Path.stepChain rfl

/-- Iterate the fundamental loop `n` times. -/
@[simp] noncomputable def lensSpaceLoopPow (p q : Nat) : Nat → lensSpaceLoopSpace p q
  | 0 => Path.refl (lensSpaceBase p q)
  | Nat.succ n => Path.trans (lensSpaceLoop p q) (lensSpaceLoopPow p q n)

/-- Interpret an element of `Z/p` as a loop path. -/
@[simp] noncomputable def lensSpaceDecodePath (p q : Nat) :
    Zp p → lensSpaceLoopSpace p q :=
  fun x => lensSpaceLoopPow p q x.val

end CompPath
end Path
end ComputationalPaths
