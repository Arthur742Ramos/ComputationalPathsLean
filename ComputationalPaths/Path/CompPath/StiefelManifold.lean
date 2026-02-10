/-
# Stiefel manifolds via computational paths

We provide a lightweight computational-path model for real Stiefel manifolds
`V_k(R^n)`. To remain axiom-free, we model each Stiefel manifold as a
subsingleton type (`PUnit'`) and expose Path-level loop helpers together with a
trivial fundamental-group equivalence.

## Key Results

- `StiefelManifoldCompPath`: computational-path model of `V_k(R^n)`.
- `stiefelManifoldBase`: basepoint of the model.
- `stiefelManifoldLoop`, `stiefelManifoldLoopPow`: Path-level loop helpers.
- `stiefelManifoldPiOneEquivUnit`: π₁(V_k(R^n)) ≃ 1 in the model.

## References

- Computational paths framework.
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Sets
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Stiefel manifold model -/

/-- Computational-path model for the real Stiefel manifold `V_k(R^n)`. -/
def StiefelManifoldCompPath (_n _k : Nat) : Type u := PUnit'

/-- The Stiefel manifold model is a subsingleton. -/
instance (n k : Nat) : Subsingleton (StiefelManifoldCompPath n k) := by
  dsimp [StiefelManifoldCompPath]
  infer_instance

/-- Basepoint of the Stiefel manifold model. -/
@[simp] def stiefelManifoldBase (n k : Nat) : StiefelManifoldCompPath n k :=
  PUnit'.unit

/-! ## Loop space helpers -/

/-- Loop space at the Stiefel manifold basepoint. -/
abbrev stiefelManifoldLoopSpace (n k : Nat) : Type u :=
  Path (A := StiefelManifoldCompPath n k)
    (stiefelManifoldBase n k) (stiefelManifoldBase n k)

/-- Fundamental loop at the Stiefel manifold basepoint. -/
@[simp] def stiefelManifoldLoop (n k : Nat) : stiefelManifoldLoopSpace n k :=
  Path.ofEq rfl

/-- Iterate the fundamental loop `m` times. -/
@[simp] def stiefelManifoldLoopPow (n k : Nat) : Nat → stiefelManifoldLoopSpace n k
  | 0 => Path.refl (stiefelManifoldBase n k)
  | Nat.succ m => Path.trans (stiefelManifoldLoop n k) (stiefelManifoldLoopPow n k m)

/-- Interpret a natural number as a loop path. -/
@[simp] def stiefelManifoldDecodePath (n k : Nat) :
    Nat → stiefelManifoldLoopSpace n k :=
  stiefelManifoldLoopPow n k

/-! ## Fundamental group -/

/-- Fundamental group of the Stiefel manifold model. -/
abbrev stiefelManifoldPiOne (n k : Nat) : Type u :=
  π₁(StiefelManifoldCompPath n k, stiefelManifoldBase n k)

/-- π₁(V_k(R^n)) ≃ 1 in the subsingleton model. -/
noncomputable def stiefelManifoldPiOneEquivUnit (n k : Nat) :
    SimpleEquiv (stiefelManifoldPiOne n k) Unit where
  toFun := fun _ => ()
  invFun := fun _ => Quot.mk _ (Path.refl (stiefelManifoldBase n k))
  left_inv := by
    intro α
    exact
      (pi1_trivial_of_subsingleton
        (A := StiefelManifoldCompPath n k) (a := stiefelManifoldBase n k) α).symm
  right_inv := by
    intro u
    cases u
    rfl

/-! ## Compatibility aliases -/

/-- Alias for the Stiefel manifold model. -/
abbrev StiefelManifold (n k : Nat) : Type u := StiefelManifoldCompPath n k

/-- Alias for the Stiefel manifold basepoint. -/
@[simp] abbrev stiefelManifoldBasepoint (n k : Nat) : StiefelManifold n k :=
  stiefelManifoldBase n k

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
