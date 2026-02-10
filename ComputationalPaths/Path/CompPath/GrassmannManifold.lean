/-
# Grassmannians via computational paths

Lightweight computational-path models for real and complex Grassmannians.
We model Gr(1, n+1) using projective spaces and collapse higher Grassmannians
to a point type. This yields a small, axiom-free model for pi_1 and pi_2.

## Key Results

- `RealGrassmann`: real Grassmannian model.
- `ComplexGrassmann`: complex Grassmannian model.
- `realGrassmannPiOneEquiv`: pi_1 model equivalence (Unit/Int/Z2).
- `complexGrassmannPiOneEquivUnit`: pi_1 of complex Grassmannians is trivial.
- `realGrassmannPiTwoEquivUnit` / `complexGrassmannPiTwoEquivUnit`: pi_2 is trivial.

## References

- Gr(1, n+1) agrees with projective space.
- Truncation results for pi_2 in computational paths.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.CompPath.ProjectiveSpace
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Sets
import ComputationalPaths.Path.Homotopy.Truncation
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Grassmannian models -/

/-- Real Grassmannian Gr(k, n) in the computational-path model. -/
def RealGrassmann : Nat → Nat → Type u
  | 0, _ => PUnit'
  | 1, 0 => PUnit'
  | 1, Nat.succ n => RealProjectiveSpace n
  | Nat.succ (Nat.succ _), _ => PUnit'

/-- Complex Grassmannian Gr(k, n) in the computational-path model. -/
def ComplexGrassmann : Nat → Nat → Type u
  | 0, _ => PUnit'
  | 1, 0 => PUnit'
  | 1, Nat.succ n => ComplexProjectiveSpace n
  | Nat.succ (Nat.succ _), _ => PUnit'

/-! ## Basepoints -/

/-- Basepoint of the real Grassmannian model. -/
@[simp] def realGrassmannBase : (k n : Nat) → RealGrassmann k n
  | 0, _ => PUnit'.unit
  | 1, 0 => PUnit'.unit
  | 1, Nat.succ n => realProjectiveSpaceBase n
  | Nat.succ (Nat.succ _), _ => PUnit'.unit

/-- Basepoint of the complex Grassmannian model. -/
@[simp] def complexGrassmannBase : (k n : Nat) → ComplexGrassmann k n
  | 0, _ => PUnit'.unit
  | 1, 0 => PUnit'.unit
  | 1, Nat.succ n => complexProjectiveBase n
  | Nat.succ (Nat.succ _), _ => PUnit'.unit

/-! ## pi_1 models for real Grassmannians -/

/-- Model for pi_1 of the real Grassmannian. -/
def realGrassmannPiOne : Nat → Nat → Type u
  | 1, Nat.succ n => realProjectivePiOne n
  | _, _ => PUnit'

/-- Group model for pi_1 of the real Grassmannian. -/
def realGrassmannPiOneModel : Nat → Nat → Type
  | 1, Nat.succ n => realProjectivePiOneModel n
  | _, _ => Unit

/-- Equivalence between the unit types used in the Grassmannian models. -/
private def punitEquivUnit : SimpleEquiv PUnit' Unit where
  toFun := fun _ => ()
  invFun := fun _ => PUnit'.unit
  left_inv := by
    intro x
    cases x
    rfl
  right_inv := by
    intro u
    cases u
    rfl

/-- pi_1 model equivalence for real Grassmannians. -/
noncomputable def realGrassmannPiOneEquiv (k n : Nat) :
    SimpleEquiv (realGrassmannPiOne k n) (realGrassmannPiOneModel k n) := by
  cases k with
  | zero =>
      simpa [realGrassmannPiOne, realGrassmannPiOneModel] using punitEquivUnit
  | succ k =>
      cases k with
      | zero =>
          cases n with
          | zero =>
              simpa [realGrassmannPiOne, realGrassmannPiOneModel] using punitEquivUnit
          | succ n =>
              simpa [realGrassmannPiOne, realGrassmannPiOneModel] using
                realProjectivePiOneEquiv n
      | succ _ =>
          simpa [realGrassmannPiOne, realGrassmannPiOneModel] using punitEquivUnit

/-! ## pi_1 of complex Grassmannians -/

/-- The fundamental group of a complex Grassmannian is trivial in this model. -/
theorem complexGrassmann_pi1_trivial (k n : Nat) :
    ∀ (α : PiOne (ComplexGrassmann k n) (complexGrassmannBase k n)),
      α = Quot.mk _ (Path.refl _) := by
  cases k with
  | zero =>
      cases n <;>
        simpa [ComplexGrassmann, complexGrassmannBase,
          ComplexProjectiveSpace, complexProjectiveBase] using
          (pi1_trivial_of_subsingleton (A := PUnit') (a := PUnit'.unit))
  | succ k =>
      cases k with
      | zero =>
          cases n <;>
            simpa [ComplexGrassmann, complexGrassmannBase,
              ComplexProjectiveSpace, complexProjectiveBase] using
              (pi1_trivial_of_subsingleton (A := PUnit') (a := PUnit'.unit))
      | succ _ =>
          cases n <;>
            simpa [ComplexGrassmann, complexGrassmannBase,
              ComplexProjectiveSpace, complexProjectiveBase] using
              (pi1_trivial_of_subsingleton (A := PUnit') (a := PUnit'.unit))

/-- pi_1(Gr_C(k, n)) ~= 1. -/
noncomputable def complexGrassmannPiOneEquivUnit (k n : Nat) :
    SimpleEquiv (PiOne (ComplexGrassmann k n) (complexGrassmannBase k n)) Unit where
  toFun := fun _ => ()
  invFun := fun _ => Quot.mk _ (Path.refl _)
  left_inv := by
    intro α
    exact (complexGrassmann_pi1_trivial k n α).symm
  right_inv := by
    intro u
    cases u
    rfl

/-! ## pi_2 triviality -/

/-- pi_2 of real Grassmannians is trivial in this framework. -/
theorem realGrassmann_pi2_trivial (k n : Nat) (a : RealGrassmann k n) :
    ∀ (α : HigherHomotopy.PiTwo (RealGrassmann k n) a),
      α = HigherHomotopy.PiTwo.id (A := RealGrassmann k n) (a := a) := by
  simpa using Truncation.pi2_trivial (A := RealGrassmann k n) a

/-- pi_2 of complex Grassmannians is trivial in this framework. -/
theorem complexGrassmann_pi2_trivial (k n : Nat) (a : ComplexGrassmann k n) :
    ∀ (α : HigherHomotopy.PiTwo (ComplexGrassmann k n) a),
      α = HigherHomotopy.PiTwo.id (A := ComplexGrassmann k n) (a := a) := by
  simpa using Truncation.pi2_trivial (A := ComplexGrassmann k n) a

/-- pi_2(Gr_R(k, n)) ~= 1. -/
noncomputable def realGrassmannPiTwoEquivUnit (k n : Nat) (a : RealGrassmann k n) :
    SimpleEquiv (HigherHomotopy.PiTwo (RealGrassmann k n) a) Unit where
  toFun := fun _ => ()
  invFun := fun _ => HigherHomotopy.PiTwo.id (A := RealGrassmann k n) (a := a)
  left_inv := by
    intro α
    exact (realGrassmann_pi2_trivial k n a α).symm
  right_inv := by
    intro u
    cases u
    rfl

/-- pi_2(Gr_C(k, n)) ~= 1. -/
noncomputable def complexGrassmannPiTwoEquivUnit (k n : Nat) (a : ComplexGrassmann k n) :
    SimpleEquiv (HigherHomotopy.PiTwo (ComplexGrassmann k n) a) Unit where
  toFun := fun _ => ()
  invFun := fun _ => HigherHomotopy.PiTwo.id (A := ComplexGrassmann k n) (a := a)
  left_inv := by
    intro α
    exact (complexGrassmann_pi2_trivial k n a α).symm
  right_inv := by
    intro u
    cases u
    rfl

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
