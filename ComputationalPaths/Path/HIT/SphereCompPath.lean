import ComputationalPaths.Path.HIT.PushoutCompPath
import ComputationalPaths.Path.HIT.CircleCompPath
import ComputationalPaths.Path.HIT.PushoutCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Sets

/-
# The 2-sphere via computational path pushouts

Defines S² as the suspension of the computational-path circle and proves that
its fundamental group is trivial (as a subsingleton pushout).

## Key Results

- `Sphere2CompPath`: suspension of `CircleCompPath`.
- `sphere2CompPath_pi1_equiv_unit`: π₁(S²) ≃ 1 (Unit).

## References

- Suspension as pushout of unit types.
- Computational paths framework.
-/

namespace ComputationalPaths
namespace Path
namespace HIT

universe u

/-! ## The 2-sphere as suspension of the computational circle -/


/-- Suspension in the computational pushout setting. -/
def SuspensionCompPath (A : Type u) : Type u :=
  PushoutCompPath PUnit' PUnit' A (fun _ => PUnit'.unit) (fun _ => PUnit'.unit)

/-- The 2-sphere as suspension of the computational circle. -/
def Sphere2CompPath : Type u :=
  SuspensionCompPath CircleCompPath

namespace Sphere2CompPath

/-! ## Basepoints -/

/-- North pole of S². -/
def north : Sphere2CompPath :=
  PushoutCompPath.inl PUnit'.unit

/-- South pole of S². -/
def south : Sphere2CompPath :=
  PushoutCompPath.inr PUnit'.unit

/-- Meridian from north to south. -/
def merid (x : CircleCompPath) : Path (north : Sphere2CompPath) south :=
  PushoutCompPath.glue (A := PUnit') (B := PUnit') (C := CircleCompPath)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) x

/-- Basepoint of S² (north pole). -/
def basepoint : Sphere2CompPath := north

instance : Nonempty Sphere2CompPath := ⟨basepoint⟩

/-! ## Subsingleton and π₁ triviality -/

instance : Subsingleton Sphere2CompPath where
  allEq x y := by
    refine Quot.inductionOn x ?_ 
    intro x'
    refine Quot.inductionOn y ?_ 
    intro y'
    cases x' <;> cases y' <;>
      first
        | rfl
        | exact
            Quot.sound
              (PushoutCompPathRel.glue
                (A := PUnit') (B := PUnit') (C := CircleCompPath)
                (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit)
                circleCompPathBase)
        | exact
            (Quot.sound
              (PushoutCompPathRel.glue
                (A := PUnit') (B := PUnit') (C := CircleCompPath)
                (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit)
                circleCompPathBase)).symm

/-- The fundamental group of S² is trivial. -/
theorem sphere2CompPath_pi1_trivial :
    ∀ (α : π₁(Sphere2CompPath, (basepoint : Sphere2CompPath))),
      α = Quot.mk _ (Path.refl _) := by
  exact pi1_trivial_of_subsingleton (A := Sphere2CompPath) (a := basepoint)

/-- π₁(S²) ≃ 1 (the trivial group). -/
noncomputable def sphere2CompPath_pi1_equiv_unit :
    SimpleEquiv (π₁(Sphere2CompPath, (basepoint : Sphere2CompPath))) Unit where
  toFun := fun _ => ()
  invFun := fun _ => Quot.mk _ (Path.refl _)
  left_inv := by
    intro α
    exact (sphere2CompPath_pi1_trivial α).symm
  right_inv := by
    intro u
    cases u
    rfl

/-! ## Summary -/

end Sphere2CompPath
end HIT
end Path
end ComputationalPaths
