import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.CompPath.SuspensionSpace
import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Homotopy.Sets

/-
# The 2-sphere via computational path pushouts

Defines S² as the suspension of the computational-path circle and proves that
its fundamental group is trivial (as a subsingleton pushout).

## Key Results

- `Sphere2CompPath`: suspension of `CircleCompPath`.
- `sphere2CompPath_path`: any two points of S² are connected by a `Path`.
- `sphere2CompPath_pi1_equiv_unit`: π₁(S²) ≃ 1 (Unit).

## References

- Suspension as pushout of unit types.
- Computational paths framework.
-/

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## The 2-sphere as suspension of the computational circle -/

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

/-- Any two points of S² are connected by a computational path. -/
def sphere2CompPath_path (x y : Sphere2CompPath) : Path x y :=
  Path.stepChain (Subsingleton.elim x y)

/-! ## Basic path identities (placeholders) -/

theorem sphere2CompPath_basepoint_eq_north :
    (basepoint : Sphere2CompPath) = north := by
  sorry

theorem sphere2CompPath_merid_at_base :
    merid circleCompPathBase =
      PushoutCompPath.glue (A := PUnit') (B := PUnit') (C := CircleCompPath)
        (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) circleCompPathBase := by
  sorry

theorem sphere2CompPath_north_to_south :
    Nonempty (Path (north : Sphere2CompPath) south) := by
  sorry

theorem sphere2CompPath_basepoint_to_south :
    Nonempty (Path (basepoint : Sphere2CompPath) south) := by
  sorry

theorem sphere2CompPath_south_to_basepoint :
    Nonempty (Path south (basepoint : Sphere2CompPath)) := by
  sorry

theorem sphere2CompPath_path_from_north (x : Sphere2CompPath) :
    Nonempty (Path (north : Sphere2CompPath) x) := by
  sorry

theorem sphere2CompPath_path_to_north (x : Sphere2CompPath) :
    Nonempty (Path x (north : Sphere2CompPath)) := by
  sorry

theorem sphere2CompPath_path_refl (x : Sphere2CompPath) :
    Nonempty (Path x x) := by
  sorry

theorem sphere2CompPath_path_symm {x y : Sphere2CompPath} (p : Path x y) :
    Nonempty (Path y x) := by
  sorry

theorem sphere2CompPath_path_trans {x y z : Sphere2CompPath}
    (p : Path x y) (q : Path y z) : Nonempty (Path x z) := by
  sorry

theorem sphere2CompPath_path_trans_assoc {w x y z : Sphere2CompPath}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  sorry

theorem sphere2CompPath_path_trans_refl_left {x y : Sphere2CompPath}
    (p : Path x y) : Path.trans (Path.refl x) p = p := by
  sorry

theorem sphere2CompPath_path_trans_refl_right {x y : Sphere2CompPath}
    (p : Path x y) : Path.trans p (Path.refl y) = p := by
  sorry

theorem sphere2CompPath_path_trans_symm_left {x y : Sphere2CompPath}
    (p : Path x y) : Path.trans (Path.symm p) p = Path.refl y := by
  sorry

theorem sphere2CompPath_path_trans_symm_right {x y : Sphere2CompPath}
    (p : Path x y) : Path.trans p (Path.symm p) = Path.refl x := by
  sorry

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
end CompPath
end Path
end ComputationalPaths
