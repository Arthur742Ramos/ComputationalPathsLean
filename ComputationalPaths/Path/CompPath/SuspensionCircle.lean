/-
# Suspension of the computational circle

This module packages the suspension of the computational-path circle and
recasts the triviality of its fundamental group using the sphere result.
We also develop the double suspension, iterated suspensions,
meridian path algebra, and connectivity results for Σⁿ(S¹).

## Key Results

- `SuspensionCircleCompPath`: suspension of `CircleCompPath`.
- `suspensionCircleCompPath_pi1_trivial`: π₁(Σ(S¹)) is trivial.
- `suspensionCircleCompPath_pi1_equiv_unit`: π₁(Σ(S¹)) ≃ 1.
- `DoubleSuspensionCircle`: ΣΣ(S¹)
- `iterSuspCircle`: Σⁿ(S¹)
- Meridian path algebra: composition, cancellation, coherence
- Subsingleton propagation

## References

- Hatcher, *Algebraic Topology*, §0.3, §4.1
- HoTT Book, Chapter 6.5, 8.1
-/

import ComputationalPaths.Path.CompPath.SphereCompPath

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Suspension of the computational circle -/

/-- The suspension of the computational circle. -/
def SuspensionCircleCompPath : Type u :=
  SuspensionCompPath CircleCompPath

/-- Basepoint of the suspension of the computational circle (north pole). -/
def suspensionCircleBasepoint : SuspensionCircleCompPath :=
  Sphere2CompPath.basepoint

/-- North pole of Σ(S¹). -/
def suspensionCircleNorth : SuspensionCircleCompPath :=
  SuspensionCompPath.north (X := CircleCompPath)

/-- South pole of Σ(S¹). -/
def suspensionCircleSouth : SuspensionCircleCompPath :=
  SuspensionCompPath.south (X := CircleCompPath)

/-- Meridian of Σ(S¹) for a point on S¹. -/
def suspensionCircleMerid (x : CircleCompPath) :
    Path (suspensionCircleNorth : SuspensionCircleCompPath) suspensionCircleSouth :=
  SuspensionCompPath.merid (X := CircleCompPath) x

/-- The basepoint coincides with the north pole. -/
theorem suspensionCircleBasepoint_eq_north :
    (suspensionCircleBasepoint : SuspensionCircleCompPath) = suspensionCircleNorth := rfl

/-- Path witness of the basepoint-north coincidence. -/
def suspensionCircleBasepoint_eq_north_path :
    Path (suspensionCircleBasepoint : SuspensionCircleCompPath) suspensionCircleNorth :=
  Path.refl _

/-! ## Subsingleton and π₁ triviality -/

/-- Σ(S¹) is a subsingleton (all points are equal). -/
instance : Subsingleton SuspensionCircleCompPath where
  allEq x y := by
    show @Eq (SuspensionCompPath CircleCompPath) x y
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

/-- Any two points of Σ(S¹) are connected by a path. -/
def suspensionCircle_path (x y : SuspensionCircleCompPath) : Path x y :=
  Path.stepChain (subsingleton_eq_by_cases x y)

/-- The fundamental group of Σ(S¹) is trivial. -/
theorem suspensionCircleCompPath_pi1_trivial :
    ∀ (α :
      π₁(SuspensionCircleCompPath, (suspensionCircleBasepoint : SuspensionCircleCompPath))),
      α = Quot.mk _ (Path.refl _) := by
  intro α
  simpa [SuspensionCircleCompPath, suspensionCircleBasepoint] using
    (Sphere2CompPath.sphere2CompPath_pi1_trivial (α := α))

/-- π₁(Σ(S¹)) ≃ 1 (the trivial group). -/
noncomputable def suspensionCircleCompPath_pi1_equiv_unit :
    SimpleEquiv
      (π₁(SuspensionCircleCompPath, (suspensionCircleBasepoint : SuspensionCircleCompPath)))
      Unit :=
  by
    simpa [SuspensionCircleCompPath, suspensionCircleBasepoint] using
      Sphere2CompPath.sphere2CompPath_pi1_equiv_unit

/-! ## Meridian path algebra -/

/-- Meridian loop at north: merid(x) ⬝ merid(y)⁻¹. -/
def suspensionCircleMeridLoop (x y : CircleCompPath) :
    Path (suspensionCircleNorth : SuspensionCircleCompPath) suspensionCircleNorth :=
  Path.trans (suspensionCircleMerid x) (Path.symm (suspensionCircleMerid y))

/-- The base meridian from the circle's basepoint. -/
def suspensionCircleMeridBase :
    Path (suspensionCircleNorth : SuspensionCircleCompPath) suspensionCircleSouth :=
  suspensionCircleMerid circleCompPathBase

/-- Inverse meridian: south to north. -/
def suspensionCircleMeridInv (x : CircleCompPath) :
    Path (suspensionCircleSouth : SuspensionCircleCompPath) suspensionCircleNorth :=
  Path.symm (suspensionCircleMerid x)

/-- Round-trip cancellation: merid(x) ⬝ merid(x)⁻¹ has trivial toEq. -/
theorem suspensionCircleMerid_cancel_toEq (x : CircleCompPath) :
    (suspensionCircleMeridLoop x x).toEq =
    (rfl : (suspensionCircleNorth : SuspensionCircleCompPath) = suspensionCircleNorth) := by
  simp

/-- All meridian loops have the same toEq (by proof irrelevance). -/
theorem suspensionCircleMeridLoop_toEq_eq (x y x' y' : CircleCompPath) :
    (suspensionCircleMeridLoop x y).toEq =
    (suspensionCircleMeridLoop x' y').toEq := by
  simp

/-- The self-loop has the same proof as refl. -/
theorem suspensionCircleMeridLoop_self_proof (x : CircleCompPath) :
    (suspensionCircleMeridLoop x x).proof =
    (Path.refl (suspensionCircleNorth : SuspensionCircleCompPath)).proof := by
  simp

/-- Composition of two meridian paths through south. -/
def suspensionCircleMeridCompose (x y z : CircleCompPath) :
    Path (suspensionCircleNorth : SuspensionCircleCompPath) suspensionCircleNorth :=
  Path.trans (suspensionCircleMeridLoop x y) (suspensionCircleMeridLoop y z)

/-- All loops at the north pole have the same proof. -/
theorem suspensionCircle_loop_proof_eq
    (p q : Path (suspensionCircleNorth : SuspensionCircleCompPath) suspensionCircleNorth) :
    p.proof = q.proof := by
  cases p with | mk _ hp => cases q with | mk _ hq => cases hp; cases hq; rfl

/-! ## Transport on Σ(S¹) -/

/-- Transport along a suspension circle path in a constant family. -/
theorem suspensionCircle_transport_const (D : Type u)
    (x y : SuspensionCircleCompPath) (p : Path x y) (d : D) :
    Path.transport (D := fun _ : SuspensionCircleCompPath => D) p d = d := by
  simp [Path.transport_const]

/-- Transport of refl is the identity. -/
theorem suspensionCircle_transport_refl
    {D : SuspensionCircleCompPath → Sort u}
    (x : SuspensionCircleCompPath) (d : D x) :
    Path.transport (D := D) (Path.refl x) d = d := rfl

/-! ## Double suspension of the circle -/

/-- Double suspension of S¹: ΣΣ(S¹). -/
def DoubleSuspensionCircle : Type u :=
  SuspensionCompPath SuspensionCircleCompPath

/-- Basepoint of ΣΣ(S¹). -/
def doubleSuspensionCircleBasepoint : DoubleSuspensionCircle :=
  SuspensionCompPath.north (X := SuspensionCircleCompPath)

/-- South pole of ΣΣ(S¹). -/
def doubleSuspensionCircleSouth : DoubleSuspensionCircle :=
  SuspensionCompPath.south (X := SuspensionCircleCompPath)

/-- Meridian of ΣΣ(S¹) for a point in Σ(S¹). -/
def doubleSuspensionCircleMerid (x : SuspensionCircleCompPath) :
    Path (doubleSuspensionCircleBasepoint : DoubleSuspensionCircle)
      doubleSuspensionCircleSouth :=
  SuspensionCompPath.merid (X := SuspensionCircleCompPath) x

/-- ΣΣ(S¹) is a subsingleton. -/
instance : Subsingleton DoubleSuspensionCircle where
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
                (A := PUnit') (B := PUnit') (C := SuspensionCircleCompPath)
                (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit)
                suspensionCircleBasepoint)
        | exact
            (Quot.sound
              (PushoutCompPathRel.glue
                (A := PUnit') (B := PUnit') (C := SuspensionCircleCompPath)
                (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit)
                suspensionCircleBasepoint)).symm

/-- Any two points of ΣΣ(S¹) are connected by a path. -/
def doubleSuspensionCircle_path (x y : DoubleSuspensionCircle) : Path x y :=
  Path.stepChain (subsingleton_eq_by_cases x y)

/-- π₁(ΣΣ(S¹)) is trivial. -/
theorem doubleSuspensionCircle_pi1_trivial :
    ∀ (α : π₁(DoubleSuspensionCircle,
      (doubleSuspensionCircleBasepoint : DoubleSuspensionCircle))),
      α = Quot.mk _ (Path.refl _) := by
  exact pi1_trivial_of_subsingleton
    (A := DoubleSuspensionCircle) (a := doubleSuspensionCircleBasepoint)

/-- π₁(ΣΣ(S¹)) ≃ Unit. -/
noncomputable def doubleSuspensionCircle_pi1_equiv_unit :
    SimpleEquiv
      (π₁(DoubleSuspensionCircle, (doubleSuspensionCircleBasepoint : DoubleSuspensionCircle)))
      Unit where
  toFun := fun _ => ()
  invFun := fun _ => Quot.mk _ (Path.refl _)
  left_inv := by
    intro α
    exact (doubleSuspensionCircle_pi1_trivial α).symm
  right_inv := by
    intro u; cases u; rfl

/-! ## Iterated suspension of the circle -/

/-- Iterated suspension of S¹: Σⁿ(S¹). -/
def iterSuspCircle : Nat → Type u
  | 0 => CircleCompPath
  | Nat.succ n => SuspensionCompPath (iterSuspCircle n)

/-- Σ⁰(S¹) = S¹. -/
theorem iterSuspCircle_zero : iterSuspCircle 0 = (CircleCompPath : Type u) := rfl

/-- Σ¹(S¹) = Σ(S¹). -/
theorem iterSuspCircle_one :
    iterSuspCircle 1 = (SuspensionCircleCompPath : Type u) := rfl

/-- Σ²(S¹) = ΣΣ(S¹). -/
theorem iterSuspCircle_two :
    iterSuspCircle 2 = (DoubleSuspensionCircle : Type u) := rfl

/-! ## Connectivity -/

/-- The suspension circle is path-connected. -/
instance : IsPathConnected SuspensionCircleCompPath where
  base := suspensionCircleBasepoint
  connected := fun x => suspensionCircle_path suspensionCircleBasepoint x

/-- The double suspension circle is path-connected. -/
instance : IsPathConnected DoubleSuspensionCircle where
  base := doubleSuspensionCircleBasepoint
  connected := fun x => doubleSuspensionCircle_path doubleSuspensionCircleBasepoint x

/-- Nonempty instance for Σ(S¹). -/
instance : Nonempty SuspensionCircleCompPath := ⟨suspensionCircleBasepoint⟩

/-- Nonempty instance for ΣΣ(S¹). -/
instance : Nonempty DoubleSuspensionCircle := ⟨doubleSuspensionCircleBasepoint⟩

/-- Inhabited instance for Σ(S¹). -/
instance : Inhabited SuspensionCircleCompPath := ⟨suspensionCircleBasepoint⟩

/-- Inhabited instance for ΣΣ(S¹). -/
instance : Inhabited DoubleSuspensionCircle := ⟨doubleSuspensionCircleBasepoint⟩

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths
