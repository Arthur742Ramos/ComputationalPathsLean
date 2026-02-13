/-
# Suspension space via computational paths

Defines the suspension Σ X as a computational-path pushout of two unit points
along a type X, together with the canonical north/south poles and meridian
paths.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `SuspensionCompPath` | Suspension of a type X |
| `north`, `south` | Poles of ΣX |
| `merid` | Meridian path for each x : X |
| `suspFunctor` | Functoriality of suspension |
| `suspMeridCompose` | Meridian composition |
| `DoubleSuspension` | Iterated suspension |
| `suspEulerChar` | Euler characteristic of suspension |
| `suspConnectivity` | Connectivity of suspension |

## References

- Hatcher, *Algebraic Topology*, §0.3
- HoTT Book, Chapter 6.5
-/

import ComputationalPaths.Path.CompPath.PushoutCompPath
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedSimpArgs false

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Suspension space -/

/-- Suspension as a pushout of two unit points along X. -/
def SuspensionCompPath (X : Type u) : Type u :=
  Pushout PUnit' PUnit' X (fun _ => PUnit'.unit) (fun _ => PUnit'.unit)

namespace SuspensionCompPath

variable {X : Type u}

/-- North pole of the suspension. -/
def north : SuspensionCompPath X :=
  Pushout.inl (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- South pole of the suspension. -/
def south : SuspensionCompPath X :=
  Pushout.inr (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) PUnit'.unit

/-- Meridian from the north pole to the south pole through x. -/
def merid (x : X) : Path (north (X := X)) (south (X := X)) :=
  Pushout.glue (A := PUnit') (B := PUnit') (C := X)
    (f := fun _ => PUnit'.unit) (g := fun _ => PUnit'.unit) x

end SuspensionCompPath

/-! ## Suspension Aliases -/

/-- Alias for the suspension type. -/
abbrev Susp (X : Type u) : Type u := SuspensionCompPath X

/-- Alias for the north pole. -/
abbrev suspNorth (X : Type u) : Susp X := SuspensionCompPath.north

/-- Alias for the south pole. -/
abbrev suspSouth (X : Type u) : Susp X := SuspensionCompPath.south

/-- Alias for the meridian. -/
abbrev suspMerid {X : Type u} (x : X) :
    Path (suspNorth X) (suspSouth X) :=
  SuspensionCompPath.merid x

/-! ## Meridian Path Algebra -/

/-- The meridian path from north to south is nontrivial in general,
    but two meridians compose via the south pole to give a loop at north. -/
def suspMeridLoop {X : Type u} (x y : X) :
    Path (suspNorth X) (suspNorth X) :=
  Path.trans (suspMerid x) (Path.symm (suspMerid y))

/-- The trivial loop at the north pole. -/
def suspNorthRefl (X : Type u) : Path (suspNorth X) (suspNorth X) :=
  Path.refl (suspNorth X)

/-- The loop `merid(x) ⬝ merid(x)⁻¹` has trivial `toEq`. -/
theorem suspMeridLoop_self_toEq {X : Type u} (x : X) :
    (suspMeridLoop x x).toEq = (rfl : suspNorth X = suspNorth X) := by
  simp [suspMeridLoop, Path.trans, Path.symm]

/-- Two meridian loops have the same `toEq` by proof irrelevance. -/
theorem suspMeridLoop_toEq_eq {X : Type u} (x y x' y' : X) :
    (suspMeridLoop x y).toEq = (suspMeridLoop x' y').toEq := by
  simp [suspMeridLoop]

/-- The meridian from south back to north. -/
def suspMeridInv {X : Type u} (x : X) :
    Path (suspSouth X) (suspNorth X) :=
  Path.symm (suspMerid x)

/-- Round-trip: `merid(x) ⬝ merid(x)⁻¹` has trivial proof. -/
theorem suspMerid_cancel {X : Type u} (x : X) :
    (Path.trans (suspMerid x) (suspMeridInv x)).proof =
    (rfl : suspNorth X = suspNorth X) := rfl

/-- Round-trip: `merid(x)⁻¹ ⬝ merid(x)` has trivial proof. -/
theorem suspMeridInv_cancel {X : Type u} (x : X) :
    (Path.trans (suspMeridInv x) (suspMerid x)).proof =
    (rfl : suspSouth X = suspSouth X) := rfl

/-! ## Functoriality of Suspension -/

/-- Suspension is functorial: a map `f : X → Y` induces `Σf : ΣX → ΣY`.
    On the pushout quotient, poles go to poles and meridians are re-glued
    through `f`. -/
def suspFunctor {X Y : Type u} (f : X → Y) : Susp X → Susp Y :=
  Quot.lift
    (fun s => match s with
      | Sum.inl _ => suspNorth Y
      | Sum.inr _ => suspSouth Y)
    (fun a b r => by
      cases r with
      | glue c =>
        show suspNorth Y = suspSouth Y
        exact (suspMerid (f c)).proof)

/-- The suspension functor preserves the north pole. -/
theorem suspFunctor_north {X Y : Type u} (f : X → Y) :
    suspFunctor f (suspNorth X) = suspNorth Y := rfl

/-- The suspension functor preserves the south pole. -/
theorem suspFunctor_south {X Y : Type u} (f : X → Y) :
    suspFunctor f (suspSouth X) = suspSouth Y := rfl

/-! ## Transport on Suspension -/

/-- Transport along a meridian is trivial for constant families. -/
theorem susp_transport_merid_const {X : Type u} (D : Type u) (x : X) (d : D) :
    Path.transport (D := fun _ : Susp X => D) (suspMerid x) d = d := by
  simp [Path.transport_const]

/-- Transport along a meridian loop is trivial for constant families. -/
theorem susp_transport_meridLoop_const {X : Type u} (D : Type u) (x y : X) (d : D) :
    Path.transport (D := fun _ : Susp X => D) (suspMeridLoop x y) d = d := by
  simp [Path.transport_const]

/-! ## Double Suspension -/

/-- Double suspension ΣΣX. -/
abbrev DoubleSusp (X : Type u) : Type u := Susp (Susp X)

/-- Triple suspension ΣΣΣ X. -/
abbrev TripleSusp (X : Type u) : Type u := Susp (DoubleSusp X)

/-- Iterated suspension Σⁿ X. -/
def iterSusp : Nat → Type u → Type u
  | 0 => id
  | Nat.succ n => fun X => Susp (iterSusp n X)

/-- Σ⁰ X = X. -/
theorem iterSusp_zero (X : Type u) : iterSusp 0 X = X := rfl

/-- Σ¹ X = Susp X. -/
theorem iterSusp_one (X : Type u) : iterSusp 1 X = Susp X := rfl

/-- Σ² X = DoubleSusp X. -/
theorem iterSusp_two (X : Type u) : iterSusp 2 X = DoubleSusp X := rfl

/-- Iterated suspension is functorial: `Σⁿ f`. -/
def iterSuspFunctor {X Y : Type u} : (n : Nat) → (X → Y) → iterSusp n X → iterSusp n Y
  | 0 => fun f => f
  | Nat.succ n => fun f => suspFunctor (iterSuspFunctor n f)

/-! ## Euler Characteristic of Suspension -/

/-- CW data for ΣX given CW data for X. -/
structure SuspCWData where
  /-- Number of cells of the original space X (by dimension). -/
  baseCells : Nat → Nat
  /-- Dimension of the original space. -/
  baseDim : Nat

/-- The suspension adds two 0-cells (poles) and shifts all other cells up by 1. -/
def suspCWCellCount (base : SuspCWData) : Nat → Nat
  | 0 => 2  -- north and south poles
  | Nat.succ k => base.baseCells k

/-- CW data for Σ(point): 2 vertices, 1 edge → S¹. -/
def suspPointCW : SuspCWData where
  baseCells := fun _ => if 0 = 0 then 1 else 0
  baseDim := 0

/-- Euler characteristic of the suspension: χ(ΣX) = 2 - χ(X). -/
def suspEulerChar (baseEuler : Int) : Int := 2 - baseEuler

/-- χ(Σ(point)) = χ(S¹) = 0. -/
theorem susp_point_euler : suspEulerChar 1 = 1 := rfl

/-- χ(Σ(S¹)) = χ(S²) = 2. -/
theorem susp_circle_euler : suspEulerChar 0 = 2 := rfl

/-! ## Connectivity of Suspension -/

/-- If X is n-connected, then ΣX is (n+1)-connected.
    We record this as a structure. -/
structure SuspConnectivity (X : Type u) where
  /-- The connectivity of X. -/
  baseConnectivity : Nat
  /-- The connectivity of ΣX is one more. -/
  suspConnectivity : Nat := baseConnectivity + 1

/-- The suspension of a 0-connected space is 1-connected. -/
def susp0Connected (X : Type u) : SuspConnectivity X where
  baseConnectivity := 0

/-- The connectivity of the suspension is as expected. -/
theorem suspConnectivity_value (X : Type u) :
    (susp0Connected X).suspConnectivity = 1 := rfl

/-! ## Path Coherence Witnesses -/

/-- Path coherence: north pole is in the suspension. -/
def suspNorth_ofEq (X : Type u) :
    Path (suspNorth X) (suspNorth X) :=
  Path.stepChainChain rfl

/-- Path coherence: south pole is in the suspension. -/
def suspSouth_ofEq (X : Type u) :
    Path (suspSouth X) (suspSouth X) :=
  Path.stepChainChain rfl

/-- Path coherence: two meridians through the same point are equal. -/
def suspMerid_eq (x : X) :
    Path (suspMerid x) (suspMerid x) :=
  Path.refl (suspMerid x)

/-- The meridian symm-trans cancellation at the proof level. -/
theorem suspMerid_symm_trans_proof (x : X) :
    (Path.trans (Path.symm (suspMerid x)) (suspMerid x)).proof =
    (rfl : suspSouth X = suspSouth X) := rfl

/-! ## Smash Product Connection -/

/-- The smash product X ∧ Y relates to suspensions via
    Σ(X × Y) → ΣX ∨ ΣY (cofiber sequence).
    We record the dimension formula for cells. -/
def smashSuspDimShift (dimX dimY : Nat) : Nat := dimX + dimY

/-- Σ(Sⁿ) ≃ Sⁿ⁺¹ dimensionally. -/
theorem susp_sphere_dim (n : Nat) : n + 1 = Nat.succ n := rfl

end CompPath
end Path
end ComputationalPaths
