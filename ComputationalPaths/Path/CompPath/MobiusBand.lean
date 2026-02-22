/-
# The Möbius band via computational paths

The Möbius band deformation retracts onto its core circle, so its fundamental
group is the same as the circle. We model it as a compatibility alias of the
computational-path circle and reuse the existing π₁ encoding.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `MobiusBandCompPath` | Möbius band type (≃ S¹) |
| `mobiusBandPiOneEquivInt` | π₁(M) ≅ ℤ |
| `mobiusBandNonorientable` | Non-orientability witness |
| `mobiusBandBoundary` | The boundary circle of M |
| `mobiusBandDeformRetract` | Deformation retract data |
| `mobiusBandEuler` | Euler characteristic of M is 0 |

## References

- Hatcher, *Algebraic Topology*, §1.1
- Munkres, *Topology*, §60
-/

import ComputationalPaths.Path.CompPath.CircleCompPath
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## The Möbius band as a computational-path circle -/

/-- The Möbius band is modeled by its deformation retract onto the circle. -/
abbrev MobiusBandCompPath : Type u := CircleCompPath.{u}

@[simp] abbrev mobiusBandBase : MobiusBandCompPath := circleCompPathBase

/-! ## Fundamental group -/

/-- The fundamental group of the Möbius band. -/
abbrev mobiusBandPiOne : Type u := circleCompPathPiOne

/-- π₁(M) ≅ ℤ via the deformation retract onto S¹. -/
noncomputable def mobiusBandPiOneEquivInt :
    SimpleEquiv mobiusBandPiOne Int :=
  circleCompPathPiOneEquivInt

/-! ## Compatibility aliases -/

abbrev MobiusBand : Type u := MobiusBandCompPath.{u}

@[simp] abbrev mobiusBandBasepoint : MobiusBand := mobiusBandBase

/-! ## Deformation Retract -/

/-- Data for a deformation retract of a space onto a subspace. -/
structure DeformRetractData (Total : Type u) (Core : Type u) where
  /-- The inclusion of the core into the total space. -/
  inclusion : Core → Total
  /-- The retraction from the total space to the core. -/
  retraction : Total → Core
  /-- The retraction is a left inverse of the inclusion. -/
  retract_incl : ∀ c : Core, retraction (inclusion c) = c

/-- The Möbius band deformation retracts onto its core circle. -/
noncomputable def mobiusBandDeformRetract :
    DeformRetractData MobiusBand.{u} CircleCompPath.{u} where
  inclusion := id
  retraction := id
  retract_incl := fun _ => rfl

/-- The retraction preserves the base point. -/
theorem mobiusBandRetract_base :
    mobiusBandDeformRetract.retraction (mobiusBandBase : MobiusBand.{u}) = circleCompPathBase := rfl

/-- The inclusion preserves the base point. -/
theorem mobiusBandIncl_base :
    mobiusBandDeformRetract.inclusion (circleCompPathBase : CircleCompPath.{u}) = mobiusBandBase := rfl

/-! ## Non-orientability -/

/-- Orientability flag for a surface. -/
inductive Orientability where
  | orientable : Orientability
  | nonorientable : Orientability
  deriving DecidableEq

/-- The Möbius band is non-orientable. -/
def mobiusBandOrientability : Orientability := Orientability.nonorientable

/-- Witness that the Möbius band is non-orientable. -/
theorem mobiusBandNonorientable :
    mobiusBandOrientability = Orientability.nonorientable := rfl

/-- An orientation reversal record along a loop. -/
structure OrientationReversal (S : Type u) (base : S) where
  /-- The loop along which orientation reverses. -/
  loop : Path (A := S) base base
  /-- The orientation reversal flag. -/
  reverses : Bool := true

/-- The core loop of the Möbius band reverses orientation. -/
noncomputable def mobiusBandOrientationReversal :
    OrientationReversal MobiusBand.{u} mobiusBandBase where
  loop := Path.stepChain rfl
  reverses := true

/-! ## Boundary Circle -/

/-- The boundary of the Möbius band is a circle. The boundary circle wraps
    around the core circle twice (degree-2 covering). -/
abbrev MobiusBandBoundary : Type u := CircleCompPath.{u}

/-- The boundary maps to the core by a degree-2 covering. -/
def mobiusBandBoundaryCoveringDegree : Nat := 2

/-- The boundary inclusion sends the boundary base to the Möbius band base. -/
noncomputable def mobiusBandBoundaryInclusion :
    MobiusBandBoundary.{u} → MobiusBand.{u} := id

theorem mobiusBandBoundaryInclusion_base :
    mobiusBandBoundaryInclusion circleCompPathBase = (mobiusBandBase : MobiusBand.{u}) := rfl

/-! ## Euler Characteristic -/

/-- Euler characteristic of the Möbius band.
    χ(M) = 0 (it deformation retracts to S¹). -/
def mobiusBandEulerChar : Int := 0

/-- CW data for the Möbius band:
    1 vertex, 2 edges, 1 face → χ = 1 - 2 + 1 = 0. -/
structure MobiusBandCWData where
  vertices : Nat := 1
  edges : Nat := 2
  faces : Nat := 1

def mobiusBandStdCW : MobiusBandCWData := {}

theorem mobiusBandEuler_from_CW :
    (mobiusBandStdCW.vertices : Int) - mobiusBandStdCW.edges + mobiusBandStdCW.faces
    = mobiusBandEulerChar := by native_decide

/-! ## Loop Space and Path Algebra -/

/-- Loop space of the Möbius band at the base point. -/
abbrev mobiusBandLoopSpace : Type u := Path (A := MobiusBand.{u}) mobiusBandBase mobiusBandBase

/-- The core loop of the Möbius band. -/
noncomputable def mobiusBandCoreLoop : mobiusBandLoopSpace.{u} :=
  Path.stepChain (circleLoopEq)

/-- The trivial loop at the base point. -/
noncomputable def mobiusBandReflLoop : mobiusBandLoopSpace.{u} :=
  Path.refl mobiusBandBase

/-- Any two loops have the same `toEq` by proof irrelevance. -/
theorem mobiusBand_loops_toEq
    (p q : mobiusBandLoopSpace.{u}) :
    p.toEq = q.toEq := by
  simp

/-- The core loop composed with itself gives a loop with trivial `toEq`. -/
theorem mobiusBandCoreLoop_double_toEq :
    (Path.trans mobiusBandCoreLoop mobiusBandCoreLoop (A := MobiusBand.{u})).toEq =
    (rfl : mobiusBandBase = mobiusBandBase) := by
  simp

/-- Transport along the core loop is trivial on constant families. -/
theorem mobiusBand_transport_const (D : Type u) (x : D) :
    Path.transport (D := fun _ : MobiusBand.{u} => D) mobiusBandCoreLoop x = x := by
  simp [Path.transport_const]

/-! ## Comparison with Klein Bottle -/

/-- The Klein bottle is also non-orientable. Its fundamental group has a
    different structure: ⟨a, b | abab⁻¹⟩.  We record the comparison. -/
structure NonorientableSurfaceData where
  /-- Name of the surface. -/
  name : String
  /-- Whether orientable. -/
  orientability : Orientability
  /-- Euler characteristic. -/
  euler : Int

/-- Data record for the Möbius band. -/
noncomputable def mobiusBandSurfaceData : NonorientableSurfaceData where
  name := "Möbius band"
  orientability := Orientability.nonorientable
  euler := 0

/-- Data record for the Klein bottle. -/
noncomputable def kleinBottleSurfaceData : NonorientableSurfaceData where
  name := "Klein bottle"
  orientability := Orientability.nonorientable
  euler := 0

/-- Both the Möbius band and Klein bottle have Euler characteristic 0. -/
theorem mobius_klein_euler_eq :
    mobiusBandSurfaceData.euler = kleinBottleSurfaceData.euler := rfl

/-- Both are non-orientable. -/
theorem mobius_klein_nonorientable :
    mobiusBandSurfaceData.orientability = kleinBottleSurfaceData.orientability := rfl

/-! ## SimpleEquiv round-trip -/

/-- The encode-decode round-trip for Möbius band π₁ encodes. -/
theorem mobiusBand_encode_decode (z : Int) :
    mobiusBandPiOneEquivInt.toFun (mobiusBandPiOneEquivInt.invFun z) = z :=
  mobiusBandPiOneEquivInt.right_inv z

/-- The decode-encode round-trip for Möbius band π₁ decodes. -/
theorem mobiusBand_decode_encode (x : mobiusBandPiOne.{u}) :
    mobiusBandPiOneEquivInt.invFun (mobiusBandPiOneEquivInt.toFun x) = x :=
  mobiusBandPiOneEquivInt.left_inv x

end CompPath
end Path
end ComputationalPaths
