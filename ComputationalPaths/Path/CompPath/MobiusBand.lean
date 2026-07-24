/-
# Möbius-band compatibility presentation over circle syntax

Classically, the Möbius band deformation retracts onto its core circle.  This
file keeps a compatibility alias of the current one-constructor circle and
reuses its **synthetic winding-expression quotient**.  It does not construct a
deformation retract or compute the genuine `PathRwQuot` of the aliased carrier.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `MobiusBandCompPath` | compatibility alias of one-constructor `CircleCompPath` |
| `mobiusBandPiOneEquivInt` | synthetic winding model ≅ ℤ |
| `mobiusBandNonorientable` | equality for a declared presentation flag |
| `MobiusBandBoundary` | compatibility alias used as boundary presentation data |
| `mobiusBandDeformRetract` | identity retraction record between identical aliases |
| `mobiusBandEulerChar` | declared Euler-characteristic label |

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

/-! ## Compatibility carrier alias -/

/-- Compatibility/presentation alias of the current one-constructor circle.
No Möbius-band carrier or topological deformation retract is constructed. -/
abbrev MobiusBandCompPath : Type u := CircleCompPath.{u}

@[simp] abbrev mobiusBandBase : MobiusBandCompPath := circleCompPathBase

/-! ## Synthetic winding model -/

/-- Legacy alias for the synthetic circle winding quotient. -/
abbrev mobiusBandPiOne : Type u := circleCompPathPiOne

/-- Synthetic winding-model equivalence with `Int`; not an equivalence from
the genuine loop quotient of `MobiusBandCompPath`. -/
noncomputable def mobiusBandPiOneEquivInt :
    SimpleEquiv mobiusBandPiOne Int :=
  circleCompPathPiOneEquivInt

/-! ## Compatibility aliases -/

abbrev MobiusBand : Type u := MobiusBandCompPath.{u}

@[simp] abbrev mobiusBandBasepoint : MobiusBand := mobiusBandBase

/-! ## Identity retraction record between aliases -/

/-- Minimal retraction data.  This structure contains no homotopy field and
does not by itself express a topological deformation retract. -/
structure DeformRetractData (Total : Type u) (Core : Type u) where
  /-- The inclusion of the core into the total space. -/
  inclusion : Core → Total
  /-- The retraction from the total space to the core. -/
  retraction : Total → Core
  /-- The retraction is a left inverse of the inclusion. -/
  retract_incl : ∀ c : Core, retraction (inclusion c) = c

/-- Identity retraction data between the definitionally identical compatibility
aliases `MobiusBand` and `CircleCompPath`; not an implemented deformation
retract of a genuine Möbius-band carrier. -/
noncomputable def mobiusBandDeformRetract :
    DeformRetractData MobiusBand.{u} CircleCompPath.{u} where
  inclusion := id
  retraction := id
  retract_incl := fun _ => rfl

/-- The identity compatibility retraction preserves the chosen point. -/
theorem mobiusBandRetract_base :
    mobiusBandDeformRetract.retraction (mobiusBandBase : MobiusBand.{u}) = circleCompPathBase := rfl

/-- The identity compatibility inclusion preserves the chosen point. -/
theorem mobiusBandIncl_base :
    mobiusBandDeformRetract.inclusion (circleCompPathBase : CircleCompPath.{u}) = mobiusBandBase := rfl

/-! ## Declared presentation metadata -/

/-- Orientability flag for a surface. -/
inductive Orientability where
  | orientable : Orientability
  | nonorientable : Orientability
  deriving DecidableEq

/-- Declared orientability label for the presentation. -/
def mobiusBandOrientability : Orientability := Orientability.nonorientable

/-- Reflexive verification of the declared nonorientability label. -/
theorem mobiusBandNonorientable :
    mobiusBandOrientability = Orientability.nonorientable := rfl

/-- An orientation reversal record along a loop. -/
structure OrientationReversal (S : Type u) (base : S) where
  /-- The loop along which orientation reverses. -/
  loop : Path (A := S) base base
  /-- The orientation reversal flag. -/
  reverses : Bool := true

/-- Presentation record assigning the `true` reversal flag to a singleton
reflexivity step.  This is data, not a derived orientation theorem. -/
noncomputable def mobiusBandOrientationReversal :
    OrientationReversal MobiusBand.{u} mobiusBandBase where
  loop := Path.stepChain rfl
  reverses := true

/-! ## Boundary presentation data -/

/-- Compatibility alias used to represent a boundary circle; no boundary
subspace or covering map is constructed. -/
abbrev MobiusBandBoundary : Type u := CircleCompPath.{u}

/-- Declared degree label for the intended boundary presentation. -/
def mobiusBandBoundaryCoveringDegree : Nat := 2

/-- Identity map between the boundary and carrier compatibility aliases. -/
noncomputable def mobiusBandBoundaryInclusion :
    MobiusBandBoundary.{u} → MobiusBand.{u} := id

theorem mobiusBandBoundaryInclusion_base :
    mobiusBandBoundaryInclusion circleCompPathBase = (mobiusBandBase : MobiusBand.{u}) := rfl

/-! ## Declared Euler-characteristic data -/

/-- Declared Euler-characteristic label for the presentation. -/
def mobiusBandEulerChar : Int := 0

/-- Declared CW-count record matching the intended presentation:
    1 vertex, 2 edges, 1 face. -/
structure MobiusBandCWData where
  vertices : Nat := 1
  edges : Nat := 2
  faces : Nat := 1

def mobiusBandStdCW : MobiusBandCWData := {}

theorem mobiusBandEuler_from_CW :
    (mobiusBandStdCW.vertices : Int) - mobiusBandStdCW.edges + mobiusBandStdCW.faces
    = mobiusBandEulerChar := by decide

/-! ## Loop Space and Path Algebra -/

/-- Raw loop space of the one-constructor compatibility carrier. -/
abbrev mobiusBandLoopSpace : Type u := Path (A := MobiusBand.{u}) mobiusBandBase mobiusBandBase

/-- Singleton-reflexivity raw path used as a legacy core-loop representative;
its genuine `PathRwQuot` class is trivial. -/
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

/-- Declared presentation metadata under the Möbius-band name. -/
noncomputable def mobiusBandSurfaceData : NonorientableSurfaceData where
  name := "Möbius band"
  orientability := Orientability.nonorientable
  euler := 0

/-- Data record for the Klein bottle. -/
noncomputable def kleinBottleSurfaceData : NonorientableSurfaceData where
  name := "Klein bottle"
  orientability := Orientability.nonorientable
  euler := 0

/-- The two declared metadata records carry the same Euler label. -/
theorem mobius_klein_euler_eq :
    mobiusBandSurfaceData.euler = kleinBottleSurfaceData.euler := rfl

/-- The two declared metadata records carry the same orientability label. -/
theorem mobius_klein_nonorientable :
    mobiusBandSurfaceData.orientability = kleinBottleSurfaceData.orientability := rfl

/-! ## Synthetic winding-equivalence round-trips -/

/-- Encode-decode for the synthetic winding quotient compatibility alias. -/
theorem mobiusBand_encode_decode (z : Int) :
    mobiusBandPiOneEquivInt.toFun (mobiusBandPiOneEquivInt.invFun z) = z :=
  mobiusBandPiOneEquivInt.right_inv z

/-- Decode-encode for the synthetic winding quotient compatibility alias. -/
theorem mobiusBand_decode_encode (x : mobiusBandPiOne.{u}) :
    mobiusBandPiOneEquivInt.invFun (mobiusBandPiOneEquivInt.toFun x) = x :=
  mobiusBandPiOneEquivInt.left_inv x

end CompPath
end Path
end ComputationalPaths
