/-
# Surface groups and curve-complex interfaces

This module introduces surface-classification data together with lightweight
interfaces for surface groups, mapping class groups, Dehn twists, and curve
complexes. The definitions are intentionally small and axioms-free, providing
structural hooks for later computational-path constructions.

## Key Results

- `SurfaceClass`: classification data for compact surfaces with boundary.
- `SurfaceData`: a surface packaged with a basepoint and classification tag.
- `surfaceGroup`: the fundamental group of a surface.
- `mappingClassGroup`: strict group structure on self-equivalences.
- `DehnTwistData`: Dehn twist interfaces and integer powers.
- `CurveComplex`: curve-complex interface for surface combinatorics.

## References

- Hatcher, "Algebraic Topology", Sections 1.3 and 2.1
- Farb–Margalit, "A Primer on Mapping Class Groups"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.CompPath.SphereCompPath
import ComputationalPaths.Path.CompPath.Torus
import ComputationalPaths.Path.CompPath.KleinBottle
import ComputationalPaths.Path.CompPath.MobiusBand

namespace ComputationalPaths
namespace Path
namespace CompPath

universe u

/-! ## Surface classification data -/

/-- Classification data for compact surfaces with boundary. -/
inductive SurfaceClass : Type
  | orientable (genus : Nat) (boundary : Nat)
  | nonorientable (crosscaps : Nat) (boundary : Nat)

/-- Boundary component count of a surface class. -/
def SurfaceClass.boundary : SurfaceClass → Nat
  | orientable _ b => b
  | nonorientable _ b => b

/-- Flag for whether a surface class is orientable. -/
def SurfaceClass.isOrientable : SurfaceClass → Bool
  | orientable _ _ => true
  | nonorientable _ _ => false

/-- Euler characteristic from surface-classification data. -/
def surfaceEulerChar : SurfaceClass → Int
  | SurfaceClass.orientable genus boundary =>
      2 - (2 * Int.ofNat genus) - Int.ofNat boundary
  | SurfaceClass.nonorientable crosscaps boundary =>
      2 - Int.ofNat crosscaps - Int.ofNat boundary

/-! ## Surface data and surface groups -/

/-- A surface packaged with a basepoint and classification tag. -/
structure SurfaceData where
  /-- Underlying carrier type. -/
  carrier : Type u
  /-- Chosen basepoint. -/
  basepoint : carrier
  /-- Classification tag. -/
  class : SurfaceClass

/-- Fundamental group of a surface. -/
abbrev surfaceGroup (S : SurfaceData) : Type u :=
  π₁(S.carrier, S.basepoint)

/-- Strict group structure on the surface fundamental group. -/
abbrev surfaceGroupStruct (S : SurfaceData) : PiOneGroup S.carrier S.basepoint :=
  PiOneGroup S.carrier S.basepoint

/-- Raw loop space at the surface basepoint. -/
abbrev surfaceLoop (S : SurfaceData) : Type u :=
  LoopSpace S.carrier S.basepoint

/-- Based curve represented by a loop class on a surface. -/
structure SurfaceCurve (S : SurfaceData) where
  /-- Loop class in the surface fundamental group. -/
  loopClass : surfaceGroup S

/-! ## Mapping class groups -/

/-- Carrier of the mapping class group (self-equivalences of the surface). -/
abbrev MappingClass (S : SurfaceData) : Type u :=
  SimpleEquiv S.carrier S.carrier

/-- Identity mapping class. -/
@[simp] def mappingClassId (S : SurfaceData) : MappingClass S :=
  SimpleEquiv.refl S.carrier

/-- Composition of mapping classes. -/
@[simp] def mappingClassComp {S : SurfaceData}
    (f g : MappingClass S) : MappingClass S :=
  SimpleEquiv.comp f g

/-- Inverse of a mapping class. -/
@[simp] def mappingClassInv {S : SurfaceData}
    (f : MappingClass S) : MappingClass S :=
  SimpleEquiv.symm f

/-- Strict group structure on mapping classes via composition. -/
def mappingClassGroup (S : SurfaceData) :
    Algebra.StrictGroup (MappingClass S) where
  mul := mappingClassComp
  one := mappingClassId S
  inv := mappingClassInv
  mul_assoc := by
    intro x y z
    simpa [mappingClassComp] using SimpleEquiv.comp_assoc x y z
  one_mul := by
    intro x
    simpa [mappingClassComp, mappingClassId] using SimpleEquiv.refl_comp x
  mul_one := by
    intro x
    simpa [mappingClassComp, mappingClassId] using SimpleEquiv.comp_refl x
  mul_left_inv := by
    intro x
    simpa [mappingClassComp, mappingClassId, mappingClassInv]
      using SimpleEquiv.symm_comp x
  mul_right_inv := by
    intro x
    simpa [mappingClassComp, mappingClassId, mappingClassInv]
      using SimpleEquiv.comp_symm x

/-! ## Dehn twists -/

/-- Data selecting a Dehn twist for each curve. -/
structure DehnTwistData (S : SurfaceData) where
  /-- Mapping class assigned to a curve. -/
  twist : SurfaceCurve S → MappingClass S

/-- Integer power of a Dehn twist using the mapping class group structure. -/
def dehnTwistPow (S : SurfaceData) (D : DehnTwistData S)
    (c : SurfaceCurve S) (n : Int) : MappingClass S :=
  Algebra.StrictGroup.zpow (mappingClassGroup S) (D.twist c) n

/-! ## Curve complex interface -/

/-- Interface for the curve complex of a surface. -/
structure CurveComplex (S : SurfaceData) where
  /-- Vertex type (isotopy classes of curves). -/
  vertex : Type u
  /-- Disjointness relation on vertices. -/
  disjoint : vertex → vertex → Prop
  /-- Symmetry of disjointness. -/
  disjoint_symm : ∀ v w, disjoint v w → disjoint w v

/-! ## Example surfaces -/

/-- The 2-sphere as a surface datum. -/
def sphereSurface : SurfaceData where
  carrier := Sphere2CompPath
  basepoint := Sphere2CompPath.basepoint
  class := SurfaceClass.orientable 0 0

/-- The torus as a surface datum. -/
def torusSurface : SurfaceData where
  carrier := _root_.ComputationalPaths.Path.Torus
  basepoint := _root_.ComputationalPaths.Path.torusBase
  class := SurfaceClass.orientable 1 0

/-- The Klein bottle as a surface datum. -/
def kleinBottleSurface : SurfaceData where
  carrier := KleinBottleCompPath
  basepoint := kleinBottleBase
  class := SurfaceClass.nonorientable 2 0

/-- The Mobius band as a surface datum. -/
def mobiusBandSurface : SurfaceData where
  carrier := MobiusBandCompPath
  basepoint := mobiusBandBase
  class := SurfaceClass.nonorientable 1 1

/-! ## Summary -/

end CompPath
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace CompPath

theorem surfaceGroups_boundary_orientable (genus boundary : Nat) :
    SurfaceClass.boundary (SurfaceClass.orientable genus boundary) = boundary := by
  sorry

theorem surfaceGroups_boundary_nonorientable (crosscaps boundary : Nat) :
    SurfaceClass.boundary (SurfaceClass.nonorientable crosscaps boundary) = boundary := by
  sorry

theorem surfaceGroups_isOrientable_orientable (genus boundary : Nat) :
    SurfaceClass.isOrientable (SurfaceClass.orientable genus boundary) = true := by
  sorry

theorem surfaceGroups_isOrientable_nonorientable (crosscaps boundary : Nat) :
    SurfaceClass.isOrientable (SurfaceClass.nonorientable crosscaps boundary) = false := by
  sorry

theorem surfaceGroups_mappingClassComp_id_left (S : SurfaceData) (f : MappingClass S) :
    mappingClassComp (mappingClassId S) f = f := by
  sorry

theorem surfaceGroups_mappingClassComp_id_right (S : SurfaceData) (f : MappingClass S) :
    mappingClassComp f (mappingClassId S) = f := by
  sorry

theorem surfaceGroups_mappingClassInv_involutive (S : SurfaceData) (f : MappingClass S) :
    mappingClassInv (mappingClassInv f) = f := by
  sorry

theorem surfaceGroups_dehnTwistPow_zero (S : SurfaceData) (D : DehnTwistData S)
    (c : SurfaceCurve S) :
    dehnTwistPow S D c 0 = mappingClassId S := by
  sorry

end CompPath
end Path
end ComputationalPaths
