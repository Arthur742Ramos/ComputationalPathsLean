/-
# Triangulated categories via computational paths

This module packages data-level structures for triangulated categories using
computational paths for the shift laws and diagram identifications.

## Key Results
- `ShiftData`, `TriangleData`, `OctahedralData`, `VerdierQuotientData`
- Trivial `PUnit` data for the above structures

## References
- Verdier, "Categories derivees"
- Neeman, "Triangulated Categories"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TriangulatedCategoryPaths

universe u v

/-! ## Shift data -/

/-- Shift/translation data with Path-valued inverse laws. -/
structure ShiftData (Obj : Type u) where
  /-- Shift endofunction. -/
  shift : Obj → Obj
  /-- Chosen inverse (negative shift). -/
  unshift : Obj → Obj
  /-- Path witnessing unshift ∘ shift = id. -/
  unshift_shift : ∀ X : Obj, Path (unshift (shift X)) X
  /-- Path witnessing shift ∘ unshift = id. -/
  shift_unshift : ∀ X : Obj, Path (shift (unshift X)) X

/-! ## Distinguished triangles -/

/-- Data of a distinguished triangle X -> Y -> Z -> T X. -/
structure TriangleData (Obj : Type u) (Hom : Obj → Obj → Type v)
    (S : ShiftData Obj) where
  /-- First object. -/
  X : Obj
  /-- Second object. -/
  Y : Obj
  /-- Third object. -/
  Z : Obj
  /-- First morphism. -/
  f : Hom X Y
  /-- Second morphism. -/
  g : Hom Y Z
  /-- Third morphism landing in the shift. -/
  h : Hom Z (S.shift X)

/-! ## Octahedral axiom data -/

/-- Data recording the octahedral axiom diagram (data-only). -/
structure OctahedralData (Obj : Type u) (Hom : Obj → Obj → Type v)
    (S : ShiftData Obj) where
  /-- Triangle for a first morphism. -/
  tri1 : TriangleData Obj Hom S
  /-- Triangle for a second morphism. -/
  tri2 : TriangleData Obj Hom S
  /-- Triangle for the composite (data-level). -/
  tri3 : TriangleData Obj Hom S
  /-- Comparison morphism between the middle objects. -/
  mapY : Hom tri1.Y tri2.Y
  /-- Comparison morphism between the third objects. -/
  mapZ : Hom tri1.Z tri2.Z
  /-- Comparison morphism into the composite triangle. -/
  mapZ' : Hom tri2.Z tri3.Z
  /-- Path identifying the shared vertex in the octahedron. -/
  overlap : Path tri3.X tri1.Z

/-! ## Verdier quotient data -/

/-- Data for a Verdier quotient/localization (data-only). -/
structure VerdierQuotientData (Obj : Type u) (Hom : Obj → Obj → Type v)
    (S : ShiftData Obj) where
  /-- Objects of the quotient. -/
  QObj : Type u
  /-- Morphisms in the quotient. -/
  QHom : QObj → QObj → Type v
  /-- Shift data on the quotient. -/
  Qshift : ShiftData QObj
  /-- Object map of the localization. -/
  onObj : Obj → QObj
  /-- Morphism map of the localization. -/
  onHom : ∀ {X Y : Obj}, Hom X Y → QHom (onObj X) (onObj Y)
  /-- Compatibility of localization with the shift. -/
  shift_compat : ∀ X : Obj, Path (Qshift.shift (onObj X)) (onObj (S.shift X))

/-! ## Trivial PUnit data -/

/-- Trivial hom type on `PUnit`. -/
def punitHom : PUnit → PUnit → Type := fun _ _ => PUnit

/-- Trivial shift data on `PUnit`. -/
def punitShift : ShiftData PUnit where
  shift := fun _ => PUnit.unit
  unshift := fun _ => PUnit.unit
  unshift_shift := by
    intro _
    exact Path.refl PUnit.unit
  shift_unshift := by
    intro _
    exact Path.refl PUnit.unit

/-- Trivial distinguished triangle on `PUnit`. -/
def punitTriangle : TriangleData PUnit punitHom punitShift where
  X := PUnit.unit
  Y := PUnit.unit
  Z := PUnit.unit
  f := PUnit.unit
  g := PUnit.unit
  h := PUnit.unit

/-- Trivial octahedral data on `PUnit`. -/
def punitOctahedral : OctahedralData PUnit punitHom punitShift where
  tri1 := punitTriangle
  tri2 := punitTriangle
  tri3 := punitTriangle
  mapY := PUnit.unit
  mapZ := PUnit.unit
  mapZ' := PUnit.unit
  overlap := Path.refl PUnit.unit

/-- Trivial Verdier quotient data on `PUnit`. -/
def punitVerdier : VerdierQuotientData PUnit punitHom punitShift where
  QObj := PUnit
  QHom := punitHom
  Qshift := punitShift
  onObj := fun _ => PUnit.unit
  onHom := fun _ => PUnit.unit
  shift_compat := by
    intro _
    exact Path.refl PUnit.unit

/-! ## Summary

We introduced data-level triangulated category structures with Path-valued
shift laws and provided trivial `PUnit` instances.
-/

end TriangulatedCategoryPaths
end Algebra
end Path
end ComputationalPaths
