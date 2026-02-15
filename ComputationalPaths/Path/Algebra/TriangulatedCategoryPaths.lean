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
import ComputationalPaths.Path.Category.LocalizationPaths
import ComputationalPaths.Path.Homotopy.GeneralizedHomology

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TriangulatedCategoryPaths

open Category.LocalizationPaths
open Homotopy.GeneralizedHomology
open PointedMapCategory

universe u v w

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

/-! ## Cross-module path dependencies -/

/-- Triangulated localization composition coherence inherited from
`Category/LocalizationPaths`. -/
def triangulated_localization_comp_path
    {C : Type u} (L : LeftExactLocalization C)
    {a b c : C} (p : Path a b) (q : Path b c) :
    RwEq (L.preserves_product (Path.trans p q))
         (Path.trans (L.preserves_product p) (L.preserves_product q)) :=
  rweq_trans (left_exact_preserves_comp_rweq L p q) (RwEq.refl _)

/-- Triangulated homology functor composition coherence inherited from
`Homology/GeneralizedHomology`. -/
def triangulated_homology_comp_path
    (E : GeneralizedHomologyTheory.{u, w})
    {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    Path (E.map (PtdMap.comp g f) n) ((E.map g n) ∘ (E.map f n)) :=
  Path.trans (GeneralizedHomologyTheory.map_comp_path E g f n) (Path.refl _)

/-- Combined triangulated cross-module dependency, composing Category and
Homology path witnesses. -/
def triangulated_cross_module_dependencies
    {C : Type u} (L : LeftExactLocalization C)
    {a b c : C} (p : Path a b) (q : Path b c)
    (E : GeneralizedHomologyTheory.{u, w})
    {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    RwEq (L.preserves_product (Path.trans p q))
      (Path.trans (L.preserves_product p) (L.preserves_product q)) ∧
    Nonempty (Path (E.map (PtdMap.comp g f) n) ((E.map g n) ∘ (E.map f n))) :=
  ⟨
    rweq_trans (triangulated_localization_comp_path L p q) (RwEq.refl _),
    ⟨Path.trans (triangulated_homology_comp_path E g f n) (Path.refl _)⟩
  ⟩

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

/-! ## Theorem stubs -/

theorem shiftData_unshift_shift_path {Obj : Type u} (S : ShiftData Obj) (X : Obj) :
    Nonempty (Path (S.unshift (S.shift X)) X) :=
  ⟨Path.ofEq (S.unshift_shift X)⟩

theorem shiftData_shift_unshift_path {Obj : Type u} (S : ShiftData Obj) (X : Obj) :
    Nonempty (Path (S.shift (S.unshift X)) X) :=
  ⟨Path.ofEq (S.shift_unshift X)⟩

theorem shiftData_unshift_shift_symm {Obj : Type u} (S : ShiftData Obj) (X : Obj) :
    Nonempty (Path X (S.unshift (S.shift X))) :=
  ⟨Path.symm (Path.ofEq (S.unshift_shift X))⟩

theorem triangleData_X_refl {Obj : Type u} {Hom : Obj → Obj → Type v}
    {S : ShiftData Obj} (T : TriangleData Obj Hom S) :
    Nonempty (Path T.X T.X) :=
  ⟨Path.refl _⟩

theorem triangleData_Y_refl {Obj : Type u} {Hom : Obj → Obj → Type v}
    {S : ShiftData Obj} (T : TriangleData Obj Hom S) :
    Nonempty (Path T.Y T.Y) :=
  ⟨Path.refl _⟩

theorem triangleData_Z_refl {Obj : Type u} {Hom : Obj → Obj → Type v}
    {S : ShiftData Obj} (T : TriangleData Obj Hom S) :
    Nonempty (Path T.Z T.Z) :=
  ⟨Path.refl _⟩

theorem octahedral_overlap_symm {Obj : Type u} {Hom : Obj → Obj → Type v}
    {S : ShiftData Obj} (O : OctahedralData Obj Hom S) :
    Nonempty (Path O.tri1.Z O.tri3.X) :=
  ⟨Path.ofEq O.overlap⟩

theorem verdier_shift_compat_path {Obj : Type u} {Hom : Obj → Obj → Type v}
    {S : ShiftData Obj} (V : VerdierQuotientData Obj Hom S) (X : Obj) :
    Nonempty (Path (V.Qshift.shift (V.onObj X)) (V.onObj (S.shift X))) :=
  ⟨Path.ofEq (V.shift_compat X)⟩

theorem triangulated_localization_functoriality
    {C : Type u} (L : LeftExactLocalization C)
    {a b c : C} (p : Path a b) (q : Path b c) :
    RwEq (L.preserves_product (Path.trans p q))
      (Path.trans (L.preserves_product p) (L.preserves_product q)) :=
  L.preserves_product_trans p q

theorem triangulated_homology_functoriality
    (E : GeneralizedHomologyTheory.{u, w})
    {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    Nonempty (Path (E.map (PtdMap.comp g f) n) ((E.map g n) ∘ (E.map f n))) :=
  ⟨Path.ofEq (E.map_comp g f n)⟩

theorem triangulated_cross_dependencies_left
    {C : Type u} (L : LeftExactLocalization C)
    {a b c : C} (p : Path a b) (q : Path b c)
    (E : GeneralizedHomologyTheory.{u, w})
    {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    RwEq (L.preserves_product (Path.trans p q))
      (Path.trans (L.preserves_product p) (L.preserves_product q)) := by
  L.preserves_product_trans p q

theorem triangulated_cross_dependencies_right
    {C : Type u} (L : LeftExactLocalization C)
    {a b c : C} (p : Path a b) (q : Path b c)
    (E : GeneralizedHomologyTheory.{u, w})
    {X Y Z : PtdType.{u}} (g : PtdMap Y Z) (f : PtdMap X Y) (n : Nat) :
    Nonempty (Path (E.map (PtdMap.comp g f) n) ((E.map g n) ∘ (E.map f n))) :=
  ⟨Path.ofEq (E.map_comp g f n)⟩

theorem punit_loop_trans_assoc (p q r : Path PUnit.unit PUnit.unit) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt p q r

theorem punit_loop_trans_comm (p q : Path PUnit.unit PUnit.unit) :
    RwEq (Path.trans p q) (Path.trans q p) :=
  rweq_eckmann_hilton p q

/-! ## Summary

We introduced data-level triangulated category structures with Path-valued
shift laws and provided trivial `PUnit` instances.
-/

end TriangulatedCategoryPaths
end Algebra
end Path
end ComputationalPaths
