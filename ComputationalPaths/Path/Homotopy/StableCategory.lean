/-
# Stable Categories

Stable category structure via computational paths.  Provides the core algebraic
scaffolding — pre-additive categories, shift functors, triangles, triangulated
categories — consumed by downstream modules (StableCategories, TorsionTheory,
DerivedCategories, StableModelCategories).
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths.Path.Homotopy.StableCategory

universe u v

/-! ## Pre-additive category -/

/-- Minimal pre-additive category bundle: objects, hom-sets, identity,
    composition, zero morphisms, negation, and the standard axioms. -/
structure PreAdditiveCategory where
  /-- Objects of the category. -/
  Obj : Type u
  /-- Morphisms between objects. -/
  Hom : Obj → Obj → Type u
  /-- Identity morphism. -/
  id  : (X : Obj) → Hom X X
  /-- Composition of morphisms. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Zero morphism between any two objects. -/
  zero : (X Y : Obj) → Hom X Y
  /-- Negation of a morphism. -/
  neg  : {X Y : Obj} → Hom X Y → Hom X Y
  /-- Left identity law. -/
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  /-- Right identity law. -/
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  /-- Associativity of composition. -/
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    comp (comp f g) h = comp f (comp g h)

/-! ## Shift functor -/

/-- A shift (suspension) endofunctor on a pre-additive category. -/
structure ShiftFunctor (C : PreAdditiveCategory.{u}) where
  /-- Action on objects. -/
  shiftObj : C.Obj → C.Obj
  /-- Action on morphisms. -/
  shiftHom : {X Y : C.Obj} → C.Hom X Y → C.Hom (shiftObj X) (shiftObj Y)
  /-- Preserves identity. -/
  shift_id : (X : C.Obj) → shiftHom (C.id X) = C.id (shiftObj X)
  /-- Preserves composition. -/
  shift_comp : {X Y Z : C.Obj} → (f : C.Hom X Y) → (g : C.Hom Y Z) →
    shiftHom (C.comp f g) = C.comp (shiftHom f) (shiftHom g)

/-! ## Triangles -/

/-- A distinguished triangle  X —f→ Y —g→ Z —h→ Σ(X). -/
structure Triangle (C : PreAdditiveCategory.{u}) (T : ShiftFunctor C) where
  X : C.Obj
  Y : C.Obj
  Z : C.Obj
  f : C.Hom X Y
  g : C.Hom Y Z
  h : C.Hom Z (T.shiftObj X)

/-! ## Triangle morphisms -/

/-- A morphism between two triangles over the same shift functor. -/
structure TriangleMorphism {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (S₁ S₂ : Triangle C T) where
  f_map : C.Hom S₁.X S₂.X
  g_map : C.Hom S₁.Y S₂.Y
  h_map : C.Hom S₁.Z S₂.Z
  comm_f : C.comp S₁.f g_map = C.comp f_map S₂.f
  comm_g : C.comp S₁.g h_map = C.comp g_map S₂.g

namespace TriangleMorphism

/-- Identity morphism of a triangle. -/
def id {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (Tr : Triangle C T) : TriangleMorphism Tr Tr where
  f_map := C.id Tr.X
  g_map := C.id Tr.Y
  h_map := C.id Tr.Z
  comm_f := by rw [C.comp_id, C.id_comp]
  comm_g := by rw [C.comp_id, C.id_comp]

end TriangleMorphism

/-! ## Exact triangles -/

/-- An exact triangle witnesses g∘f = 0 and h∘g = 0. -/
structure ExactTriangle {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (Tr : Triangle C T) where
  gf_zero : C.comp Tr.f Tr.g = C.zero Tr.X Tr.Z
  hg_zero : C.comp Tr.g Tr.h = C.zero Tr.Y (T.shiftObj Tr.X)

/-! ## Zero object -/

/-- A zero object in a pre-additive category. -/
structure ZeroObject (C : PreAdditiveCategory.{u}) where
  /-- The zero object. -/
  zero : C.Obj
  /-- Morphism from zero to any object. -/
  from_zero : (X : C.Obj) → C.Hom zero X
  /-- Morphism from any object to zero. -/
  to_zero : (X : C.Obj) → C.Hom X zero

/-! ## Triangulated category -/

/-- A triangulated category: a pre-additive category with a shift functor
    and a class of distinguished triangles satisfying the standard axioms. -/
structure TriangulatedCategory where
  /-- The underlying pre-additive category. -/
  cat : PreAdditiveCategory.{u}
  /-- The shift functor. -/
  shift : ShiftFunctor cat
  /-- Predicate selecting distinguished triangles. -/
  distinguished : Triangle cat shift → Prop
  /-- Every morphism extends to a distinguished triangle (TR2). -/
  tr2_complete : {X Y : cat.Obj} → (f : cat.Hom X Y) →
    ∃ (Z : cat.Obj) (g : cat.Hom Y Z) (h : cat.Hom Z (shift.shiftObj X)),
      distinguished ⟨X, Y, Z, f, g, h⟩

end ComputationalPaths.Path.Homotopy.StableCategory
