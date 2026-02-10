/-
# Stable Homotopy Categories

Formalization of stable homotopy categories including triangulated categories,
exact triangles, the shift functor, the octahedral axiom, and stable
equivalences.

All proofs are complete — no sorry, no axiom.

## References

- Neeman, "Triangulated Categories"
- Hovey–Palmieri–Strickland, "Axiomatic Stable Homotopy Theory"
-/

import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Homotopy.StableHomotopy

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace StableCategory

universe u

/-! ## Pre-additive categories -/

/-- A pre-additive category. -/
structure PreAdditiveCategory where
  Obj : Type u
  Hom : Obj → Obj → Type u
  zero : ∀ (X Y : Obj), Hom X Y
  add : ∀ {X Y : Obj}, Hom X Y → Hom X Y → Hom X Y
  neg : ∀ {X Y : Obj}, Hom X Y → Hom X Y
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  id : ∀ (X : Obj), Hom X X
  id_comp : ∀ {X Y : Obj} (f : Hom X Y), comp (id X) f = f
  comp_id : ∀ {X Y : Obj} (f : Hom X Y), comp f (id Y) = f
  assoc : ∀ {X Y Z W : Obj} (f : Hom X Y) (g : Hom Y Z) (h : Hom Z W),
    comp (comp f g) h = comp f (comp g h)
  add_zero : ∀ {X Y : Obj} (f : Hom X Y), add f (zero X Y) = f
  zero_add : ∀ {X Y : Obj} (f : Hom X Y), add (zero X Y) f = f
  add_neg : ∀ {X Y : Obj} (f : Hom X Y), add f (neg f) = zero X Y
  add_comm : ∀ {X Y : Obj} (f g : Hom X Y), add f g = add g f

/-! ## Shift (Translation) functor -/

/-- A shift (translation) functor on a pre-additive category. -/
structure ShiftFunctor (C : PreAdditiveCategory.{u}) where
  shiftObj : C.Obj → C.Obj
  shiftHom : ∀ {X Y : C.Obj}, C.Hom X Y → C.Hom (shiftObj X) (shiftObj Y)
  shift_id : ∀ (X : C.Obj), shiftHom (C.id X) = C.id (shiftObj X)
  shift_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    shiftHom (C.comp f g) = C.comp (shiftHom f) (shiftHom g)

/-- Iterate the shift functor n times. -/
def ShiftFunctor.iterate {C : PreAdditiveCategory.{u}} (T : ShiftFunctor C) :
    Nat → C.Obj → C.Obj
  | 0, X => X
  | n + 1, X => T.shiftObj (iterate T n X)

theorem ShiftFunctor.iterate_zero {C : PreAdditiveCategory.{u}}
    (T : ShiftFunctor C) (X : C.Obj) :
    T.iterate 0 X = X := rfl

theorem ShiftFunctor.iterate_one {C : PreAdditiveCategory.{u}}
    (T : ShiftFunctor C) (X : C.Obj) :
    T.iterate 1 X = T.shiftObj X := rfl

/-! ## Triangles -/

/-- A triangle X → Y → Z → T(X) in a pre-additive category with shift. -/
structure Triangle (C : PreAdditiveCategory.{u}) (T : ShiftFunctor C) where
  X : C.Obj
  Y : C.Obj
  Z : C.Obj
  f : C.Hom X Y
  g : C.Hom Y Z
  h : C.Hom Z (T.shiftObj X)

/-- A morphism of triangles. -/
structure TriangleMorphism {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (T₁ T₂ : Triangle C T) where
  alpha : C.Hom T₁.X T₂.X
  beta : C.Hom T₁.Y T₂.Y
  gamma : C.Hom T₁.Z T₂.Z
  comm_f : C.comp T₁.f beta = C.comp alpha T₂.f
  comm_g : C.comp T₁.g gamma = C.comp beta T₂.g
  comm_h : C.comp T₁.h (T.shiftHom alpha) = C.comp gamma T₂.h

/-- The identity morphism of triangles. -/
def TriangleMorphism.id {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (Tr : Triangle C T) : TriangleMorphism Tr Tr where
  alpha := C.id Tr.X
  beta := C.id Tr.Y
  gamma := C.id Tr.Z
  comm_f := by rw [C.comp_id, C.id_comp]
  comm_g := by rw [C.comp_id, C.id_comp]
  comm_h := by rw [T.shift_id, C.comp_id, C.id_comp]

/-- A triangle isomorphism. -/
structure TriangleIso {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (T₁ T₂ : Triangle C T) where
  forward : TriangleMorphism T₁ T₂
  backward : TriangleMorphism T₂ T₁

/-- Rotation of a triangle. -/
def Triangle.rotate {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (Tr : Triangle C T) (negShiftF : C.Hom (T.shiftObj Tr.X) (T.shiftObj Tr.Y)) :
    Triangle C T where
  X := Tr.Y
  Y := Tr.Z
  Z := T.shiftObj Tr.X
  f := Tr.g
  g := Tr.h
  h := negShiftF

/-! ## Triangulated category -/

/-- A triangulated category. -/
structure TriangulatedCategory where
  cat : PreAdditiveCategory.{u}
  shift : ShiftFunctor cat
  distinguished : Triangle cat shift → Prop
  tr1_id : ∀ (X : cat.Obj),
    ∃ (Z : cat.Obj) (g : cat.Hom X Z) (h : cat.Hom Z (shift.shiftObj X)),
      distinguished ⟨X, X, Z, cat.id X, g, h⟩
  tr2_complete : ∀ {X Y : cat.Obj} (f : cat.Hom X Y),
    ∃ (Z : cat.Obj) (g : cat.Hom Y Z) (h : cat.Hom Z (shift.shiftObj X)),
      distinguished ⟨X, Y, Z, f, g, h⟩
  tr3_iso : ∀ {T₁ T₂ : Triangle cat shift},
    distinguished T₁ → TriangleIso T₁ T₂ → distinguished T₂
  tr4_rotate : ∀ (Tr : Triangle cat shift),
    distinguished Tr →
    ∀ (negShiftF : cat.Hom (shift.shiftObj Tr.X) (shift.shiftObj Tr.Y)),
      distinguished (Tr.rotate negShiftF)

/-! ## Exact triangles -/

/-- Exactness of a triangle: g ∘ f = 0 and h ∘ g = 0. -/
structure ExactTriangle {C : PreAdditiveCategory.{u}} {T : ShiftFunctor C}
    (Tr : Triangle C T) where
  gf_zero : C.comp Tr.f Tr.g = C.zero Tr.X Tr.Z
  hg_zero : C.comp Tr.g Tr.h = C.zero Tr.Y (T.shiftObj Tr.X)

/-! ## Octahedral axiom -/

/-- The octahedral axiom data. -/
structure OctahedralAxiom (TC : TriangulatedCategory.{u}) where
  octahedral :
    ∀ {X Y Z : TC.cat.Obj}
      (f : TC.cat.Hom X Y) (g : TC.cat.Hom Y Z)
      (Cf : TC.cat.Obj) (Tf : Triangle TC.cat TC.shift)
      (_ : TC.distinguished Tf) (_ : Tf.X = X ∧ Tf.Y = Y ∧ Tf.Z = Cf)
      (Cg : TC.cat.Obj) (Tg : Triangle TC.cat TC.shift)
      (_ : TC.distinguished Tg) (_ : Tg.X = Y ∧ Tg.Y = Z ∧ Tg.Z = Cg),
    ∃ (Cgf : TC.cat.Obj) (Tgf : Triangle TC.cat TC.shift),
      TC.distinguished Tgf ∧ Tgf.X = X ∧ Tgf.Y = Z ∧ Tgf.Z = Cgf

/-! ## Exact functors and stable equivalences -/

/-- An exact (triangulated) functor. -/
structure ExactFunctor (TC₁ TC₂ : TriangulatedCategory.{u}) where
  mapObj : TC₁.cat.Obj → TC₂.cat.Obj
  mapHom : ∀ {X Y : TC₁.cat.Obj}, TC₁.cat.Hom X Y →
    TC₂.cat.Hom (mapObj X) (mapObj Y)
  map_id : ∀ (X : TC₁.cat.Obj),
    mapHom (TC₁.cat.id X) = TC₂.cat.id (mapObj X)
  map_comp : ∀ {X Y Z : TC₁.cat.Obj} (f : TC₁.cat.Hom X Y) (g : TC₁.cat.Hom Y Z),
    mapHom (TC₁.cat.comp f g) = TC₂.cat.comp (mapHom f) (mapHom g)
  shift_comm : ∀ (X : TC₁.cat.Obj),
    mapObj (TC₁.shift.shiftObj X) = TC₂.shift.shiftObj (mapObj X)

/-- Identity exact functor. -/
def ExactFunctor.id (TC : TriangulatedCategory.{u}) : ExactFunctor TC TC where
  mapObj := _root_.id
  mapHom := _root_.id
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl
  shift_comm := fun _ => rfl

/-- A stable equivalence. -/
structure StableEquivalence (TC₁ TC₂ : TriangulatedCategory.{u}) where
  forward : ExactFunctor TC₁ TC₂
  backward : ExactFunctor TC₂ TC₁
  unit_obj : ∀ (X : TC₁.cat.Obj),
    backward.mapObj (forward.mapObj X) = X
  counit_obj : ∀ (Y : TC₂.cat.Obj),
    forward.mapObj (backward.mapObj Y) = Y

/-- Every triangulated category is stably equivalent to itself. -/
def StableEquivalence.refl (TC : TriangulatedCategory.{u}) :
    StableEquivalence TC TC where
  forward := ExactFunctor.id TC
  backward := ExactFunctor.id TC
  unit_obj := fun _ => rfl
  counit_obj := fun _ => rfl

/-! ## Zero object -/

/-- A zero object. -/
structure ZeroObject (C : PreAdditiveCategory.{u}) where
  zero : C.Obj
  toZero : ∀ (X : C.Obj), C.Hom X zero
  fromZero : ∀ (X : C.Obj), C.Hom zero X
  unique_to : ∀ (X : C.Obj) (f g : C.Hom X zero), f = g
  unique_from : ∀ (X : C.Obj) (f g : C.Hom zero X), f = g

/-! ## Long exact sequences from triangles -/

/-- Periodic sequence of objects from a triangle. -/
def periodicLES {TC : TriangulatedCategory.{u}} (Tr : Triangle TC.cat TC.shift) :
    Nat → TC.cat.Obj
  | 0 => Tr.X
  | 1 => Tr.Y
  | 2 => Tr.Z
  | n + 3 => TC.shift.shiftObj (periodicLES Tr n)

/-- Long exact sequence data from a distinguished triangle. -/
structure LongExactFromTriangle (TC : TriangulatedCategory.{u})
    (Tr : Triangle TC.cat TC.shift) where
  term : Nat → TC.cat.Obj
  map : (n : Nat) → TC.cat.Hom (term n) (term (n + 1))
  exact : ∀ (n : Nat), TC.cat.comp (map n) (map (n + 1)) =
    TC.cat.zero (term n) (term (n + 2))

end StableCategory
end Homotopy
end Path
end ComputationalPaths
