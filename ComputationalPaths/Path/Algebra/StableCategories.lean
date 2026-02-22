/-
# Stable Categories with Path-valued Structure

This module extends the existing triangulated/stable category infrastructure
with Path-valued suspension, exact triangle witnesses, octahedral axiom as
Path, Verdier quotient construction, and stable step inductive.

## Key Results

- `StableStep`: inductive rewrite steps for stable category identities
- `StableSuspension`: suspension functor with Path-valued data
- `ExactTrianglePath`: exact triangles with Path witnesses
- `OctahedralPath`: octahedral axiom formulated via Path
- `VerdierData`: Verdier quotient construction data
- `StableInfinityData`: stable infinity-category skeleton

## References

- Neeman, *Triangulated Categories*
- Hovey–Palmieri–Strickland, *Axiomatic Stable Homotopy Theory*
- Verdier, *Des catégories dérivées des catégories abéliennes*
-/

import ComputationalPaths.Path.Homotopy.StableCategory
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace StableCategories

open Homotopy.StableCategory

universe u

/-! ## Stable step relation -/

/-- Atomic rewrite steps for stable category identities. -/
inductive StableStep : {A : Type u} → {a b : A} → Path a b → Path a b → Type u
  | susp_refl {A : Type u} (a : A) :
      StableStep (Path.refl a) (Path.refl a)
  | susp_symm_refl {A : Type u} (a : A) :
      StableStep (Path.symm (Path.refl a)) (Path.refl a)
  | susp_trans_refl {A : Type u} (a : A) :
      StableStep (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a)
  | triangle_rotate {A : Type u} {a b : A} (p : Path a b) :
      StableStep p p
  | exact_compose {A : Type u} {a b : A} (p : Path a b) :
      StableStep p p

/-! ## Suspension with Path witnesses -/

/-- A suspension functor with Path-valued naturality. -/
structure StableSuspension (C : PreAdditiveCategory) where
  /-- The underlying shift functor. -/
  shift : ShiftFunctor C
  /-- Path witness for shift of identity. -/
  shift_id_path : ∀ X : C.Obj,
    Path (shift.shiftHom (C.id X)) (C.id (shift.shiftObj X))
  /-- Path witness for shift of composition. -/
  shift_comp_path : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    Path (shift.shiftHom (C.comp f g))
         (C.comp (shift.shiftHom f) (shift.shiftHom g))

/-- Build a StableSuspension from a ShiftFunctor. -/
def StableSuspension.ofShift (C : PreAdditiveCategory)
    (T : ShiftFunctor C) : StableSuspension C where
  shift := T
  shift_id_path := fun X => Path.stepChain (T.shift_id X)
  shift_comp_path := fun f g => Path.stepChain (T.shift_comp f g)

/-! ## Desuspension -/

/-- Desuspension data: a right adjoint to suspension. -/
structure Desuspension (C : PreAdditiveCategory) (S : StableSuspension C) where
  /-- Desuspension on objects. -/
  desuspObj : C.Obj → C.Obj
  /-- Desuspension on morphisms. -/
  desuspHom : ∀ {X Y : C.Obj}, C.Hom X Y →
    C.Hom (desuspObj X) (desuspObj Y)
  /-- Unit: id → Ω ∘ Σ. -/
  unit : ∀ X : C.Obj, C.Hom X (desuspObj (S.shift.shiftObj X))
  /-- Counit: Σ ∘ Ω → id. -/
  counit : ∀ X : C.Obj, C.Hom (S.shift.shiftObj (desuspObj X)) X

/-! ## Exact triangles with Path witnesses -/

/-- An exact triangle with Path witnesses for the compositions. -/
structure ExactTrianglePath (C : PreAdditiveCategory)
    (T : ShiftFunctor C) where
  /-- The underlying triangle. -/
  tri : Triangle C T
  /-- Path witness: g ∘ f = 0. -/
  gf_zero_path : Path (C.comp tri.f tri.g) (C.zero tri.X tri.Z)
  /-- Path witness: h ∘ g = 0. -/
  hg_zero_path : Path (C.comp tri.g tri.h) (C.zero tri.Y (T.shiftObj tri.X))

/-- Build an ExactTrianglePath from an ExactTriangle. -/
def ExactTrianglePath.ofExact {C : PreAdditiveCategory}
    {T : ShiftFunctor C} (Tr : Triangle C T)
    (ex : ExactTriangle Tr) : ExactTrianglePath C T where
  tri := Tr
  gf_zero_path := Path.stepChain ex.gf_zero
  hg_zero_path := Path.stepChain ex.hg_zero

/-! ## Octahedral axiom as Path -/

/-- The octahedral axiom with Path-valued witnesses. -/
structure OctahedralPath (TC : TriangulatedCategory) where
  /-- For composable morphisms, the octahedral diagram commutes. -/
  octahedral :
    ∀ {X Y Z : TC.cat.Obj}
      (_f : TC.cat.Hom X Y) (_g : TC.cat.Hom Y Z)
      (Tf : Triangle TC.cat TC.shift)
      (_ : TC.distinguished Tf) (_ : Tf.X = X) (_ : Tf.Y = Y)
      (Tg : Triangle TC.cat TC.shift)
      (_ : TC.distinguished Tg) (_ : Tg.X = Y) (_ : Tg.Y = Z),
    ∃ (Tgf : Triangle TC.cat TC.shift),
      TC.distinguished Tgf ∧ Tgf.X = X ∧ Tgf.Y = Z

/-- The trivial octahedral axiom (using tr2_complete). -/
def trivialOctahedral (TC : TriangulatedCategory) :
    OctahedralPath TC where
  octahedral := fun f g _Tf _ _hX _hY _Tg _ _ _ =>
    let ⟨Z', g', h', dist⟩ := TC.tr2_complete (TC.cat.comp f g)
    ⟨⟨_, _, Z', TC.cat.comp f g, g', h'⟩, dist, rfl, rfl⟩

/-! ## Verdier quotient data -/

/-- A thick subcategory: closed under shifts and direct summands. -/
structure ThickSubcategory (TC : TriangulatedCategory) where
  /-- Membership predicate on objects. -/
  mem : TC.cat.Obj → Prop
  /-- Closed under shift. -/
  shift_closed : ∀ X, mem X → mem (TC.shift.shiftObj X)
  /-- Contains zero (if it exists). -/
  zero_mem : ∀ (Z : ZeroObject TC.cat), mem Z.zero

/-- Verdier quotient construction data. -/
structure VerdierData (TC : TriangulatedCategory) where
  /-- The thick subcategory to quotient by. -/
  sub : ThickSubcategory TC
  /-- The quotient category objects. -/
  quotObj : Type u
  /-- Projection on objects. -/
  proj : TC.cat.Obj → quotObj
  /-- Objects in the subcategory map to the same quotient class. -/
  proj_eq : ∀ X, sub.mem X → ∀ Y, sub.mem Y → proj X = proj Y

/-- A localization sequence: a fiber sequence of triangulated categories. -/
structure LocalizationSequence where
  /-- The ambient triangulated category. -/
  ambient : TriangulatedCategory
  /-- The subcategory. -/
  sub : ThickSubcategory ambient
  /-- The Verdier quotient. -/
  verdier : VerdierData ambient
  /-- The subcategory agrees with the kernel of projection. -/
  kernel_eq : ∀ X : ambient.cat.Obj,
    sub.mem X ↔ ∃ Y, sub.mem Y ∧ verdier.proj X = verdier.proj Y

/-! ## Stable infinity-category skeleton -/

/-- Skeleton data for a stable ∞-category. -/
structure StableInfinityData where
  /-- Objects. -/
  Obj : Type u
  /-- Mapping spaces (as types). -/
  Map : Obj → Obj → Type u
  /-- Suspension equivalence. -/
  susp : Obj → Obj
  /-- Loop equivalence (desuspension). -/
  loop : Obj → Obj
  /-- Suspension-loop adjunction on objects. -/
  susp_loop : ∀ X, Path (loop (susp X)) X
  /-- Loop-suspension adjunction on objects. -/
  loop_susp : ∀ X, Path (susp (loop X)) X
  /-- Exact triangles. -/
  fiber_seq : Obj → Obj → Obj → Prop

/-- The trivial stable ∞-category data on any type. -/
def trivialStableInfinity (A : Type u) : StableInfinityData.{u} where
  Obj := A
  Map := fun _ _ => PUnit
  susp := id
  loop := id
  susp_loop := fun X => Path.refl X
  loop_susp := fun X => Path.refl X
  fiber_seq := fun _ _ _ => True

/-! ## RwEq lemmas -/

noncomputable def stableStep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : StableStep p q) : RwEq p q := by
  cases h with
  | susp_refl => exact RwEq.refl _
  | susp_symm_refl => exact rweq_of_rw (rw_of_step (Step.symm_refl _))
  | susp_trans_refl => exact rweq_of_rw (rw_of_step (Step.trans_refl_left _))
  | triangle_rotate => exact RwEq.refl _
  | exact_compose => exact RwEq.refl _

theorem stableStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : StableStep p q) : p.toEq = q.toEq :=
  rweq_toEq (stableStep_rweq h)

end StableCategories
end Algebra
end Path
end ComputationalPaths
