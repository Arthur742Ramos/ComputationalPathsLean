/-
# Triangulated Categories Deep: Shift, Distinguished Triangles, Octahedral, T-structures

Deep results on triangulated categories via computational paths.

## References
- Verdier, Neeman, Beilinson-Bernstein-Deligne
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TriangulatedDeep

open ComputationalPaths.Path

universe u v

/-! ## Category operations -/

structure CatOps (Obj : Type u) (Hom : Obj → Obj → Type v) where
  id   : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  zero : (X Y : Obj) → Hom X Y

variable {Obj : Type u} {Hom : Obj → Obj → Type v} (ops : CatOps Obj Hom)

/-! ## Shift functor -/

structure ShiftData where
  shift : Obj → Obj
  shiftHom : {X Y : Obj} → Hom X Y → Hom (shift X) (shift Y)
  unshift : Obj → Obj
  unshift_shift : (X : Obj) → Path (unshift (shift X)) X
  shift_unshift : (X : Obj) → Path (shift (unshift X)) X
  shift_id : (X : Obj) → Path (shiftHom (ops.id X)) (ops.id (shift X))
  shift_comp : {X Y Z : Obj} → (f : Hom X Y) → (g : Hom Y Z) →
    Path (shiftHom (ops.comp f g)) (ops.comp (shiftHom f) (shiftHom g))

variable (S : ShiftData ops)

/-! ## 1: Shift preserves identity -/

def shift_preserves_id (X : Obj) :
    Path (S.shiftHom (ops.id X)) (ops.id (S.shift X)) :=
  S.shift_id X

/-! ## 2: Shift preserves composition -/

def shift_preserves_comp {X Y Z : Obj} (f : Hom X Y) (g : Hom Y Z) :
    Path (S.shiftHom (ops.comp f g)) (ops.comp (S.shiftHom f) (S.shiftHom g)) :=
  S.shift_comp f g

/-! ## 3: Shift-unshift roundtrip -/

def shift_unshift_roundtrip (X : Obj) :
    Path (S.unshift (S.shift X)) X :=
  S.unshift_shift X

/-! ## 4: Unshift-shift roundtrip -/

def unshift_shift_roundtrip (X : Obj) :
    Path (S.shift (S.unshift X)) X :=
  S.shift_unshift X

/-! ## Distinguished triangles -/

structure Triangle where
  X : Obj
  Y : Obj
  Z : Obj
  f : Hom X Y
  g : Hom Y Z
  h : Hom Z (S.shift X)

/-! ## Rotation -/

def rotate_triangle (T : Triangle ops S) : Triangle ops S where
  X := T.Y
  Y := T.Z
  Z := S.shift T.X
  f := T.g
  g := T.h
  h := S.shiftHom T.f

/-! ## 5: Double rotation -/

def rotate_twice (T : Triangle ops S) : Triangle ops S :=
  rotate_triangle ops S (rotate_triangle ops S T)

/-! ## 6: Rotate source -/

def rotate_source (T : Triangle ops S) :
    Path (rotate_triangle ops S T).X T.Y :=
  Path.refl _

/-! ## 7: Rotate middle -/

def rotate_middle (T : Triangle ops S) :
    Path (rotate_triangle ops S T).Y T.Z :=
  Path.refl _

/-! ## 8: Double rotate source -/

def rotate_twice_X (T : Triangle ops S) :
    Path (rotate_twice ops S T).X T.Z :=
  Path.refl _

/-! ## Triangle morphism -/

structure TriangleMor (T₁ T₂ : Triangle ops S) where
  fX : Hom T₁.X T₂.X
  fY : Hom T₁.Y T₂.Y
  fZ : Hom T₁.Z T₂.Z
  sq1 : Path (ops.comp T₁.f fY) (ops.comp fX T₂.f)
  sq2 : Path (ops.comp T₁.g fZ) (ops.comp fY T₂.g)

/-! ## 9: Triangle morphism square 1 -/

def triangle_mor_sq1 {T₁ T₂ : Triangle ops S} (m : TriangleMor ops S T₁ T₂) :
    Path (ops.comp T₁.f m.fY) (ops.comp m.fX T₂.f) :=
  m.sq1

/-! ## 10: Triangle morphism square 2 -/

def triangle_mor_sq2 {T₁ T₂ : Triangle ops S} (m : TriangleMor ops S T₁ T₂) :
    Path (ops.comp T₁.g m.fZ) (ops.comp m.fY T₂.g) :=
  m.sq2

/-! ## Octahedral axiom data -/

structure OctahedralData where
  X : Obj
  Y : Obj
  Z : Obj
  f : Hom X Y
  g : Hom Y Z
  fg : Hom X Z
  fg_eq : Path fg (ops.comp f g)
  T_f : Triangle ops S
  T_g : Triangle ops S
  T_fg : Triangle ops S
  T_f_src : Path T_f.X X
  T_f_tgt : Path T_f.Y Y
  T_g_src : Path T_g.X Y
  T_g_tgt : Path T_g.Y Z
  T_fg_src : Path T_fg.X X
  T_fg_tgt : Path T_fg.Y Z

/-! ## 11: Octahedral composition -/

def octahedral_comp (d : OctahedralData ops S) :
    Path d.fg (ops.comp d.f d.g) :=
  d.fg_eq

/-! ## 12: Octahedral source T_f -/

def octahedral_Tf_src (d : OctahedralData ops S) :
    Path d.T_f.X d.X :=
  d.T_f_src

/-! ## 13: Octahedral source T_fg -/

def octahedral_Tfg_src (d : OctahedralData ops S) :
    Path d.T_fg.X d.X :=
  d.T_fg_src

/-! ## 14: Octahedral target chain -/

def octahedral_tgt_chain (d : OctahedralData ops S) :
    Path d.T_f.Y d.Y :=
  d.T_f_tgt

/-! ## T-structure -/

structure TStructure where
  D_leq_zero : Obj → Prop
  D_geq_zero : Obj → Prop
  trunc_leq : (X : Obj) → Obj
  trunc_geq : (X : Obj) → Obj
  trunc_leq_mem : (X : Obj) → D_leq_zero (trunc_leq X)
  trunc_geq_mem : (X : Obj) → D_geq_zero (trunc_geq X)
  triangle : (X : Obj) → Triangle ops S
  triangle_src : (X : Obj) → Path (triangle X).X (trunc_leq X)
  triangle_tgt : (X : Obj) → Path (triangle X).Y X

/-! ## 15: Truncation in D≤0 -/

def trunc_leq_in_D (ts : TStructure ops S) (X : Obj) :
    ts.D_leq_zero (ts.trunc_leq X) :=
  ts.trunc_leq_mem X

/-! ## 16: Truncation in D≥0 -/

def trunc_geq_in_D (ts : TStructure ops S) (X : Obj) :
    ts.D_geq_zero (ts.trunc_geq X) :=
  ts.trunc_geq_mem X

/-! ## 17: Truncation triangle source -/

def trunc_triangle_src (ts : TStructure ops S) (X : Obj) :
    Path (ts.triangle X).X (ts.trunc_leq X) :=
  ts.triangle_src X

/-! ## 18: Truncation triangle target -/

def trunc_triangle_tgt (ts : TStructure ops S) (X : Obj) :
    Path (ts.triangle X).Y X :=
  ts.triangle_tgt X

/-! ## Heart -/

structure HeartObj (ts : TStructure ops S) where
  obj : Obj
  in_leq : ts.D_leq_zero obj
  in_geq : ts.D_geq_zero obj

/-! ## 19: Heart inclusion -/

def heart_to_obj (ts : TStructure ops S) (h : HeartObj ops S ts) : Obj :=
  h.obj

/-! ## 20: Heart is in D≤0 -/

def heart_in_leq (ts : TStructure ops S) (h : HeartObj ops S ts) :
    ts.D_leq_zero h.obj :=
  h.in_leq

/-! ## 21: Heart is in D≥0 -/

def heart_in_geq (ts : TStructure ops S) (h : HeartObj ops S ts) :
    ts.D_geq_zero h.obj :=
  h.in_geq

/-! ## Verdier quotient data -/

structure VerdierQuotientData where
  subcategory : Obj → Prop
  quotientObj : Obj → Obj
  quotientHom : {X Y : Obj} → Hom X Y → Hom (quotientObj X) (quotientObj Y)
  quotient_id : (X : Obj) → Path (quotientHom (ops.id X)) (ops.id (quotientObj X))

/-! ## 22: Verdier quotient preserves id -/

def verdier_preserves_id (V : VerdierQuotientData ops) (X : Obj) :
    Path (V.quotientHom (ops.id X)) (ops.id (V.quotientObj X)) :=
  V.quotient_id X

/-! ## 23: Shift double application -/

def shift_double (X : Obj) :
    Path (S.shift (S.shift X)) (S.shift (S.shift X)) :=
  Path.refl _

/-! ## 24: Shift of zero morphism -/

def shift_zero_path {X Y : Obj} :
    Path (S.shiftHom (ops.comp (ops.id X) (ops.zero X Y)))
         (ops.comp (S.shiftHom (ops.id X)) (S.shiftHom (ops.zero X Y))) :=
  S.shift_comp (ops.id X) (ops.zero X Y)

/-! ## 25: Triangle from morphism -/

def triangle_from_mor {X Y : Obj} (f : Hom X Y) (Z : Obj)
    (g : Hom Y Z) (h : Hom Z (S.shift X)) : Triangle ops S :=
  { X := X, Y := Y, Z := Z, f := f, g := g, h := h }

/-! ## 26: Rotate morphism is g -/

def rotate_mor_is_g (T : Triangle ops S) :
    Path (rotate_triangle ops S T).f T.g :=
  Path.refl _

/-! ## 27: Rotate second morphism is h -/

def rotate_second_is_h (T : Triangle ops S) :
    Path (rotate_triangle ops S T).g T.h :=
  Path.refl _

/-! ## 28: Octahedral T_g source -/

def octahedral_Tg_src (d : OctahedralData ops S) :
    Path d.T_g.X d.Y :=
  d.T_g_src

/-! ## 29: Octahedral T_g target -/

def octahedral_Tg_tgt (d : OctahedralData ops S) :
    Path d.T_g.Y d.Z :=
  d.T_g_tgt

/-! ## 30: Multi-step path chains -/

def shift_unshift_roundtrip_inv (X : Obj) :
    Path X (S.unshift (S.shift X)) :=
  Path.symm (shift_unshift_roundtrip (ops := ops) (S := S) X)

def shift_unshift_loop (X : Obj) :
    Path (S.unshift (S.shift X)) (S.unshift (S.shift X)) :=
  Path.trans (shift_unshift_roundtrip (ops := ops) (S := S) X)
    (shift_unshift_roundtrip_inv (ops := ops) (S := S) X)

def shift_after_unshift_shift (X : Obj) :
    Path (S.shift (S.unshift (S.shift X))) (S.shift X) :=
  Path.congrArg S.shift (shift_unshift_roundtrip (ops := ops) (S := S) X)

def unshift_after_shift_unshift (X : Obj) :
    Path (S.unshift (S.shift (S.unshift X))) (S.unshift X) :=
  Path.congrArg S.unshift (unshift_shift_roundtrip (ops := ops) (S := S) X)

def rotate_middle_to_twice_source (T : Triangle ops S) :
    Path (rotate_triangle ops S T).Y (rotate_twice ops S T).X :=
  Path.trans (rotate_middle (ops := ops) (S := S) T)
    (Path.symm (rotate_twice_X (ops := ops) (S := S) T))

def octahedral_source_bridge (d : OctahedralData ops S) :
    Path d.T_f.X d.T_fg.X :=
  Path.trans (octahedral_Tf_src (ops := ops) (S := S) d)
    (Path.symm (octahedral_Tfg_src (ops := ops) (S := S) d))

end TriangulatedDeep
end Algebra
end Path
end ComputationalPaths
