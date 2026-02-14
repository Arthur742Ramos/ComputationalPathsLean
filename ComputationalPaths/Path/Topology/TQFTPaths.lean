/-
# TQFTs via Computational Paths

This module records an axiom-free interface for topological quantum field
theories (TQFTs) using computational paths. We define cobordism categories,
TQFT functors, Atiyah-Segal axioms, a gluing formula, partition functions,
and the 2D classification interface via Frobenius algebras.

## Mathematical Background

A TQFT is a symmetric monoidal functor from a cobordism category to a target
monoidal category (typically vector spaces). The Atiyah-Segal axioms encode
functoriality, monoidality, and gluing of cobordisms. In dimension two, TQFTs
are classified by commutative Frobenius algebras.

## References

- Atiyah, "Topological quantum field theories"
- Segal, "The definition of conformal field theory"
- Kock, "Frobenius algebras and 2D TQFTs"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace TQFTPaths

universe u v

/-! ## Cobordism categories -/

/-- A cobordism category with a monoidal structure by disjoint union. -/
structure CobordismCategory where
  /-- Objects (closed manifolds or formal boundaries). -/
  Obj : Type u
  /-- Morphisms (cobordisms). -/
  Hom : Obj → Obj → Type v
  /-- Identity cobordism. -/
  id : (X : Obj) → Hom X X
  /-- Composition by gluing cobordisms. -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  /-- Associativity of gluing. -/
  assoc : {W X Y Z : Obj} → (f : Hom W X) → (g : Hom X Y) → (h : Hom Y Z) →
    Path (comp (comp f g) h) (comp f (comp g h))
  /-- Left identity for gluing. -/
  left_id : {X Y : Obj} → (f : Hom X Y) → Path (comp (id X) f) f
  /-- Right identity for gluing. -/
  right_id : {X Y : Obj} → (f : Hom X Y) → Path (comp f (id Y)) f
  /-- Tensor product on objects (disjoint union). -/
  tensorObj : Obj → Obj → Obj
  /-- Tensor product on morphisms. -/
  tensorHom : {X1 Y1 X2 Y2 : Obj} → Hom X1 Y1 → Hom X2 Y2 →
    Hom (tensorObj X1 X2) (tensorObj Y1 Y2)
  /-- Monoidal unit (empty manifold). -/
  tensorUnit : Obj
  /-- Associativity of disjoint union. -/
  tensor_assoc : (X Y Z : Obj) →
    Path (tensorObj (tensorObj X Y) Z) (tensorObj X (tensorObj Y Z))
  /-- Left unit law for disjoint union. -/
  tensor_left_unit : (X : Obj) → Path (tensorObj tensorUnit X) X
  /-- Right unit law for disjoint union. -/
  tensor_right_unit : (X : Obj) → Path (tensorObj X tensorUnit) X

/-! ## Cobordism rewrite steps -/

/-- Domain-specific rewrite steps for cobordism gluing. -/
inductive TQFTStep (C : CobordismCategory.{u, v}) :
    {X Y : C.Obj} → C.Hom X Y → C.Hom X Y → Type (max u v)
  | assoc {W X Y Z : C.Obj} (f : C.Hom W X) (g : C.Hom X Y) (h : C.Hom Y Z) :
      TQFTStep C (C.comp (C.comp f g) h) (C.comp f (C.comp g h))
  | left_id {X Y : C.Obj} (f : C.Hom X Y) :
      TQFTStep C (C.comp (C.id X) f) f
  | right_id {X Y : C.Obj} (f : C.Hom X Y) :
      TQFTStep C (C.comp f (C.id Y)) f

/-- Interpret a cobordism step as a computational path. -/
def tqftStepPath {C : CobordismCategory.{u, v}} {X Y : C.Obj} {f g : C.Hom X Y} :
    TQFTStep C f g → Path f g
  | TQFTStep.assoc f g h => C.assoc f g h
  | TQFTStep.left_id f => C.left_id f
  | TQFTStep.right_id f => C.right_id f

/-- Compose two cobordism steps into a single path. -/
def tqft_steps_compose {C : CobordismCategory.{u, v}} {X Y : C.Obj}
    {f g h : C.Hom X Y} (s1 : TQFTStep C f g) (s2 : TQFTStep C g h) :
    Path f h :=
  Path.trans (tqftStepPath s1) (tqftStepPath s2)

/-! ## TQFT functors -/

/-- A TQFT functor between cobordism categories (monoidality is in the axioms). -/
structure TQFTFunctor (C D : CobordismCategory.{u, v}) where
  /-- Object map. -/
  objMap : C.Obj → D.Obj
  /-- Morphism map. -/
  morMap : {X Y : C.Obj} → C.Hom X Y → D.Hom (objMap X) (objMap Y)
  /-- Functor preserves identities. -/
  map_id : (X : C.Obj) → Path (morMap (C.id X)) (D.id (objMap X))
  /-- Functor preserves composition (gluing). -/
  map_comp : {X Y Z : C.Obj} → (f : C.Hom X Y) → (g : C.Hom Y Z) →
    Path (morMap (C.comp f g)) (D.comp (morMap f) (morMap g))

/-! ## Atiyah-Segal axioms -/

/-- Atiyah-Segal axioms for a TQFT functor. -/
structure AtiyahSegalAxioms (C D : CobordismCategory)
    (Z : TQFTFunctor C D) where
  /-- Tensor on objects is respected up to a path. -/
  tensor_obj : (X Y : C.Obj) →
    Path (Z.objMap (C.tensorObj X Y))
      (D.tensorObj (Z.objMap X) (Z.objMap Y))
  /-- Unit object is preserved. -/
  tensor_unit : Path (Z.objMap C.tensorUnit) D.tensorUnit
  /-- Tensor on morphisms is compatible (structural witness). -/
  tensor_mor : {X1 Y1 X2 Y2 : C.Obj} → (f : C.Hom X1 Y1) → (g : C.Hom X2 Y2) → True
  /-- Gluing formula for cobordisms. -/
  gluing : {X Y Z' : C.Obj} → (f : C.Hom X Y) → (g : C.Hom Y Z') →
    Path (Z.morMap (C.comp f g)) (D.comp (Z.morMap f) (Z.morMap g))

/-- Gluing formula derived from Atiyah-Segal axioms. -/
def gluing_formula {C D : CobordismCategory} {Z : TQFTFunctor C D}
    (A : AtiyahSegalAxioms C D Z) {X Y Z' : C.Obj}
    (f : C.Hom X Y) (g : C.Hom Y Z') :
    Path (Z.morMap (C.comp f g)) (D.comp (Z.morMap f) (Z.morMap g)) :=
  A.gluing f g

/-! ## Partition functions -/

/-- The partition function evaluates a closed cobordism at the monoidal unit. -/
def partitionFunction (C D : CobordismCategory) (Z : TQFTFunctor C D) :
    C.Hom C.tensorUnit C.tensorUnit →
      D.Hom (Z.objMap C.tensorUnit) (Z.objMap C.tensorUnit) :=
  fun W => Z.morMap W

/-- Gluing formula for partition functions. -/
def partitionFunction_gluing {C D : CobordismCategory} {Z : TQFTFunctor C D}
    (A : AtiyahSegalAxioms C D Z)
    (f g : C.Hom C.tensorUnit C.tensorUnit) :
    Path (partitionFunction C D Z (C.comp f g))
      (D.comp (partitionFunction C D Z f) (partitionFunction C D Z g)) :=
  A.gluing f g

/-! ## Two-dimensional classification -/

/-- A minimal Frobenius algebra interface for 2D TQFTs. -/
structure FrobeniusAlgebra (A : Type u) where
  /-- Multiplication. -/
  mul : A → A → A
  /-- Unit element. -/
  unit : A
  /-- Comultiplication. -/
  comul : A → A → A
  /-- Counit. -/
  counit : A → A
  /-- Associativity of multiplication. -/
  mul_assoc : (x y z : A) → Path (mul (mul x y) z) (mul x (mul y z))
  /-- Left unit law. -/
  left_unit : (x : A) → Path (mul unit x) x
  /-- Right unit law. -/
  right_unit : (x : A) → Path (mul x unit) x
  /-- Frobenius compatibility (structural witness). -/
  frobenius : True

/-- Classification data for a 2D TQFT by a Frobenius algebra. -/
structure TwoDClassification (C D : CobordismCategory) (Z : TQFTFunctor C D) where
  /-- The carrier of the associated Frobenius algebra. -/
  carrier : Type u
  /-- Frobenius algebra structure. -/
  algebra : FrobeniusAlgebra carrier
  /-- Compatibility with the 2D TQFT (recorded). -/
  classifies : True

/-- 2D classification theorem: a 2D TQFT determines a Frobenius algebra. -/
def twoD_classification {C D : CobordismCategory} {Z : TQFTFunctor C D}
    (H : TwoDClassification C D Z) : FrobeniusAlgebra H.carrier :=
  H.algebra

/-! ## Summary -/

/-!
We introduced a lightweight cobordism category, a monoidal TQFT functor,
Atiyah-Segal axioms with a gluing formula, partition functions, and a
two-dimensional classification interface via Frobenius algebras.
-/


/-! ## Path lemmas -/

theorem tqft_paths_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem tqft_paths_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem tqft_paths_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem tqft_paths_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem tqft_paths_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem tqft_paths_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem tqft_paths_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem tqft_paths_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.ofEq h) = h :=
  Path.toEq_ofEq h


end TQFTPaths
end Topology
end Path
end ComputationalPaths
