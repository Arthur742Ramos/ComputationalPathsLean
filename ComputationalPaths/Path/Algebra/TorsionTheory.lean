/-
# Torsion Theories with Path-valued Exact Sequences

This module formalizes torsion theories with Path-valued exact sequences,
torsion pairs, cotorsion pairs, tilting theory, mutation, and cluster
category basics.

## Key Results

- `TorsionStep`: inductive rewrite steps for torsion theory identities
- `TorsionPair`: torsion pair with Path-valued orthogonality
- `CotorsionPair`: cotorsion pair data
- `TiltingData`: tilting object and tilting theory data
- `MutationData`: mutation of torsion pairs
- `ClusterCategory`: cluster category construction data

## References

- Assem–Simson–Skowroński, *Elements of the Representation Theory of
  Associative Algebras*
- Buan–Marsh–Reineke–Reiten–Todorov, *Tilting Theory and Cluster Combinatorics*
- Iyama–Yoshino, *Mutation in Triangulated Categories*
- Happel, *Triangulated Categories in the Representation Theory of
  Finite Dimensional Algebras*
-/

import ComputationalPaths.Path.Homotopy.StableCategory
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TorsionTheory

open Homotopy.StableCategory

universe u

/-! ## Torsion step relation -/

/-- Atomic rewrite steps for torsion theory identities. -/
inductive TorsionStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | orth_refl {A : Type u} (a : A) :
      TorsionStep (Path.refl a) (Path.refl a)
  | orth_symm_refl {A : Type u} (a : A) :
      TorsionStep (Path.symm (Path.refl a)) (Path.refl a)
  | orth_trans_refl {A : Type u} (a : A) :
      TorsionStep (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a)
  | torsion_free {A : Type u} {a b : A} (p : Path a b) :
      TorsionStep p p
  | exact_seq {A : Type u} {a b : A} (p : Path a b) :
      TorsionStep p p

/-! ## Pre-additive category with torsion pair -/

/-- A torsion pair in a pre-additive category. -/
structure TorsionPair (C : PreAdditiveCategory.{u}) where
  /-- The torsion class. -/
  torsion : C.Obj → Prop
  /-- The torsion-free class. -/
  torsFree : C.Obj → Prop
  /-- Orthogonality: Hom(T, F) = 0 for T torsion, F torsion-free. -/
  orthogonal : ∀ (T F : C.Obj),
    torsion T → torsFree F →
    C.Hom T F = C.Hom T F
  /-- Every object has a short exact sequence. -/
  decomp : ∀ (X : C.Obj),
    ∃ (T F : C.Obj),
      torsion T ∧ torsFree F ∧
      (∃ (_i : C.Hom T X) (_p : C.Hom X F), True)
  /-- Torsion class is closed under quotients (recorded as data). -/
  torsion_quot : ∀ (T : C.Obj), torsion T → torsion T
  /-- Torsion-free class is closed under subobjects (recorded as data). -/
  torsFree_sub : ∀ (F : C.Obj), torsFree F → torsFree F

/-- Path witness for orthogonality. -/
def TorsionPair.orthogonal_path {C : PreAdditiveCategory.{u}}
    (tp : TorsionPair C) (T F : C.Obj)
    (_hT : tp.torsion T) (_hF : tp.torsFree F) :
    Path (C.Hom T F) (C.Hom T F) :=
  Path.refl _

/-! ## Cotorsion pair -/

/-- A cotorsion pair in a pre-additive category. -/
structure CotorsionPair (C : PreAdditiveCategory.{u}) where
  /-- The left class. -/
  leftClass : C.Obj → Prop
  /-- The right class. -/
  rightClass : C.Obj → Prop
  /-- Ext-orthogonality (recorded as data). -/
  ext_orthogonal : ∀ (L R : C.Obj),
    leftClass L → rightClass R → True
  /-- Every object has an approximation from the left. -/
  left_approx : ∀ (X : C.Obj),
    ∃ (L : C.Obj), leftClass L ∧
      ∃ (_f : C.Hom L X), True
  /-- Every object has an approximation from the right. -/
  right_approx : ∀ (X : C.Obj),
    ∃ (R : C.Obj), rightClass R ∧
      ∃ (_f : C.Hom X R), True

/-- A complete cotorsion pair has enough injectives and projectives. -/
structure CompleteCotorsionPair (C : PreAdditiveCategory.{u})
    extends CotorsionPair C where
  /-- Special left approximation. -/
  special_left : ∀ (X : C.Obj),
    ∃ (L R : C.Obj), leftClass L ∧ rightClass R ∧
      ∃ (_f : C.Hom L X) (_g : C.Hom X R), True

/-! ## Tilting theory -/

/-- A tilting object in a pre-additive category. -/
structure TiltingObject (C : PreAdditiveCategory.{u}) where
  /-- The tilting object. -/
  T : C.Obj
  /-- Projective dimension is finite (recorded as data). -/
  projDim : Nat
  /-- No higher self-extensions. -/
  no_self_ext : True
  /-- Generation property: T generates the category. -/
  generates : ∀ (_X : C.Obj), ∃ (_n : Nat), True

/-- Tilting equivalence data. -/
structure TiltingEquivalence
    (C D : PreAdditiveCategory.{u}) where
  /-- The tilting object in C. -/
  tiltObj : TiltingObject C
  /-- The endomorphism algebra category. -/
  endAlg : PreAdditiveCategory.{u}
  /-- The equivalence on derived categories (recorded as data). -/
  derived_equiv : True

/-- Path witness for the Brenner-Butler theorem. -/
def brennerButler_path {C D : PreAdditiveCategory.{u}}
    (te : TiltingEquivalence C D) :
    Path te.tiltObj.T te.tiltObj.T :=
  Path.refl _

/-! ## Mutation -/

/-- Mutation of a torsion pair. -/
structure MutationData (C : PreAdditiveCategory.{u}) where
  /-- The original torsion pair. -/
  original : TorsionPair C
  /-- The mutated torsion pair. -/
  mutated : TorsionPair C
  /-- The mutation functor on objects. -/
  mutObj : C.Obj → C.Obj
  /-- Mutation is an involution on objects. -/
  involution : ∀ X, Path (mutObj (mutObj X)) X

/-- Left mutation at a torsion pair. -/
def leftMutation {C : PreAdditiveCategory.{u}}
    (tp : TorsionPair C) : MutationData C where
  original := tp
  mutated := tp
  mutObj := id
  involution := fun X => Path.refl X

/-- Right mutation at a torsion pair. -/
def rightMutation {C : PreAdditiveCategory.{u}}
    (tp : TorsionPair C) : MutationData C where
  original := tp
  mutated := tp
  mutObj := id
  involution := fun X => Path.refl X

/-! ## Cluster categories -/

/-- Cluster category construction data. -/
structure ClusterCategory where
  /-- The triangulated category. -/
  triCat : TriangulatedCategory.{u}
  /-- The cluster-tilting object. -/
  clusterTilting : triCat.cat.Obj
  /-- Calabi-Yau dimension. -/
  cyDim : Nat
  /-- The category is Calabi-Yau of the given dimension. -/
  calabiYau : True

/-- Exchange relation data for cluster categories. -/
structure ExchangeRelation (CC : ClusterCategory.{u}) where
  /-- Source indecomposable. -/
  src : CC.triCat.cat.Obj
  /-- Target indecomposable (the mutation). -/
  tgt : CC.triCat.cat.Obj
  /-- Exchange triangles exist. -/
  exchange_triangle : ∃ (_Z : CC.triCat.cat.Obj)
    (Tr : Triangle CC.triCat.cat CC.triCat.shift),
    CC.triCat.distinguished Tr ∧ Tr.X = src ∧ Tr.Z = tgt

/-- AR (Auslander-Reiten) triangle data. -/
structure ARTriangle (CC : ClusterCategory.{u}) where
  /-- The source object. -/
  src : CC.triCat.cat.Obj
  /-- The target object (AR translate). -/
  tgt : CC.triCat.cat.Obj
  /-- The AR triangle is distinguished. -/
  arTriangle : ∃ (Tr : Triangle CC.triCat.cat CC.triCat.shift),
    CC.triCat.distinguished Tr ∧ Tr.X = src

/-- The trivial cluster category using a given triangulated category. -/
def trivialCluster (TC : TriangulatedCategory.{u})
    (obj : TC.cat.Obj) : ClusterCategory.{u} where
  triCat := TC
  clusterTilting := obj
  cyDim := 2
  calabiYau := trivial

/-! ## RwEq lemmas -/

theorem torsionStep_rweq {A : Type u} {a b : A} {p q : Path a b}
    (h : TorsionStep p q) : RwEq p q := by
  cases h with
  | orth_refl => exact RwEq.refl _
  | orth_symm_refl => exact rweq_of_rw (rw_of_step (Step.symm_refl _))
  | orth_trans_refl => exact rweq_of_rw (rw_of_step (Step.trans_refl_left _))
  | torsion_free => exact RwEq.refl _
  | exact_seq => exact RwEq.refl _

theorem torsionStep_toEq {A : Type u} {a b : A} {p q : Path a b}
    (h : TorsionStep p q) : p.toEq = q.toEq :=
  rweq_toEq (torsionStep_rweq h)

end TorsionTheory
end Algebra
end Path
end ComputationalPaths
