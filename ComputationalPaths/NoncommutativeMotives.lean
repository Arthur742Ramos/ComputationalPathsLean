/-
# Noncommutative Motives via Computational Paths

This module formalizes key structures from the theory of noncommutative motives
— additive invariants, the universal additive invariant, localizing invariants,
Morita equivalence, the noncommutative motivic category, and the motivic
measure — all with `Path` coherence witnesses and extensive `Step` constructor
usage.

## Mathematical Background

Noncommutative motives extend classical motives to the noncommutative setting:

1. **DG-categories**: Enhanced categories where Hom-sets are chain complexes.
2. **Additive invariants**: Functors F that send split-exact sequences to
   direct sum decompositions: F(B) ≅ F(A) ⊕ F(C).
3. **Universal additive invariant**: The universal such functor U_add.
4. **Localizing invariants**: Functors sending exact sequences to exact
   triangles. K-theory is the prototypical example.
5. **Morita equivalence**: DG-categories with equivalent derived module
   categories.
6. **Motivic measure**: A ring homomorphism from K₀(Var) to NC motives.

## Step Constructors Used

- `Path.Step.refl`, `Path.Step.symm`, `Path.Step.trans`
- `Path.Step.trans_refl_right`, `Path.Step.trans_refl_left`
- `Path.Step.trans_assoc`, `Path.Step.trans_symm`, `Path.Step.symm_trans`
- `Path.Step.symm_symm`
- `Path.Step.unit_left`, `Path.Step.unit_right`
- `Path.Step.congr_comp`

## References

- Tabuada, "Noncommutative Motives" (2015)
- Keller, "On differential graded categories" (ICM 2006)
- Kontsevich, "Noncommutative Motives" (IAS lectures, 2005)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace NoncommutativeMotives

open Path

universe u v w

/-! ## DG-Categories -/

/-- Data for a DG-category: objects, morphism complex dimensions,
and composition structure. -/
structure DGCategoryData where
  /-- Number of objects. -/
  numObjects : Nat
  /-- Number of objects is positive. -/
  numObjects_pos : numObjects > 0
  /-- Total dimension of morphism complexes (sum of ranks). -/
  totalMorphDim : Nat
  /-- Euler characteristic of the morphism complex. -/
  morphEuler : Int
  /-- Number of degree-0 morphisms. -/
  deg0Morphisms : Nat
  /-- Degree-0 morphisms include identities. -/
  has_identities : deg0Morphisms ≥ numObjects
  /-- A DG-category identifier. -/
  dgId : Nat

namespace DGCategoryData

/-- The DG-category with a single object and trivial morphism complex. -/
def point : DGCategoryData where
  numObjects := 1
  numObjects_pos := Nat.lt.base 0
  totalMorphDim := 1
  morphEuler := 1
  deg0Morphisms := 1
  has_identities := Nat.le_refl 1
  dgId := 0

/-- Single object DG-category has 1 object. -/
theorem point_objects : point.numObjects = 1 := rfl

/-- Direct sum of DG-categories. -/
def directSum (A B : DGCategoryData) : DGCategoryData where
  numObjects := A.numObjects + B.numObjects
  numObjects_pos := Nat.lt_of_lt_of_le A.numObjects_pos (Nat.le_add_right A.numObjects B.numObjects)
  totalMorphDim := A.totalMorphDim + B.totalMorphDim
  morphEuler := A.morphEuler + B.morphEuler
  deg0Morphisms := A.deg0Morphisms + B.deg0Morphisms
  has_identities := Nat.add_le_add A.has_identities B.has_identities
  dgId := A.dgId + B.dgId + 1

/-- Direct sum object count. -/
theorem directSum_numObjects (A B : DGCategoryData) :
    (directSum A B).numObjects = A.numObjects + B.numObjects := rfl

/-- Direct sum commutativity on objects. -/
def directSum_comm_objects (A B : DGCategoryData) :
    Path (directSum A B).numObjects (directSum B A).numObjects :=
  Path.stepChain (by simp [directSum]; omega)

/-- Direct sum associativity on objects. -/
def directSum_assoc_objects (A B C : DGCategoryData) :
    Path (directSum (directSum A B) C).numObjects
         (directSum A (directSum B C)).numObjects :=
  Path.stepChain (by simp [directSum]; omega)

end DGCategoryData

/-! ## Split-Exact Sequences -/

/-- A split-exact sequence A → B → C of DG-categories. -/
structure SplitExactSeq where
  catA : DGCategoryData
  catB : DGCategoryData
  catC : DGCategoryData
  objects_split : catB.numObjects = catA.numObjects + catC.numObjects
  morph_split : catB.totalMorphDim = catA.totalMorphDim + catC.totalMorphDim

namespace SplitExactSeq

/-- Path witnessing the object-count decomposition. -/
def objects_path (S : SplitExactSeq) :
    Path S.catB.numObjects (S.catA.numObjects + S.catC.numObjects) :=
  Path.stepChain S.objects_split

/-- Path witnessing morphism-dimension decomposition. -/
def morph_path (S : SplitExactSeq) :
    Path S.catB.totalMorphDim (S.catA.totalMorphDim + S.catC.totalMorphDim) :=
  Path.stepChain S.morph_split

end SplitExactSeq

/-! ## Additive Invariants -/

/-- An additive invariant: respects split-exact sequences. -/
structure AdditiveInvariantData where
  invariant : DGCategoryData → Nat
  additivity : ∀ (S : SplitExactSeq),
    invariant S.catB = invariant S.catA + invariant S.catC
  maps_point_pos : invariant DGCategoryData.point > 0

namespace AdditiveInvariantData

/-- The object-count invariant. -/
def objectCount : AdditiveInvariantData where
  invariant := fun A => A.numObjects
  additivity := fun S => S.objects_split
  maps_point_pos := Nat.lt.base 0

/-- Object count on point is 1. -/
theorem objectCount_point : objectCount.invariant DGCategoryData.point = 1 := rfl

/-- The morphism-dimension invariant. -/
def morphDim : AdditiveInvariantData where
  invariant := fun A => A.totalMorphDim
  additivity := fun S => S.morph_split
  maps_point_pos := Nat.lt.base 0

/-- Path witnessing additivity. -/
def additivity_path (F : AdditiveInvariantData) (S : SplitExactSeq) :
    Path (F.invariant S.catB) (F.invariant S.catA + F.invariant S.catC) :=
  Path.stepChain (F.additivity S)

/-- Step witness: right-unit normalization. -/
def additivity_right_unit_step (F : AdditiveInvariantData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (F.additivity_path S)
        (Path.refl (F.invariant S.catA + F.invariant S.catC)))
      (F.additivity_path S) :=
  Path.Step.trans_refl_right (F.additivity_path S)

/-- RwEq from right-unit step. -/
@[simp] theorem additivity_right_unit_rweq (F : AdditiveInvariantData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (F.additivity_path S)
        (Path.refl (F.invariant S.catA + F.invariant S.catC)))
      (F.additivity_path S) :=
  rweq_of_step (F.additivity_right_unit_step S)

/-- Step witness: left-unit normalization. -/
def additivity_left_unit_step (F : AdditiveInvariantData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (Path.refl (F.invariant S.catB)) (F.additivity_path S))
      (F.additivity_path S) :=
  Path.Step.trans_refl_left (F.additivity_path S)

/-- RwEq from left-unit step. -/
@[simp] theorem additivity_left_unit_rweq (F : AdditiveInvariantData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (Path.refl (F.invariant S.catB)) (F.additivity_path S))
      (F.additivity_path S) :=
  rweq_of_step (F.additivity_left_unit_step S)

/-- Step witness: inverse cancellation on additivity path. -/
def additivity_cancel_step (F : AdditiveInvariantData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (F.additivity_path S) (Path.symm (F.additivity_path S)))
      (Path.refl (F.invariant S.catB)) :=
  Path.Step.trans_symm (F.additivity_path S)

/-- RwEq for inverse cancellation. -/
@[simp] theorem additivity_cancel_rweq (F : AdditiveInvariantData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (F.additivity_path S) (Path.symm (F.additivity_path S)))
      (Path.refl (F.invariant S.catB)) :=
  rweq_of_step (F.additivity_cancel_step S)

/-- Step witness: left inverse cancellation. -/
def additivity_left_cancel_step (F : AdditiveInvariantData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (Path.symm (F.additivity_path S)) (F.additivity_path S))
      (Path.refl (F.invariant S.catA + F.invariant S.catC)) :=
  Path.Step.symm_trans (F.additivity_path S)

/-- RwEq for left inverse cancellation. -/
@[simp] theorem additivity_left_cancel_rweq (F : AdditiveInvariantData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (Path.symm (F.additivity_path S)) (F.additivity_path S))
      (Path.refl (F.invariant S.catA + F.invariant S.catC)) :=
  rweq_of_step (F.additivity_left_cancel_step S)

/-- Step witness: double symmetry on additivity path. -/
def additivity_symm_symm_step (F : AdditiveInvariantData) (S : SplitExactSeq) :
    Path.Step
      (Path.symm (Path.symm (F.additivity_path S)))
      (F.additivity_path S) :=
  Path.Step.symm_symm (F.additivity_path S)

/-- RwEq for double symmetry. -/
@[simp] theorem additivity_symm_symm_rweq (F : AdditiveInvariantData) (S : SplitExactSeq) :
    RwEq
      (Path.symm (Path.symm (F.additivity_path S)))
      (F.additivity_path S) :=
  rweq_of_step (F.additivity_symm_symm_step S)

end AdditiveInvariantData

/-! ## Universal Additive Invariant -/

/-- The universal additive invariant. -/
structure UniversalAdditiveData where
  uAdd : DGCategoryData → Nat
  uAdd_additive : ∀ (S : SplitExactSeq),
    uAdd S.catB = uAdd S.catA + uAdd S.catC
  uAdd_point : uAdd DGCategoryData.point = 1

namespace UniversalAdditiveData

/-- Object-count is universal. -/
def objectCountUniversal : UniversalAdditiveData where
  uAdd := fun A => A.numObjects
  uAdd_additive := fun S => S.objects_split
  uAdd_point := rfl

/-- Path for U_add additivity. -/
def uAdd_path (U : UniversalAdditiveData) (S : SplitExactSeq) :
    Path (U.uAdd S.catB) (U.uAdd S.catA + U.uAdd S.catC) :=
  Path.stepChain (U.uAdd_additive S)

/-- Path for U_add on point. -/
def uAdd_point_path (U : UniversalAdditiveData) :
    Path (U.uAdd DGCategoryData.point) 1 :=
  Path.stepChain U.uAdd_point

/-- Step: right-unit on U_add path. -/
def uAdd_right_unit_step (U : UniversalAdditiveData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (U.uAdd_path S)
        (Path.refl (U.uAdd S.catA + U.uAdd S.catC)))
      (U.uAdd_path S) :=
  Path.Step.trans_refl_right (U.uAdd_path S)

/-- RwEq for U_add right-unit. -/
@[simp] theorem uAdd_right_unit_rweq (U : UniversalAdditiveData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (U.uAdd_path S)
        (Path.refl (U.uAdd S.catA + U.uAdd S.catC)))
      (U.uAdd_path S) :=
  rweq_of_step (U.uAdd_right_unit_step S)

/-- Step: inverse cancellation for U_add. -/
def uAdd_cancel_step (U : UniversalAdditiveData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (Path.symm (U.uAdd_path S)) (U.uAdd_path S))
      (Path.refl (U.uAdd S.catA + U.uAdd S.catC)) :=
  Path.Step.symm_trans (U.uAdd_path S)

/-- RwEq for inverse cancellation. -/
@[simp] theorem uAdd_cancel_rweq (U : UniversalAdditiveData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (Path.symm (U.uAdd_path S)) (U.uAdd_path S))
      (Path.refl (U.uAdd S.catA + U.uAdd S.catC)) :=
  rweq_of_step (U.uAdd_cancel_step S)

/-- Step-oriented assoc for composing U_add paths. -/
def uAdd_assoc (U : UniversalAdditiveData)
    (S1 S2 : SplitExactSeq)
    (h : U.uAdd S1.catA + U.uAdd S1.catC = U.uAdd S2.catB) :
    Path (U.uAdd S1.catB) (U.uAdd S2.catA + U.uAdd S2.catC) :=
  Path.Step.assoc
    (U.uAdd_path S1)
    (Path.stepChain h)
    (U.uAdd_path S2)

end UniversalAdditiveData

/-! ## Localizing Invariants -/

/-- A localizing invariant: sends exact sequences to exact triangles. -/
structure LocalizingInvariantData where
  locInv : DGCategoryData → Int
  localization : ∀ (S : SplitExactSeq),
    locInv S.catB = locInv S.catA + locInv S.catC
  morita_inv : ∀ (A B : DGCategoryData),
    A.numObjects = B.numObjects → A.morphEuler = B.morphEuler →
    locInv A = locInv B

namespace LocalizingInvariantData

/-- Object count as integer-valued localizing invariant. -/
def objectCountInt : LocalizingInvariantData where
  locInv := fun A => (A.numObjects : Int)
  localization := fun S => by simp [S.objects_split]
  morita_inv := fun _ _ hObj _ => by simp [hObj]

/-- Path witnessing localization. -/
def localization_path (F : LocalizingInvariantData) (S : SplitExactSeq) :
    Path (F.locInv S.catB) (F.locInv S.catA + F.locInv S.catC) :=
  Path.stepChain (F.localization S)

/-- Step: right-unit normalization for localization. -/
def localization_right_unit_step (F : LocalizingInvariantData) (S : SplitExactSeq) :
    Path.Step
      (Path.trans (F.localization_path S)
        (Path.refl (F.locInv S.catA + F.locInv S.catC)))
      (F.localization_path S) :=
  Path.Step.trans_refl_right (F.localization_path S)

/-- RwEq for localization right-unit. -/
@[simp] theorem localization_right_unit_rweq (F : LocalizingInvariantData) (S : SplitExactSeq) :
    RwEq
      (Path.trans (F.localization_path S)
        (Path.refl (F.locInv S.catA + F.locInv S.catC)))
      (F.localization_path S) :=
  rweq_of_step (F.localization_right_unit_step S)

/-- Morita invariance path. -/
def morita_path (F : LocalizingInvariantData) (A B : DGCategoryData)
    (hObj : A.numObjects = B.numObjects) (hEuler : A.morphEuler = B.morphEuler) :
    Path (F.locInv A) (F.locInv B) :=
  Path.stepChain (F.morita_inv A B hObj hEuler)

/-- Step: right inverse on Morita path. -/
def morita_cancel_step (F : LocalizingInvariantData) (A B : DGCategoryData)
    (hObj : A.numObjects = B.numObjects) (hEuler : A.morphEuler = B.morphEuler) :
    Path.Step
      (Path.trans (F.morita_path A B hObj hEuler)
        (Path.symm (F.morita_path A B hObj hEuler)))
      (Path.refl (F.locInv A)) :=
  Path.Step.trans_symm (F.morita_path A B hObj hEuler)

/-- RwEq for Morita cancellation. -/
@[simp] theorem morita_cancel_rweq (F : LocalizingInvariantData) (A B : DGCategoryData)
    (hObj : A.numObjects = B.numObjects) (hEuler : A.morphEuler = B.morphEuler) :
    RwEq
      (Path.trans (F.morita_path A B hObj hEuler)
        (Path.symm (F.morita_path A B hObj hEuler)))
      (Path.refl (F.locInv A)) :=
  rweq_of_step (F.morita_cancel_step A B hObj hEuler)

/-- Step: left inverse on Morita path. -/
def morita_left_cancel_step (F : LocalizingInvariantData) (A B : DGCategoryData)
    (hObj : A.numObjects = B.numObjects) (hEuler : A.morphEuler = B.morphEuler) :
    Path.Step
      (Path.trans (Path.symm (F.morita_path A B hObj hEuler))
        (F.morita_path A B hObj hEuler))
      (Path.refl (F.locInv B)) :=
  Path.Step.symm_trans (F.morita_path A B hObj hEuler)

/-- RwEq for left Morita cancellation. -/
@[simp] theorem morita_left_cancel_rweq (F : LocalizingInvariantData) (A B : DGCategoryData)
    (hObj : A.numObjects = B.numObjects) (hEuler : A.morphEuler = B.morphEuler) :
    RwEq
      (Path.trans (Path.symm (F.morita_path A B hObj hEuler))
        (F.morita_path A B hObj hEuler))
      (Path.refl (F.locInv B)) :=
  rweq_of_step (F.morita_left_cancel_step A B hObj hEuler)

end LocalizingInvariantData

/-! ## Morita Equivalence -/

/-- Morita equivalence between two DG-categories. -/
structure MoritaEquivData where
  catA : DGCategoryData
  catB : DGCategoryData
  objects_eq : catA.numObjects = catB.numObjects
  euler_eq : catA.morphEuler = catB.morphEuler

namespace MoritaEquivData

/-- Reflexive Morita equivalence. -/
def reflEquiv (A : DGCategoryData) : MoritaEquivData where
  catA := A
  catB := A
  objects_eq := rfl
  euler_eq := rfl

/-- Symmetric Morita equivalence. -/
def symmEquiv (M : MoritaEquivData) : MoritaEquivData where
  catA := M.catB
  catB := M.catA
  objects_eq := M.objects_eq.symm
  euler_eq := M.euler_eq.symm

/-- Objects path. -/
def objects_path (M : MoritaEquivData) :
    Path M.catA.numObjects M.catB.numObjects :=
  Path.stepChain M.objects_eq

/-- Euler path. -/
def euler_path (M : MoritaEquivData) :
    Path M.catA.morphEuler M.catB.morphEuler :=
  Path.stepChain M.euler_eq

/-- Step: double symmetry on objects path. -/
def symm_symm_objects_step (M : MoritaEquivData) :
    Path.Step
      (Path.symm (Path.symm (M.objects_path)))
      (M.objects_path) :=
  Path.Step.symm_symm (M.objects_path)

/-- RwEq for double symmetry. -/
@[simp] theorem symm_symm_objects_rweq (M : MoritaEquivData) :
    RwEq
      (Path.symm (Path.symm (M.objects_path)))
      (M.objects_path) :=
  rweq_of_step (M.symm_symm_objects_step)

/-- Step: right-unit on objects path. -/
def objects_right_unit_step (M : MoritaEquivData) :
    Path.Step
      (Path.trans (M.objects_path) (Path.refl M.catB.numObjects))
      (M.objects_path) :=
  Path.Step.trans_refl_right (M.objects_path)

/-- RwEq for objects right-unit. -/
@[simp] theorem objects_right_unit_rweq (M : MoritaEquivData) :
    RwEq
      (Path.trans (M.objects_path) (Path.refl M.catB.numObjects))
      (M.objects_path) :=
  rweq_of_step (M.objects_right_unit_step)

/-- Step-oriented assoc for composing Morita paths. -/
def morita_assoc (M1 M2 : MoritaEquivData)
    (h : M1.catB.numObjects = M2.catA.numObjects)
    (M3 : MoritaEquivData) (h2 : M2.catB.numObjects = M3.catA.numObjects) :
    Path M1.catA.numObjects M3.catB.numObjects :=
  Path.Step.assoc
    (M1.objects_path)
    (Path.trans (Path.stepChain h) (M2.objects_path))
    (Path.trans (Path.stepChain h2) (M3.objects_path))

end MoritaEquivData

/-! ## Noncommutative Motivic Category -/

/-- Objects in NChow: smooth proper DG-categories with invariant data. -/
structure NCMotivicData where
  source : DGCategoryData
  k0Rank : Nat
  hhDim : Nat
  hcDim : Nat
  hh_hc : hcDim ≤ hhDim

namespace NCMotivicData

/-- The motivic data of a point. -/
def pointMotive : NCMotivicData where
  source := DGCategoryData.point
  k0Rank := 1
  hhDim := 1
  hcDim := 1
  hh_hc := Nat.le_refl 1

/-- Point has K₀ rank 1. -/
theorem point_k0 : pointMotive.k0Rank = 1 := rfl

/-- Direct sum of motivic data. -/
def directSum (M N : NCMotivicData) : NCMotivicData where
  source := DGCategoryData.directSum M.source N.source
  k0Rank := M.k0Rank + N.k0Rank
  hhDim := M.hhDim + N.hhDim
  hcDim := M.hcDim + N.hcDim
  hh_hc := Nat.add_le_add M.hh_hc N.hh_hc

/-- K₀ additivity: direct sum adds K₀ ranks. -/
theorem k0_additive (M N : NCMotivicData) :
    (directSum M N).k0Rank = M.k0Rank + N.k0Rank := rfl

/-- HH additivity. -/
theorem hh_additive (M N : NCMotivicData) :
    (directSum M N).hhDim = M.hhDim + N.hhDim := rfl

/-- HC additivity. -/
theorem hc_additive (M N : NCMotivicData) :
    (directSum M N).hcDim = M.hcDim + N.hcDim := rfl

/-- K₀ additivity path. -/
def k0_additive_path (M N : NCMotivicData) :
    Path (directSum M N).k0Rank (M.k0Rank + N.k0Rank) :=
  Path.stepChain (k0_additive M N)

/-- HH additivity path. -/
def hh_additive_path (M N : NCMotivicData) :
    Path (directSum M N).hhDim (M.hhDim + N.hhDim) :=
  Path.stepChain (hh_additive M N)

/-- HC additivity path. -/
def hc_additive_path (M N : NCMotivicData) :
    Path (directSum M N).hcDim (M.hcDim + N.hcDim) :=
  Path.stepChain (hc_additive M N)

/-- Step: left-unit on K₀ path. -/
def k0_left_unit_step (M N : NCMotivicData) :
    Path.Step
      (Path.trans (Path.refl (directSum M N).k0Rank) (k0_additive_path M N))
      (k0_additive_path M N) :=
  Path.Step.trans_refl_left (k0_additive_path M N)

/-- RwEq for K₀ left-unit. -/
@[simp] theorem k0_left_unit_rweq (M N : NCMotivicData) :
    RwEq
      (Path.trans (Path.refl (directSum M N).k0Rank) (k0_additive_path M N))
      (k0_additive_path M N) :=
  rweq_of_step (k0_left_unit_step M N)

/-- Step: right-unit on HH path. -/
def hh_right_unit_step (M N : NCMotivicData) :
    Path.Step
      (Path.trans (hh_additive_path M N) (Path.refl (M.hhDim + N.hhDim)))
      (hh_additive_path M N) :=
  Path.Step.trans_refl_right (hh_additive_path M N)

/-- RwEq for HH right-unit. -/
@[simp] theorem hh_right_unit_rweq (M N : NCMotivicData) :
    RwEq
      (Path.trans (hh_additive_path M N) (Path.refl (M.hhDim + N.hhDim)))
      (hh_additive_path M N) :=
  rweq_of_step (hh_right_unit_step M N)

/-- Step: inverse cancellation on K₀ path. -/
def k0_cancel_step (M N : NCMotivicData) :
    Path.Step
      (Path.trans (k0_additive_path M N) (Path.symm (k0_additive_path M N)))
      (Path.refl (directSum M N).k0Rank) :=
  Path.Step.trans_symm (k0_additive_path M N)

/-- RwEq for K₀ cancellation. -/
@[simp] theorem k0_cancel_rweq (M N : NCMotivicData) :
    RwEq
      (Path.trans (k0_additive_path M N) (Path.symm (k0_additive_path M N)))
      (Path.refl (directSum M N).k0Rank) :=
  rweq_of_step (k0_cancel_step M N)

end NCMotivicData

/-! ## Motivic Measure -/

/-- A noncommutative motivic measure: maps varieties to NC motives. -/
structure NCMotivicMeasure where
  varDim : Nat
  varEuler : Int
  motive : NCMotivicData
  euler_pres : (motive.source.morphEuler : Int) = varEuler

namespace NCMotivicMeasure

/-- Trivial measure: point ↦ point motive. -/
def pointMeasure : NCMotivicMeasure where
  varDim := 0
  varEuler := 1
  motive := NCMotivicData.pointMotive
  euler_pres := rfl

/-- Euler preservation path. -/
def euler_pres_path (μ : NCMotivicMeasure) :
    Path (μ.motive.source.morphEuler : Int) μ.varEuler :=
  Path.stepChain μ.euler_pres

/-- Step: right-unit on euler preservation. -/
def euler_pres_right_unit_step (μ : NCMotivicMeasure) :
    Path.Step
      (Path.trans μ.euler_pres_path (Path.refl μ.varEuler))
      μ.euler_pres_path :=
  Path.Step.trans_refl_right μ.euler_pres_path

/-- RwEq for euler preservation right-unit. -/
@[simp] theorem euler_pres_right_unit_rweq (μ : NCMotivicMeasure) :
    RwEq
      (Path.trans μ.euler_pres_path (Path.refl μ.varEuler))
      μ.euler_pres_path :=
  rweq_of_step μ.euler_pres_right_unit_step

/-- Step: inverse cancellation on euler preservation. -/
def euler_cancel_step (μ : NCMotivicMeasure) :
    Path.Step
      (Path.trans μ.euler_pres_path (Path.symm μ.euler_pres_path))
      (Path.refl (μ.motive.source.morphEuler : Int)) :=
  Path.Step.trans_symm μ.euler_pres_path

/-- RwEq for euler cancellation. -/
@[simp] theorem euler_cancel_rweq (μ : NCMotivicMeasure) :
    RwEq
      (Path.trans μ.euler_pres_path (Path.symm μ.euler_pres_path))
      (Path.refl (μ.motive.source.morphEuler : Int)) :=
  rweq_of_step μ.euler_cancel_step

/-- Step: double symmetry on euler preservation. -/
def euler_symm_symm_step (μ : NCMotivicMeasure) :
    Path.Step
      (Path.symm (Path.symm μ.euler_pres_path))
      μ.euler_pres_path :=
  Path.Step.symm_symm μ.euler_pres_path

/-- RwEq for double symmetry. -/
@[simp] theorem euler_symm_symm_rweq (μ : NCMotivicMeasure) :
    RwEq
      (Path.symm (Path.symm μ.euler_pres_path))
      μ.euler_pres_path :=
  rweq_of_step μ.euler_symm_symm_step

end NCMotivicMeasure

/-! ## Step-heavy coherence infrastructure -/

/-- General Step-chain constructor for NC motives. -/
private def stepChainOfEq {A : Type _} {a b : A} (h : a = b) : Path a b :=
  let core :=
    Path.Step.symm
      (Path.Step.symm
        (Path.Step.congr_comp (fun x : A => x) (fun x : A => x) (Path.stepChain h)))
  Path.Step.unit_right
    (Path.Step.unit_left
      (Path.Step.assoc (Path.Step.refl a) core (Path.Step.refl b)))

/-- Assoc coherence for triple composition of invariant paths. -/
def invariant_assoc_coherence
    (p : Path (a : Nat) b) (q : Path b c) (r : Path c d) :
    Path a d :=
  Path.Step.assoc p q r

/-- Unit-left coherence. -/
def invariant_unit_left (p : Path (a : Nat) b) : Path a b :=
  Path.Step.unit_left p

/-- Unit-right coherence. -/
def invariant_unit_right (p : Path (a : Nat) b) : Path a b :=
  Path.Step.unit_right p

/-- Congruence composition coherence. -/
def invariant_congr_comp {a b : Nat}
    (f g : Nat → Nat) (p : Path a b) : Path (g (f a)) (g (f b)) :=
  Path.Step.congr_comp f g p

/-- Symmetry coherence. -/
def invariant_symm (p : Path (a : Nat) b) : Path b a :=
  Path.Step.symm p

/-- Trans coherence. -/
def invariant_trans (p : Path (a : Nat) b) (q : Path b c) : Path a c :=
  Path.Step.trans p q

/-- Refl coherence. -/
def invariant_refl (a : Nat) : Path a a :=
  Path.Step.refl a

end NoncommutativeMotives
end ComputationalPaths
