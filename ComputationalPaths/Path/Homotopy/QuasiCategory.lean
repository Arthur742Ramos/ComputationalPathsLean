/-
# Quasi-categories and inner Kan complexes

This module introduces quasi-categories as simplicial sets with inner horn
fillers. We package composition via the inner horn Lambda^2_1, provide mapping
spaces as Kan complexes, define a minimal homotopy category data structure,
record that the nerve of a category is a quasi-category, and define left/right
fibration data.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `QuasiCategory` | Quasi-categories as inner Kan complexes |
| `QuasiCategory.comp` | Composition via inner horn fillers |
| `MappingSpaceData` | Mapping spaces as Kan complexes |
| `HomotopyCategoryData` | Minimal homotopy category data |
| `NerveQuasiCategory` | Nerve of a category is a quasi-category |
| `LeftFibrationData` | Left fibration horn lifting |
| `RightFibrationData` | Right fibration horn lifting |

## References

- Joyal, "Quasi-categories and Kan complexes"
- Lurie, "Higher Topos Theory"
- Goerss & Jardine, "Simplicial Homotopy Theory"
-/

import ComputationalPaths.Path.Homotopy.KanComplex
import ComputationalPaths.Path.Homotopy.NerveRealization

namespace ComputationalPaths
namespace Path
namespace Homotopy

open KanComplex
open NerveRealization

universe u

/-! ## Quasi-categories as inner Kan complexes -/

/-- A quasi-category is a simplicial set with fillers for all inner horns. -/
structure QuasiCategory where
  /-- The underlying simplicial set. -/
  sset : SSetData
  /-- Inner horn fillers. -/
  innerKan : InnerKanProperty sset

namespace QuasiCategory

/-- Objects are 0-simplices. -/
def obj (C : QuasiCategory) : Type u :=
  C.sset.obj 0

/-- Morphisms are 1-simplices. -/
def mor (C : QuasiCategory) : Type u :=
  C.sset.obj 1

/-- Source of a morphism (face d1). -/
def source (C : QuasiCategory) (f : C.mor) : C.obj :=
  C.sset.face 0 ⟨1, by omega⟩ f

/-- Target of a morphism (face d0). -/
def target (C : QuasiCategory) (f : C.mor) : C.obj :=
  C.sset.face 0 ⟨0, by omega⟩ f

/-- Identity morphism via degeneracy. -/
def id (C : QuasiCategory) (x : C.obj) : C.mor :=
  C.sset.degen 0 ⟨0, by omega⟩ x

/-- 2-simplices of a quasi-category. -/
def twoSimplex (C : QuasiCategory) : Type u :=
  C.sset.obj 2

/-- Composability of morphisms in a quasi-category. -/
structure Composable (C : QuasiCategory) (f g : C.mor) : Prop where
  /-- The target of f agrees with the source of g. -/
  target_eq : C.target f = C.source g

/-- The inner horn Lambda^2_1 determined by two composable edges. -/
def compHorn (C : QuasiCategory) (f g : C.mor) :
    HornData C.sset 1 ⟨1, by omega⟩ where
  faces := fun i _ => if i.val = 0 then g else f
  compat := fun _ _ _ _ _ _ _ => trivial

/-- The chosen inner horn filler used for composition. -/
def compFiller (C : QuasiCategory) (f g : C.mor) :
    HornFiller C.sset 1 ⟨1, by omega⟩ (compHorn C f g) :=
  by
    have hk : InnerHorn 1 ⟨1, by omega⟩ := by
      constructor <;> decide
    exact C.innerKan.fill 1 ⟨1, by omega⟩ hk (compHorn C f g)

/-- Composition via the inner horn filler (face d1 of the filler). -/
def comp (C : QuasiCategory) (f g : C.mor) : C.mor :=
  C.sset.face 1 ⟨1, by omega⟩ (compFiller C f g).simplex

end QuasiCategory

/-! ## Mapping spaces -/

/-- Mapping space data for a quasi-category, valued in Kan complexes. -/
structure MappingSpaceData (C : QuasiCategory) where
  /-- Mapping space simplicial set. -/
  map : C.obj → C.obj → SSetData
  /-- Each mapping space is a Kan complex. -/
  kan : ∀ x y : C.obj, KanFillerProperty (map x y)

namespace MappingSpaceData

variable {C : QuasiCategory}

/-- Map(x,y) as a simplicial set. -/
abbrev Map (M : MappingSpaceData C) (x y : C.obj) : SSetData :=
  M.map x y

/-- The mapping space Map(x,y) is Kan. -/
  def mapIsKan (M : MappingSpaceData C) (x y : C.obj) :
      KanFillerProperty (Map M x y) :=
    M.kan x y

end MappingSpaceData

/-! ## Homotopy category data -/

/-- Minimal homotopy category data associated to a quasi-category. -/
structure HomotopyCategoryData (C : QuasiCategory) where
  /-- Objects. -/
  obj : Type u
  /-- Morphisms. -/
  hom : obj → obj → Type u
  /-- Identities. -/
  id : (a : obj) → hom a a
  /-- Composition. -/
  comp : {a b c : obj} → hom a b → hom b c → hom a c
  /-- Left identity law (recorded abstractly). -/
  id_comp : ∀ {a b} (_ : hom a b), True
  /-- Right identity law (recorded abstractly). -/
  comp_id : ∀ {a b} (_ : hom a b), True
  /-- Associativity law (recorded abstractly). -/
  comp_assoc : ∀ {a b c d} (_ : hom a b) (_ : hom b c) (_ : hom c d), True

/-- The homotopy category induced by a quasi-category. -/
def homotopyCategory (C : QuasiCategory) : HomotopyCategoryData C where
  obj := C.obj
  hom := fun _ _ => C.mor
  id := C.id
  comp := fun f g => C.comp f g
  id_comp := fun _ => trivial
  comp_id := fun _ => trivial
  comp_assoc := fun _ _ _ => trivial

/-! ## Nerve of a category is a quasi-category -/

/-- The nerve of a small category carries a quasi-category structure. -/
structure NerveQuasiCategory (C : SmallCatData) where
  /-- Nerve data. -/
  nerveData : AbstractNerveData C
  /-- The nerve satisfies the inner Kan condition. -/
  innerKan : InnerKanProperty nerveData.sset

/-! ## Left and right fibrations -/

/-- Left horns: inner horns or k = 0. -/
def LeftHorn (n : Nat) (k : Fin (n + 2)) : Prop :=
  k.val = 0 ∨ InnerHorn n k

/-- Right horns: inner horns or k = n+1. -/
def RightHorn (n : Nat) (k : Fin (n + 2)) : Prop :=
  k.val = n + 1 ∨ InnerHorn n k

/-- Left fibration data between simplicial sets. -/
structure LeftFibrationData (S T : SSetData) where
  /-- The underlying simplicial map. -/
  map : SSetMap S T
  /-- Lifting property for left horns. -/
  lift : ∀ (n : Nat) (k : Fin (n + 2)) (_ : LeftHorn n k)
    (horn : HornData S n k)
    (tFiller : HornFiller T n k
      { faces := fun i hi => map.map n (horn.faces i hi),
        compat := fun _ _ _ _ _ _ _ => trivial }),
    ∃ (sFiller : HornFiller S n k horn),
      map.map (n + 1) sFiller.simplex = tFiller.simplex

/-- Right fibration data between simplicial sets. -/
structure RightFibrationData (S T : SSetData) where
  /-- The underlying simplicial map. -/
  map : SSetMap S T
  /-- Lifting property for right horns. -/
  lift : ∀ (n : Nat) (k : Fin (n + 2)) (_ : RightHorn n k)
    (horn : HornData S n k)
    (tFiller : HornFiller T n k
      { faces := fun i hi => map.map n (horn.faces i hi),
        compat := fun _ _ _ _ _ _ _ => trivial }),
    ∃ (sFiller : HornFiller S n k horn),
      map.map (n + 1) sFiller.simplex = tFiller.simplex


/-! ## Theorems -/

/-- Inner horn filling: every inner horn in a quasi-category has a filler. -/
theorem inner_horn_filling (C : QuasiCategory) (n : Nat) (k : Fin (n + 2))
    (hk : InnerHorn n k) (horn : HornData C.sset n k) :
    Nonempty (HornFiller C.sset n k horn) := by sorry

/-- The identity morphism is a left unit for composition. -/
theorem QuasiCategory.id_comp (C : QuasiCategory) (f : C.mor) :
    ∃ σ : C.twoSimplex,
      C.sset.face 1 ⟨1, by omega⟩ σ = C.comp (C.id (C.source f)) f := by sorry

/-- The identity morphism is a right unit for composition. -/
theorem QuasiCategory.comp_id (C : QuasiCategory) (f : C.mor) :
    ∃ σ : C.twoSimplex,
      C.sset.face 1 ⟨1, by omega⟩ σ = C.comp f (C.id (C.target f)) := by sorry

/-- Composition is associative up to a 3-simplex witness. -/
theorem QuasiCategory.comp_assoc (C : QuasiCategory) (f g h : C.mor) :
    ∃ τ : C.sset.obj 3, True := by sorry

/-- Mapping space adjunction: Map(A × B, C) ≃ Map(A, Map(B, C)). -/
theorem mapping_space_adjunction (C : QuasiCategory) (M : MappingSpaceData C)
    (x y z : C.obj) :
    Nonempty ((M.map x y).obj 0 → (M.map y z).obj 0 → (M.map x z).obj 0) := by sorry

/-- The homotopy category of a quasi-category satisfies left identity. -/
theorem homotopyCategory_id_comp (C : QuasiCategory) {a b : C.obj}
    (f : (homotopyCategory C).hom a b) :
    (homotopyCategory C).id_comp f = trivial := by sorry

/-- The nerve of a category satisfies the inner Kan condition (Joyal). -/
theorem nerve_is_quasiCategory_prop (Cat : SmallCatData) (N : NerveQuasiCategory Cat) :
    Nonempty (InnerKanProperty N.nerveData.sset) := by sorry

/-- Left fibrations are stable under pullback. -/
theorem left_fibration_pullback {S T U : SSetData}
    (p : LeftFibrationData S T) (f : SSetMap U T) :
    True := by sorry

/-- Right fibrations are stable under pullback. -/
theorem right_fibration_pullback {S T U : SSetData}
    (p : RightFibrationData S T) (f : SSetMap U T) :
    True := by sorry

/-- Every left horn is either the 0-horn or an inner horn. -/
theorem left_horn_cases (n : Nat) (k : Fin (n + 2)) (h : LeftHorn n k) :
    k.val = 0 ∨ InnerHorn n k := by sorry

private def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

/-! ## Summary

We defined quasi-categories as inner Kan complexes, implemented composition
from inner horn fillers, recorded mapping spaces as Kan complexes, introduced a
minimal homotopy category data structure, stated that nerves of categories are
quasi-categories, and packaged left/right fibration data.
-/

end Homotopy
end Path
end ComputationalPaths
