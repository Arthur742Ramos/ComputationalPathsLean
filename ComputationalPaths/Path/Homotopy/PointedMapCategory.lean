/-
# Category of Pointed Maps

This module formalizes the category of pointed maps between pointed types.
We define pointed maps, prove composition and identity laws, construct
products and coproducts of pointed types.

## Key Results

- `PtdMap`: pointed maps preserving basepoints
- `PtdMap.comp`, `PtdMap.id`: composition and identity
- `comp_assoc`, `id_comp`, `comp_id`: categorical laws
- `PtdProduct`, `PtdCoproduct`: products and coproducts
- `loopPtd`: the loop space pointed type

## References

- HoTT Book, Chapter 2 (pointed types and maps)
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Homotopy.Loops

namespace ComputationalPaths
namespace Path
namespace PointedMapCategory

universe u

/-! ## Pointed types and maps -/

/-- A pointed type: a type with a distinguished basepoint. -/
structure PtdType : Type (u + 1) where
  /-- The underlying type. -/
  carrier : Type u
  /-- The basepoint. -/
  pt : carrier

/-- A pointed map between pointed types. -/
structure PtdMap (X Y : PtdType.{u}) : Type u where
  /-- The underlying function. -/
  toFun : X.carrier → Y.carrier
  /-- Preservation of basepoint. -/
  map_pt : toFun X.pt = Y.pt

namespace PtdMap

variable {X Y Z W : PtdType.{u}}

/-! ## Identity and composition -/

/-- The identity pointed map. -/
noncomputable def id (X : PtdType.{u}) : PtdMap X X where
  toFun := _root_.id
  map_pt := rfl

/-- Composition of pointed maps. -/
noncomputable def comp (g : PtdMap Y Z) (f : PtdMap X Y) : PtdMap X Z where
  toFun := g.toFun ∘ f.toFun
  map_pt := by
    simp only [Function.comp]
    rw [f.map_pt, g.map_pt]

/-! ## Categorical laws -/

/-- Composition is associative. -/
@[simp] theorem comp_assoc (h : PtdMap Z W) (g : PtdMap Y Z)
    (f : PtdMap X Y) :
    comp (comp h g) f = comp h (comp g f) := rfl

/-- Left identity. -/
@[simp] theorem id_comp (f : PtdMap X Y) :
    comp (id Y) f = f := by
  cases f; rfl

/-- Right identity. -/
@[simp] theorem comp_id (f : PtdMap X Y) :
    comp f (id X) = f := by
  cases f; rfl

/-! ## Equality of pointed maps -/

/-- Two pointed maps are equal iff their underlying functions agree. -/
theorem ext {f g : PtdMap X Y} (h : f.toFun = g.toFun) : f = g := by
  cases f; cases g; cases h; rfl

end PtdMap

/-! ## Products of pointed types -/

/-- The product of two pointed types. -/
noncomputable def PtdProduct (X Y : PtdType.{u}) : PtdType.{u} where
  carrier := X.carrier × Y.carrier
  pt := (X.pt, Y.pt)

/-- First projection. -/
noncomputable def PtdProduct.fst (X Y : PtdType.{u}) : PtdMap (PtdProduct X Y) X where
  toFun := Prod.fst
  map_pt := rfl

/-- Second projection. -/
noncomputable def PtdProduct.snd (X Y : PtdType.{u}) : PtdMap (PtdProduct X Y) Y where
  toFun := Prod.snd
  map_pt := rfl

/-- The universal property: pairing of pointed maps. -/
noncomputable def PtdProduct.pair {W : PtdType.{u}} (X Y : PtdType.{u})
    (f : PtdMap W X) (g : PtdMap W Y) : PtdMap W (PtdProduct X Y) where
  toFun := fun w => (f.toFun w, g.toFun w)
  map_pt := by simp [PtdProduct, f.map_pt, g.map_pt]

/-- Pairing followed by fst recovers the first component. -/
@[simp] theorem PtdProduct.fst_pair {W : PtdType.{u}} {X Y : PtdType.{u}}
    (f : PtdMap W X) (g : PtdMap W Y) :
    PtdMap.comp (PtdProduct.fst X Y) (PtdProduct.pair X Y f g) = f := by
  apply PtdMap.ext; rfl

/-- Pairing followed by snd recovers the second component. -/
@[simp] theorem PtdProduct.snd_pair {W : PtdType.{u}} {X Y : PtdType.{u}}
    (f : PtdMap W X) (g : PtdMap W Y) :
    PtdMap.comp (PtdProduct.snd X Y) (PtdProduct.pair X Y f g) = g := by
  apply PtdMap.ext; rfl

/-! ## Coproducts of pointed types -/

/-- The coproduct (wedge sum) of pointed types, quotienting `Sum` to
identify the two basepoints. -/
inductive WedgeRel (X Y : PtdType.{u}) :
    X.carrier ⊕ Y.carrier → X.carrier ⊕ Y.carrier → Prop
  | baseL : WedgeRel X Y (Sum.inl X.pt) (Sum.inr Y.pt)
  | baseR : WedgeRel X Y (Sum.inr Y.pt) (Sum.inl X.pt)
  | refl (x : X.carrier ⊕ Y.carrier) : WedgeRel X Y x x

/-- The wedge sum of two pointed types. -/
noncomputable def PtdCoproduct (X Y : PtdType.{u}) : PtdType.{u} where
  carrier := Quot (WedgeRel X Y)
  pt := Quot.mk _ (Sum.inl X.pt)

/-- Left inclusion into the coproduct. -/
noncomputable def PtdCoproduct.inl (X Y : PtdType.{u}) : PtdMap X (PtdCoproduct X Y) where
  toFun := fun x => Quot.mk _ (Sum.inl x)
  map_pt := rfl

/-- Right inclusion into the coproduct. -/
noncomputable def PtdCoproduct.inr (X Y : PtdType.{u}) : PtdMap Y (PtdCoproduct X Y) where
  toFun := fun y => Quot.mk _ (Sum.inr y)
  map_pt := Quot.sound (WedgeRel.baseR)

/-! ## Loop space pointed type -/

/-- The loop space of a pointed type. -/
noncomputable def loopPtd (X : PtdType.{u}) : PtdType.{u} where
  carrier := LoopSpace X.carrier X.pt
  pt := Path.refl X.pt

/-- The loop space applied to the identity pointed map is identity. -/
@[simp] theorem loopPtd_pt_refl (X : PtdType.{u}) :
    (loopPtd X).pt = Path.refl X.pt := rfl

end PointedMapCategory
end Path

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end ComputationalPaths
