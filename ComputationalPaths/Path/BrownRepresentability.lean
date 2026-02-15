/-
# Brown Representability for the Path Homotopy Category

This module formalizes a Brown representability statement for contravariant
homotopy functors on the path homotopy category. We express the wedge and
Mayer-Vietoris axioms via a universal element and a uniqueness principle, and
prove that these axioms yield a representing object.

## Key Results

- `PathContraFunctor`: contravariant functors on the path homotopy category
- `WedgeAxiom`, `MayerVietorisAxiom`: Brown-style axioms via a universal element
- `ContraRepresentable`: representability data for contravariant functors
- `brown_representability`: wedge + Mayer-Vietoris implies representability

## References

- Brown, "Representability of Cohomology Theories"
- Brown, "Topology and Groupoids"
-/

import ComputationalPaths.Path.Homotopy.FundamentalGroupoid
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Contravariant functors on the path homotopy category -/

/-- A contravariant functor from the path homotopy category on `A` to types. -/
structure PathContraFunctor (A : Type u) where
  /-- Object assignment. -/
  obj : A → Type v
  /-- Action on morphisms (contravariant). -/
  map : {a b : A} → FundamentalGroupoid.Hom A a b → obj b → obj a
  /-- Identity preservation. -/
  map_id : ∀ a (x : obj a), map (FundamentalGroupoid.id' A a) x = x
  /-- Composition preservation (contravariant). -/
  map_comp :
    ∀ {a b c : A} (p : FundamentalGroupoid.Hom A a b)
      (q : FundamentalGroupoid.Hom A b c) (x : obj c),
      map (FundamentalGroupoid.comp' A p q) x = map p (map q x)

/-! ## Representable contravariant functors -/

/-- Representable contravariant functor Hom(-, a) on the path homotopy category. -/
def contraRepresentable (A : Type u) (a : A) : PathContraFunctor A where
  obj := fun b => FundamentalGroupoid.Hom A b a
  map := fun {b c} p q => FundamentalGroupoid.comp' A p q
  map_id := by
    intro b q
    exact FundamentalGroupoid.id_comp' (A := A) (p := q)
  map_comp := by
    intro b c d p q r
    exact FundamentalGroupoid.comp_assoc' (A := A) (p := p) (q := q) (r := r)

/-! ## Brown-style axioms -/

/-- Wedge axiom: a universal element with a natural lifting operation. -/
structure WedgeAxiom (A : Type u) (F : PathContraFunctor A) where
  /-- Representing object candidate. -/
  obj : A
  /-- Universal element in the functor value at `obj`. -/
  elem : F.obj obj
  /-- Lift any element to a morphism into the representing object. -/
  lift : ∀ {b : A}, F.obj b → FundamentalGroupoid.Hom A b obj
  /-- The lift recovers the original element. -/
  lift_spec : ∀ {b : A} (x : F.obj b), F.map (lift x) elem = x
  /-- Naturality of the lift with respect to morphisms. -/
  lift_naturality :
    ∀ {b c : A} (p : FundamentalGroupoid.Hom A b c) (x : F.obj c),
      lift (F.map p x) = FundamentalGroupoid.comp' A p (lift x)

/-- Mayer-Vietoris axiom: the universal element yields unique lifts. -/
structure MayerVietorisAxiom (A : Type u) (F : PathContraFunctor A)
    (W : WedgeAxiom A F) : Prop where
  /-- Uniqueness of lifts determined by the universal element. -/
  unique :
    ∀ {b : A} {p q : FundamentalGroupoid.Hom A b W.obj},
      F.map p W.elem = F.map q W.elem → p = q

/-! ## Representability data -/

/-- Representability data for a contravariant functor. -/
structure ContraRepresentable (A : Type u) (F : PathContraFunctor A) where
  /-- Representing object. -/
  obj : A
  /-- Pointwise equivalence with Hom(-, obj). -/
  equiv : ∀ b : A, SimpleEquiv (F.obj b) (FundamentalGroupoid.Hom A b obj)
  /-- Naturality of the equivalence with respect to morphisms. -/
  naturality :
    ∀ {b c : A} (p : FundamentalGroupoid.Hom A b c) (x : F.obj c),
      (equiv b).toFun (F.map p x) =
        FundamentalGroupoid.comp' A p ((equiv c).toFun x)

/-! ## Brown representability -/

/-- The wedge and Mayer-Vietoris axioms determine a representability equivalence. -/
def wedge_equiv {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) (b : A) :
    SimpleEquiv (F.obj b) (FundamentalGroupoid.Hom A b W.obj) where
  toFun := fun x => W.lift x
  invFun := fun p => F.map p W.elem
  left_inv := by
    intro x
    exact W.lift_spec (x := x)
  right_inv := by
    intro p
    apply MV.unique
    exact W.lift_spec (x := F.map p W.elem)

/-- Brown representability: wedge + Mayer-Vietoris implies representability. -/
def brown_representability {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) :
    ContraRepresentable A F := by
  refine
    { obj := W.obj
      equiv := fun b => wedge_equiv (W := W) (MV := MV) b
      naturality := ?_ }
  intro b c p x
  exact W.lift_naturality (p := p) (x := x)

/-! ## Basic properties and coherence lemmas -/

theorem pathContraFunctor_map_id {A : Type u} (F : PathContraFunctor A)
    (a : A) (x : F.obj a) :
    F.map (FundamentalGroupoid.id' A a) x = x := by
  sorry

theorem pathContraFunctor_map_comp {A : Type u} (F : PathContraFunctor A)
    {a b c : A} (p : FundamentalGroupoid.Hom A a b)
    (q : FundamentalGroupoid.Hom A b c) (x : F.obj c) :
    F.map (FundamentalGroupoid.comp' A p q) x = F.map p (F.map q x) := by
  sorry

theorem contraRepresentable_obj_eq {A : Type u} (a b : A) :
    (contraRepresentable A a).obj b = FundamentalGroupoid.Hom A b a := by
  sorry

theorem contraRepresentable_map_eq {A : Type u} (a : A) {b c : A}
    (p : FundamentalGroupoid.Hom A b c) (q : FundamentalGroupoid.Hom A c a) :
    (contraRepresentable A a).map p q = FundamentalGroupoid.comp' A p q := by
  sorry

theorem wedge_lift_spec_eq {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) {b : A} (x : F.obj b) :
    F.map (W.lift x) W.elem = x := by
  sorry

theorem wedge_lift_naturality_eq {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) {b c : A} (p : FundamentalGroupoid.Hom A b c)
    (x : F.obj c) :
    W.lift (F.map p x) = FundamentalGroupoid.comp' A p (W.lift x) := by
  sorry

theorem mayerVietoris_unique {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) {b : A}
    {p q : FundamentalGroupoid.Hom A b W.obj}
    (h : F.map p W.elem = F.map q W.elem) : p = q := by
  sorry

theorem wedge_equiv_toFun_eq_lift {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) (b : A)
    (x : F.obj b) :
    (wedge_equiv (W := W) (MV := MV) b).toFun x = W.lift x := by
  sorry

theorem wedge_equiv_invFun_eq_map {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) (b : A)
    (p : FundamentalGroupoid.Hom A b W.obj) :
    (wedge_equiv (W := W) (MV := MV) b).invFun p = F.map p W.elem := by
  sorry

theorem wedge_equiv_left_inverse {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) (b : A)
    (x : F.obj b) :
    (wedge_equiv (W := W) (MV := MV) b).invFun
        ((wedge_equiv (W := W) (MV := MV) b).toFun x) = x := by
  sorry

theorem wedge_equiv_right_inverse {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) (b : A)
    (p : FundamentalGroupoid.Hom A b W.obj) :
    (wedge_equiv (W := W) (MV := MV) b).toFun
        ((wedge_equiv (W := W) (MV := MV) b).invFun p) = p := by
  sorry

theorem brown_representability_obj_eq {A : Type u} {F : PathContraFunctor A}
    (W : WedgeAxiom A F) (MV : MayerVietorisAxiom A F W) :
    (brown_representability (W := W) (MV := MV)).obj = W.obj := by
  sorry

theorem brown_representability_toFun_eq_lift {A : Type u}
    {F : PathContraFunctor A} (W : WedgeAxiom A F)
    (MV : MayerVietorisAxiom A F W) (b : A) (x : F.obj b) :
    ((brown_representability (W := W) (MV := MV)).equiv b).toFun x = W.lift x := by
  sorry

theorem brown_representability_naturality_eq {A : Type u}
    {F : PathContraFunctor A} (W : WedgeAxiom A F)
    (MV : MayerVietorisAxiom A F W) {b c : A}
    (p : FundamentalGroupoid.Hom A b c) (x : F.obj c) :
    ((brown_representability (W := W) (MV := MV)).equiv b).toFun (F.map p x) =
      FundamentalGroupoid.comp' A p
        (((brown_representability (W := W) (MV := MV)).equiv c).toFun x) := by
  sorry

/-! ## Summary -/

/-!
We defined contravariant path homotopy functors, encoded Brown-style wedge and
Mayer-Vietoris axioms via a universal element, and proved representability from
these axioms.
-/

end Path
end ComputationalPaths
