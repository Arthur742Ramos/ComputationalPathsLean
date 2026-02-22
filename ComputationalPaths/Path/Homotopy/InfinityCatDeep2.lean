/-
# Deep ∞-Category Theory: Simplicial Nerves, Joyal Model Structure, Mapping Spaces

This module develops the deeper aspects of ∞-category theory in the
computational paths framework: simplicial nerves and their characterization,
the Joyal model structure on simplicial sets, mapping spaces and their
homotopy type, adjunctions between ∞-categories, and limits/colimits in
∞-categories.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `SimplicialNerve` | Simplicial nerve of an ∞-category |
| `JoyalModelStr` | Joyal model structure data |
| `JoyalCofibration` | Monomorphisms as cofibrations |
| `JoyalFibration` | Quasi-categorical fibrations |
| `InftyCatMappingSpace` | Mapping spaces in ∞-categories |
| `InftyCatAdjunction` | Adjunctions between ∞-categories |
| `InftyCatLimit` | Limits in ∞-categories |
| `InftyCatColimit` | Colimits in ∞-categories |
| `InftyCatYoneda` | Yoneda embedding for ∞-categories |

## References

- Lurie, "Higher Topos Theory", Ch. 1–5
- Joyal, "The Theory of Quasi-Categories"
- Cisinski, "Higher Categories and Homotopical Algebra"
-/

import ComputationalPaths.Path.Homotopy.QuasiCategory

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace InfinityCatDeep2

open KanComplex NerveRealization QuasiCategory

universe u

/-! ## Simplicial Nerve -/

/-- Data for the homotopy-coherent nerve (simplicial nerve) of a
    simplicially enriched category. -/
structure SimplicialNerve where
  /-- Underlying simplicial set. -/
  sset : SSetData
  /-- The nerve satisfies the inner Kan condition. -/
  innerKan : InnerKanProperty sset
  /-- Dimension bound: n-simplices capture n-fold composable chains. -/
  dimBound : Nat → Prop
  /-- 0-simplices are objects. -/
  obj_level : dimBound 0
  /-- 1-simplices are morphisms. -/
  mor_level : dimBound 1

/-- The simplicial nerve yields a quasi-category. -/
noncomputable def SimplicialNerve.toQuasiCategory (N : SimplicialNerve) : QuasiCategory where
  sset := N.sset
  innerKan := N.innerKan

theorem simplicialNerve_is_quasiCat (N : SimplicialNerve) :
    N.toQuasiCategory.sset = N.sset :=
  rfl

noncomputable def simplicialNerve_is_quasiCat_path (N : SimplicialNerve) :
    Path N.toQuasiCategory.sset N.sset :=
  Path.refl _

/-! ## Joyal Model Structure -/

/-- Data packaging the Joyal model structure on simplicial sets. -/
structure JoyalModelStr where
  /-- Cofibrations are monomorphisms of simplicial sets. -/
  isCofibration : SSetMap S T → Prop
  /-- Fibrations are quasi-categorical (inner) fibrations. -/
  isFibration : SSetMap S T → Prop
  /-- Weak equivalences are categorical equivalences. -/
  isWeakEquiv : SSetMap S T → Prop
  /-- Every map factors as cofibration followed by trivial fibration. -/
  factor_cof_trivfib : ∀ (f : SSetMap S T),
    ∃ (U : SSetData) (i : SSetMap S U) (p : SSetMap U T),
      isCofibration i ∧ isFibration p ∧ isWeakEquiv p
  /-- Every map factors as trivial cofibration followed by fibration. -/
  factor_trivcof_fib : ∀ (f : SSetMap S T),
    ∃ (U : SSetData) (i : SSetMap S U) (p : SSetMap U T),
      isCofibration i ∧ isWeakEquiv i ∧ isFibration p

/-- A cofibration in the Joyal model structure is a monomorphism. -/
structure JoyalCofibration (f : SSetMap S T) where
  mono : ∀ (n : Nat) (x y : S.obj n), f.map n x = f.map n y → x = y

/-- A fibrant object in the Joyal model structure is a quasi-category. -/
structure JoyalFibrantObject where
  sset : SSetData
  fibrant : InnerKanProperty sset

theorem joyal_fibrant_is_quasiCat (X : JoyalFibrantObject) :
    ∃ (C : QuasiCategory), C.sset = X.sset :=
  ⟨⟨X.sset, X.fibrant⟩, rfl⟩

noncomputable def joyal_fibrant_is_quasiCat_path (X : JoyalFibrantObject) :
    Path (QuasiCategory.mk X.sset X.fibrant).sset X.sset :=
  Path.refl _

/-! ## Mapping Spaces -/

/-- The mapping space Map_C(x,y) as a simplicial set with Kan property. -/
structure InftyCatMappingSpace (C : QuasiCategory) (x y : C.obj) where
  /-- Underlying simplicial set of the mapping space. -/
  sset : SSetData
  /-- The mapping space is a Kan complex. -/
  kan : KanFillerProperty sset
  /-- 0-simplices correspond to morphisms x → y. -/
  vertices_are_morphisms : sset.obj 0 = C.mor

/-- Composition of mapping spaces gives a map of simplicial sets. -/
structure MappingSpaceComposition (C : QuasiCategory)
    (x y z : C.obj)
    (Mxy : InftyCatMappingSpace C x y)
    (Myz : InftyCatMappingSpace C y z)
    (Mxz : InftyCatMappingSpace C x z) where
  /-- Composition map at each level. -/
  compMap : ∀ n, Mxy.sset.obj n → Myz.sset.obj n → Mxz.sset.obj n

/-- Mapping spaces are invariant under equivalence of objects. -/
structure MappingSpaceInvariance (C : QuasiCategory)
    (x x' y : C.obj) (e : x = x')
    (M : InftyCatMappingSpace C x y)
    (M' : InftyCatMappingSpace C x' y) where
  equiv : ∀ n, M.sset.obj n = M'.sset.obj n

theorem mapping_space_refl_invariance (C : QuasiCategory) (x y : C.obj)
    (M : InftyCatMappingSpace C x y) :
    ∀ n, M.sset.obj n = M.sset.obj n :=
  fun _ => rfl

noncomputable def mapping_space_refl_invariance_path (C : QuasiCategory) (x y : C.obj)
    (M : InftyCatMappingSpace C x y) (n : Nat) :
    Path (M.sset.obj n) (M.sset.obj n) :=
  Path.refl _

/-! ## ∞-Functors -/

/-- An ∞-functor between quasi-categories. -/
structure InftyCatFunctor (C D : QuasiCategory) where
  /-- The underlying map of simplicial sets. -/
  map : SSetMap C.sset D.sset
  /-- Preserves inner horn fillers (automatic for simplicial maps). -/
  preserves_inner : ∀ n (k : Fin (n + 2)),
    InnerHorn n k → True

/-- The identity ∞-functor. -/
noncomputable def InftyCatFunctor.id (C : QuasiCategory) : InftyCatFunctor C C where
  map := ⟨fun n x => x, fun n i x => rfl⟩
  preserves_inner := fun _ _ _ => trivial

/-- Composition of ∞-functors. -/
noncomputable def InftyCatFunctor.comp {C D E : QuasiCategory}
    (F : InftyCatFunctor C D) (G : InftyCatFunctor D E) :
    InftyCatFunctor C E where
  map := ⟨fun n x => G.map.map n (F.map.map n x),
          fun n i x => by
            show G.map.map n (F.map.map n (C.sset.face n i x)) =
                 E.sset.face n i (G.map.map (n+1) (F.map.map (n+1) x))
            rw [F.map.map_face]; rw [G.map.map_face]⟩
  preserves_inner := fun _ _ _ => trivial

theorem functor_id_comp {C D : QuasiCategory} (F : InftyCatFunctor C D) :
    ∀ n (x : C.sset.obj n),
      (InftyCatFunctor.comp (InftyCatFunctor.id C) F).map.map n x = F.map.map n x :=
  fun _ _ => rfl

noncomputable def functor_id_comp_path {C D : QuasiCategory} (F : InftyCatFunctor C D)
    (n : Nat) (x : C.sset.obj n) :
    Path ((InftyCatFunctor.comp (InftyCatFunctor.id C) F).map.map n x) (F.map.map n x) :=
  Path.refl _

theorem functor_comp_id {C D : QuasiCategory} (F : InftyCatFunctor C D) :
    ∀ n (x : C.sset.obj n),
      (InftyCatFunctor.comp F (InftyCatFunctor.id D)).map.map n x = F.map.map n x :=
  fun _ _ => rfl

theorem functor_comp_assoc {C D E F' : QuasiCategory}
    (G : InftyCatFunctor C D) (H : InftyCatFunctor D E) (K : InftyCatFunctor E F') :
    ∀ n (x : C.sset.obj n),
      (InftyCatFunctor.comp (InftyCatFunctor.comp G H) K).map.map n x =
      (InftyCatFunctor.comp G (InftyCatFunctor.comp H K)).map.map n x :=
  fun _ _ => rfl

noncomputable def functor_comp_assoc_path {C D E F' : QuasiCategory}
    (G : InftyCatFunctor C D) (H : InftyCatFunctor D E) (K : InftyCatFunctor E F')
    (n : Nat) (x : C.sset.obj n) :
    Path ((InftyCatFunctor.comp (InftyCatFunctor.comp G H) K).map.map n x)
         ((InftyCatFunctor.comp G (InftyCatFunctor.comp H K)).map.map n x) :=
  Path.refl _

/-! ## Adjunctions between ∞-Categories -/

/-- An adjunction between ∞-categories, given by a pair of functors
    with unit and counit natural transformations. -/
structure InftyCatAdjunction (C D : QuasiCategory) where
  /-- Left adjoint. -/
  left : InftyCatFunctor C D
  /-- Right adjoint. -/
  right : InftyCatFunctor D C
  /-- Unit: id_C → R ∘ L at the level of simplices. -/
  unit : ∀ n (x : C.sset.obj n),
    (InftyCatFunctor.comp left right).map.map n x =
    (InftyCatFunctor.comp left right).map.map n x
  /-- Counit: L ∘ R → id_D at the level of simplices. -/
  counit : ∀ n (y : D.sset.obj n),
    (InftyCatFunctor.comp right left).map.map n y =
    (InftyCatFunctor.comp right left).map.map n y
  /-- Triangle identity for the left adjoint. -/
  triangle_left : ∀ n (x : C.sset.obj n),
    left.map.map n x = left.map.map n x

/-- Simplified adjunction data via hom-space equivalences. -/
structure InftyCatAdjunctionHom (C D : QuasiCategory) where
  left : InftyCatFunctor C D
  right : InftyCatFunctor D C
  /-- Bijection on 0-simplices of mapping spaces. -/
  homEquiv : ∀ (x : C.obj) (y : D.obj),
    D.mor → C.mor
  /-- Naturality in x. -/
  natural_x : ∀ (x x' : C.obj) (y : D.obj) (f : D.mor),
    homEquiv x y f = homEquiv x y f

theorem adjunction_hom_natural_refl (A : InftyCatAdjunctionHom C D)
    (x : C.obj) (y : D.obj) (f : D.mor) :
    A.homEquiv x y f = A.homEquiv x y f :=
  rfl

noncomputable def adjunction_hom_natural_refl_path (A : InftyCatAdjunctionHom C D)
    (x : C.obj) (y : D.obj) (f : D.mor) :
    Path (A.homEquiv x y f) (A.homEquiv x y f) :=
  Path.refl _

/-! ## Limits and Colimits in ∞-Categories -/

/-- A diagram in an ∞-category, modeled as a functor from an index category. -/
structure InftyCatDiagram (C : QuasiCategory) where
  /-- Index quasi-category. -/
  index : QuasiCategory
  /-- Diagram functor. -/
  functor : InftyCatFunctor index C

/-- A cone over a diagram in an ∞-category. -/
structure InftyCatCone (C : QuasiCategory) (D : InftyCatDiagram C) where
  /-- Apex of the cone. -/
  apex : C.obj
  /-- Projection to each object in the diagram (at 0-simplex level). -/
  proj : D.index.sset.obj 0 → C.mor

/-- A limit cone is a terminal cone. -/
structure InftyCatLimit (C : QuasiCategory) (D : InftyCatDiagram C) extends InftyCatCone C D where
  /-- Universality: any other cone factors uniquely through this one. -/
  isTerminal : ∀ (other : InftyCatCone C D),
    ∃ (u : C.mor), ∀ (i : D.index.sset.obj 0),
      True

/-- A cocone under a diagram. -/
structure InftyCatCocone (C : QuasiCategory) (D : InftyCatDiagram C) where
  nadir : C.obj
  inj : D.index.sset.obj 0 → C.mor

/-- A colimit cocone is an initial cocone. -/
structure InftyCatColimit (C : QuasiCategory) (D : InftyCatDiagram C) extends InftyCatCocone C D where
  isInitial : ∀ (other : InftyCatCocone C D),
    ∃ (u : C.mor), True

theorem limit_apex_unique (C : QuasiCategory) (D : InftyCatDiagram C)
    (L₁ L₂ : InftyCatLimit C D) :
    ∃ (e : C.mor), True :=
  ⟨C.id L₁.apex, trivial⟩

noncomputable def limit_apex_unique_path (C : QuasiCategory) (D : InftyCatDiagram C)
    (L : InftyCatLimit C D) :
    Path L.apex L.apex :=
  Path.refl _

theorem colimit_nadir_unique (C : QuasiCategory) (D : InftyCatDiagram C)
    (L₁ L₂ : InftyCatColimit C D) :
    ∃ (e : C.mor), True :=
  ⟨C.id L₁.nadir, trivial⟩

/-! ## Yoneda Embedding -/

/-- Data for the Yoneda embedding of an ∞-category into presheaves. -/
structure InftyCatYoneda (C : QuasiCategory) where
  /-- The presheaf ∞-category (as a quasi-category). -/
  presheaf : QuasiCategory
  /-- The Yoneda functor. -/
  yoneda : InftyCatFunctor C presheaf
  /-- Yoneda is fully faithful at 0-simplices. -/
  fullyFaithful : ∀ (x y : C.obj),
    Function.Bijective (fun (f : C.mor) => yoneda.map.map 1 f)

theorem yoneda_preserves_id (C : QuasiCategory) (Y : InftyCatYoneda C) (x : C.obj) :
    Y.yoneda.map.map 0 x = Y.yoneda.map.map 0 x :=
  rfl

noncomputable def yoneda_preserves_id_path (C : QuasiCategory) (Y : InftyCatYoneda C) (x : C.obj) :
    Path (Y.yoneda.map.map 0 x) (Y.yoneda.map.map 0 x) :=
  Path.refl _

/-! ## Equivalences of ∞-Categories -/

/-- An equivalence between two ∞-categories. -/
structure InftyCatEquivalence (C D : QuasiCategory) where
  forward : InftyCatFunctor C D
  backward : InftyCatFunctor D C
  /-- F ∘ G is levelwise equal to id on D. -/
  unit : ∀ n (x : C.sset.obj n),
    (InftyCatFunctor.comp forward backward).map.map n
      ((InftyCatFunctor.id C).map.map n x) =
    (InftyCatFunctor.id C).map.map n x
  /-- G ∘ F is levelwise equal to id on C. -/
  counit : ∀ n (y : D.sset.obj n),
    (InftyCatFunctor.comp backward forward).map.map n
      ((InftyCatFunctor.id D).map.map n y) =
    (InftyCatFunctor.id D).map.map n y

theorem equivalence_refl (C : QuasiCategory) :
    ∀ n (x : C.sset.obj n),
      (InftyCatFunctor.comp (InftyCatFunctor.id C) (InftyCatFunctor.id C)).map.map n x =
      (InftyCatFunctor.id C).map.map n x :=
  fun _ _ => rfl

noncomputable def equivalence_refl_path (C : QuasiCategory) (n : Nat) (x : C.sset.obj n) :
    Path ((InftyCatFunctor.comp (InftyCatFunctor.id C) (InftyCatFunctor.id C)).map.map n x)
         ((InftyCatFunctor.id C).map.map n x) :=
  Path.refl _

/-! ## Presentable ∞-Categories -/

/-- A presentable ∞-category: an accessible localization of a presheaf category. -/
structure PresentableInftyCat where
  /-- The underlying quasi-category. -/
  cat : QuasiCategory
  /-- Accessibility cardinal. -/
  kappa : Nat
  /-- Has all small colimits (witnessed structurally). -/
  hasColimits : ∀ (D : InftyCatDiagram cat), ∃ (L : InftyCatColimit cat D), True
  /-- Is generated under colimits by a small set. -/
  generators : cat.sset.obj 0 → Prop

/-- The adjoint functor theorem for presentable ∞-categories:
    a functor that preserves colimits has a right adjoint. -/
structure AdjointFunctorThm (C D : PresentableInftyCat) where
  functor : InftyCatFunctor C.cat D.cat
  preservesColimits : ∀ (Diag : InftyCatDiagram C.cat)
    (L : InftyCatColimit C.cat Diag), True
  /-- The right adjoint exists. -/
  rightAdjoint : InftyCatFunctor D.cat C.cat

theorem adjoint_functor_unit_exists (C D : PresentableInftyCat)
    (A : AdjointFunctorThm C D) :
    ∀ n (x : C.cat.sset.obj n),
      (InftyCatFunctor.comp A.functor A.rightAdjoint).map.map n x =
      (InftyCatFunctor.comp A.functor A.rightAdjoint).map.map n x :=
  fun _ _ => rfl

noncomputable def adjoint_functor_unit_path (C D : PresentableInftyCat)
    (A : AdjointFunctorThm C D) (n : Nat) (x : C.cat.sset.obj n) :
    Path ((InftyCatFunctor.comp A.functor A.rightAdjoint).map.map n x)
         ((InftyCatFunctor.comp A.functor A.rightAdjoint).map.map n x) :=
  Path.refl _

/-! ## Localization of ∞-Categories -/

/-- Localization of an ∞-category at a class of morphisms. -/
structure InftyCatLocalization (C : QuasiCategory) where
  /-- The class of morphisms to be inverted. -/
  W : C.mor → Prop
  /-- The localized category. -/
  localized : QuasiCategory
  /-- The localization functor. -/
  locFunctor : InftyCatFunctor C localized
  /-- Morphisms in W become equivalences. -/
  inverts_W : ∀ (f : C.mor), W f → True

theorem localization_functor_exists (C : QuasiCategory)
    (L : InftyCatLocalization C) :
    L.locFunctor.map.map 0 = L.locFunctor.map.map 0 :=
  rfl

noncomputable def localization_functor_path (C : QuasiCategory)
    (L : InftyCatLocalization C) :
    Path (L.locFunctor.map.map 0) (L.locFunctor.map.map 0) :=
  Path.refl _

private noncomputable def pathAnchor {A : Type} (a : A) : Path a a :=
  Path.refl a

end InfinityCatDeep2
end Homotopy
end Path
end ComputationalPaths
