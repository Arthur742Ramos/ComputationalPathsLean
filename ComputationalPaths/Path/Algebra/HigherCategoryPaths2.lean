/-
# (∞,2)-Categories via Computational Paths

This module develops (∞,2)-category theory using `Path`-witnessed
constructions. We formalize scaled simplicial sets, complicial sets,
Gray tensor product, lax functors, lax natural transformations,
(∞,2)-Grothendieck construction, and straightening for fibrations.

## References

- Lurie, "(∞,2)-Categories and the Goodwillie Calculus"
- Gagna–Harpaz–Lanari, "On the equivalence of all models for (∞,2)-categories"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace HigherCategory2

universe u v

/-! ## Scaled Simplicial Sets -/

structure SimplicialSetData where
  simplices : Nat → Type u
  face : ∀ {n : Nat} (i : Fin (n + 2)), simplices (n + 1) → simplices n
  degen : ∀ {n : Nat} (i : Fin (n + 1)), simplices n → simplices (n + 1)

structure ScaledSimplicialSet extends SimplicialSetData.{u} where
  thin : simplices 2 → Prop
  thinDegen : ∀ (σ : simplices 1), thin (degen ⟨1, by omega⟩ σ)

structure ScaledMap (X Y : ScaledSimplicialSet.{u}) where
  mapSimplices : ∀ (n : Nat), X.simplices n → Y.simplices n
  preservesFace : ∀ {n : Nat} (i : Fin (n + 2)) (σ : X.simplices (n + 1)),
    mapSimplices n (X.face i σ) = Y.face i (mapSimplices (n + 1) σ)
  preservesThin : ∀ (σ : X.simplices 2), X.thin σ → Y.thin (mapSimplices 2 σ)

noncomputable def ScaledMap.identity (X : ScaledSimplicialSet.{u}) : ScaledMap X X where
  mapSimplices := fun _ x => x
  preservesFace := fun _ _ => rfl
  preservesThin := fun _ h => h

noncomputable def ScaledMap.comp {X Y Z : ScaledSimplicialSet.{u}}
    (f : ScaledMap X Y) (g : ScaledMap Y Z) : ScaledMap X Z where
  mapSimplices := fun n x => g.mapSimplices n (f.mapSimplices n x)
  preservesFace := fun i σ => by
    simp [f.preservesFace, g.preservesFace]
  preservesThin := fun σ h => g.preservesThin _ (f.preservesThin σ h)

noncomputable def scaled_id_comp_path {X Y : ScaledSimplicialSet.{u}} (f : ScaledMap X Y) :
    Path (ScaledMap.comp (ScaledMap.identity X) f).mapSimplices f.mapSimplices :=
  Path.refl _

structure MinimalScaling (X : ScaledSimplicialSet.{u}) where
  minimalProp : ∀ (σ : X.simplices 2), X.thin σ →
    ∃ (τ : X.simplices 1), X.degen ⟨1, by omega⟩ τ = σ

structure MaximalScaling (X : ScaledSimplicialSet.{u}) where
  maximalProp : ∀ (σ : X.simplices 2), X.thin σ

/-! ## Complicial Sets -/

structure ComplicialSet extends SimplicialSetData.{u} where
  marked : ∀ (n : Nat), simplices n → Prop
  markedDegen : ∀ {n : Nat} (σ : simplices n),
    marked (n + 1) (degen ⟨0, Nat.zero_lt_succ n⟩ σ)

structure ComplicialMap (X Y : ComplicialSet.{u}) where
  mapSimplices : ∀ (n : Nat), X.simplices n → Y.simplices n
  preservesMarked : ∀ (n : Nat) (σ : X.simplices n),
    X.marked n σ → Y.marked n (mapSimplices n σ)

structure NTrivialComplicial (X : ComplicialSet.{u}) (n : Nat) where
  trivialAbove : ∀ (k : Nat) (σ : X.simplices k),
    k > n → X.marked k σ

noncomputable def complic_map_refl {X Y : ComplicialSet.{u}}
    (f : ComplicialMap X Y) (n : Nat) (σ : X.simplices n) :
    Path (f.mapSimplices n σ) (f.mapSimplices n σ) :=
  Path.refl _

/-! ## Gray Tensor Product -/

structure GrayTensor (C D : ScaledSimplicialSet.{u}) where
  result : ScaledSimplicialSet.{u}
  leftInclusion : ∀ (n : Nat), C.simplices n → result.simplices n
  rightInclusion : ∀ (n : Nat), D.simplices n → result.simplices n

structure GrayAssociator {A B C : ScaledSimplicialSet.{u}}
    (AB : GrayTensor A B) (BC : GrayTensor B C)
    (AB_C : GrayTensor AB.result C) (A_BC : GrayTensor A BC.result) where
  assocMap : ScaledMap AB_C.result A_BC.result
  isEquiv : Prop

structure GrayUnit where
  unitSet : ScaledSimplicialSet.{u}
  unitSimplices : ∀ (n : Nat), unitSet.simplices n
  uniqueness : ∀ (n : Nat) (x y : unitSet.simplices n), x = y

noncomputable def gray_unit_path (U : GrayUnit.{u}) (n : Nat)
    (x y : U.unitSet.simplices n) :
    Path x y :=
  Path.ofEq (U.uniqueness n x y)

structure GraySymmetry {C D : ScaledSimplicialSet.{u}}
    (CD : GrayTensor C D) (DC : GrayTensor D C) where
  swapMap : ScaledMap CD.result DC.result
  swapInverse : ScaledMap DC.result CD.result
  roundtrip : ∀ (n : Nat) (x : CD.result.simplices n),
    swapInverse.mapSimplices n (swapMap.mapSimplices n x) = x

noncomputable def gray_symmetry_path {C D : ScaledSimplicialSet.{u}}
    {CD : GrayTensor C D} {DC : GrayTensor D C}
    (S : GraySymmetry CD DC) (n : Nat) (x : CD.result.simplices n) :
    Path (S.swapInverse.mapSimplices n (S.swapMap.mapSimplices n x)) x :=
  Path.ofEq (S.roundtrip n x)

/-! ## Lax Functors -/

structure LaxFunctor (C D : ScaledSimplicialSet.{u}) where
  onObjects : C.simplices 0 → D.simplices 0
  onMorphisms : C.simplices 1 → D.simplices 1
  on2Cells : C.simplices 2 → D.simplices 2

structure OplaxFunctor (C D : ScaledSimplicialSet.{u}) where
  onObjects : C.simplices 0 → D.simplices 0
  onMorphisms : C.simplices 1 → D.simplices 1
  on2Cells : C.simplices 2 → D.simplices 2

structure StrictFunctor (C D : ScaledSimplicialSet.{u}) extends LaxFunctor C D where
  preservesThin : ∀ (σ : C.simplices 2), C.thin σ → D.thin (on2Cells σ)

noncomputable def LaxFunctor.identity (C : ScaledSimplicialSet.{u}) : LaxFunctor C C where
  onObjects := id
  onMorphisms := id
  on2Cells := id

noncomputable def LaxFunctor.comp {A B C : ScaledSimplicialSet.{u}}
    (F : LaxFunctor A B) (G : LaxFunctor B C) : LaxFunctor A C where
  onObjects := G.onObjects ∘ F.onObjects
  onMorphisms := G.onMorphisms ∘ F.onMorphisms
  on2Cells := G.on2Cells ∘ F.on2Cells

noncomputable def lax_id_comp_path {A B : ScaledSimplicialSet.{u}} (F : LaxFunctor A B) :
    Path (LaxFunctor.comp (LaxFunctor.identity A) F).onObjects F.onObjects :=
  Path.refl _

/-! ## Lax Natural Transformations -/

structure LaxNatTrans {C D : ScaledSimplicialSet.{u}}
    (F G : LaxFunctor C D) where
  component : ∀ (x : C.simplices 0), D.simplices 1
  naturality2Cell : ∀ (f : C.simplices 1), D.simplices 2

structure OplaxNatTrans {C D : ScaledSimplicialSet.{u}}
    (F G : LaxFunctor C D) where
  component : ∀ (x : C.simplices 0), D.simplices 1
  oplaxCell : ∀ (f : C.simplices 1), D.simplices 2

structure LaxNatTransVComp {C D : ScaledSimplicialSet.{u}}
    {F G H : LaxFunctor C D}
    (α : LaxNatTrans F G) (β : LaxNatTrans G H) where
  result : LaxNatTrans F H

structure LaxNatTransHComp {A B C : ScaledSimplicialSet.{u}}
    {F G : LaxFunctor A B} {H K : LaxFunctor B C}
    (α : LaxNatTrans F G) (β : LaxNatTrans H K) where
  result : LaxNatTrans (LaxFunctor.comp F H) (LaxFunctor.comp G K)

noncomputable def lax_nat_comp_refl {C D : ScaledSimplicialSet.{u}}
    {F G : LaxFunctor C D} (α : LaxNatTrans F G) (x : C.simplices 0) :
    Path (α.component x) (α.component x) :=
  Path.refl _

/-! ## (∞,2)-Fibrations -/

structure Infty2InnerFibration (p : ScaledSimplicialSet.{u})
    (B : ScaledSimplicialSet.{u}) where
  projMap : ScaledMap p B
  liftingProp : ∀ (n : Nat) (σ : B.simplices (n + 1))
    (boundary : Fin (n + 2) → p.simplices n),
    (∀ (i : Fin (n + 2)),
      projMap.mapSimplices n (boundary i) = B.face i σ) →
    p.simplices (n + 1)

structure Infty2CartesianFibration (p : ScaledSimplicialSet.{u})
    (B : ScaledSimplicialSet.{u})
    extends Infty2InnerFibration p B where
  cartesianLifts : ∀ (f : B.simplices 1) (y : p.simplices 0),
    projMap.mapSimplices 0 y = B.face ⟨1, by omega⟩ f →
    p.simplices 1

structure Infty2CoCartFibration (p : ScaledSimplicialSet.{u})
    (B : ScaledSimplicialSet.{u})
    extends Infty2InnerFibration p B where
  cocartesianLifts : ∀ (f : B.simplices 1) (x : p.simplices 0),
    projMap.mapSimplices 0 x = B.face ⟨0, by omega⟩ f →
    p.simplices 1

noncomputable def infty2_cart_refl {p B : ScaledSimplicialSet.{u}}
    (F : Infty2CartesianFibration p B) (f : B.simplices 1)
    (y : p.simplices 0) (h : F.projMap.mapSimplices 0 y = B.face ⟨1, by omega⟩ f) :
    Path (F.cartesianLifts f y h) (F.cartesianLifts f y h) :=
  Path.refl _

/-! ## (∞,2)-Grothendieck Construction -/

structure Infty2Grothendieck (B : ScaledSimplicialSet.{u}) where
  totalSpace : ScaledSimplicialSet.{u}
  projection : ScaledMap totalSpace B
  fiberOver : B.simplices 0 → ScaledSimplicialSet.{u}
  fiberInclusion : ∀ (b : B.simplices 0) (n : Nat),
    (fiberOver b).simplices n → totalSpace.simplices n

structure Infty2Unstraightening (B : ScaledSimplicialSet.{u})
    (Cat2 : ScaledSimplicialSet.{u}) where
  functor : LaxFunctor B Cat2
  fibration : Infty2Grothendieck B
  equiv : Prop

structure Infty2Straightening (B : ScaledSimplicialSet.{u})
    (Cat2 : ScaledSimplicialSet.{u}) where
  fibration : Infty2Grothendieck B
  functor : LaxFunctor B Cat2
  equiv : Prop

noncomputable def groth_proj_refl {B : ScaledSimplicialSet.{u}}
    (G : Infty2Grothendieck B) (n : Nat)
    (x : G.totalSpace.simplices n) :
    Path (G.projection.mapSimplices n x) (G.projection.mapSimplices n x) :=
  Path.refl _

structure StraighteningEquiv (B : ScaledSimplicialSet.{u})
    (Cat2 : ScaledSimplicialSet.{u}) where
  straighten : Infty2Straightening B Cat2
  unstraighten : Infty2Unstraightening B Cat2
  roundtrip : Prop

/-! ## (∞,2)-Adjunctions -/

structure Infty2Adjunction (C : ScaledSimplicialSet.{u}) where
  left : C.simplices 1
  right : C.simplices 1
  unit : C.simplices 2
  counit : C.simplices 2
  unitThin : C.thin unit
  counitThin : C.thin counit

structure MateCorrespondence {C : ScaledSimplicialSet.{u}}
    (adj1 adj2 : Infty2Adjunction C) where
  mateMap : C.simplices 2 → C.simplices 2
  mateInverse : C.simplices 2 → C.simplices 2
  roundtrip : ∀ (σ : C.simplices 2),
    mateInverse (mateMap σ) = σ

noncomputable def mate_roundtrip_path {C : ScaledSimplicialSet.{u}}
    {adj1 adj2 : Infty2Adjunction C}
    (M : MateCorrespondence adj1 adj2) (σ : C.simplices 2) :
    Path (M.mateInverse (M.mateMap σ)) σ :=
  Path.ofEq (M.roundtrip σ)

/-! ## (∞,2)-Limits and Colimits -/

structure Infty2Limit (C : ScaledSimplicialSet.{u}) where
  diagram : ScaledSimplicialSet.{u}
  diagramMap : LaxFunctor diagram C
  limitCone : C.simplices 0
  projections : ∀ (d : diagram.simplices 0), C.simplices 1

structure Infty2Colimit (C : ScaledSimplicialSet.{u}) where
  diagram : ScaledSimplicialSet.{u}
  diagramMap : LaxFunctor diagram C
  colimitCocone : C.simplices 0
  inclusions : ∀ (d : diagram.simplices 0), C.simplices 1

structure LaxLimit (C : ScaledSimplicialSet.{u}) where
  diagram : ScaledSimplicialSet.{u}
  diagramMap : LaxFunctor diagram C
  laxCone : C.simplices 0
  laxProjections : ∀ (d : diagram.simplices 0), C.simplices 1
  laxCoherences : ∀ (f : diagram.simplices 1), C.simplices 2

noncomputable def infty2_limit_refl {C : ScaledSimplicialSet.{u}}
    (L : Infty2Limit C) :
    Path L.limitCone L.limitCone :=
  Path.refl _

/-! ## (∞,2)-Kan Extensions -/

structure Infty2LeftKan {A B C : ScaledSimplicialSet.{u}}
    (F : LaxFunctor A C) (p : LaxFunctor A B) where
  extension : LaxFunctor B C
  universalProp : ∀ (G : LaxFunctor B C),
    LaxNatTrans F (LaxFunctor.comp p G) →
    LaxNatTrans extension G

structure Infty2RightKan {A B C : ScaledSimplicialSet.{u}}
    (F : LaxFunctor A C) (p : LaxFunctor A B) where
  extension : LaxFunctor B C

noncomputable def infty2_lkan_refl {A B C : ScaledSimplicialSet.{u}}
    {F : LaxFunctor A C} {p : LaxFunctor A B}
    (K : Infty2LeftKan F p) :
    Path K.extension.onObjects K.extension.onObjects :=
  Path.refl _

/-! ## (∞,2)-Monadicity -/

structure Infty2Monad (C : ScaledSimplicialSet.{u}) where
  carrier : C.simplices 0
  endomorphism : C.simplices 1
  multiplication : C.simplices 2
  unit : C.simplices 2

structure Infty2MonadAlgebra {C : ScaledSimplicialSet.{u}}
    (T : Infty2Monad C) where
  algebraObj : C.simplices 0
  algebraMap : C.simplices 1
  algebraCoherence : C.simplices 2

structure Infty2BarrBeck {C : ScaledSimplicialSet.{u}}
    (adj : Infty2Adjunction C) where
  monad : Infty2Monad C
  monadicity : Prop
  conservativity : Prop

noncomputable def infty2_monad_refl {C : ScaledSimplicialSet.{u}}
    (T : Infty2Monad C) :
    Path T.carrier T.carrier :=
  Path.refl _

end HigherCategory2
end Algebra
end Path
end ComputationalPaths
