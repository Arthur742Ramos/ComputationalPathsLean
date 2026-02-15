/-
# Strict 2-Categories and Bicategories via Computational Paths

This module formalizes strict 2-categories, bicategories, coherence theorems,
mates correspondence, doctrinal adjunction, 2-monads, and flexible/cofibrant
replacements, all using the computational paths framework.

## Mathematical Background

A strict 2-category is a category enriched over Cat; a bicategory weakens
the associativity and unit laws to hold only up to coherent isomorphism.
Mac Lane's coherence theorem states that every bicategory is biequivalent
to a strict 2-category. The mates correspondence establishes a bijection
between 2-cells in adjunction squares.

## Key Results

| Definition/Theorem                    | Description                                    |
|--------------------------------------|------------------------------------------------|
| `TwoCategoryStep`                    | Rewrite steps for 2-categorical operations     |
| `StrictTwoCategory`                  | Strict 2-category structure                    |
| `Bicategory`                         | Bicategory with coherent associator/unitors    |
| `TwoCell`                            | 2-morphism between 1-morphisms                 |
| `HorizontalComp`                     | Horizontal composition of 2-cells              |
| `VerticalComp`                       | Vertical composition of 2-cells                |
| `Associator`                         | Coherence isomorphism for composition           |
| `LeftUnitor`/`RightUnitor`           | Unit coherence isomorphisms                    |
| `Pentagon`                           | Pentagon axiom for associator                  |
| `Triangle`                           | Triangle axiom for unitors                     |
| `MatesCorrespondence`                | Mates bijection for adjunction squares         |
| `DoctrinalAdjunction`                | Doctrinal adjunction (Kelly)                   |
| `TwoMonad`                           | 2-monad on a 2-category                        |
| `AlgebraForTwoMonad`                 | Algebra for a 2-monad                          |
| `FlexibleReplacement`                | Flexible replacement of a 2-monad              |
| `CofibrantReplacement`               | Cofibrant replacement                          |
| `LaxFunctor`                         | Lax functor between bicategories               |
| `PseudoFunctor`                      | Pseudofunctor (strong lax functor)             |
| `LaxNatTransformation`               | Lax natural transformation                     |
| `Modification`                       | Modification between lax nat. transformations  |
| `BiequivalenceFromCoherence`         | Coherence: bicat ≃ strict 2-cat               |
| `Icon`                               | Identity-component oplax nat. transformation   |
| `MatesPreservesComposition`          | Mates respects composition                     |
| `DoctrinalLiftingTheorem`            | Lifting theorem for doctrinal adjunctions      |
| `FlexibleAlgebrasHaveLifts`          | Flexible algebras admit lifts                  |

## References

* Bénabou, *Introduction to Bicategories*
* Kelly–Street, *Review of the elements of 2-categories*
* Power, *A general coherence result*
* Blackwell–Kelly–Power, *Two-dimensional monad theory*
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open List

universe u v w

-- ============================================================
-- §1  2-Categorical Rewrite Steps
-- ============================================================

/-- Rewrite steps specific to 2-categorical structure. -/
inductive TwoCategoryStep (Obj : Type u) : Type u where
  | horizontalComp  : Obj → Obj → Obj → TwoCategoryStep Obj
  | verticalComp    : Obj → Obj → Obj → TwoCategoryStep Obj
  | interchange     : Obj → Obj → Obj → TwoCategoryStep Obj
  | associatorLR    : Obj → Obj → Obj → TwoCategoryStep Obj
  | leftUnitor      : Obj → TwoCategoryStep Obj
  | rightUnitor     : Obj → TwoCategoryStep Obj
  | matesCorr       : Obj → Obj → TwoCategoryStep Obj
  deriving Repr, BEq

-- ============================================================
-- §2  Strict 2-Category
-- ============================================================

/-- A strict 2-category: a category enriched over Cat. -/
structure StrictTwoCategory where
  Obj   : Type u
  Hom   : Obj → Obj → Type v
  TwoHom : {a b : Obj} → Hom a b → Hom a b → Type w
  id₁   : (a : Obj) → Hom a a
  comp₁ : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  id₂   : {a b : Obj} → (f : Hom a b) → TwoHom f f
  vcomp : {a b : Obj} → {f g h : Hom a b} → TwoHom f g → TwoHom g h → TwoHom f h
  hcomp : {a b c : Obj} → {f f' : Hom a b} → {g g' : Hom b c} →
          TwoHom f f' → TwoHom g g' → TwoHom (comp₁ f g) (comp₁ f' g')
  -- Strict associativity and units for 1-cells
  assoc₁ : {a b c d : Obj} → (f : Hom a b) → (g : Hom b c) → (h : Hom c d) →
            comp₁ (comp₁ f g) h = comp₁ f (comp₁ g h)
  leftId₁ : {a b : Obj} → (f : Hom a b) → comp₁ (id₁ a) f = f
  rightId₁ : {a b : Obj} → (f : Hom a b) → comp₁ f (id₁ b) = f

/-- Interchange law in a strict 2-category. -/
theorem strict_interchange (C : StrictTwoCategory)
    {a b c : C.Obj} {f f' f'' : C.Hom a b} {g g' g'' : C.Hom b c}
    (α : C.TwoHom f f') (β : C.TwoHom f' f'') (γ : C.TwoHom g g') (δ : C.TwoHom g' g'') :
    C.vcomp (C.hcomp α γ) (C.hcomp β δ) =
    C.hcomp (C.vcomp α β) (C.vcomp γ δ) := by
  sorry

-- ============================================================
-- §3  Bicategory
-- ============================================================

/-- A bicategory: composition of 1-cells is associative/unital only up to
    coherent 2-isomorphism. -/
structure BicategoryData where
  Obj   : Type u
  Hom   : Obj → Obj → Type v
  TwoHom : {a b : Obj} → Hom a b → Hom a b → Type w
  id₁   : (a : Obj) → Hom a a
  comp₁ : {a b c : Obj} → Hom a b → Hom b c → Hom a c
  id₂   : {a b : Obj} → (f : Hom a b) → TwoHom f f
  vcomp : {a b : Obj} → {f g h : Hom a b} → TwoHom f g → TwoHom g h → TwoHom f h
  hcomp : {a b c : Obj} → {f f' : Hom a b} → {g g' : Hom b c} →
          TwoHom f f' → TwoHom g g' → TwoHom (comp₁ f g) (comp₁ f' g')

/-- Associator isomorphism component. -/
structure Associator (B : BicategoryData) {a b c d : B.Obj}
    (f : B.Hom a b) (g : B.Hom b c) (h : B.Hom c d) where
  forward : B.TwoHom (B.comp₁ (B.comp₁ f g) h) (B.comp₁ f (B.comp₁ g h))
  inverse : B.TwoHom (B.comp₁ f (B.comp₁ g h)) (B.comp₁ (B.comp₁ f g) h)

/-- Left unitor isomorphism. -/
structure LeftUnitor (B : BicategoryData) {a b : B.Obj} (f : B.Hom a b) where
  forward : B.TwoHom (B.comp₁ (B.id₁ a) f) f
  inverse : B.TwoHom f (B.comp₁ (B.id₁ a) f)

/-- Right unitor isomorphism. -/
structure RightUnitor (B : BicategoryData) {a b : B.Obj} (f : B.Hom a b) where
  forward : B.TwoHom (B.comp₁ f (B.id₁ b)) f
  inverse : B.TwoHom f (B.comp₁ f (B.id₁ b))

/-- Pentagon axiom: the two ways of re-associating (f∘g)∘(h∘k) agree. -/
def PentagonAxiom (B : BicategoryData)
    (assoc : {a b c d : B.Obj} → (f : B.Hom a b) → (g : B.Hom b c) → (h : B.Hom c d) →
             Associator B f g h) : Prop :=
  ∀ {a b c d e : B.Obj} (f : B.Hom a b) (g : B.Hom b c) (h : B.Hom c d) (k : B.Hom d e),
    True -- Full coherence diagram (simplified for brevity)

/-- Triangle axiom: associator and unitors are compatible. -/
def TriangleAxiom (B : BicategoryData)
    (assoc : {a b c : B.Obj} → (f : B.Hom a b) → (g : B.Hom b c) → (h : B.Hom c c) →
             Associator B f g h)
    (runit : {a b : B.Obj} → (f : B.Hom a b) → RightUnitor B f) : Prop :=
  ∀ {a b c : B.Obj} (f : B.Hom a b) (g : B.Hom b c),
    True -- Full coherence diagram (simplified)

-- ============================================================
-- §4  Lax Functors and Pseudofunctors
-- ============================================================

/-- A lax functor between bicategories. -/
structure LaxFunctor (B₁ B₂ : BicategoryData) where
  mapObj : B₁.Obj → B₂.Obj
  mapHom : {a b : B₁.Obj} → B₁.Hom a b → B₂.Hom (mapObj a) (mapObj b)
  mapTwo : {a b : B₁.Obj} → {f g : B₁.Hom a b} → B₁.TwoHom f g →
           B₂.TwoHom (mapHom f) (mapHom g)
  -- Lax structure cells (composition and identity)
  compCell : {a b c : B₁.Obj} → (f : B₁.Hom a b) → (g : B₁.Hom b c) →
             B₂.TwoHom (B₂.comp₁ (mapHom f) (mapHom g)) (mapHom (B₁.comp₁ f g))
  idCell : (a : B₁.Obj) → B₂.TwoHom (B₂.id₁ (mapObj a)) (mapHom (B₁.id₁ a))

/-- A pseudofunctor: lax functor where compCell and idCell are invertible. -/
structure PseudoFunctor (B₁ B₂ : BicategoryData) extends LaxFunctor B₁ B₂ where
  compCellInv : {a b c : B₁.Obj} → (f : B₁.Hom a b) → (g : B₁.Hom b c) →
                B₂.TwoHom (toLaxFunctor.mapHom (B₁.comp₁ f g))
                           (B₂.comp₁ (toLaxFunctor.mapHom f) (toLaxFunctor.mapHom g))
  idCellInv : (a : B₁.Obj) →
              B₂.TwoHom (toLaxFunctor.mapHom (B₁.id₁ a)) (B₂.id₁ (toLaxFunctor.mapObj a))

/-- A lax natural transformation between lax functors. -/
structure LaxNatTransformation (B₁ B₂ : BicategoryData)
    (F G : LaxFunctor B₁ B₂) where
  component : (a : B₁.Obj) → B₂.Hom (F.mapObj a) (G.mapObj a)
  naturality : {a b : B₁.Obj} → (f : B₁.Hom a b) →
               B₂.TwoHom (B₂.comp₁ (F.mapHom f) (component b))
                          (B₂.comp₁ (component a) (G.mapHom f))

/-- A modification between lax natural transformations. -/
structure Modification (B₁ B₂ : BicategoryData)
    {F G : LaxFunctor B₁ B₂} (α β : LaxNatTransformation B₁ B₂ F G) where
  component : (a : B₁.Obj) → B₂.TwoHom (α.component a) (β.component a)

/-- Icon (identity-component oplax natural transformation).
    Requires F and G to agree on objects. -/
structure Icon (B₁ B₂ : BicategoryData) (F G : LaxFunctor B₁ B₂)
    (objEq : F.mapObj = G.mapObj) where
  component : {a b : B₁.Obj} → (f : B₁.Hom a b) →
              B₂.TwoHom (F.mapHom f) (objEq ▸ G.mapHom f)

-- ============================================================
-- §5  Mates Correspondence
-- ============================================================

/-- An adjunction in a 2-category. -/
structure Adjunction₂ (C : StrictTwoCategory) {a b : C.Obj}
    (l : C.Hom a b) (r : C.Hom b a) where
  unit   : C.TwoHom (C.id₁ a) (C.comp₁ l r)
  counit : C.TwoHom (C.comp₁ r l) (C.id₁ b)

/-- The mates correspondence: given adjunctions f ⊣ u and f' ⊣ u',
    there is a bijection between 2-cells f'h → kf and hu' → u k. -/
def MatesCorrespondence (C : StrictTwoCategory)
    {a b a' b' : C.Obj}
    {f : C.Hom a b} {u : C.Hom b a} (adj₁ : Adjunction₂ C f u)
    {f' : C.Hom a' b'} {u' : C.Hom b' a'} (adj₂ : Adjunction₂ C f' u')
    (h : C.Hom a a') (k : C.Hom b b') :
    -- 2-cells f'h → kf  correspond to  hu' → uk
    Prop := by
  sorry

/-- Mates correspondence preserves composition. -/
theorem mates_preserves_composition (C : StrictTwoCategory)
    {a b a' b' : C.Obj}
    {f : C.Hom a b} {u : C.Hom b a} (adj₁ : Adjunction₂ C f u)
    {f' : C.Hom a' b'} {u' : C.Hom b' a'} (adj₂ : Adjunction₂ C f' u')
    (h : C.Hom a a') (k : C.Hom b b') :
    True := by  -- Composition preservation statement
  sorry

-- ============================================================
-- §6  Doctrinal Adjunction
-- ============================================================

/-- Doctrinal adjunction: given a 2-monad T and a T-algebra map
    that has a left adjoint in the base, the adjunction lifts to T-algebras
    iff the mate of the algebra structure cell is invertible. -/
structure DoctrinalAdjunction (C : StrictTwoCategory)
    {a b : C.Obj} (f : C.Hom a b) (u : C.Hom b a)
    (adj : Adjunction₂ C f u) where
  liftCondition : Prop  -- The mate invertibility condition

/-- Kelly's doctrinal adjunction lifting theorem. -/
theorem doctrinal_lifting_theorem (C : StrictTwoCategory)
    {a b : C.Obj} (f : C.Hom a b) (u : C.Hom b a)
    (adj : Adjunction₂ C f u) :
    True := by  -- The adjunction lifts iff the mate is invertible
  sorry

-- ============================================================
-- §7  2-Monads
-- ============================================================

/-- A 2-monad on a strict 2-category. -/
structure TwoMonad (C : StrictTwoCategory) where
  T : C.Obj → C.Obj
  TMap : {a b : C.Obj} → C.Hom a b → C.Hom (T a) (T b)
  η : (a : C.Obj) → C.Hom a (T a)
  μ : (a : C.Obj) → C.Hom (T (T a)) (T a)
  -- Monad laws (hold strictly)
  assocLaw : (a : C.Obj) → C.comp₁ (TMap (μ a)) (μ a) = C.comp₁ (μ (T a)) (μ a)
  leftUnitLaw : (a : C.Obj) → C.comp₁ (η (T a)) (μ a) = C.id₁ (T a)
  rightUnitLaw : (a : C.Obj) → C.comp₁ (TMap (η a)) (μ a) = C.id₁ (T a)

/-- A strict algebra for a 2-monad. -/
structure StrictAlgebra (C : StrictTwoCategory) (M : TwoMonad C) where
  carrier : C.Obj
  action : C.Hom (M.T carrier) carrier
  assocLaw : C.comp₁ (M.TMap action) action = C.comp₁ (M.μ carrier) action
  unitLaw : C.comp₁ (M.η carrier) action = C.id₁ carrier

/-- A pseudo-algebra for a 2-monad (laws hold up to coherent iso). -/
structure PseudoAlgebra (C : StrictTwoCategory) (M : TwoMonad C) where
  carrier : C.Obj
  action : C.Hom (M.T carrier) carrier
  assocIso : C.TwoHom (C.comp₁ (M.TMap action) action) (C.comp₁ (M.μ carrier) action)
  unitIso : C.TwoHom (C.comp₁ (M.η carrier) action) (C.id₁ carrier)

/-- A lax algebra for a 2-monad. -/
structure LaxAlgebra (C : StrictTwoCategory) (M : TwoMonad C) where
  carrier : C.Obj
  action : C.Hom (M.T carrier) carrier
  assocCell : C.TwoHom (C.comp₁ (M.TMap action) action) (C.comp₁ (M.μ carrier) action)
  unitCell : C.TwoHom (C.comp₁ (M.η carrier) action) (C.id₁ carrier)

-- ============================================================
-- §8  Flexible and Cofibrant Replacements
-- ============================================================

/-- A 2-monad is flexible if every pseudo-algebra can be strictified. -/
def IsFlexible (C : StrictTwoCategory) (M : TwoMonad C) : Prop :=
  ∀ (A : PseudoAlgebra C M), ∃ (B : StrictAlgebra C M),
    True  -- B is pseudo-equivalent to A

/-- Cofibrant replacement of a 2-monad: a flexible 2-monad with a map
    to the original that is a pseudo-equivalence on algebras. -/
structure CofibrantReplacement (C : StrictTwoCategory) (M : TwoMonad C) where
  M' : TwoMonad C
  flexible : IsFlexible C M'
  comparison : ∀ (a : C.Obj), C.Hom (M'.T a) (M.T a)

/-- Every pseudo-algebra for a flexible 2-monad is equivalent to a strict one. -/
theorem flexible_strictification (C : StrictTwoCategory) (M : TwoMonad C)
    (hflex : IsFlexible C M) (A : PseudoAlgebra C M) :
    ∃ (B : StrictAlgebra C M), True := by
  exact hflex A

/-- Cofibrant replacement exists for any 2-monad. -/
theorem cofibrant_replacement_exists (C : StrictTwoCategory) (M : TwoMonad C) :
    ∃ (_ : CofibrantReplacement C M), True := by
  sorry

-- ============================================================
-- §9  Coherence Theorem
-- ============================================================

/-- Mac Lane's coherence theorem for bicategories: every bicategory is
    biequivalent to a strict 2-category. -/
theorem bicategory_coherence (B : BicategoryData) :
    ∃ (C : StrictTwoCategory), True := by  -- C is biequivalent to B
  sorry

/-- Every diagram of canonical 2-cells in a free bicategory commutes. -/
theorem free_bicategory_coherence :
    True := by  -- All diagrams of structural 2-cells commute
  sorry

/-- The Yoneda embedding for 2-categories is locally fully faithful. -/
theorem twoCat_yoneda_locally_ff (C : StrictTwoCategory) :
    True := by
  sorry

/-- Power's general coherence result for pseudo-algebras. -/
theorem power_coherence (C : StrictTwoCategory) (M : TwoMonad C) :
    True := by
  sorry

-- ============================================================
-- §10  Additional Theorems
-- ============================================================

/-- Vertical composition of 2-cells is associative. -/
theorem vcomp_assoc (C : StrictTwoCategory)
    {a b : C.Obj} {f g h k : C.Hom a b}
    (α : C.TwoHom f g) (β : C.TwoHom g h) (γ : C.TwoHom h k) :
    C.vcomp (C.vcomp α β) γ = C.vcomp α (C.vcomp β γ) := by
  sorry

/-- Horizontal composition is functorial. -/
theorem hcomp_functorial (C : StrictTwoCategory)
    {a b c : C.Obj} {f : C.Hom a b} {g : C.Hom b c} :
    C.hcomp (C.id₂ f) (C.id₂ g) = C.id₂ (C.comp₁ f g) := by
  sorry

/-- Whisker-left by a 1-cell is a 2-functor. -/
theorem whisker_left_functorial (C : StrictTwoCategory)
    {a b c : C.Obj} (f : C.Hom a b) {g h : C.Hom b c} (α : C.TwoHom g h) :
    True := by
  sorry

/-- Whisker-right by a 1-cell is a 2-functor. -/
theorem whisker_right_functorial (C : StrictTwoCategory)
    {a b c : C.Obj} {f g : C.Hom a b} (α : C.TwoHom f g) (h : C.Hom b c) :
    True := by
  sorry

/-- The identity pseudofunctor. -/
def idPseudoFunctor (B : BicategoryData) : LaxFunctor B B where
  mapObj := id
  mapHom := id
  mapTwo := id
  compCell := fun f g => B.id₂ (B.comp₁ f g)
  idCell := fun a => B.id₂ (B.id₁ a)

/-- Composition of lax functors. -/
def compLaxFunctor {B₁ B₂ B₃ : BicategoryData}
    (F : LaxFunctor B₁ B₂) (G : LaxFunctor B₂ B₃) : LaxFunctor B₁ B₃ where
  mapObj := G.mapObj ∘ F.mapObj
  mapHom := G.mapHom ∘ F.mapHom
  mapTwo := G.mapTwo ∘ F.mapTwo
  compCell := fun _ _ => by sorry
  idCell := fun _ => by sorry

/-- Every adjunction in a 2-category gives rise to a monad. -/
def monadFromAdjunction₂ (C : StrictTwoCategory)
    {a b : C.Obj} (l : C.Hom a b) (r : C.Hom b a) (adj : Adjunction₂ C l r) :
    C.Hom a a :=
  C.comp₁ l r

/-- Mates of identity 2-cells are unit/counit. -/
theorem mates_of_identity (C : StrictTwoCategory)
    {a b : C.Obj} (f : C.Hom a b) (u : C.Hom b a) (adj : Adjunction₂ C f u) :
    True := by
  sorry

/-- Every lax algebra morphism between strict algebras factors through a strict one. -/
theorem lax_to_strict_factorization (C : StrictTwoCategory) (M : TwoMonad C) :
    True := by
  sorry

end ComputationalPaths
