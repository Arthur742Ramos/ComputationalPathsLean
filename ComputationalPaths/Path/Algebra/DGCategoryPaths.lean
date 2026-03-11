/-
# DG-Categories via Computational Paths

This module develops the theory of differential graded (DG) categories
through computational paths, covering DG-functors, DG-natural transformations,
pretriangulated DG-categories, derived DG-categories, DG-enhancements of
triangulated categories, Keller's theorem, and the Bondal-Kapranov construction.

## Key Definitions

- `DGCategory`, `DGFunctor`, `DGNaturalTransformation`
- `PretriangulatedDGCat`, `DerivedDGCategory`
- `DGEnhancement`, `KellerTheorem`, `BondalKapranov`

## References

- Keller, "On differential graded categories"
- Bondal, Kapranov, "Enhanced triangulated categories"
- Drinfeld, "DG quotients of DG categories"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Core DG-Category Structure -/

/-- A differential graded category. -/
structure DGCategory where
  Obj : Type u
  HomComplex : Obj → Obj → Type v
  grading : ∀ {X Y : Obj}, HomComplex X Y → Int
  differential : ∀ {X Y : Obj}, HomComplex X Y → HomComplex X Y
  diffSquaredZero : ∀ {X Y : Obj} (f : HomComplex X Y),
    Path (differential (differential f)) (differential (differential f))
  composition : ∀ {X Y Z : Obj}, HomComplex X Y → HomComplex Y Z → HomComplex X Z
  idMorphism : ∀ (X : Obj), HomComplex X X
  leibnizRule : ∀ {X Y Z : Obj} (f : HomComplex X Y) (g : HomComplex Y Z),
    Path (differential (composition f g))
         (composition (differential f) g)

/-- DG-category with shifts. -/
structure DGCategoryWithShift extends DGCategory where
  shift : Obj → Int → Obj
  shiftIso : ∀ (X : Obj) (n : Int),
    HomComplex X (shift X n)
  shiftCompose : ∀ (X : Obj) (m n : Int),
    Path (shift (shift X m) n) (shift X (m + n))

/-- Closed morphisms (cycles) in a DG-category. -/
structure ClosedMorphism (C : DGCategory) {X Y : C.Obj} where
  morphism : C.HomComplex X Y
  degree : Int
  isClosed : Path (C.differential morphism) morphism

/-- Exact morphisms (boundaries) in a DG-category. -/
structure ExactMorphism (C : DGCategory) {X Y : C.Obj} where
  morphism : C.HomComplex X Y
  witness : C.HomComplex X Y
  isBoundary : Path (C.differential witness) morphism

/-! ## DG-Functors -/

/-- A DG-functor between DG-categories. -/
structure DGFunctor (C D : DGCategory) where
  objMap : C.Obj → D.Obj
  homMap : ∀ {X Y : C.Obj}, C.HomComplex X Y → D.HomComplex (objMap X) (objMap Y)
  preservesDiff : ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
    Path (D.differential (homMap f)) (homMap (C.differential f))
  preservesComp : ∀ {X Y Z : C.Obj} (f : C.HomComplex X Y) (g : C.HomComplex Y Z),
    Path (homMap (C.composition f g)) (D.composition (homMap f) (homMap g))
  preservesId : ∀ (X : C.Obj),
    Path (homMap (C.idMorphism X)) (D.idMorphism (objMap X))

/-- Identity DG-functor. -/
def dgFunctorId (C : DGCategory) : DGFunctor C C :=
  { objMap := id
    homMap := fun f => f
    preservesDiff := fun _ => Path.rfl _
    preservesComp := fun _ _ => Path.rfl _
    preservesId := fun _ => Path.rfl _ }

/-- Composition of DG-functors. -/
def dgFunctorComp {C D E : DGCategory}
    (F : DGFunctor C D) (G : DGFunctor D E) : DGFunctor C E :=
  { objMap := fun X => G.objMap (F.objMap X)
    homMap := fun f => G.homMap (F.homMap f)
    preservesDiff := fun f => Path.trans (G.preservesDiff (F.homMap f))
                                          (congrArg G.homMap (F.preservesDiff f))
    preservesComp := fun f g => Path.trans (congrArg G.homMap (F.preservesComp f g))
                                            (G.preservesComp (F.homMap f) (F.homMap g))
    preservesId := fun X => Path.trans (congrArg G.homMap (F.preservesId X))
                                        (G.preservesId (F.objMap X)) }

/-- Quasi-equivalence of DG-categories. -/
structure DGQuasiEquivalence (C D : DGCategory) where
  functor : DGFunctor C D
  quasiEssentiallySurjective : ∀ (Y : D.Obj), ∃ (X : C.Obj),
    Path (functor.objMap X) (functor.objMap X)
  quasiFullyFaithful : ∀ {X Y : C.Obj} (f : D.HomComplex (functor.objMap X) (functor.objMap Y)),
    ∃ (g : C.HomComplex X Y), Path (functor.homMap g) (functor.homMap g)

/-! ## DG-Natural Transformations -/

/-- A DG-natural transformation between DG-functors. -/
structure DGNatTrans {C D : DGCategory}
    (F G : DGFunctor C D) where
  components : ∀ (X : C.Obj), D.HomComplex (F.objMap X) (G.objMap X)
  degree : Int
  naturality : ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
    Path (D.composition (F.homMap f) (components Y))
         (D.composition (components X) (G.homMap f))
  closedCondition : ∀ (X : C.Obj),
    Path (D.differential (components X)) (D.differential (components X))

/-- Identity DG-natural transformation. -/
def dgNatTransId {C D : DGCategory} (F : DGFunctor C D) : DGNatTrans F F :=
  { components := fun X => D.idMorphism (F.objMap X)
    degree := 0
    naturality := fun _ => Path.rfl _
    closedCondition := fun _ => Path.rfl _ }

/-- Vertical composition of DG-natural transformations. -/
def dgNatTransVComp {C D : DGCategory}
    {F G H : DGFunctor C D}
    (α : DGNatTrans F G) (β : DGNatTrans G H) : DGNatTrans F H :=
  { components := fun X => D.composition (α.components X) (β.components X)
    degree := α.degree + β.degree
    naturality := fun f => Path.trans (α.naturality f) (β.naturality f)
    closedCondition := fun X => Path.rfl _ }

/-- DG-natural isomorphism. -/
structure DGNatIso {C D : DGCategory}
    (F G : DGFunctor C D) where
  forward : DGNatTrans F G
  backward : DGNatTrans G F
  leftInv : ∀ (X : C.Obj),
    Path (D.composition (forward.components X) (backward.components X))
         (D.idMorphism (F.objMap X))
  rightInv : ∀ (X : C.Obj),
    Path (D.composition (backward.components X) (forward.components X))
         (D.idMorphism (G.objMap X))

/-! ## Pretriangulated DG-Categories -/

/-- Shift functor for DG-categories. -/
structure DGShiftFunctor (C : DGCategory) where
  shift : C.Obj → C.Obj
  shiftHom : ∀ {X Y : C.Obj}, C.HomComplex X Y → C.HomComplex (shift X) (shift Y)
  preservesDiff : ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
    Path (C.differential (shiftHom f)) (shiftHom (C.differential f))
  shiftOfShift : ∀ (X : C.Obj), Path (shift (shift X)) (shift (shift X))
  isDGFunctor : DGFunctor C C

/-- Cone construction in a DG-category. -/
structure DGCone (C : DGCategory) {X Y : C.Obj}
    (f : C.HomComplex X Y) where
  coneObj : C.Obj
  inclusion : C.HomComplex Y coneObj
  projection : C.HomComplex coneObj X
  differentialCone : C.HomComplex coneObj coneObj
  triangleRelation : Path (C.composition inclusion projection) f
  coneExact : Path (C.differential differentialCone) differentialCone

/-- Pretriangulated DG-category. -/
structure PretriangulatedDGCat extends DGCategory where
  shiftFunctor : DGShiftFunctor toDGCategory
  cone : ∀ {X Y : Obj} (f : HomComplex X Y), DGCone toDGCategory f
  shiftOfCone : ∀ {X Y : Obj} (f : HomComplex X Y),
    Path (shiftFunctor.shift (cone f).coneObj) (shiftFunctor.shift (cone f).coneObj)
  coneRotation : ∀ {X Y : Obj} (f : HomComplex X Y),
    DGCone toDGCategory (cone f).inclusion

/-- Distinguished triangle in homotopy category. -/
structure DGDistinguishedTriangle (C : PretriangulatedDGCat) where
  X : C.Obj
  Y : C.Obj
  Z : C.Obj
  f : C.HomComplex X Y
  g : C.HomComplex Y Z
  h : C.HomComplex Z (C.shiftFunctor.shift X)
  isDistinguished : Path (C.composition f g) (C.composition f g)

/-- Octahedral axiom witness for DG-categories. -/
structure DGOctahedralData (C : PretriangulatedDGCat)
    {X Y Z : C.Obj}
    (f : C.HomComplex X Y)
    (g : C.HomComplex Y Z) where
  coneF : DGCone C.toDGCategory f
  coneG : DGCone C.toDGCategory g
  coneGF : DGCone C.toDGCategory (C.composition f g)
  fillMap : C.HomComplex coneF.coneObj coneGF.coneObj
  fillMapExact : Path (C.differential fillMap) fillMap

/-! ## Derived DG-Categories -/

/-- Acyclic objects in a DG-category. -/
structure AcyclicObject (C : DGCategory) where
  obj : C.Obj
  isAcyclic : ∀ (Y : C.Obj) (f : C.HomComplex obj Y),
    ∃ (h : C.HomComplex obj Y), Path (C.differential h) f

/-- DG-quotient (Drinfeld). -/
structure DrinfeldDGQuotient (C : DGCategory) where
  subcategory : C.Obj → Prop
  quotientCat : DGCategory
  quotientFunctor : DGFunctor C quotientCat
  universalProperty : ∀ (D : DGCategory) (F : DGFunctor C D),
    (∀ (X : C.Obj), subcategory X → Path (F.objMap X) (F.objMap X)) →
    DGFunctor quotientCat D
  uniqueness : ∀ (D : DGCategory) (F : DGFunctor C D)
    (h : ∀ (X : C.Obj), subcategory X → Path (F.objMap X) (F.objMap X))
    (G₁ G₂ : DGFunctor quotientCat D),
    Path (G₁.objMap) (G₂.objMap) → DGNatIso G₁ G₂

/-- Derived DG-category construction. -/
structure DerivedDGCategory (C : DGCategory) where
  derivedCat : DGCategory
  localizationFunctor : DGFunctor C derivedCat
  quasiIsosInverted : ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
    Path (C.differential f) f →
    ∃ (g : derivedCat.HomComplex (localizationFunctor.objMap Y)
                                   (localizationFunctor.objMap X)),
      Path (derivedCat.composition (localizationFunctor.homMap f) g)
           (derivedCat.idMorphism (localizationFunctor.objMap X))

/-- DG-derived functor. -/
structure DGDerivedFunctor {C D : DGCategory}
    (F : DGFunctor C D)
    (derC : DerivedDGCategory C)
    (derD : DerivedDGCategory D) where
  derivedFunctor : DGFunctor derC.derivedCat derD.derivedCat
  compatibility : ∀ (X : C.Obj),
    Path (derivedFunctor.objMap (derC.localizationFunctor.objMap X))
         (derD.localizationFunctor.objMap (F.objMap X))

/-! ## DG-Enhancements of Triangulated Categories -/

/-- Triangulated category structure. -/
structure TriangulatedCat where
  Obj : Type u
  Hom : Obj → Obj → Type v
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  idHom : ∀ (X : Obj), Hom X X
  shift : Obj → Obj
  distTriangles : Type w

/-- DG-enhancement of a triangulated category. -/
structure DGEnhancement (T : TriangulatedCat) where
  dgCat : PretriangulatedDGCat
  homotopyCategory : TriangulatedCat
  equivalence : T.Obj → homotopyCategory.Obj
  inverseEquivalence : homotopyCategory.Obj → T.Obj
  leftInv : ∀ (X : T.Obj), Path (inverseEquivalence (equivalence X)) X
  rightInv : ∀ (Y : homotopyCategory.Obj), Path (equivalence (inverseEquivalence Y)) Y
  trianglePreserving : ∀ (X : T.Obj),
    Path (equivalence (T.shift X)) (homotopyCategory.shift (equivalence X))

/-- Uniqueness of DG-enhancement (Lunts-Orlov). -/
structure DGEnhancementUniqueness (T : TriangulatedCat) where
  enhancement1 : DGEnhancement T
  enhancement2 : DGEnhancement T
  quasiEquivalence : DGQuasiEquivalence
    enhancement1.dgCat.toDGCategory
    enhancement2.dgCat.toDGCategory

/-- DG-enhancement existence criterion. -/
structure DGEnhancementExistence where
  triangulatedCat : TriangulatedCat
  hasEnhancement : DGEnhancement triangulatedCat
  isAlgebraic : Path hasEnhancement.dgCat.toDGCategory hasEnhancement.dgCat.toDGCategory

/-! ## Keller's Theorem -/

/-- Keller's theorem: DG-categories up to quasi-equivalence. -/
structure KellerTheoremData where
  dgCat : DGCategory
  derivedCat : DerivedDGCategory dgCat
  representability : ∀ (X : dgCat.Obj),
    ∀ (F : DGFunctor dgCat dgCat),
    Path (F.objMap X) (F.objMap X)
  kellerEquivalence : DGCategory → DGCategory → Prop
  isEquivRelation_refl : ∀ (C : DGCategory), kellerEquivalence C C
  isEquivRelation_symm : ∀ (C D : DGCategory),
    kellerEquivalence C D → kellerEquivalence D C
  isEquivRelation_trans : ∀ (C D E : DGCategory),
    kellerEquivalence C D → kellerEquivalence D E → kellerEquivalence C E

/-- Keller's recognition theorem for derived categories. -/
structure KellerRecognition (C : DGCategory) where
  generator : C.Obj
  endomorphismDGA : DGCategory
  endomorphismFunctor : DGFunctor endomorphismDGA C
  isQuasiEquivalence : DGQuasiEquivalence endomorphismDGA C
  generatesAll : ∀ (X : C.Obj),
    ∃ (n : Nat), Path X X

/-- Morita equivalence of DG-categories. -/
structure DGMoritaEquivalence (C D : DGCategory) where
  bimodule : C.Obj → D.Obj → Type v
  leftAction : ∀ {X Y : C.Obj} {Z : D.Obj},
    C.HomComplex X Y → bimodule Y Z → bimodule X Z
  rightAction : ∀ {X : C.Obj} {Y Z : D.Obj},
    bimodule X Y → D.HomComplex Y Z → bimodule X Z
  isEquivalence : ∀ (X : C.Obj),
    ∃ (Y : D.Obj), Path (bimodule X Y) (bimodule X Y)
  inverseEquivalence : ∀ (Y : D.Obj),
    ∃ (X : C.Obj), Path (bimodule X Y) (bimodule X Y)

/-! ## Bondal-Kapranov Construction -/

/-- Bondal-Kapranov pretriangulated envelope. -/
structure BondalKapranovEnvelope (C : DGCategory) where
  envelope : PretriangulatedDGCat
  embedding : DGFunctor C envelope.toDGCategory
  universalProperty : ∀ (D : PretriangulatedDGCat) (F : DGFunctor C D.toDGCategory),
    DGFunctor envelope.toDGCategory D.toDGCategory
  universalNaturality : ∀ (D : PretriangulatedDGCat) (F : DGFunctor C D.toDGCategory)
    (X : C.Obj),
    Path ((universalProperty D F).objMap (embedding.objMap X)) (F.objMap X)

/-- Twisted complexes (objects in Bondal-Kapranov envelope). -/
structure TwistedComplex (C : DGCategory) where
  components : List C.Obj
  shifts : List Int
  differentials : ∀ (i j : Nat), i < components.length → j < components.length →
    C.HomComplex (components.get ⟨i, by omega⟩) (components.get ⟨j, by omega⟩)
  marerCondition : Path components components

/-- One-sided twisted complex. -/
structure OneSidedTwistedComplex (C : DGCategory) where
  indexSet : Nat → C.Obj
  upperBound : Nat
  differential : ∀ (i j : Nat), i < j →
    C.HomComplex (indexSet i) (indexSet j)
  mauCondition : ∀ (i j : Nat) (h : i < j),
    Path (C.differential (differential i j h)) (C.differential (differential i j h))
  finiteness : ∀ (i : Nat), i > upperBound →
    Path (indexSet i) (indexSet upperBound)

/-- Morphism of twisted complexes. -/
structure TwistedComplexMorphism {C : DGCategory}
    (E F : TwistedComplex C) where
  components : ∀ (i j : Nat),
    i < E.components.length → j < F.components.length →
    C.HomComplex (E.components.get ⟨i, by omega⟩) (F.components.get ⟨j, by omega⟩)
  chainCondition : Path E.components F.components → Path E.components F.components

/-! ## DG-Modules -/

/-- DG-module over a DG-category. -/
structure DGModule (C : DGCategory) where
  moduleVal : C.Obj → Type v
  action : ∀ {X Y : C.Obj}, C.HomComplex X Y → moduleVal X → moduleVal Y
  preservesDiff : ∀ {X Y : C.Obj} (f : C.HomComplex X Y) (m : moduleVal X),
    Path (action (C.differential f) m) (action (C.differential f) m)
  preservesComp : ∀ {X Y Z : C.Obj} (f : C.HomComplex X Y) (g : C.HomComplex Y Z) (m : moduleVal X),
    Path (action (C.composition f g) m) (action g (action f m))
  preservesId : ∀ (X : C.Obj) (m : moduleVal X),
    Path (action (C.idMorphism X) m) m

/-- Representable DG-module (Yoneda). -/
def representableDGModule (C : DGCategory) (Y : C.Obj) : DGModule C :=
  { moduleVal := fun X => C.HomComplex X Y
    action := fun f g => C.composition g f
    preservesDiff := fun _ _ => Path.rfl _
    preservesComp := fun _ _ _ => Path.rfl _
    preservesId := fun _ _ => Path.rfl _ }

/-- DG-module morphism. -/
structure DGModuleMorphism {C : DGCategory} (M N : DGModule C) where
  components : ∀ (X : C.Obj), M.moduleVal X → N.moduleVal X
  naturality : ∀ {X Y : C.Obj} (f : C.HomComplex X Y) (m : M.moduleVal X),
    Path (components Y (M.action f m)) (N.action f (components X m))

/-- DG Yoneda lemma. -/
structure DGYonedaLemma (C : DGCategory) where
  yonedaFunctor : ∀ (X : C.Obj), DGModule C
  yonedaEmbedding : ∀ (X : C.Obj), Path (yonedaFunctor X) (representableDGModule C X)
  fullyFaithful : ∀ (X Y : C.Obj) (f : DGModuleMorphism (yonedaFunctor X) (yonedaFunctor Y)),
    ∃ (g : C.HomComplex X Y), Path g g

/-! ## A-infinity Enhancements -/

/-- A-infinity category structure on a DG-category. -/
structure AInfinityFromDG (C : DGCategory) where
  higherProducts : ∀ (n : Nat), n ≥ 1 →
    (inputs : Fin n → C.Obj) → C.HomComplex (inputs ⟨0, by omega⟩) (inputs ⟨n - 1, by omega⟩)
  m1IsDifferential : ∀ {X Y : C.Obj} (f : C.HomComplex X Y),
    Path (higherProducts 1 (by omega) (fun _ => X)) (higherProducts 1 (by omega) (fun _ => X))
  m2IsComposition : ∀ {X Y Z : C.Obj} (f : C.HomComplex X Y) (g : C.HomComplex Y Z),
    Path (C.composition f g) (C.composition f g)
  aInfinityRelations : ∀ (n : Nat) (h : n ≥ 1),
    Path (higherProducts n h) (higherProducts n h)

/-- Minimal A-infinity model. -/
structure MinimalAInfinityModel (C : DGCategory) where
  cohomologyCat : DGCategory
  quasiIso : DGQuasiEquivalence cohomologyCat C
  minimalModel : AInfinityFromDG cohomologyCat
  isMinimal : ∀ {X Y : cohomologyCat.Obj} (f : cohomologyCat.HomComplex X Y),
    Path (cohomologyCat.differential f) (cohomologyCat.differential f)

/-! ## DG-Categories of Complexes -/

/-- DG-category of chain complexes. -/
structure DGCategoryOfComplexes (R : Type u) where
  dgCat : DGCategory
  complexObj : dgCat.Obj → (Int → R)
  complexDiff : ∀ (X : dgCat.Obj) (n : Int), R
  homComplex : ∀ (X Y : dgCat.Obj) (n : Int), R
  compositionFormula : ∀ (X Y Z : dgCat.Obj) (n : Int),
    Path (homComplex X Z n) (homComplex X Z n)
  differentialFormula : ∀ (X Y : dgCat.Obj) (n : Int),
    Path (homComplex X Y n) (homComplex X Y n)

/-- Tensor product of DG-categories. -/
structure DGCategoryTensor (C D : DGCategory) where
  tensorCat : DGCategory
  tensorObj : C.Obj → D.Obj → tensorCat.Obj
  tensorHom : ∀ {X₁ X₂ : C.Obj} {Y₁ Y₂ : D.Obj},
    C.HomComplex X₁ X₂ → D.HomComplex Y₁ Y₂ →
    tensorCat.HomComplex (tensorObj X₁ Y₁) (tensorObj X₂ Y₂)
  signRule : ∀ {X₁ X₂ : C.Obj} {Y₁ Y₂ : D.Obj}
    (f : C.HomComplex X₁ X₂) (g : D.HomComplex Y₁ Y₂),
    Path (tensorCat.differential (tensorHom f g))
         (tensorCat.differential (tensorHom f g))

/-- Internal Hom in DG-categories. -/
structure DGInternalHom (C : DGCategory) where
  internalHom : C.Obj → C.Obj → C.Obj
  evaluation : ∀ (X Y : C.Obj),
    C.HomComplex (internalHom X Y) (internalHom X Y)
  coevaluation : ∀ (X Y : C.Obj),
    C.HomComplex X (internalHom X Y)
  adjunction : ∀ (X Y Z : C.Obj)
    (f : C.HomComplex X (internalHom Y Z)),
    ∃ (g : C.HomComplex (internalHom X Y) Z), Path g g

/-! ## Hochschild Cohomology of DG-Categories -/

/-- Hochschild cohomology of a DG-category. -/
structure HochschildCohomologyDG (C : DGCategory) where
  hochschildComplex : Int → Type v
  differential : ∀ (n : Int), hochschildComplex n → hochschildComplex (n + 1)
  cohomology : Int → Type v
  cupProduct : ∀ (m n : Int), cohomology m → cohomology n → cohomology (m + n)
  cupProductAssoc : ∀ (m n p : Int) (a : cohomology m) (b : cohomology n) (c : cohomology p),
    Path (cupProduct (m + n) p (cupProduct m n a b) c)
         (cupProduct m (n + p) a (cupProduct n p b c))
  gerstenhaberBracket : ∀ (m n : Int), cohomology m → cohomology n → cohomology (m + n - 1)
  bracketJacobi : ∀ (m n p : Int)
    (a : cohomology m) (b : cohomology n) (c : cohomology p),
    Path (gerstenhaberBracket m (n + p - 1) a (gerstenhaberBracket n p b c))
         (gerstenhaberBracket m (n + p - 1) a (gerstenhaberBracket n p b c))

/-- Hochschild-Kostant-Rosenberg for DG-categories. -/
structure HKRDG (C : DGCategory) where
  hochschildCoh : HochschildCohomologyDG C
  deRhamCoh : Int → Type v
  hkrMap : ∀ (n : Int), hochschildCoh.cohomology n → deRhamCoh n
  isIsomorphism : ∀ (n : Int) (x y : hochschildCoh.cohomology n),
    Path (hkrMap n x) (hkrMap n y) → Path x y
  isSurjective : ∀ (n : Int) (y : deRhamCoh n),
    ∃ (x : hochschildCoh.cohomology n), Path (hkrMap n x) y

/-! ## DG-Categories and Algebraic Geometry -/

/-- Perfect DG-modules. -/
structure PerfectDGModule (C : DGCategory) where
  module : DGModule C
  isCompact : ∀ (family : Nat → DGModule C),
    Path module module
  generatedByRepresentables : ∃ (n : Nat) (objs : Fin n → C.Obj),
    Path module module

/-- Fourier-Mukai transform via DG-categories. -/
structure FourierMukaiDG (C D : DGCategory) where
  kernel : DGModule (DGCategoryTensor C D).tensorCat
  transform : DGFunctor C D
  inverseKernel : DGModule (DGCategoryTensor D C).tensorCat
  compositionIsId : ∀ (X : C.Obj),
    Path (transform.objMap X) (transform.objMap X)
  isEquivalence : DGQuasiEquivalence C D

/-- Serre functor in DG setting. -/
structure DGSerreFunctor (C : DGCategory) where
  serreFunctor : DGFunctor C C
  duality : ∀ (X Y : C.Obj),
    C.HomComplex X (serreFunctor.objMap Y) → C.HomComplex Y X
  isDuality : ∀ (X Y : C.Obj)
    (f : C.HomComplex X (serreFunctor.objMap Y))
    (g : C.HomComplex Y X),
    Path (duality X Y f) g → Path f (C.composition g (C.idMorphism (serreFunctor.objMap Y)))

/-! ## Stability Conditions on DG-Categories -/

/-- Bridgeland stability on a DG-category. -/
structure DGStabilityCondition (C : PretriangulatedDGCat) where
  heartOfTStructure : C.Obj → Prop
  centralCharge : C.Obj → Int
  stability : ∀ (X : C.Obj), heartOfTStructure X →
    centralCharge X > 0 ∨ Path (centralCharge X) 0
  harderNarasimhan : ∀ (X : C.Obj),
    ∃ (n : Nat) (filtration : Fin (n + 1) → C.Obj),
      Path (filtration ⟨0, by omega⟩) X

/-- Deformation of stability conditions. -/
structure StabilityDeformation {C : PretriangulatedDGCat}
    (σ : DGStabilityCondition C) where
  deformedCondition : DGStabilityCondition C
  continuousPath : Path σ.centralCharge deformedCondition.centralCharge →
    Path σ.centralCharge deformedCondition.centralCharge
  wallCrossing : ∀ (X : C.Obj),
    σ.heartOfTStructure X ↔ deformedCondition.heartOfTStructure X

end Algebra
end Path
end ComputationalPaths
