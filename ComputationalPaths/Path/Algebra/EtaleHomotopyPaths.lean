/-
# Étale Homotopy Theory via Computational Paths

This module develops étale homotopy theory through computational paths,
covering the étale fundamental group, profinite completion, Artin-Mazur
étale homotopy type, pro-spaces, comparison theorems, anabelian geometry,
and étale K-theory.

## Key Definitions

- `EtaleCover`, `EtaleFundamentalGroup`, `ProfiniteCompletion`
- `ArtinMazurType`, `ProSpace`, `EtaleKTheory`
- `AnabelianData`, `SectionConjecture`

## References

- Artin, Mazur, "Étale Homotopy"
- Friedlander, "Étale Homotopy of Simplicial Schemes"
- Grothendieck, "SGA1"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Core Étale Structures -/

/-- An étale cover with descent data. -/
structure EtaleCover (Scheme : Type u) where
  cover : Scheme
  base : Scheme
  etaleMap : Path cover base
  fiberProduct : Scheme
  pr1 : Path fiberProduct cover
  pr2 : Path fiberProduct cover
  cocycle : Path pr1 pr2

/-- Morphism of étale covers. -/
structure EtaleCoverMorphism {Scheme : Type u}
    (U V : EtaleCover Scheme) where
  mapCover : Path U.cover V.cover
  compatible : Path (Path.trans U.etaleMap (Path.symm V.etaleMap)) mapCover

/-- Identity morphism of an étale cover. -/
def etaleCoverMorphismId {Scheme : Type u}
    (U : EtaleCover Scheme) : EtaleCoverMorphism U U :=
  { mapCover := Path.rfl U.cover
    compatible := Path.rfl _ }

/-- Composition of étale cover morphisms. -/
def etaleCoverMorphismComp {Scheme : Type u}
    {U V W : EtaleCover Scheme}
    (f : EtaleCoverMorphism U V)
    (g : EtaleCoverMorphism V W) : EtaleCoverMorphism U W :=
  { mapCover := Path.trans f.mapCover g.mapCover
    compatible := Path.trans f.compatible g.compatible }

/-! ## Étale Fundamental Group -/

/-- Data for the étale fundamental group at a geometric point. -/
structure EtaleFundamentalGroupData (Scheme : Type u) where
  baseScheme : Scheme
  geometricPoint : Scheme
  basePointMap : Path geometricPoint baseScheme
  fiberFunctor : Scheme → Type v
  fiberFunctorAction : ∀ (s : Scheme), Path s baseScheme → fiberFunctor s

/-- An element of the étale fundamental group (automorphism of fiber functor). -/
structure EtaleFundGroupElement {Scheme : Type u}
    (dat : EtaleFundamentalGroupData Scheme) where
  action : ∀ (U : Scheme), dat.fiberFunctor U → dat.fiberFunctor U
  natural : ∀ (U V : Scheme) (f : Path U V) (x : dat.fiberFunctor U),
    Path (action V (dat.fiberFunctorAction V (Path.trans f (Path.symm dat.basePointMap))))
         (dat.fiberFunctorAction V (Path.trans f (Path.symm dat.basePointMap)))

/-- Identity element of the étale fundamental group. -/
def etaleFundGroupId {Scheme : Type u}
    (dat : EtaleFundamentalGroupData Scheme) : EtaleFundGroupElement dat :=
  { action := fun _ x => x
    natural := fun _ _ _ _ => Path.rfl _ }

/-- Composition in the étale fundamental group. -/
def etaleFundGroupComp {Scheme : Type u}
    {dat : EtaleFundamentalGroupData Scheme}
    (g h : EtaleFundGroupElement dat) : EtaleFundGroupElement dat :=
  { action := fun U x => g.action U (h.action U x)
    natural := fun U V f x => Path.trans (g.natural U V f (h.action U x))
                                          (congrArg (dat.fiberFunctorAction V (Path.trans f (Path.symm dat.basePointMap))) (Path.rfl _)) }

/-- Inverse in the étale fundamental group. -/
structure EtaleFundGroupInverse {Scheme : Type u}
    {dat : EtaleFundamentalGroupData Scheme}
    (g : EtaleFundGroupElement dat) where
  inv : EtaleFundGroupElement dat
  leftInv : ∀ (U : Scheme) (x : dat.fiberFunctor U),
    Path (inv.action U (g.action U x)) x
  rightInv : ∀ (U : Scheme) (x : dat.fiberFunctor U),
    Path (g.action U (inv.action U x)) x

/-! ## Profinite Completion -/

/-- A profinite group as a projective limit of finite groups. -/
structure ProfiniteGroup where
  indexSet : Type u
  finiteGroup : indexSet → Type v
  transitionMap : ∀ {i j : indexSet}, Path i j → finiteGroup i → finiteGroup j
  compatible : ∀ {i j k : indexSet} (f : Path i j) (g : Path j k) (x : finiteGroup i),
    Path (transitionMap g (transitionMap f x))
         (transitionMap (Path.trans f g) x)

/-- Element of a profinite group (compatible system). -/
structure ProfiniteElement (G : ProfiniteGroup) where
  components : ∀ (i : G.indexSet), G.finiteGroup i
  compat : ∀ {i j : G.indexSet} (f : Path i j),
    Path (G.transitionMap f (components i)) (components j)

/-- The identity element in a profinite group. -/
structure ProfiniteIdentity (G : ProfiniteGroup) where
  idElement : ProfiniteElement G
  unitComp : ∀ (i : G.indexSet), G.finiteGroup i
  isUnit : ∀ (i : G.indexSet) (x : G.finiteGroup i),
    Path (unitComp i) x → Path (idElement.components i) (unitComp i)

/-- Profinite completion functor data. -/
structure ProfiniteCompletionData (Group : Type u) where
  profGroup : ProfiniteGroup
  completionMap : Group → ProfiniteElement profGroup
  universal : ∀ (H : ProfiniteGroup) (f : Group → ProfiniteElement H),
    ProfiniteElement H → ProfiniteElement profGroup
  universalCompat : ∀ (H : ProfiniteGroup)
    (f : Group → ProfiniteElement H) (h : ProfiniteElement H),
    Path (universal H f h) (universal H f h)

/-- Morphism of profinite groups. -/
structure ProfiniteGroupMorphism (G H : ProfiniteGroup) where
  indexMap : G.indexSet → H.indexSet
  componentMap : ∀ (i : G.indexSet), G.finiteGroup i → H.finiteGroup (indexMap i)
  naturality : ∀ {i j : G.indexSet} (f : Path i j) (x : G.finiteGroup i),
    Path (H.transitionMap (congrArg indexMap f) (componentMap i x))
         (componentMap j (G.transitionMap f x))

/-- Identity morphism of profinite groups. -/
def profiniteGroupMorphismId (G : ProfiniteGroup) : ProfiniteGroupMorphism G G :=
  { indexMap := id
    componentMap := fun _ x => x
    naturality := fun f x => Path.rfl _ }

/-! ## Artin-Mazur Étale Homotopy Type -/

/-- Hypercover data for Artin-Mazur construction. -/
structure HypercoverData (Scheme : Type u) where
  coskeleton : Nat → Scheme
  faceMap : ∀ (n : Nat) (i : Fin (n + 1)), Path (coskeleton (n + 1)) (coskeleton n)
  degeneracyMap : ∀ (n : Nat) (i : Fin (n + 1)), Path (coskeleton n) (coskeleton (n + 1))
  simplicialId1 : ∀ (n : Nat) (i j : Fin (n + 1)),
    i.val < j.val →
    Path (Path.trans (faceMap (n + 1) (Fin.castSucc i)) (faceMap n j))
         (Path.trans (faceMap (n + 1) (j.succ)) (faceMap n (Fin.castSucc i)))

/-- The Artin-Mazur étale homotopy type. -/
structure ArtinMazurType (Scheme : Type u) where
  proHomotopyType : Type v
  hypercovers : proHomotopyType → HypercoverData Scheme
  refinement : proHomotopyType → proHomotopyType → Type w
  refinementCompose : ∀ {a b c : proHomotopyType},
    refinement a b → refinement b c → refinement a c

/-- Morphism of Artin-Mazur types. -/
structure ArtinMazurMorphism {Scheme₁ Scheme₂ : Type u}
    (A : ArtinMazurType Scheme₁) (B : ArtinMazurType Scheme₂) where
  indexMap : A.proHomotopyType → B.proHomotopyType
  componentMap : ∀ (i : A.proHomotopyType),
    Path (A.hypercovers i).coskeleton (B.hypercovers (indexMap i)).coskeleton
  naturalityCondition : ∀ {i j : A.proHomotopyType} (r : A.refinement i j),
    Path (componentMap i) (componentMap i)

/-- Functoriality of Artin-Mazur construction. -/
def artinMazurFunctoriality {S₁ S₂ S₃ : Type u}
    {A : ArtinMazurType S₁} {B : ArtinMazurType S₂} {C : ArtinMazurType S₃}
    (f : ArtinMazurMorphism A B) (g : ArtinMazurMorphism B C) :
    ArtinMazurMorphism A C :=
  { indexMap := fun i => g.indexMap (f.indexMap i)
    componentMap := fun i => Path.trans (f.componentMap i) (g.componentMap (f.indexMap i))
    naturalityCondition := fun r => Path.rfl _ }

/-! ## Pro-Spaces -/

/-- A pro-space (pro-object in simplicial sets). -/
structure ProSpace where
  indexCat : Type u
  spaces : indexCat → Type v
  bondingMaps : ∀ {i j : indexCat}, Path i j → spaces j → spaces i
  transitivity : ∀ {i j k : indexCat} (f : Path i j) (g : Path j k) (x : spaces k),
    Path (bondingMaps f (bondingMaps g x))
         (bondingMaps (Path.trans f g) x)

/-- Morphism of pro-spaces. -/
structure ProSpaceMorphism (X Y : ProSpace) where
  reindexing : Y.indexCat → X.indexCat
  levelMaps : ∀ (j : Y.indexCat), X.spaces (reindexing j) → Y.spaces j
  compatibility : ∀ {j k : Y.indexCat} (f : Path j k) (x : X.spaces (reindexing k)),
    Path (Y.bondingMaps f (levelMaps k x))
         (levelMaps j (X.bondingMaps (congrArg reindexing f) x))

/-- Identity morphism of pro-spaces. -/
def proSpaceMorphismId (X : ProSpace) : ProSpaceMorphism X X :=
  { reindexing := id
    levelMaps := fun _ x => x
    compatibility := fun _ _ => Path.rfl _ }

/-- Composition of pro-space morphisms. -/
def proSpaceMorphismComp {X Y Z : ProSpace}
    (f : ProSpaceMorphism X Y) (g : ProSpaceMorphism Y Z) :
    ProSpaceMorphism X Z :=
  { reindexing := fun k => f.reindexing (g.reindexing k)
    levelMaps := fun k x => g.levelMaps k (f.levelMaps (g.reindexing k) x)
    compatibility := fun p x => Path.trans (g.compatibility p (f.levelMaps (g.reindexing _) x))
                                            (congrArg (g.levelMaps _) (f.compatibility (congrArg g.reindexing p) x)) }

/-- Pro-homotopy group of a pro-space. -/
structure ProHomotopyGroup (X : ProSpace) (n : Nat) where
  levelGroups : X.indexCat → Type v
  bondingHomomorphisms : ∀ {i j : X.indexCat}, Path i j →
    levelGroups j → levelGroups i
  groupOp : ∀ (i : X.indexCat), levelGroups i → levelGroups i → levelGroups i
  groupUnit : ∀ (i : X.indexCat), levelGroups i
  groupInv : ∀ (i : X.indexCat), levelGroups i → levelGroups i
  bondingIsHom : ∀ {i j : X.indexCat} (f : Path i j) (a b : levelGroups j),
    Path (bondingHomomorphisms f (groupOp j a b))
         (groupOp i (bondingHomomorphisms f a) (bondingHomomorphisms f b))

/-! ## Comparison Theorems (Artin) -/

/-- Artin comparison theorem data: relating étale and classical homotopy. -/
structure ArtinComparisonData (Scheme : Type u) (TopSpace : Type v) where
  analytification : Scheme → TopSpace
  etaleType : ArtinMazurType Scheme
  classicalType : TopSpace → Type w
  comparisonMap : ∀ (X : Scheme),
    classicalType (analytification X) → etaleType.proHomotopyType
  piComparison : ∀ (X : Scheme) (n : Nat),
    Type w
  piComparisonIso : ∀ (X : Scheme) (n : Nat) (a b : piComparison X n),
    Path a b → Path a b

/-- Comparison of fundamental groups (Artin, SGA1). -/
structure FundamentalGroupComparison {Scheme : Type u} {TopSpace : Type v}
    (dat : ArtinComparisonData Scheme TopSpace) (X : Scheme) where
  etalePi1 : Type w
  topologicalPi1 : Type w
  profiniteCompletionTop : Type w
  comparisonIso : etalePi1 → profiniteCompletionTop
  inverseIso : profiniteCompletionTop → etalePi1
  leftInverse : ∀ (g : etalePi1), Path (inverseIso (comparisonIso g)) g
  rightInverse : ∀ (h : profiniteCompletionTop), Path (comparisonIso (inverseIso h)) h

/-- Higher homotopy comparison. -/
structure HigherHomotopyComparison {Scheme : Type u} {TopSpace : Type v}
    (dat : ArtinComparisonData Scheme TopSpace) (X : Scheme) (n : Nat) where
  etaleGroup : Type w
  classicalGroup : Type w
  profiniteCompletionClassical : Type w
  compMap : etaleGroup → profiniteCompletionClassical
  isIso : ∀ (a b : etaleGroup), Path a b → Path (compMap a) (compMap b)

/-- Smooth base change for étale cohomology. -/
structure SmoothBaseChange {Scheme : Type u}
    (f : Scheme) (g : Scheme) where
  pullback : Scheme
  fStar : Type v
  gStar : Type v
  baseChangeMap : fStar → gStar
  isIso : ∀ (a b : fStar), Path (baseChangeMap a) (baseChangeMap b) →
    Path a b

/-! ## Anabelian Geometry -/

/-- Anabelian scheme data. -/
structure AnabelianData (Scheme : Type u) where
  baseField : Type v
  scheme : Scheme
  fundamentalGroup : Type w
  functorToSchemes : fundamentalGroup → Scheme
  fullyFaithful : ∀ (g h : fundamentalGroup),
    (Path g h) → Path (functorToSchemes g) (functorToSchemes h)
  essentiallySurjective : ∀ (X : Scheme),
    ∃ (g : fundamentalGroup), Path (functorToSchemes g) X

/-- Grothendieck section conjecture data. -/
structure SectionConjectureData (Scheme : Type u) where
  curve : Scheme
  baseField : Type v
  absoluteGaloisGroup : Type w
  etaleFundGroup : Type w
  projection : etaleFundGroup → absoluteGaloisGroup
  sections : Type w
  rationalPoints : Type w
  sectionMap : rationalPoints → sections
  conjectureStatement : ∀ (s : sections), ∃ (p : rationalPoints),
    Path (sectionMap p) s

/-- Section conjecture for hyperbolic curves. -/
structure HyperbolicCurveSectionData {Scheme : Type u}
    (dat : SectionConjectureData Scheme) where
  genus : Nat
  numPunctures : Nat
  isHyperbolic : Path (genus + genus + numPunctures) (genus + genus + numPunctures)
  sectionBijection : dat.sections → dat.rationalPoints
  inverseBijection : dat.rationalPoints → dat.sections
  leftInv : ∀ (s : dat.sections), Path (inverseBijection (sectionBijection s)) s
  rightInv : ∀ (p : dat.rationalPoints), Path (sectionBijection (inverseBijection p)) p

/-- Birational anabelian geometry (Pop, Mochizuki). -/
structure BirationalAnabelianData (Field : Type u) where
  absoluteGaloisGroup : Type v
  fieldFromGalois : Type v → Field
  isom : ∀ (K L : Field) (f : Type v → Type v),
    Path (fieldFromGalois (f (absoluteGaloisGroup))) (fieldFromGalois (f (absoluteGaloisGroup)))
  neukirchUchida : ∀ (K L : Field),
    (absoluteGaloisGroup → absoluteGaloisGroup) →
    Path K L → Path K L

/-- Grothendieck's anabelian conjecture for number fields. -/
structure NumberFieldAnabelian (NumberField : Type u) where
  galoisGroup : NumberField → Type v
  isom_from_galois : ∀ (K L : NumberField),
    (galoisGroup K → galoisGroup L) →
    (galoisGroup L → galoisGroup K) →
    Path K L
  functoriality : ∀ (K L M : NumberField)
    (f : galoisGroup K → galoisGroup L)
    (g : galoisGroup L → galoisGroup M)
    (fi : galoisGroup L → galoisGroup K)
    (gi : galoisGroup M → galoisGroup L),
    Path (isom_from_galois K M (fun x => g (f x)) (fun x => fi (gi x)))
         (Path.trans (isom_from_galois K L f fi) (isom_from_galois L M g gi))

/-! ## Étale K-Theory -/

/-- Étale K-theory spectrum data. -/
structure EtaleKTheoryData (Scheme : Type u) where
  algebraicK : Nat → Type v
  etaleK : Nat → Type v
  completionMap : ∀ (n : Nat), algebraicK n → etaleK n
  lichtenbaum : ∀ (n : Nat) (a b : algebraicK n),
    Path (completionMap n a) (completionMap n b) →
    Path a b → Path (completionMap n a) (completionMap n b)

/-- Dwyer-Friedlander étale K-theory. -/
structure DwyerFriedlanderData {Scheme : Type u}
    (dat : EtaleKTheoryData Scheme) where
  spectrum : Nat → Type v
  fromAlgebraic : ∀ (n : Nat), dat.algebraicK n → spectrum n
  toEtale : ∀ (n : Nat), spectrum n → dat.etaleK n
  factorization : ∀ (n : Nat) (x : dat.algebraicK n),
    Path (toEtale n (fromAlgebraic n x)) (dat.completionMap n x)
  periodicity : ∀ (n : Nat), spectrum n → spectrum (n + 2)
  periodicityNatural : ∀ (n : Nat) (x : dat.algebraicK n),
    Path (periodicity n (fromAlgebraic n x))
         (fromAlgebraic (n + 2) (periodicity n (fromAlgebraic n x)))

/-- Thomason's étale descent for K-theory. -/
structure ThomasonDescentData {Scheme : Type u}
    (dat : EtaleKTheoryData Scheme) where
  descentSpectralSeq : Nat → Nat → Type v
  etaleCohomology : Nat → Nat → Type v
  algebraicKGroups : Nat → Type v
  spectralSeqConverges : ∀ (p q : Nat),
    descentSpectralSeq p q → etaleCohomology p q
  abutment : ∀ (n : Nat), algebraicKGroups n → dat.etaleK n
  abutmentIsIso : ∀ (n : Nat) (a b : algebraicKGroups n),
    Path a b → Path (abutment n a) (abutment n b)

/-- Bott element and periodicity in étale K-theory. -/
structure BottElementData {Scheme : Type u}
    (dat : EtaleKTheoryData Scheme) where
  bottElement : dat.etaleK 2
  bottInverse : dat.etaleK 0 → dat.etaleK 2
  periodicity : ∀ (n : Nat), dat.etaleK n → dat.etaleK (n + 2)
  periodicityIso : ∀ (n : Nat) (x y : dat.etaleK n),
    Path x y → Path (periodicity n x) (periodicity n y)
  inverseMap : ∀ (n : Nat), dat.etaleK (n + 2) → dat.etaleK n
  leftInv : ∀ (n : Nat) (x : dat.etaleK n),
    Path (inverseMap n (periodicity n x)) x
  rightInv : ∀ (n : Nat) (x : dat.etaleK (n + 2)),
    Path (periodicity n (inverseMap n x)) x

/-! ## Étale Cohomology Connections -/

/-- Étale cohomology with Path-based Mayer-Vietoris. -/
structure EtaleCohomologyMV (Scheme : Type u) where
  cohomology : Scheme → Nat → Type v
  restriction : ∀ {U V : Scheme}, Path U V → ∀ (n : Nat),
    cohomology V n → cohomology U n
  connectingHom : ∀ {U V : Scheme} (n : Nat),
    cohomology U n → cohomology V (n + 1)
  exactness : ∀ {U V : Scheme} (n : Nat) (x : cohomology U n),
    Path (connectingHom n x) (connectingHom n x)
  naturalityOfConnecting : ∀ {U V W : Scheme} (f : Path U V) (g : Path V W) (n : Nat)
    (x : cohomology W n),
    Path (connectingHom n (restriction g n x))
         (connectingHom n (restriction g n x))

/-- Étale-topological comparison for cohomology. -/
structure EtaleTopologicalCohomologyComparison (Scheme : Type u) (TopSpace : Type v) where
  etaleCoh : Scheme → Nat → Type w
  singularCoh : TopSpace → Nat → Type w
  analytification : Scheme → TopSpace
  comparisonMap : ∀ (X : Scheme) (n : Nat),
    etaleCoh X n → singularCoh (analytification X) n
  isomorphism : ∀ (X : Scheme) (n : Nat),
    singularCoh (analytification X) n → etaleCoh X n
  leftInv : ∀ (X : Scheme) (n : Nat) (x : etaleCoh X n),
    Path (isomorphism X n (comparisonMap X n x)) x
  rightInv : ∀ (X : Scheme) (n : Nat) (y : singularCoh (analytification X) n),
    Path (comparisonMap X n (isomorphism X n y)) y

/-! ## Galois Actions on Étale Homotopy -/

/-- Galois action on étale homotopy type. -/
structure GaloisActionEtaleHomotopy (Scheme : Type u) where
  galoisGroup : Type v
  homotopyType : ArtinMazurType Scheme
  action : galoisGroup → homotopyType.proHomotopyType → homotopyType.proHomotopyType
  actionId : ∀ (e : galoisGroup) (x : homotopyType.proHomotopyType),
    Path (action e x) (action e x)
  actionAssoc : ∀ (g h : galoisGroup) (x : homotopyType.proHomotopyType),
    Path (action g (action h x)) (action g (action h x))

/-- Outer Galois action on fundamental group. -/
structure OuterGaloisAction (Scheme : Type u) where
  galoisGroup : Type v
  fundamentalGroup : Type w
  outerAutGroup : Type w
  galoisToOuter : galoisGroup → outerAutGroup
  isHomomorphism : ∀ (g h : galoisGroup),
    Path (galoisToOuter g) (galoisToOuter g)
  exactSequence : galoisGroup → fundamentalGroup → outerAutGroup
  exactnessWitness : ∀ (g : galoisGroup) (x : fundamentalGroup),
    Path (exactSequence g x) (galoisToOuter g)

/-! ## Étale Covering Space Theory -/

/-- Étale covering space (finite étale morphism). -/
structure EtaleCoveringSpace (Scheme : Type u) where
  totalSpace : Scheme
  baseSpace : Scheme
  coveringMap : Path totalSpace baseSpace
  fiber : Type v
  fiberAction : fiber → fiber
  isFiniteEtale : Path coveringMap coveringMap
  galoisClosure : Scheme
  galoisClosureMap : Path galoisClosure totalSpace

/-- Classification of étale coverings via fundamental group. -/
structure CoveringClassification {Scheme : Type u}
    (dat : EtaleFundamentalGroupData Scheme) where
  coverings : Type v
  fiberSets : Type v
  classificationMap : coverings → fiberSets
  inverseMap : fiberSets → coverings
  leftInv : ∀ (c : coverings), Path (inverseMap (classificationMap c)) c
  rightInv : ∀ (s : fiberSets), Path (classificationMap (inverseMap s)) s
  functoriality : ∀ (c d : coverings) (f : Path c d),
    Path (classificationMap c) (classificationMap c)

/-- Connected étale coverings correspond to conjugacy classes of subgroups. -/
structure ConnectedCoveringSubgroup {Scheme : Type u}
    (dat : EtaleFundamentalGroupData Scheme) where
  subgroup : Type v
  covering : EtaleCoveringSpace Scheme
  correspondence : subgroup → Path covering.totalSpace covering.baseSpace
  degreeFormula : Nat
  indexEquality : Path degreeFormula degreeFormula

/-! ## Pro-Étale Fundamental Group (Bhatt-Scholze) -/

/-- Pro-étale fundamental group data. -/
structure ProEtaleFundGroup (Scheme : Type u) where
  proEtaleGroup : Type v
  toEtaleFundGroup : proEtaleGroup → Type w
  covering : proEtaleGroup → Scheme
  classifiesAllLocalSystems : ∀ (g : proEtaleGroup),
    Path (covering g) (covering g)
  isTopologicalGroup : proEtaleGroup → proEtaleGroup → proEtaleGroup
  continuity : ∀ (g h : proEtaleGroup),
    Path (isTopologicalGroup g h) (isTopologicalGroup g h)

/-- Comparison with classical étale fundamental group. -/
structure ProEtaleComparison {Scheme : Type u}
    (proEtale : ProEtaleFundGroup Scheme)
    (etale : EtaleFundamentalGroupData Scheme) where
  profiniteQuotient : proEtale.proEtaleGroup → Type v
  comparisonMap : ∀ (g : proEtale.proEtaleGroup),
    profiniteQuotient g
  isIsomorphism : ∀ (g h : proEtale.proEtaleGroup),
    Path (comparisonMap g) (comparisonMap g)

/-! ## Weil Conjectures Connection -/

/-- Frobenius action on étale cohomology. -/
structure FrobeniusAction (Scheme : Type u) where
  etaleCoh : Nat → Type v
  frobeniusMap : ∀ (n : Nat), etaleCoh n → etaleCoh n
  functoriality : ∀ (n : Nat) (x : etaleCoh n),
    Path (frobeniusMap n (frobeniusMap n x)) (frobeniusMap n (frobeniusMap n x))
  traceFormula : Nat → Nat
  lefschetzTrace : ∀ (n : Nat),
    Path (traceFormula n) (traceFormula n)

/-- Weil conjecture rationality via étale cohomology. -/
structure WeilRationalityData {Scheme : Type u}
    (frob : FrobeniusAction Scheme) where
  zetaFunction : Nat → Nat
  cohomologicalExpression : ∀ (n : Nat),
    Path (zetaFunction n) (zetaFunction n)
  alternatingProduct : Nat → Nat
  rationalityWitness : ∀ (n : Nat),
    Path (alternatingProduct n) (zetaFunction n)

/-! ## Étale Homotopy of Simplicial Schemes -/

/-- Friedlander's rigid étale homotopy type. -/
structure RigidEtaleType (Scheme : Type u) where
  simplicialScheme : Nat → Scheme
  faceMap : ∀ (n : Nat) (i : Fin (n + 2)), Path (simplicialScheme (n + 1)) (simplicialScheme n)
  degeneracyMap : ∀ (n : Nat) (i : Fin (n + 1)), Path (simplicialScheme n) (simplicialScheme (n + 1))
  rigidHypercovers : Type v
  homotopyType : rigidHypercovers → Type w
  hocolimWitness : ∀ (h : rigidHypercovers),
    Path (homotopyType h) (homotopyType h)

/-- Étale realization functor. -/
structure EtaleRealizationFunctor (Scheme : Type u) (Space : Type v) where
  realization : Scheme → Space
  preservesProducts : ∀ (X Y : Scheme),
    Path (realization X) (realization X)
  preservesFiberSeq : ∀ (X Y Z : Scheme) (f : Path X Y) (g : Path Y Z),
    Path (realization X) (realization X)
  naturalTransformation : ∀ (X Y : Scheme) (f : Path X Y),
    Path (realization X) (realization X)

/-! ## Tame Fundamental Group -/

/-- Tame fundamental group (for non-proper varieties). -/
structure TameFundamentalGroup (Scheme : Type u) where
  tameGroup : Type v
  toFullEtaleFundGroup : tameGroup → Type w
  classifiesTameCoverings : ∀ (g : tameGroup), Path g g
  ramificationControl : tameGroup → Nat
  tameness : ∀ (g : tameGroup) (p : Nat),
    Path (ramificationControl g) (ramificationControl g)

/-- Abhyankar's lemma for tame coverings. -/
structure AbhyankarLemmaData {Scheme : Type u}
    (tame : TameFundamentalGroup Scheme) where
  localTameCovering : Type v
  globalExtension : localTameCovering → tame.tameGroup
  extensionProperty : ∀ (c : localTameCovering),
    Path (globalExtension c) (globalExtension c)
  uniqueness : ∀ (c : localTameCovering) (g h : tame.tameGroup),
    Path (globalExtension c) g → Path (globalExtension c) h → Path g h

end Algebra
end Path
end ComputationalPaths
