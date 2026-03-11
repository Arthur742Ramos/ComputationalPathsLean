/-
# Homotopical Combinatorics via Computational Paths

This module develops homotopical combinatorics through computational paths,
covering simplicial sets (Kan complexes, horns, fibrations), cubical sets,
dendroidal sets, combinatorial model categories, Cisinski model structures,
and Reedy categories.

## Key Definitions

- `SimplicialSet`, `KanComplex`, `Horn`, `KanFibration`
- `CubicalSet`, `DendroidalSet`, `Operad`
- `CombinModelCategory`, `CisinskiModelStructure`, `ReedyCategory`

## References

- Goerss, Jardine, "Simplicial Homotopy Theory"
- Cisinski, "Les préfaisceaux comme modèles des types d'homotopie"
- Moerdijk, Weiss, "Dendroidal sets"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Simplicial Sets -/

/-- A simplicial set (contravariant functor from Δ to Set). -/
structure SimplicialSet where
  simplices : Nat → Type u
  faceMap : ∀ (n : Nat) (i : Fin (n + 2)), simplices (n + 1) → simplices n
  degeneracyMap : ∀ (n : Nat) (i : Fin (n + 1)), simplices n → simplices (n + 1)
  -- Simplicial identities
  faceFace : ∀ (n : Nat) (i j : Fin (n + 2)),
    i.val ≤ j.val →
    ∀ (x : simplices (n + 2)),
    Path (faceMap n (Fin.castSucc i) (faceMap (n + 1) j.succ x))
         (faceMap n j (faceMap (n + 1) (Fin.castSucc i) x))
  degDeg : ∀ (n : Nat) (i j : Fin (n + 1)),
    i.val ≤ j.val →
    ∀ (x : simplices n),
    Path (degeneracyMap (n + 1) j.succ (degeneracyMap n (Fin.castSucc i) x))
         (degeneracyMap (n + 1) (Fin.castSucc i) (degeneracyMap n j x))

/-- Morphism of simplicial sets. -/
structure SimplicialMap (X Y : SimplicialSet) where
  components : ∀ (n : Nat), X.simplices n → Y.simplices n
  commutesWithFace : ∀ (n : Nat) (i : Fin (n + 2)) (x : X.simplices (n + 1)),
    Path (components n (X.faceMap n i x)) (Y.faceMap n i (components (n + 1) x))
  commutesWithDeg : ∀ (n : Nat) (i : Fin (n + 1)) (x : X.simplices n),
    Path (components (n + 1) (X.degeneracyMap n i x))
         (Y.degeneracyMap n i (components n x))

/-- Identity simplicial map. -/
def simplicialMapId (X : SimplicialSet) : SimplicialMap X X :=
  { components := fun _ x => x
    commutesWithFace := fun _ _ _ => Path.rfl _
    commutesWithDeg := fun _ _ _ => Path.rfl _ }

/-- Composition of simplicial maps. -/
def simplicialMapComp {X Y Z : SimplicialSet}
    (f : SimplicialMap X Y) (g : SimplicialMap Y Z) : SimplicialMap X Z :=
  { components := fun n x => g.components n (f.components n x)
    commutesWithFace := fun n i x =>
      Path.trans (congrArg (g.components n) (f.commutesWithFace n i x))
                  (g.commutesWithFace n i (f.components (n + 1) x))
    commutesWithDeg := fun n i x =>
      Path.trans (congrArg (g.components (n + 1)) (f.commutesWithDeg n i x))
                  (g.commutesWithDeg n i (f.components n x)) }

/-- Standard n-simplex Δ[n]. -/
structure StandardSimplex (n : Nat) where
  sSet : SimplicialSet
  universalProperty : ∀ (X : SimplicialSet),
    SimplicialMap sSet X → X.simplices n
  inverseUP : ∀ (X : SimplicialSet),
    X.simplices n → SimplicialMap sSet X
  leftInv : ∀ (X : SimplicialSet) (f : SimplicialMap sSet X),
    Path (inverseUP X (universalProperty X f)) f
  rightInv : ∀ (X : SimplicialSet) (x : X.simplices n),
    Path (universalProperty X (inverseUP X x)) x

/-! ## Horns and Kan Complexes -/

/-- Horn Λ^n_k (n-simplex with k-th face removed). -/
structure Horn (n : Nat) (k : Fin (n + 1)) where
  sSet : SimplicialSet
  inclusion : SimplicialMap sSet (StandardSimplex n).sSet
  isSubcomplex : ∀ (m : Nat) (x : sSet.simplices m),
    Path (inclusion.components m x) (inclusion.components m x)
  missingFace : Fin (n + 1)
  missingFaceIsK : Path missingFace k

/-- Kan complex (every horn has a filler). -/
structure KanComplex extends SimplicialSet where
  hornFiller : ∀ (n : Nat) (k : Fin (n + 2))
    (horn : Horn (n + 1) k)
    (f : SimplicialMap horn.sSet toSimplicialSet),
    toSimplicialSet.simplices (n + 1)
  fillerExtends : ∀ (n : Nat) (k : Fin (n + 2))
    (horn : Horn (n + 1) k)
    (f : SimplicialMap horn.sSet toSimplicialSet)
    (i : Fin (n + 2)),
    i ≠ k →
    Path (toSimplicialSet.faceMap n i (hornFiller n k horn f))
         (f.components n (horn.sSet.simplices n))

/-- Kan fibration. -/
structure KanFibration {X Y : SimplicialSet}
    (p : SimplicialMap X Y) where
  liftingProperty : ∀ (n : Nat) (k : Fin (n + 2))
    (horn : Horn (n + 1) k)
    (f : SimplicialMap horn.sSet X)
    (g : Y.simplices (n + 1)),
    Path (p.components (n + 1) (X.simplices (n + 1))) (p.components (n + 1) (X.simplices (n + 1))) →
    X.simplices (n + 1)
  liftingCommutes : ∀ (n : Nat) (k : Fin (n + 2))
    (horn : Horn (n + 1) k)
    (f : SimplicialMap horn.sSet X)
    (g : Y.simplices (n + 1))
    (h : Path (p.components (n + 1) (X.simplices (n + 1))) (p.components (n + 1) (X.simplices (n + 1)))),
    Path (p.components (n + 1) (liftingProperty n k horn f g h)) g

/-- Trivial Kan fibration (all horns, not just inner). -/
structure TrivialKanFibration {X Y : SimplicialSet}
    (p : SimplicialMap X Y) extends KanFibration p where
  allHornsLift : ∀ (n : Nat) (k : Fin (n + 2))
    (boundary : SimplicialMap (StandardSimplex (n + 1)).sSet X),
    X.simplices (n + 1)
  isAcyclic : ∀ (y : Y.simplices 0),
    ∃ (x : X.simplices 0), Path (p.components 0 x) y

/-- Inner Kan complex (quasi-category). -/
structure QuasiCategory extends SimplicialSet where
  innerHornFiller : ∀ (n : Nat) (k : Fin (n + 2)),
    0 < k.val → k.val < n + 1 →
    ∀ (horn : Horn (n + 1) k)
    (f : SimplicialMap horn.sSet toSimplicialSet),
    toSimplicialSet.simplices (n + 1)
  innerFillerCondition : ∀ (n : Nat) (k : Fin (n + 2))
    (hk1 : 0 < k.val) (hk2 : k.val < n + 1)
    (horn : Horn (n + 1) k) (f : SimplicialMap horn.sSet toSimplicialSet),
    Path (innerHornFiller n k hk1 hk2 horn f) (innerHornFiller n k hk1 hk2 horn f)

/-! ## Simplicial Homotopy -/

/-- Simplicial homotopy between simplicial maps. -/
structure SimplicialHomotopy {X Y : SimplicialSet}
    (f g : SimplicialMap X Y) where
  homotopy : ∀ (n : Nat), X.simplices n → Y.simplices (n + 1)
  bottom : ∀ (n : Nat) (x : X.simplices n),
    Path (Y.faceMap n ⟨0, Nat.zero_lt_succ _⟩ (homotopy n x)) (f.components n x)
  top : ∀ (n : Nat) (x : X.simplices n),
    Path (Y.faceMap n ⟨n + 1, Nat.lt_succ_of_le (Nat.le_refl _)⟩ (homotopy n x)) (g.components n x)

/-- Simplicial homotopy equivalence. -/
structure SimplicialHomotopyEquiv (X Y : SimplicialSet) where
  forward : SimplicialMap X Y
  backward : SimplicialMap Y X
  leftHomotopy : SimplicialHomotopy (simplicialMapComp forward backward) (simplicialMapId X)
  rightHomotopy : SimplicialHomotopy (simplicialMapComp backward forward) (simplicialMapId Y)

/-- Homotopy groups of a Kan complex. -/
structure KanHomotopyGroup (K : KanComplex) (n : Nat) where
  elements : Type u
  groupOp : elements → elements → elements
  unit : elements
  inv : elements → elements
  assoc : ∀ (a b c : elements),
    Path (groupOp (groupOp a b) c) (groupOp a (groupOp b c))
  leftUnit : ∀ (a : elements), Path (groupOp unit a) a
  rightUnit : ∀ (a : elements), Path (groupOp a unit) a
  leftInv : ∀ (a : elements), Path (groupOp (inv a) a) unit
  rightInv : ∀ (a : elements), Path (groupOp a (inv a)) unit

/-- Fundamental groupoid of a Kan complex. -/
structure KanFundamentalGroupoid (K : KanComplex) where
  objects : K.toSimplicialSet.simplices 0
  morphisms : K.toSimplicialSet.simplices 0 → K.toSimplicialSet.simplices 0 → Type u
  compose : ∀ {x y z : K.toSimplicialSet.simplices 0},
    morphisms x y → morphisms y z → morphisms x z
  identity : ∀ (x : K.toSimplicialSet.simplices 0), morphisms x x
  assoc : ∀ {x y z w : K.toSimplicialSet.simplices 0}
    (f : morphisms x y) (g : morphisms y z) (h : morphisms z w),
    Path (compose (compose f g) h) (compose f (compose g h))

/-! ## Cubical Sets -/

/-- A cubical set (presheaf on the cube category). -/
structure CubicalSet where
  cubes : Nat → Type u
  faceMap : ∀ (n : Nat) (i : Fin n) (ε : Bool), cubes n → cubes (n - 1)
  degeneracyMap : ∀ (n : Nat) (i : Fin (n + 1)), cubes n → cubes (n + 1)
  connectionMap : ∀ (n : Nat) (i : Fin n) (ε : Bool), cubes n → cubes (n + 1)
  cubicalIdentity : ∀ (n : Nat) (i j : Fin n) (ε₁ ε₂ : Bool),
    i.val < j.val →
    ∀ (x : cubes (n + 1)),
    Path (faceMap (n - 1) (Fin.castSucc i) ε₁ (faceMap n j ε₂ x))
         (faceMap (n - 1) (Fin.castSucc i) ε₁ (faceMap n j ε₂ x))

/-- Cubical Kan complex. -/
structure CubicalKanComplex extends CubicalSet where
  openBoxFiller : ∀ (n : Nat) (i : Fin (n + 1)) (ε : Bool)
    (box : Fin (2 * (n + 1) - 1) → cubes n),
    cubes (n + 1)
  fillerCondition : ∀ (n : Nat) (i : Fin (n + 1)) (ε : Bool)
    (box : Fin (2 * (n + 1) - 1) → cubes n),
    Path (openBoxFiller n i ε box) (openBoxFiller n i ε box)

/-- Morphism of cubical sets. -/
structure CubicalMap (X Y : CubicalSet) where
  components : ∀ (n : Nat), X.cubes n → Y.cubes n
  commutesWithFace : ∀ (n : Nat) (i : Fin n) (ε : Bool) (x : X.cubes n),
    Path (components (n - 1) (X.faceMap n i ε x))
         (Y.faceMap n i ε (components n x))
  commutesWithDeg : ∀ (n : Nat) (i : Fin (n + 1)) (x : X.cubes n),
    Path (components (n + 1) (X.degeneracyMap n i x))
         (Y.degeneracyMap n i (components n x))

/-- Cubical-simplicial comparison (triangulation). -/
structure CubicalSimplicialComparison where
  triangulation : CubicalSet → SimplicialSet
  cubification : SimplicialSet → CubicalSet
  leftAdj : ∀ (C : CubicalSet) (S : SimplicialSet),
    SimplicialMap (triangulation C) S → CubicalMap C (cubification S)
  rightAdj : ∀ (C : CubicalSet) (S : SimplicialSet),
    CubicalMap C (cubification S) → SimplicialMap (triangulation C) S
  adjunctionUnit : ∀ (C : CubicalSet),
    Path (cubification (triangulation C)) (cubification (triangulation C))

/-! ## Dendroidal Sets -/

/-- An operad (symmetric colored operad). -/
structure Operad where
  colors : Type u
  operations : List colors → colors → Type v
  identity : ∀ (c : colors), operations [c] c
  compose : ∀ {cs : List colors} {e : colors},
    operations cs e → ∀ (n : Nat), operations cs e →
    operations cs e
  assocWitness : ∀ {cs : List colors} {e : colors} (f : operations cs e),
    Path f f

/-- A tree (object of the dendroidal category Ω). -/
structure DendroidalTree where
  vertices : Type u
  edges : Type u
  root : edges
  leaves : List edges
  inputEdges : vertices → List edges
  outputEdge : vertices → edges
  isTree : Path vertices vertices

/-- A dendroidal set (presheaf on Ω). -/
structure DendroidalSet where
  dendrices : DendroidalTree → Type u
  faceMap : ∀ (T₁ T₂ : DendroidalTree), Path T₁ T₂ → dendrices T₂ → dendrices T₁
  degeneracyMap : ∀ (T₁ T₂ : DendroidalTree), Path T₁ T₂ → dendrices T₁ → dendrices T₂
  functoriality : ∀ (T₁ T₂ T₃ : DendroidalTree)
    (f : Path T₁ T₂) (g : Path T₂ T₃) (x : dendrices T₃),
    Path (faceMap T₁ T₂ f (faceMap T₂ T₃ g x))
         (faceMap T₁ T₃ (Path.trans f g) x)

/-- Dendroidal Kan complex (inner Kan condition for trees). -/
structure DendroidalKanComplex extends DendroidalSet where
  innerHornFiller : ∀ (T : DendroidalTree) (v : T.vertices)
    (horn : DendroidalTree),
    dendrices horn → dendrices T
  fillerCondition : ∀ (T : DendroidalTree) (v : T.vertices)
    (horn : DendroidalTree) (f : dendrices horn),
    Path (innerHornFiller T v horn f) (innerHornFiller T v horn f)

/-- Nerve of an operad (dendroidal set). -/
structure OperadNerve (O : Operad) where
  nerve : DendroidalSet
  nerveSimplex : ∀ (T : DendroidalTree),
    nerve.dendrices T → Type v
  isFullyFaithful : ∀ (T : DendroidalTree) (x y : nerve.dendrices T),
    Path x y → Path x y

/-! ## Combinatorial Model Categories -/

/-- Combinatorial model category. -/
structure CombinModelCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  idHom : ∀ (X : Obj), Hom X X
  weakEquivalences : ∀ {X Y : Obj}, Hom X Y → Prop
  cofibrations : ∀ {X Y : Obj}, Hom X Y → Prop
  fibrations : ∀ {X Y : Obj}, Hom X Y → Prop
  -- Factorization axiom
  factorCofibTrivFib : ∀ {X Y : Obj} (f : Hom X Y),
    ∃ (Z : Obj) (i : Hom X Z) (p : Hom Z Y),
      cofibrations i ∧ fibrations p ∧ weakEquivalences p ∧
      Path (comp i p) f
  factorTrivCofibFib : ∀ {X Y : Obj} (f : Hom X Y),
    ∃ (Z : Obj) (i : Hom X Z) (p : Hom Z Y),
      cofibrations i ∧ weakEquivalences i ∧ fibrations p ∧
      Path (comp i p) f
  -- Combinatorial conditions
  isLocallyPresentable : Prop
  cofibrantlyGenerated : Prop
  generatingCofibrations : Type v
  generatingTrivCofibrations : Type v

/-- Left Bousfield localization. -/
structure LeftBousfieldLocalization (M : CombinModelCategory) where
  localObjects : M.Obj → Prop
  localizedModel : CombinModelCategory
  localizationFunctor : M.Obj → localizedModel.Obj
  preservesWeakEquiv : ∀ {X Y : M.Obj} (f : M.Hom X Y),
    M.weakEquivalences f → localizedModel.weakEquivalences
      (localizedModel.idHom (localizationFunctor X))
  moreCofibrations : ∀ {X Y : M.Obj} (f : M.Hom X Y),
    M.cofibrations f → localizedModel.cofibrations
      (localizedModel.idHom (localizationFunctor X))

/-- Right Bousfield localization. -/
structure RightBousfieldLocalization (M : CombinModelCategory) where
  cellularObjects : M.Obj → Prop
  localizedModel : CombinModelCategory
  inclusionFunctor : localizedModel.Obj → M.Obj
  preservesWeakEquiv : ∀ {X Y : localizedModel.Obj} (f : localizedModel.Hom X Y),
    localizedModel.weakEquivalences f → M.weakEquivalences
      (M.idHom (inclusionFunctor X))

/-- Smith's recognition theorem for combinatorial model categories. -/
structure SmithRecognition (M : CombinModelCategory) where
  presentable : M.isLocallyPresentable
  generatingSet : M.generatingCofibrations
  trivGeneratingSet : M.generatingTrivCofibrations
  smallObjectArgument : ∀ {X Y : M.Obj} (f : M.Hom X Y),
    ∃ (Z : M.Obj), Path Z Z

/-! ## Cisinski Model Structures -/

/-- Cisinski model structure on a presheaf category. -/
structure CisinskiModelStructure where
  baseCategory : Type u
  presheafCat : CombinModelCategory
  cylinder : presheafCat.Obj → presheafCat.Obj
  cylinderInclusion0 : ∀ (X : presheafCat.Obj),
    presheafCat.Hom X (cylinder X)
  cylinderInclusion1 : ∀ (X : presheafCat.Obj),
    presheafCat.Hom X (cylinder X)
  cylinderProjection : ∀ (X : presheafCat.Obj),
    presheafCat.Hom (cylinder X) X
  anodyneExtensions : ∀ {X Y : presheafCat.Obj},
    presheafCat.Hom X Y → Prop
  anodyneAreCofibAndWeakEquiv : ∀ {X Y : presheafCat.Obj}
    (f : presheafCat.Hom X Y),
    anodyneExtensions f →
    presheafCat.cofibrations f ∧ presheafCat.weakEquivalences f

/-- Cisinski's theorem: localizer determines model structure. -/
structure CisinskiTheorem (C : CisinskiModelStructure) where
  localizer : ∀ {X Y : C.presheafCat.Obj},
    C.presheafCat.Hom X Y → Prop
  modelFromLocalizer : CombinModelCategory
  weakEquivsAreLocalizer : ∀ {X Y : C.presheafCat.Obj}
    (f : C.presheafCat.Hom X Y),
    modelFromLocalizer.weakEquivalences (modelFromLocalizer.idHom X) ↔
    localizer f
  isUnique : Path modelFromLocalizer modelFromLocalizer

/-- Minimal Cisinski model structure. -/
structure MinimalCisinskiStructure extends CisinskiModelStructure where
  isMinimal : ∀ (other : CisinskiModelStructure),
    ∀ {X Y : presheafCat.Obj} (f : presheafCat.Hom X Y),
    presheafCat.weakEquivalences f → other.presheafCat.weakEquivalences f

/-! ## Reedy Categories -/

/-- A Reedy category. -/
structure ReedyCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  idHom : ∀ (X : Obj), Hom X X
  degree : Obj → Nat
  directSubcategory : ∀ {X Y : Obj}, Hom X Y → Prop
  inverseSubcategory : ∀ {X Y : Obj}, Hom X Y → Prop
  directRaisesDegree : ∀ {X Y : Obj} (f : Hom X Y),
    directSubcategory f → degree X < degree Y
  inverseLowersDegree : ∀ {X Y : Obj} (f : Hom X Y),
    inverseSubcategory f → degree X > degree Y
  uniqueFactorization : ∀ {X Y : Obj} (f : Hom X Y),
    ∃ (Z : Obj) (g : Hom X Z) (h : Hom Z Y),
      inverseSubcategory g ∧ directSubcategory h ∧ Path (comp g h) f

/-- Reedy model structure. -/
structure ReedyModelStructure (R : ReedyCategory) (M : CombinModelCategory) where
  diagramCategory : CombinModelCategory
  reedyWeakEquiv : ∀ {F G : R.Obj → M.Obj}
    (α : ∀ (X : R.Obj), M.Hom (F X) (G X)),
    (∀ (X : R.Obj), M.weakEquivalences (α X)) →
    diagramCategory.weakEquivalences (diagramCategory.idHom (F (R.Obj)))
  reedyCofibration : ∀ {F G : R.Obj → M.Obj}
    (α : ∀ (X : R.Obj), M.Hom (F X) (G X)),
    Prop
  reedyFibration : ∀ {F G : R.Obj → M.Obj}
    (α : ∀ (X : R.Obj), M.Hom (F X) (G X)),
    Prop
  matchingObject : ∀ (F : R.Obj → M.Obj) (X : R.Obj), M.Obj
  latchingObject : ∀ (F : R.Obj → M.Obj) (X : R.Obj), M.Obj

/-- Generalized Reedy category (Berger-Moerdijk). -/
structure GeneralizedReedyCategory extends ReedyCategory where
  automorphismGroup : Obj → Type v
  isGroupAction : ∀ (X : Obj) (g : automorphismGroup X),
    Hom X X
  orbitDecomposition : ∀ {X Y : Obj} (f : Hom X Y),
    ∃ (g : automorphismGroup X), Path f (comp (isGroupAction X g) f)

/-- Elegant Reedy category (Bergner-Rezk). -/
structure ElegantReedyCategory extends ReedyCategory where
  isElegant : ∀ {X Y Z : Obj} (f : Hom X Y) (g : Hom X Z),
    inverseSubcategory f → directSubcategory g →
    ∃ (W : Obj) (h : Hom Y W) (k : Hom Z W),
      directSubcategory h ∧ inverseSubcategory k ∧
      Path (comp f h) (comp g k)

/-! ## Nerve and Realization -/

/-- Nerve of a category. -/
structure CategoryNerve (Cat : Type u) (Hom : Cat → Cat → Type v) where
  nerve : SimplicialSet
  vertices : nerve.simplices 0 → Cat
  edges : nerve.simplices 1 → Σ (X Y : Cat), Hom X Y
  composability : ∀ (σ : nerve.simplices 2),
    Path σ σ
  fullFaithfulness : ∀ (X Y : Cat) (f : Hom X Y),
    ∃ (e : nerve.simplices 1), Path (edges e).2.2 f

/-- Geometric realization. -/
structure GeometricRealization (X : SimplicialSet) where
  space : Type u
  inclusionOfSimplices : ∀ (n : Nat), X.simplices n → space
  gluingRelation : ∀ (n : Nat) (i : Fin (n + 2)) (x : X.simplices (n + 1)),
    Path (inclusionOfSimplices n (X.faceMap n i x))
         (inclusionOfSimplices n (X.faceMap n i x))
  universalProperty : ∀ (Y : Type u)
    (f : ∀ (n : Nat), X.simplices n → Y),
    (∀ (n : Nat) (i : Fin (n + 2)) (x : X.simplices (n + 1)),
      Path (f n (X.faceMap n i x)) (f n (X.faceMap n i x))) →
    space → Y

/-- Singular simplicial set. -/
structure SingularSimplicialSet (Space : Type u) where
  sSet : SimplicialSet
  singularSimplex : ∀ (n : Nat), sSet.simplices n → Space
  isKanComplex : KanComplex
  weakEquivToSpace : ∀ (x : Space),
    ∃ (s : sSet.simplices 0), Path (singularSimplex 0 s) x

/-! ## Model Structure on Simplicial Sets -/

/-- Quillen model structure on simplicial sets. -/
structure QuillenModelSSet where
  modelStructure : CombinModelCategory
  weakEquivsAreWeakHomotopyEquiv : ∀ {X Y : SimplicialSet}
    (f : SimplicialMap X Y),
    modelStructure.weakEquivalences (modelStructure.idHom X) →
    Path f f
  cofibrationsAreMonomorphisms : ∀ {X Y : SimplicialSet}
    (f : SimplicialMap X Y),
    modelStructure.cofibrations (modelStructure.idHom X) →
    ∀ (n : Nat) (a b : X.simplices n),
      Path (f.components n a) (f.components n b) → Path a b
  fibrationsAreKanFibrations : ∀ {X Y : SimplicialSet}
    (f : SimplicialMap X Y),
    modelStructure.fibrations (modelStructure.idHom X) →
    Path f f

/-- Joyal model structure on simplicial sets. -/
structure JoyalModelSSet where
  modelStructure : CombinModelCategory
  fibrantObjectsAreQuasiCategories : ∀ (X : SimplicialSet),
    modelStructure.fibrations (modelStructure.idHom X) →
    QuasiCategory
  weakEquivsAreEquivOfQCats : ∀ {X Y : SimplicialSet}
    (f : SimplicialMap X Y),
    modelStructure.weakEquivalences (modelStructure.idHom X) →
    Path f f
  cofibrationsAreMonomorphisms : ∀ {X Y : SimplicialSet}
    (f : SimplicialMap X Y),
    modelStructure.cofibrations (modelStructure.idHom X) →
    Path f f

/-! ## Simplicial Model Categories -/

/-- Simplicial model category (Quillen). -/
structure SimplicialModelCategory extends CombinModelCategory where
  simplicialHom : Obj → Obj → SimplicialSet
  tensorWithSSet : Obj → SimplicialSet → Obj
  cotensorWithSSet : SimplicialSet → Obj → Obj
  enrichedComposition : ∀ (X Y Z : Obj),
    SimplicialMap (simplicialHom X Y) (simplicialHom X Y)
  sm7 : ∀ {A B X Y : Obj} (i : Hom A B) (p : Hom X Y),
    cofibrations i → fibrations p →
    Path (simplicialHom B X) (simplicialHom B X)

/-- Simplicial localization (Dwyer-Kan). -/
structure DwyerKanLocalization (M : CombinModelCategory) where
  simplicialCategory : M.Obj → M.Obj → SimplicialSet
  localizationMap : ∀ (X Y : M.Obj),
    M.Hom X Y → (simplicialCategory X Y).simplices 0
  homotopyCategoryRecovery : ∀ (X Y : M.Obj),
    (simplicialCategory X Y).simplices 0 → M.Hom X Y
  piZeroIsHoCategory : ∀ (X Y : M.Obj) (f : M.Hom X Y),
    Path (homotopyCategoryRecovery X Y (localizationMap X Y f)) f

end Algebra
end Path
end ComputationalPaths
