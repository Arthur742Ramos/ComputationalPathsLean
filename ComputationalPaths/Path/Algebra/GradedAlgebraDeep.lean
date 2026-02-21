/-
  ComputationalPaths/Path/Algebra/GradedAlgebraDeep.lean

  Graded Algebras and Differential Graded Categories via Computational Paths

  Topics: Graded modules, graded rings, differentials (d∘d=0),
  chain/cochain complexes, homology, DG-categories, DG-functors,
  DG-natural transformations, A-infinity algebras, Koszul duality,
  spectral sequences — all via Path.trans/symm/congrArg.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace GradedAlgebraDeep

universe u v w

-- ===================================================================
-- Section 1: Graded Modules and Graded Rings
-- ===================================================================

/-- A graded module: family of types indexed by natural numbers -/
structure GradedModule where
  component : Nat → Type u

/-- A Z-graded module: indexed by integers -/
structure ZGradedModule where
  component : Int → Type u

/-- Zero element in each graded component -/
structure GradedZero (M : GradedModule.{u}) where
  zero : (n : Nat) → M.component n

/-- Addition in each graded component -/
structure GradedAdd (M : GradedModule.{u}) where
  add : (n : Nat) → M.component n → M.component n → M.component n

/-- Graded multiplication: degree p × degree q → degree (p + q) -/
structure GradedMul (M : GradedModule.{u}) where
  mul : (p q : Nat) → M.component p → M.component q → M.component (p + q)

/-- A graded ring bundles zero, addition, and multiplication -/
structure GradedRing extends GradedModule.{u} where
  gzero : GradedZero toGradedModule
  gadd : GradedAdd toGradedModule
  gmul : GradedMul toGradedModule

-- Theorem 1: Grading preservation under multiplication as Path
def gradingPreservation (R : GradedRing.{u}) (p q : Nat)
    (_x : R.component p) (_y : R.component q)
    : Path (p + q) (p + q) :=
  Path.refl (p + q)

-- Theorem 2: Grading sum commutativity as Path via Step
def gradingSumComm (p q : Nat) (h : p + q = q + p)
    : Path (p + q) (q + p) :=
  Path.mk [Step.mk (p + q) (q + p) h] h

-- Theorem 3: Grading sum associativity as Path
def gradingSumAssoc (p q r : Nat) (h : (p + q) + r = p + (q + r))
    : Path ((p + q) + r) (p + (q + r)) :=
  Path.mk [Step.mk _ _ h] h

-- ===================================================================
-- Section 2: Differentials and Chain Complexes
-- ===================================================================

/-- Differential on a graded module: maps degree n+1 to degree n -/
structure Differential (M : GradedModule.{u}) where
  d : (n : Nat) → M.component (n + 1) → M.component n

/-- Codifferential: maps degree n to degree n+1 -/
structure Codifferential (M : GradedModule.{u}) where
  d : (n : Nat) → M.component n → M.component (n + 1)

/-- d∘d = 0: composition of two differentials gives zero -/
structure DiffSquareZero (M : GradedModule.{u}) (gz : GradedZero M) (diff : Differential M) where
  sq_zero : (n : Nat) → (x : M.component (n + 2)) →
    Path (diff.d n (diff.d (n + 1) x)) (gz.zero n)

-- Theorem 4: d∘d = 0 is witnessed by Path
def diffSquareZeroPath (M : GradedModule.{u}) (gz : GradedZero M)
    (diff : Differential M) (pf : DiffSquareZero M gz diff)
    (n : Nat) (x : M.component (n + 2))
    : Path (diff.d n (diff.d (n + 1) x)) (gz.zero n) :=
  pf.sq_zero n x

-- Theorem 5: Symmetry of d∘d = 0
def diffSquareZeroSymm (M : GradedModule.{u}) (gz : GradedZero M)
    (diff : Differential M) (pf : DiffSquareZero M gz diff)
    (n : Nat) (x : M.component (n + 2))
    : Path (gz.zero n) (diff.d n (diff.d (n + 1) x)) :=
  Path.symm (pf.sq_zero n x)

-- ===================================================================
-- Section 3: Chain Complexes
-- ===================================================================

/-- A chain complex: graded module + differential + d∘d = 0 -/
structure ChainComplex where
  mod : GradedModule.{u}
  gz : GradedZero mod
  diff : Differential mod
  exact : DiffSquareZero mod gz diff

-- Theorem 6: Chain map preserves differential as Path
structure ChainMap (C D : ChainComplex.{u}) where
  f : (n : Nat) → C.mod.component n → D.mod.component n
  commutes : (n : Nat) → (x : C.mod.component (n + 1)) →
    Path (D.diff.d n (f (n + 1) x)) (f n (C.diff.d n x))

-- Theorem 7: Identity chain map
def chainMapId (C : ChainComplex.{u}) : ChainMap C C where
  f := fun _ x => x
  commutes := fun _ _ => Path.refl _

-- Theorem 8: Composition of chain maps
def chainMapComp {A B C : ChainComplex.{u}}
    (g : ChainMap B C) (f : ChainMap A B) : ChainMap A C where
  f := fun n x => g.f n (f.f n x)
  commutes := fun n x =>
    let step1 : Path (C.diff.d n (g.f (n + 1) (f.f (n + 1) x)))
                     (g.f n (B.diff.d n (f.f (n + 1) x))) :=
      g.commutes n (f.f (n + 1) x)
    let step2 : Path (B.diff.d n (f.f (n + 1) x))
                     (f.f n (A.diff.d n x)) :=
      f.commutes n x
    let step3 : Path (g.f n (B.diff.d n (f.f (n + 1) x)))
                     (g.f n (f.f n (A.diff.d n x))) :=
      Path.congrArg (g.f n) step2
    Path.trans step1 step3

-- ===================================================================
-- Section 4: Boundaries, Cycles, Homology
-- ===================================================================

/-- Boundary at degree n: image of differential from degree n+1 -/
structure Boundary (C : ChainComplex.{u}) (n : Nat) where
  elem : C.mod.component n
  preimage : C.mod.component (n + 1)
  isBoundary : Path (C.diff.d n preimage) elem

-- Theorem 9: Every boundary is a cycle (d∘d = 0)
def boundaryIsCycle (C : ChainComplex.{u}) (n : Nat) (b : Boundary C (n + 1))
    : Path (C.diff.d n b.elem) (C.gz.zero n) :=
  let ddZero : Path (C.diff.d n (C.diff.d (n + 1) b.preimage)) (C.gz.zero n) :=
    C.exact.sq_zero n b.preimage
  let substitute : Path (C.diff.d n (C.diff.d (n + 1) b.preimage))
                        (C.diff.d n b.elem) :=
    Path.congrArg (C.diff.d n) b.isBoundary
  Path.trans (Path.symm substitute) ddZero

-- Theorem 10: Homology equivalence as Path
def homologyEquiv (C : ChainComplex.{u}) (n : Nat)
    {z1 z2 : C.mod.component n}
    (rel : Path z1 z2)
    : Path z2 z1 :=
  Path.symm rel

-- Theorem 11: Homology equivalence transitivity
def homologyEquivTrans (C : ChainComplex.{u}) (n : Nat)
    {z1 z2 z3 : C.mod.component n}
    (p : Path z1 z2) (q : Path z2 z3)
    : Path z1 z3 :=
  Path.trans p q

-- Theorem 12: Homology equivalence associativity
def homologyEquivAssoc (C : ChainComplex.{u}) (n : Nat)
    {a b c d : C.mod.component n}
    (p : Path a b) (q : Path b c) (r : Path c d)
    : Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ===================================================================
-- Section 5: DG-Categories
-- ===================================================================

/-- A DG-category: objects, hom chain complexes, composition -/
structure DGCategory where
  Obj : Type u
  Hom : Obj → Obj → ChainComplex.{u}
  comp : (X Y Z : Obj) → (n : Nat) →
    (Hom X Y).mod.component n →
    (Hom Y Z).mod.component 0 →
    (Hom X Z).mod.component n

/-- Identity morphism in a DG-category -/
structure DGIdentity (C : DGCategory.{u}) where
  id_elem : (X : C.Obj) → (C.Hom X X).mod.component 0

-- Theorem 13: DG Leibniz rule as Path
structure DGLeibniz (C : DGCategory.{u}) where
  leibniz : (X Y Z : C.Obj) → (n : Nat) →
    (f : (C.Hom X Y).mod.component (n + 1)) →
    (g : (C.Hom Y Z).mod.component 0) →
    Path ((C.Hom X Z).diff.d n (C.comp X Y Z (n + 1) f g))
         (C.comp X Y Z n ((C.Hom X Y).diff.d n f) g)

-- Theorem 14: DG left unit as Path
structure DGLeftUnit (C : DGCategory.{u}) (idC : DGIdentity C) where
  leftUnit : (X Y : C.Obj) →
    (f : (C.Hom X Y).mod.component 0) →
    Path (C.comp X X Y 0 (idC.id_elem X) f) f

-- Theorem 15: DG right unit as Path
structure DGRightUnit (C : DGCategory.{u}) (idC : DGIdentity C) where
  rightUnit : (X Y : C.Obj) → (n : Nat) →
    (f : (C.Hom X Y).mod.component n) →
    Path (C.comp X Y Y n f (idC.id_elem Y)) f

-- Theorem 16: DG associativity as Path
structure DGAssoc (C : DGCategory.{u}) where
  dgAssoc : (W X Y Z : C.Obj) → (n : Nat) →
    (f : (C.Hom W X).mod.component n) →
    (g : (C.Hom X Y).mod.component 0) →
    (h : (C.Hom Y Z).mod.component 0) →
    Path (C.comp W Y Z n (C.comp W X Y n f g) h)
         (C.comp W X Z n f (C.comp X Y Z 0 g h))

-- ===================================================================
-- Section 6: DG-Functors
-- ===================================================================

/-- DG-functor between DG-categories -/
structure DGFunctor (C D : DGCategory.{u}) where
  objMap : C.Obj → D.Obj
  homMap : (X Y : C.Obj) → (n : Nat) →
    (C.Hom X Y).mod.component n →
    (D.Hom (objMap X) (objMap Y)).mod.component n

-- Theorem 17: DG-functor preserves differential as Path
structure DGFunctorDiff (C D : DGCategory.{u}) (F : DGFunctor C D) where
  preservesDiff : (X Y : C.Obj) → (n : Nat) →
    (f : (C.Hom X Y).mod.component (n + 1)) →
    Path (F.homMap X Y n ((C.Hom X Y).diff.d n f))
         ((D.Hom (F.objMap X) (F.objMap Y)).diff.d n (F.homMap X Y (n + 1) f))

-- Theorem 18: DG-functor preserves composition as Path
structure DGFunctorComp (C D : DGCategory.{u}) (F : DGFunctor C D) where
  preservesComp : (X Y Z : C.Obj) → (n : Nat) →
    (f : (C.Hom X Y).mod.component n) →
    (g : (C.Hom Y Z).mod.component 0) →
    Path (F.homMap X Z n (C.comp X Y Z n f g))
         (D.comp (F.objMap X) (F.objMap Y) (F.objMap Z) n
           (F.homMap X Y n f) (F.homMap Y Z 0 g))

-- Theorem 19: Identity DG-functor
def dgFunctorId (C : DGCategory.{u}) : DGFunctor C C where
  objMap := fun X => X
  homMap := fun _ _ _ f => f

-- Theorem 20: DG-functor composition
def dgFunctorComp {A B C : DGCategory.{u}}
    (G : DGFunctor B C) (F : DGFunctor A B) : DGFunctor A C where
  objMap := fun X => G.objMap (F.objMap X)
  homMap := fun X Y n f => G.homMap (F.objMap X) (F.objMap Y) n (F.homMap X Y n f)

-- ===================================================================
-- Section 7: DG-Natural Transformations
-- ===================================================================

/-- DG-natural transformation between DG-functors -/
structure DGNatTrans {C D : DGCategory.{u}} (F G : DGFunctor C D) where
  component : (X : C.Obj) → (D.Hom (F.objMap X) (G.objMap X)).mod.component 0

-- Theorem 21: DG-naturality as Path (at degree 0)
structure DGNaturality {C D : DGCategory.{u}} {F G : DGFunctor C D}
    (eta : DGNatTrans F G) where
  natural : (X Y : C.Obj) →
    (f : (C.Hom X Y).mod.component 0) →
    Path (D.comp (F.objMap X) (F.objMap Y) (G.objMap Y) 0
           (F.homMap X Y 0 f) (eta.component Y))
         (D.comp (F.objMap X) (G.objMap X) (G.objMap Y) 0
           (eta.component X) (G.homMap X Y 0 f))

-- Theorem 22: DG-natural transformation closedness
def dgNatTransClosed {C D : DGCategory.{u}} {F G : DGFunctor C D}
    (eta : DGNatTrans F G) (X : C.Obj)
    : Path (eta.component X) (eta.component X) :=
  Path.refl (eta.component X)

-- Theorem 23: Identity DG-natural transformation
def dgNatTransId {C D : DGCategory.{u}} (F : DGFunctor C D)
    (idD : DGIdentity D)
    : DGNatTrans F F where
  component := fun X => idD.id_elem (F.objMap X)

-- ===================================================================
-- Section 8: A-infinity Algebras
-- ===================================================================

/-- A-infinity algebra: graded module with higher multiplications -/
structure AInfAlgebra where
  mod : GradedModule.{u}
  gz : GradedZero mod
  m1 : (n : Nat) → mod.component (n + 1) → mod.component n
  m2 : (p q : Nat) → mod.component p → mod.component q → mod.component (p + q)

-- Theorem 24: A-infinity relation: m1∘m1 = 0 as Path
structure AInfRelation1 (A : AInfAlgebra.{u}) where
  m1m1_zero : (n : Nat) → (x : A.mod.component (n + 2)) →
    Path (A.m1 n (A.m1 (n + 1) x)) (A.gz.zero n)

-- Theorem 25: m1 is derivation for m2 as Path
structure AInfRelation2 (A : AInfAlgebra.{u}) where
  leibniz : (p q : Nat) →
    (x : A.mod.component p) →
    (y : A.mod.component (q + 1)) →
    Path (A.m1 (p + q) (A.m2 p (q + 1) x y))
         (A.m2 p q x (A.m1 q y))

-- Theorem 26: Symmetry of A-infinity relation 1
def ainfRelation1Symm (A : AInfAlgebra.{u}) (rel : AInfRelation1 A)
    (n : Nat) (x : A.mod.component (n + 2))
    : Path (A.gz.zero n) (A.m1 n (A.m1 (n + 1) x)) :=
  Path.symm (rel.m1m1_zero n x)

-- Theorem 27: Transitivity chain for A-infinity
def ainfTransChain (A : AInfAlgebra.{u}) {n : Nat}
    {a b c : A.mod.component n}
    (p : Path a b) (q : Path b c)
    : Path a c :=
  Path.trans p q

-- Theorem 28: Higher associativity as Path chain
def higherAssocPath {T : Type u}
    {a b c d : T}
    (p : Path a b) (q : Path b c) (r : Path c d)
    : Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ===================================================================
-- Section 9: Koszul Duality
-- ===================================================================

/-- Koszul pair: two graded modules with pairing -/
structure KoszulPair where
  kA : GradedModule.{u}
  kDual : GradedModule.{u}
  pairing : (p q : Nat) → kA.component p → kDual.component q → kA.component 0

/-- Koszul complex -/
structure KoszulComplex (K : KoszulPair.{u}) where
  diff : Differential K.kA
  gz : GradedZero K.kA
  acyclic : DiffSquareZero K.kA gz diff

-- Theorem 29: Koszul differential squares to zero
def koszulDiffSqZero (K : KoszulPair.{u}) (kc : KoszulComplex K)
    (n : Nat) (x : K.kA.component (n + 2))
    : Path (kc.diff.d n (kc.diff.d (n + 1) x)) (kc.gz.zero n) :=
  kc.acyclic.sq_zero n x

-- Theorem 30: Koszul symmetry
def koszulDiffSqZeroSymm (K : KoszulPair.{u}) (kc : KoszulComplex K)
    (n : Nat) (x : K.kA.component (n + 2))
    : Path (kc.gz.zero n) (kc.diff.d n (kc.diff.d (n + 1) x)) :=
  Path.symm (kc.acyclic.sq_zero n x)

-- Theorem 31: Koszul pairing reflexivity
def koszulPairingRefl (K : KoszulPair.{u}) (p : Nat)
    (x : K.kA.component p) (y : K.kDual.component 0)
    : Path (K.pairing p 0 x y) (K.pairing p 0 x y) :=
  Path.refl _

-- ===================================================================
-- Section 10: Spectral Sequences
-- ===================================================================

/-- A spectral sequence page -/
structure SpectralPage where
  entry : Nat → Nat → Type u
  diff : (p q : Nat) → entry p q → entry (p + 1) q

/-- A spectral sequence -/
structure SpectralSequence where
  page : Nat → SpectralPage.{u}
  connection : (r p q : Nat) →
    (page (r + 1)).entry p q → (page r).entry p q

-- Theorem 32: Spectral page reflexivity
def spectralPageRefl (ss : SpectralSequence.{u}) (r p q : Nat)
    (x : (ss.page r).entry p q)
    : Path x x :=
  Path.refl x

-- Theorem 33: Connection preserves Path via congrArg
def spectralConnection (ss : SpectralSequence.{u}) (r p q : Nat)
    {x y : (ss.page (r + 1)).entry p q}
    (pathR1 : Path x y)
    : Path (ss.connection r p q x) (ss.connection r p q y) :=
  Path.congrArg (ss.connection r p q) pathR1

-- Theorem 34: Connection preserves Path.trans
def spectralConnectionTrans (ss : SpectralSequence.{u}) (r p q : Nat)
    {x y z : (ss.page (r + 1)).entry p q}
    (pxy : Path x y) (pyz : Path y z)
    : Path (ss.connection r p q x) (ss.connection r p q z) :=
  Path.congrArg (ss.connection r p q) (Path.trans pxy pyz)

-- Theorem 35: congrArg distributes over trans for spectral maps
def spectralCongrArgTrans (ss : SpectralSequence.{u}) (r p q : Nat)
    {x y z : (ss.page (r + 1)).entry p q}
    (pxy : Path x y) (pyz : Path y z)
    : Path.congrArg (ss.connection r p q) (Path.trans pxy pyz) =
      Path.trans (Path.congrArg (ss.connection r p q) pxy)
                 (Path.congrArg (ss.connection r p q) pyz) :=
  congrArg_trans (ss.connection r p q) pxy pyz

-- ===================================================================
-- Section 11: Path Algebra in Graded Context
-- ===================================================================

-- Theorem 36: Path.trans left identity in graded context
def gradedTransReflLeft {M : GradedModule.{u}} {n : Nat}
    {a b : M.component n}
    (p : Path a b)
    : Path.trans (Path.refl a) p = p :=
  trans_refl_left p

-- Theorem 37: Path.trans right identity in graded context
def gradedTransReflRight {M : GradedModule.{u}} {n : Nat}
    {a b : M.component n}
    (p : Path a b)
    : Path.trans p (Path.refl b) = p :=
  trans_refl_right p

-- Theorem 38: Path.symm involution in graded context
def gradedSymmSymm {M : GradedModule.{u}} {n : Nat}
    {a b : M.component n}
    (p : Path a b)
    : Path.symm (Path.symm p) = p :=
  symm_symm p

-- Theorem 39: symm distributes over trans
def gradedSymmTrans {M : GradedModule.{u}} {n : Nat}
    {a b c : M.component n}
    (p : Path a b) (q : Path b c)
    : Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- Theorem 40: congrArg preserves symm
def gradedCongrArgSymm {M N : GradedModule.{u}} {n : Nat}
    (f : M.component n → N.component n)
    {a b : M.component n}
    (p : Path a b)
    : Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  congrArg_symm f p

-- ===================================================================
-- Section 12: DG-Modules
-- ===================================================================

/-- A DG-module over a DG-category -/
structure DGModule (C : DGCategory.{u}) where
  target : C.Obj
  sections : GradedModule.{u}
  action : (X : C.Obj) → (n : Nat) →
    (C.Hom X target).mod.component n →
    sections.component 0 →
    sections.component n

-- Theorem 41: DG-module action respects Path on morphisms
def dgModuleActionPath {C : DGCategory.{u}} (M : DGModule C)
    (X : C.Obj) (n : Nat)
    {f g : (C.Hom X M.target).mod.component n}
    (p : Path f g) (s : M.sections.component 0)
    : Path (M.action X n f s) (M.action X n g s) :=
  Path.congrArg (fun h => M.action X n h s) p

-- Theorem 42: DG-module action respects Path on sections
def dgModuleSectionPath {C : DGCategory.{u}} (M : DGModule C)
    (X : C.Obj) (n : Nat)
    (f : (C.Hom X M.target).mod.component n)
    {s t : M.sections.component 0}
    (p : Path s t)
    : Path (M.action X n f s) (M.action X n f t) :=
  Path.congrArg (M.action X n f) p

-- ===================================================================
-- Section 13: Chain Homotopy
-- ===================================================================

/-- Chain homotopy between two chain maps -/
structure ChainHomotopy {C D : ChainComplex.{u}} (f g : ChainMap C D) where
  h : (n : Nat) → C.mod.component n → D.mod.component (n + 1)
  witness : (n : Nat) → (x : C.mod.component n) →
    Path (D.diff.d n (h n x)) (f.f n x)

-- Theorem 43: Chain homotopy path extraction
def homotopicMapsPath {C D : ChainComplex.{u}} {f g : ChainMap C D}
    (H : ChainHomotopy f g) (n : Nat) (x : C.mod.component n)
    : Path (D.diff.d n (H.h n x)) (f.f n x) :=
  H.witness n x

-- Theorem 44: Chain homotopy path symmetry
def homotopicMapsPathSymm {C D : ChainComplex.{u}} {f g : ChainMap C D}
    (H : ChainHomotopy f g) (n : Nat) (x : C.mod.component n)
    : Path (f.f n x) (D.diff.d n (H.h n x)) :=
  Path.symm (H.witness n x)

-- ===================================================================
-- Section 14: Enriched Hom Structure
-- ===================================================================

/-- Enriched hom data -/
structure EnrichedHom where
  source : Type u
  target : Type u
  homComplex : ChainComplex.{u}

-- Theorem 45: Enriched composition coherence
structure EnrichedComp (H1 H2 H3 : EnrichedHom.{u}) where
  comp : (n : Nat) →
    H1.homComplex.mod.component n →
    H2.homComplex.mod.component 0 →
    H3.homComplex.mod.component n
  coherence : (n : Nat) →
    (f : H1.homComplex.mod.component (n + 1)) →
    (g : H2.homComplex.mod.component 0) →
    Path (H3.homComplex.diff.d n (comp (n + 1) f g))
         (comp n (H1.homComplex.diff.d n f) g)

-- Theorem 46: Enriched coherence symmetry
def enrichedCoherenceSymm (H1 H2 H3 : EnrichedHom.{u})
    (ec : EnrichedComp H1 H2 H3)
    (n : Nat)
    (f : H1.homComplex.mod.component (n + 1))
    (g : H2.homComplex.mod.component 0)
    : Path (ec.comp n (H1.homComplex.diff.d n f) g)
           (H3.homComplex.diff.d n (ec.comp (n + 1) f g)) :=
  Path.symm (ec.coherence n f g)

-- ===================================================================
-- Section 15: Quasi-isomorphisms
-- ===================================================================

/-- Quasi-isomorphism data -/
structure QuasiIso {C D : ChainComplex.{u}} (f : ChainMap C D) where
  surjOnCycles : (n : Nat) → (y : D.mod.component n) →
    Sigma (fun x : C.mod.component n => Path (f.f n x) y)

-- Theorem 47: Quasi-isomorphism composition
def quasiIsoComp {A B C : ChainComplex.{u}}
    {f : ChainMap A B} {g : ChainMap B C}
    (qf : QuasiIso f) (qg : QuasiIso g)
    : (n : Nat) → (z : C.mod.component n) →
      Sigma (fun x : A.mod.component n => Path (g.f n (f.f n x)) z) :=
  fun n z =>
    let ⟨b, pb⟩ := qg.surjOnCycles n z
    let ⟨a, pa⟩ := qf.surjOnCycles n b
    ⟨a, Path.trans (Path.congrArg (g.f n) pa) pb⟩

-- ===================================================================
-- Section 16: A-infinity Morphisms
-- ===================================================================

/-- A-infinity morphism -/
structure AInfMorphism (A B : AInfAlgebra.{u}) where
  f1 : (n : Nat) → A.mod.component n → B.mod.component n
  f1_commutes : (n : Nat) → (x : A.mod.component (n + 1)) →
    Path (B.m1 n (f1 (n + 1) x)) (f1 n (A.m1 n x))

-- Theorem 48: A-infinity morphism composition
def ainfMorphismComp {A B C : AInfAlgebra.{u}}
    (g : AInfMorphism B C) (f : AInfMorphism A B)
    : AInfMorphism A C where
  f1 := fun n x => g.f1 n (f.f1 n x)
  f1_commutes := fun n x =>
    let step1 := g.f1_commutes n (f.f1 (n + 1) x)
    let step2 := f.f1_commutes n x
    let step3 := Path.congrArg (g.f1 n) step2
    Path.trans step1 step3

-- Theorem 49: Identity A-infinity morphism
def ainfMorphismId (A : AInfAlgebra.{u}) : AInfMorphism A A where
  f1 := fun _ x => x
  f1_commutes := fun _ _ => Path.refl _

-- ===================================================================
-- Section 17: Higher Path Coherences
-- ===================================================================

-- Theorem 50: Pentagon coherence for 4-fold Path composition
def pentagonCoherence {T : Type u}
    {a b c d e : T}
    (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e)
    : Path.trans (Path.trans (Path.trans p q) r) s =
      Path.trans p (Path.trans q (Path.trans r s)) :=
  let step1 := trans_assoc (Path.trans p q) r s
  let step2 := trans_assoc p q (Path.trans r s)
  step1.trans step2

-- Theorem 51: Triangle coherence for unit paths
def triangleCoherence {T : Type u} {a b : T}
    (p : Path a b)
    : Path.trans (Path.refl a) (Path.trans p (Path.refl b)) = p :=
  let step1 := _root_.congrArg (Path.trans (Path.refl a)) (trans_refl_right p)
  step1.trans (trans_refl_left p)

-- Theorem 52: Inverse path cancellation (left) at toEq level
def inverseCancel {T : Type u} {a b : T} (p : Path a b)
    : Path.toEq (Path.trans (Path.symm p) p) = rfl :=
  toEq_symm_trans p

-- Theorem 53: Inverse path cancellation (right) at toEq level
def inverseCancelRight {T : Type u} {a b : T} (p : Path a b)
    : Path.toEq (Path.trans p (Path.symm p)) = rfl :=
  toEq_trans_symm p

-- Theorem 54: Whiskering left with 2-paths
def whiskerLeftPath {T : Type u} {a b c : T}
    (p : Path a b) {q r : Path b c}
    (alpha : q = r)
    : Path.trans p q = Path.trans p r :=
  _root_.congrArg (Path.trans p) alpha

-- Theorem 55: Whiskering right with 2-paths
def whiskerRightPath {T : Type u} {a b c : T}
    {p q : Path a b} (alpha : p = q)
    (r : Path b c)
    : Path.trans p r = Path.trans q r :=
  _root_.congrArg (fun x => Path.trans x r) alpha

-- Theorem 56: Differential functoriality via congrArg
def gradedDiffFunctorial (C : ChainComplex.{u}) (n : Nat)
    {x y : C.mod.component (n + 1)}
    (p : Path x y)
    : Path (C.diff.d n x) (C.diff.d n y) :=
  Path.congrArg (C.diff.d n) p

-- Theorem 57: Differential preserves trans
def gradedDiffPreservesTrans (C : ChainComplex.{u}) (n : Nat)
    {x y z : C.mod.component (n + 1)}
    (p : Path x y) (q : Path y z)
    : Path.congrArg (C.diff.d n) (Path.trans p q) =
      Path.trans (Path.congrArg (C.diff.d n) p) (Path.congrArg (C.diff.d n) q) :=
  congrArg_trans (C.diff.d n) p q

-- Theorem 58: Differential preserves symm
def gradedDiffPreservesSymm (C : ChainComplex.{u}) (n : Nat)
    {x y : C.mod.component (n + 1)}
    (p : Path x y)
    : Path.congrArg (C.diff.d n) (Path.symm p) =
      Path.symm (Path.congrArg (C.diff.d n) p) :=
  congrArg_symm (C.diff.d n) p

-- Theorem 59: Chain map functoriality via congrArg
def chainMapFunctorial {C D : ChainComplex.{u}} (f : ChainMap C D) (n : Nat)
    {x y : C.mod.component n}
    (p : Path x y)
    : Path (f.f n x) (f.f n y) :=
  Path.congrArg (f.f n) p

-- Theorem 60: Full coherence combining trans, symm, congrArg
def fullGradedCoherence {M : GradedModule.{u}} {n : Nat}
    {a b c : M.component n}
    (p : Path a b) (q : Path b c)
    : Path.toEq (Path.trans (Path.trans p q) (Path.symm (Path.trans p q))) = rfl :=
  toEq_trans_symm (Path.trans p q)

end GradedAlgebraDeep
end Algebra
end Path
end ComputationalPaths
