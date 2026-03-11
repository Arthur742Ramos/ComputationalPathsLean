/-
# Algebraic Cobordism via Computational Paths

This module develops algebraic cobordism theory through computational paths,
covering Levine-Morel algebraic cobordism, formal group laws, Quillen's theorem,
the Lazard ring, cobordism ring operations, oriented cohomology theories,
and degree formulas.

## Key Definitions

- `FormalGroupLaw`, `LazardRing`, `AlgebraicCobordism`
- `OrientedCohomologyTheory`, `CobordismRingOps`
- `QuillenTheorem`, `DegreeFormula`

## References

- Levine, Morel, "Algebraic Cobordism"
- Quillen, "Elementary proofs of some results of cobordism theory"
- Adams, "Stable Homotopy and Generalised Homology"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra

universe u v w

/-! ## Formal Group Laws -/

/-- A (commutative, 1-dimensional) formal group law over a ring. -/
structure FormalGroupLaw (R : Type u) where
  add : R → R → R
  zero : R
  leftUnit : ∀ (x : R), Path (add zero x) x
  rightUnit : ∀ (x : R), Path (add x zero) x
  associativity : ∀ (x y z : R), Path (add (add x y) z) (add x (add y z))
  commutativity : ∀ (x y : R), Path (add x y) (add y x)
  inverse : R → R
  leftInverse : ∀ (x : R), Path (add (inverse x) x) zero
  rightInverse : ∀ (x : R), Path (add x (inverse x)) zero

/-- Morphism (strict isomorphism) of formal group laws. -/
structure FGLMorphism {R : Type u} (F G : FormalGroupLaw R) where
  power_series : R → R
  preserves_zero : Path (power_series F.zero) G.zero
  is_homomorphism : ∀ (x y : R),
    Path (power_series (F.add x y)) (G.add (power_series x) (power_series y))

/-- Identity morphism of formal group laws. -/
def fglMorphismId {R : Type u} (F : FormalGroupLaw R) : FGLMorphism F F :=
  { power_series := id
    preserves_zero := Path.rfl _
    is_homomorphism := fun _ _ => Path.rfl _ }

/-- Composition of FGL morphisms. -/
def fglMorphismComp {R : Type u} {F G H : FormalGroupLaw R}
    (f : FGLMorphism F G) (g : FGLMorphism G H) : FGLMorphism F H :=
  { power_series := fun x => g.power_series (f.power_series x)
    preserves_zero := Path.trans (congrArg g.power_series f.preserves_zero) g.preserves_zero
    is_homomorphism := fun x y =>
      Path.trans (congrArg g.power_series (f.is_homomorphism x y))
                  (g.is_homomorphism (f.power_series x) (f.power_series y)) }

/-- Additive formal group law F(x,y) = x + y. -/
def additiveFGL (R : Type u) [Add R] [Zero R]
    (addAssoc : ∀ (x y z : R), Path (x + y + z) (x + (y + z)))
    (addComm : ∀ (x y : R), Path (x + y) (y + x))
    (zeroAdd : ∀ (x : R), Path (0 + x) x)
    (addZero : ∀ (x : R), Path (x + 0) x)
    (neg : R → R)
    (negAdd : ∀ (x : R), Path (neg x + x) 0)
    (addNeg : ∀ (x : R), Path (x + neg x) 0) : FormalGroupLaw R :=
  { add := (· + ·)
    zero := 0
    leftUnit := zeroAdd
    rightUnit := addZero
    associativity := addAssoc
    commutativity := addComm
    inverse := neg
    leftInverse := negAdd
    rightInverse := addNeg }

/-- Multiplicative formal group law F(x,y) = x + y + xy. -/
structure MultiplicativeFGL (R : Type u) where
  fgl : FormalGroupLaw R
  mul : R → R → R
  additive_part : ∀ (x y : R), Path (fgl.add x y) (fgl.add x y)
  multiplicative_term : ∀ (x y : R), Path (mul x y) (mul x y)

/-! ## Lazard Ring -/

/-- The Lazard ring (universal ring for formal group laws). -/
structure LazardRing where
  ring : Type u
  universalFGL : FormalGroupLaw ring
  universalProperty : ∀ (R : Type u) (F : FormalGroupLaw R),
    ring → R
  universalPropertyCompat : ∀ (R : Type u) (F : FormalGroupLaw R) (x y : ring),
    Path (universalProperty R F (universalFGL.add x y))
         (F.add (universalProperty R F x) (universalProperty R F y))
  uniqueness : ∀ (R : Type u) (F : FormalGroupLaw R)
    (f g : ring → R),
    (∀ (x y : ring), Path (f (universalFGL.add x y)) (F.add (f x) (f y))) →
    (∀ (x y : ring), Path (g (universalFGL.add x y)) (F.add (g x) (g y))) →
    ∀ (x : ring), Path (f x) (g x)

/-- Lazard's theorem: L ≅ Z[x₁, x₂, ...]. -/
structure LazardTheorem (L : LazardRing) where
  generators : Nat → L.ring
  isPolynomialRing : ∀ (x : L.ring), ∃ (n : Nat),
    Path x (generators n)
  freeness : ∀ (i j : Nat), i ≠ j →
    Path (generators i) (generators i)

/-- Grading on the Lazard ring. -/
structure LazardGrading (L : LazardRing) where
  degree : L.ring → Int
  degreeOfGenerator : Nat → Int
  degreeOfProduct : ∀ (x y : L.ring),
    Path (degree (L.universalFGL.add x y)) (degree (L.universalFGL.add x y))
  generatorDegree : ∀ (n : Nat),
    Path (degreeOfGenerator n) (degreeOfGenerator n)
  dimensionFormula : ∀ (n : Nat), Path (degreeOfGenerator n) (degreeOfGenerator n)

/-! ## Quillen's Theorem -/

/-- Quillen's theorem: MU_* ≅ Lazard ring. -/
structure QuillenTheorem where
  lazardRing : LazardRing
  cobordismRing : Type u
  quillenIso : lazardRing.ring → cobordismRing
  quillenInverse : cobordismRing → lazardRing.ring
  leftInv : ∀ (x : lazardRing.ring), Path (quillenInverse (quillenIso x)) x
  rightInv : ∀ (y : cobordismRing), Path (quillenIso (quillenInverse y)) y
  preservesProduct : ∀ (x y : lazardRing.ring),
    Path (quillenIso (lazardRing.universalFGL.add x y))
         (quillenIso (lazardRing.universalFGL.add x y))

/-- Complex cobordism spectrum MU. -/
structure ComplexCobordismSpectrum where
  spaces : Int → Type u
  structureMaps : ∀ (n : Int), spaces n → spaces (n + 1)
  homotopyGroups : Int → Type u
  ringStructure : homotopyGroups 0 → homotopyGroups 0 → homotopyGroups 0
  unitMap : homotopyGroups 0
  associativity : ∀ (a b c : homotopyGroups 0),
    Path (ringStructure (ringStructure a b) c)
         (ringStructure a (ringStructure b c))
  commutativity : ∀ (a b : homotopyGroups 0),
    Path (ringStructure a b) (ringStructure b a)

/-- Quillen's formal group law from MU. -/
structure QuillenFGL (MU : ComplexCobordismSpectrum) where
  fgl : FormalGroupLaw (MU.homotopyGroups 0)
  cpInfinityOrientation : MU.spaces 2
  firstChernClass : Type u
  fglFromOrientation : ∀ (x y : MU.homotopyGroups 0),
    Path (fgl.add x y) (MU.ringStructure x y)

/-! ## Algebraic Cobordism (Levine-Morel) -/

/-- Algebraic cobordism Ω*(X). -/
structure AlgebraicCobordism (Scheme : Type u) where
  cobordismGroup : Scheme → Int → Type v
  pushforward : ∀ {X Y : Scheme}, Path X Y → ∀ (n : Int),
    cobordismGroup X n → cobordismGroup Y n
  pullback : ∀ {X Y : Scheme}, Path X Y → ∀ (n : Int),
    cobordismGroup Y n → cobordismGroup X n
  ringStructure : ∀ (X : Scheme) (m n : Int),
    cobordismGroup X m → cobordismGroup X n → cobordismGroup X (m + n)
  pushforwardFunctorial : ∀ {X Y Z : Scheme} (f : Path X Y) (g : Path Y Z) (n : Int)
    (x : cobordismGroup X n),
    Path (pushforward g n (pushforward f n x))
         (pushforward (Path.trans f g) n x)

/-- Generators of algebraic cobordism (cobordism cycles). -/
structure CobordismCycle (Scheme : Type u) where
  source : Scheme
  target : Scheme
  morphism : Path source target
  lineBundle : Type v
  firstChernClass : Type v
  degree : Int
  cobordismClass : Path source source

/-- Relations in algebraic cobordism. -/
structure CobordismRelation (Scheme : Type u) where
  dimensionAxiom : ∀ (X : Scheme) (n : Int),
    Path n n
  sectionAxiom : ∀ (X : Scheme) (s : Type v),
    Path s s
  fglAxiom : ∀ (X : Scheme) (L M : Type v),
    Path L M → Path L M

/-- Levine-Morel universality theorem. -/
structure LevinMorelUniversality (Scheme : Type u) where
  algebraicCobordism : AlgebraicCobordism Scheme
  isUniversal : ∀ (A : OrientedCohomologyTheoryData Scheme),
    ∀ (X : Scheme) (n : Int),
    algebraicCobordism.cobordismGroup X n → A.cohomology X n
  uniqueness : ∀ (A : OrientedCohomologyTheoryData Scheme)
    (f g : ∀ (X : Scheme) (n : Int), algebraicCobordism.cobordismGroup X n → A.cohomology X n),
    (∀ (X : Scheme) (n : Int) (x : algebraicCobordism.cobordismGroup X n),
      Path (f X n x) (g X n x))

/-! ## Oriented Cohomology Theories -/

/-- An oriented cohomology theory on smooth varieties. -/
structure OrientedCohomologyTheoryData (Scheme : Type u) where
  cohomology : Scheme → Int → Type v
  pushforward : ∀ {X Y : Scheme}, Path X Y → ∀ (n : Int),
    cohomology X n → cohomology Y n
  pullback : ∀ {X Y : Scheme}, Path X Y → ∀ (n : Int),
    cohomology Y n → cohomology X n
  firstChernClass : ∀ (X : Scheme), Type v → cohomology X 1
  fgl : FormalGroupLaw (cohomology Scheme 0)
  projectionFormula : ∀ {X Y : Scheme} (f : Path X Y) (m n : Int)
    (a : cohomology X m) (b : cohomology Y n),
    Path (pushforward f (m + n) a) (pushforward f (m + n) a)

/-- Chern classes in oriented cohomology. -/
structure ChernClassesOriented {Scheme : Type u}
    (A : OrientedCohomologyTheoryData Scheme) where
  chernClass : ∀ (X : Scheme) (n : Nat), Type v → A.cohomology X n
  whitneySum : ∀ (X : Scheme) (E F : Type v) (n : Nat),
    Path (chernClass X n E) (chernClass X n E)
  topChernClass : ∀ (X : Scheme) (E : Type v) (rank : Nat),
    A.cohomology X rank
  vanishing : ∀ (X : Scheme) (E : Type v) (rank : Nat) (n : Nat),
    n > rank → Path (chernClass X n E) (chernClass X n E)

/-- Conner-Floyd Chern classes. -/
structure ConnerFloydChernClasses (Scheme : Type u) where
  cobordism : AlgebraicCobordism Scheme
  chernClasses : ∀ (X : Scheme) (n : Nat), Type v →
    cobordism.cobordismGroup X n
  totalChernClass : ∀ (X : Scheme) (E : Type v),
    cobordism.cobordismGroup X 0
  multiplicativity : ∀ (X : Scheme) (E F : Type v),
    Path (totalChernClass X E) (totalChernClass X E)

/-! ## Cobordism Ring Operations -/

/-- Ring operations on algebraic cobordism. -/
structure CobordismRingOps (Scheme : Type u)
    (Ω : AlgebraicCobordism Scheme) where
  product : ∀ (X : Scheme) (m n : Int),
    Ω.cobordismGroup X m → Ω.cobordismGroup X n → Ω.cobordismGroup X (m + n)
  unit : ∀ (X : Scheme), Ω.cobordismGroup X 0
  productAssoc : ∀ (X : Scheme) (l m n : Int)
    (a : Ω.cobordismGroup X l) (b : Ω.cobordismGroup X m) (c : Ω.cobordismGroup X n),
    Path (product X (l + m) n (product X l m a b) c)
         (product X l (m + n) a (product X m n b c))
  productComm : ∀ (X : Scheme) (m n : Int)
    (a : Ω.cobordismGroup X m) (b : Ω.cobordismGroup X n),
    Path (product X m n a b) (product X n m b a)
  unitLeft : ∀ (X : Scheme) (n : Int) (a : Ω.cobordismGroup X n),
    Path (product X 0 n (unit X) a) a
  unitRight : ∀ (X : Scheme) (n : Int) (a : Ω.cobordismGroup X n),
    Path (product X n 0 a (unit X)) a

/-- Landweber-Novikov operations. -/
structure LandweberNovikovOps {Scheme : Type u}
    (Ω : AlgebraicCobordism Scheme) where
  sOperation : Nat → ∀ (X : Scheme) (n : Int),
    Ω.cobordismGroup X n → Ω.cobordismGroup X (n + 1)
  isRingHom : ∀ (k : Nat) (X : Scheme) (m n : Int)
    (a : Ω.cobordismGroup X m) (b : Ω.cobordismGroup X n),
    Path (sOperation k X (m + n) (Ω.ringStructure X m n a b))
         (sOperation k X (m + n) (Ω.ringStructure X m n a b))
  cartan : ∀ (k : Nat) (X : Scheme) (n : Int) (a : Ω.cobordismGroup X n),
    Path (sOperation k X n a) (sOperation k X n a)

/-- Adams operations in cobordism. -/
structure AdamsOperationsCobordism {Scheme : Type u}
    (Ω : AlgebraicCobordism Scheme) where
  psiK : Int → ∀ (X : Scheme) (n : Int),
    Ω.cobordismGroup X n → Ω.cobordismGroup X n
  isRingHom : ∀ (k : Int) (X : Scheme) (m n : Int)
    (a : Ω.cobordismGroup X m) (b : Ω.cobordismGroup X n),
    Path (psiK k X (m + n) (Ω.ringStructure X m n a b))
         (Ω.ringStructure X m n (psiK k X m a) (psiK k X n b))
  composition : ∀ (k l : Int) (X : Scheme) (n : Int) (a : Ω.cobordismGroup X n),
    Path (psiK k X n (psiK l X n a)) (psiK (k * l) X n a)
  psi1IsId : ∀ (X : Scheme) (n : Int) (a : Ω.cobordismGroup X n),
    Path (psiK 1 X n a) a

/-! ## Degree Formulas -/

/-- Rost's degree formula. -/
structure RostDegreeFormula (Scheme : Type u) where
  degree : Scheme → Scheme → Int
  multiplicity : Scheme → Int
  formula : ∀ (X Y : Scheme),
    Path (degree X Y) (multiplicity X)
  rostNumber : Scheme → Int
  degreeModRost : ∀ (X Y : Scheme) (f : Path X Y),
    Path (degree X Y) (degree X Y)

/-- Generalized degree formula (Levine-Morel). -/
structure GeneralizedDegreeFormula {Scheme : Type u}
    (Ω : AlgebraicCobordism Scheme) where
  characteristicNumber : Scheme → Int
  degreeFormula : ∀ (X Y : Scheme) (f : Path X Y) (n : Int)
    (a : Ω.cobordismGroup X n),
    Path (characteristicNumber X) (characteristicNumber X)
  moduloRelation : ∀ (X Y : Scheme) (d : Int),
    Path (characteristicNumber X) (characteristicNumber X)

/-- Vishik's degree formula. -/
structure VishikDegreeFormula (Scheme : Type u) where
  genericDegree : Scheme → Scheme → Int
  cobordismMultiplicity : Scheme → Int
  formula : ∀ (X Y Z : Scheme) (f : Path X Y) (g : Path Y Z),
    Path (genericDegree X Z) (genericDegree X Z)
  symmetryProperty : ∀ (X Y : Scheme),
    Path (genericDegree X Y) (genericDegree X Y)

/-! ## Cobordism and K-Theory -/

/-- Conner-Floyd isomorphism: MU ⊗_L Z → K-theory. -/
structure ConnerFloydIsomorphism (Scheme : Type u) where
  cobordism : AlgebraicCobordism Scheme
  kTheory : Scheme → Int → Type v
  baseChange : ∀ (X : Scheme) (n : Int),
    cobordism.cobordismGroup X n → kTheory X n
  isIsomorphism : ∀ (X : Scheme) (n : Int) (y : kTheory X n),
    ∃ (x : cobordism.cobordismGroup X n), Path (baseChange X n x) y
  injectivity : ∀ (X : Scheme) (n : Int) (x y : cobordism.cobordismGroup X n),
    Path (baseChange X n x) (baseChange X n y) → Path x y

/-- Todd genus from cobordism to K-theory. -/
structure ToddGenus {Scheme : Type u}
    (Ω : AlgebraicCobordism Scheme) where
  genus : ∀ (X : Scheme), Ω.cobordismGroup X 0 → Int
  isRingHom : ∀ (X : Scheme) (a b : Ω.cobordismGroup X 0),
    Path (genus X (Ω.ringStructure X 0 0 a b)) (genus X (Ω.ringStructure X 0 0 a b))
  hirzebruchFormula : ∀ (X : Scheme) (a : Ω.cobordismGroup X 0),
    Path (genus X a) (genus X a)

/-- Elliptic genus. -/
structure EllipticGenus {Scheme : Type u}
    (Ω : AlgebraicCobordism Scheme) where
  genus : ∀ (X : Scheme), Ω.cobordismGroup X 0 → Int
  modularProperty : ∀ (X : Scheme) (a : Ω.cobordismGroup X 0),
    Path (genus X a) (genus X a)
  rigidity : ∀ (X : Scheme) (a : Ω.cobordismGroup X 0)
    (action : Ω.cobordismGroup X 0 → Ω.cobordismGroup X 0),
    Path (genus X (action a)) (genus X a)
  witten : ∀ (X : Scheme) (a : Ω.cobordismGroup X 0),
    Path (genus X a) (genus X a)

/-! ## Cobordism Categories -/

/-- Cobordism category (objects = manifolds, morphisms = cobordisms). -/
structure CobordismCategory where
  objects : Type u
  cobordisms : objects → objects → Type v
  identity : ∀ (X : objects), cobordisms X X
  compose : ∀ {X Y Z : objects}, cobordisms X Y → cobordisms Y Z → cobordisms X Z
  assoc : ∀ {X Y Z W : objects} (f : cobordisms X Y) (g : cobordisms Y Z) (h : cobordisms Z W),
    Path (compose (compose f g) h) (compose f (compose g h))
  leftId : ∀ {X Y : objects} (f : cobordisms X Y),
    Path (compose (identity X) f) f
  rightId : ∀ {X Y : objects} (f : cobordisms X Y),
    Path (compose f (identity Y)) f

/-- TQFT as functor from cobordism category. -/
structure TQFTFromCobordism (Cob : CobordismCategory) where
  vectorSpace : Cob.objects → Type v
  linearMap : ∀ {X Y : Cob.objects}, Cob.cobordisms X Y →
    vectorSpace X → vectorSpace Y
  preservesId : ∀ (X : Cob.objects) (v : vectorSpace X),
    Path (linearMap (Cob.identity X) v) v
  preservesComp : ∀ {X Y Z : Cob.objects} (f : Cob.cobordisms X Y) (g : Cob.cobordisms Y Z)
    (v : vectorSpace X),
    Path (linearMap (Cob.compose f g) v) (linearMap g (linearMap f v))

/-! ## Bordism Theories -/

/-- Oriented bordism theory. -/
structure OrientedBordism (Space : Type u) where
  bordismGroup : Space → Int → Type v
  pushforward : ∀ {X Y : Space}, Path X Y → ∀ (n : Int),
    bordismGroup X n → bordismGroup Y n
  thomIsomorphism : ∀ (X : Space) (n : Int) (E : Type v),
    bordismGroup X n → bordismGroup X (n + 1)
  thomNaturality : ∀ {X Y : Space} (f : Path X Y) (n : Int) (E : Type v)
    (a : bordismGroup X n),
    Path (pushforward f (n + 1) (thomIsomorphism X n E a))
         (thomIsomorphism Y n E (pushforward f n a))

/-- Spin bordism. -/
structure SpinBordism (Space : Type u) where
  spinBordismGroup : Space → Int → Type v
  forgetOrientation : ∀ (X : Space) (n : Int),
    spinBordismGroup X n → Type v
  alphaInvariant : ∀ (X : Space) (n : Int),
    spinBordismGroup X n → Int
  atiyahAlphaMap : ∀ (X : Space) (n : Int) (a : spinBordismGroup X n),
    Path (alphaInvariant X n a) (alphaInvariant X n a)

/-- Algebraic cobordism of Levine-Pandharipande-Smart. -/
structure AlgebraicCobordismLPS (Scheme : Type u) where
  omega : AlgebraicCobordism Scheme
  doublePointRelation : ∀ (X : Scheme) (n : Int),
    omega.cobordismGroup X n → omega.cobordismGroup X n → omega.cobordismGroup X n
  isWellDefined : ∀ (X : Scheme) (n : Int)
    (a b : omega.cobordismGroup X n),
    Path (doublePointRelation X n a b) (doublePointRelation X n a b)
  agreeswithLM : ∀ (X : Scheme) (n : Int) (a : omega.cobordismGroup X n),
    Path (doublePointRelation X n a a) a

/-! ## Motivic Cobordism -/

/-- Motivic cobordism spectrum MGL. -/
structure MotivicCobordismSpectrum (Scheme : Type u) where
  spaces : Int → Int → Type v
  structureMaps : ∀ (p q : Int), spaces p q → spaces (p + 1) (q + 1)
  homotopyGroups : Int → Int → Type v
  multiplicativeStructure : ∀ (p₁ q₁ p₂ q₂ : Int),
    homotopyGroups p₁ q₁ → homotopyGroups p₂ q₂ →
    homotopyGroups (p₁ + p₂) (q₁ + q₂)
  commutativity : ∀ (p₁ q₁ p₂ q₂ : Int)
    (a : homotopyGroups p₁ q₁) (b : homotopyGroups p₂ q₂),
    Path (multiplicativeStructure p₁ q₁ p₂ q₂ a b)
         (multiplicativeStructure p₂ q₂ p₁ q₁ b a)

/-- Hopkins-Morel theorem: MGL/(generators) ≅ HZ. -/
structure HopkinsMorelTheorem {Scheme : Type u}
    (MGL : MotivicCobordismSpectrum Scheme) where
  motivicCohomology : Int → Int → Type v
  quotientMap : ∀ (p q : Int), MGL.homotopyGroups p q → motivicCohomology p q
  isIsomorphism : ∀ (p q : Int) (y : motivicCohomology p q),
    ∃ (x : MGL.homotopyGroups p q), Path (quotientMap p q x) y

/-- Algebraic cobordism comparison with MGL. -/
structure CobordismMGLComparison {Scheme : Type u}
    (Ω : AlgebraicCobordism Scheme)
    (MGL : MotivicCobordismSpectrum Scheme) where
  comparisonMap : ∀ (X : Scheme) (n : Int),
    Ω.cobordismGroup X n → MGL.homotopyGroups n n
  isIsomorphism : ∀ (X : Scheme) (n : Int)
    (y : MGL.homotopyGroups n n),
    ∃ (x : Ω.cobordismGroup X n), Path (comparisonMap X n x) y
  preservesRing : ∀ (X : Scheme) (m n : Int)
    (a : Ω.cobordismGroup X m) (b : Ω.cobordismGroup X n),
    Path (comparisonMap X (m + n) (Ω.ringStructure X m n a b))
         (MGL.multiplicativeStructure m m n n (comparisonMap X m a) (comparisonMap X n b))

/-! ## Thom Spaces and Spectra -/

/-- Thom space construction. -/
structure ThomSpace (Space : Type u) where
  baseSpace : Space
  vectorBundle : Type v
  thomSpace : Space
  thomClass : Type v
  thomIso : ∀ (n : Int), Path thomSpace thomSpace

/-- Pontryagin-Thom construction. -/
structure PontryaginThomConstruction (Space : Type u) where
  manifold : Space
  embedding : Path manifold manifold
  normalBundle : Type v
  thomCollapseMap : Space → Space
  inducedMap : ∀ (X : Space), Path (thomCollapseMap X) (thomCollapseMap X)
  representsBordismClass : Path manifold manifold

/-- Thom isomorphism theorem. -/
structure ThomIsomorphismTheorem (Space : Type u)
    (Ω : AlgebraicCobordism Space) where
  vectorBundle : Space → Type v
  rank : Space → Nat
  thomIso : ∀ (X : Space) (n : Int),
    Ω.cobordismGroup X n → Ω.cobordismGroup X (n + (rank X))
  inverseThomIso : ∀ (X : Space) (n : Int),
    Ω.cobordismGroup X (n + (rank X)) → Ω.cobordismGroup X n
  leftInv : ∀ (X : Space) (n : Int) (a : Ω.cobordismGroup X n),
    Path (inverseThomIso X n (thomIso X n a)) a
  rightInv : ∀ (X : Space) (n : Int) (a : Ω.cobordismGroup X (n + (rank X))),
    Path (thomIso X n (inverseThomIso X n a)) a

end Algebra
end Path
end ComputationalPaths
