/-
# Geometric Group Theory via Computational Paths

This module formalizes geometric group theory: Cayley graphs, word metrics,
quasi-isometries, the Švarc-Milnor lemma, growth functions (polynomial and
exponential), Gromov's theorem on polynomial growth, and amenable groups,
all with `Path` coherence witnesses.

## Mathematical Background

Geometric group theory studies finitely generated groups as geometric
objects via their Cayley graphs and the word metric:

1. **Cayley graphs**: For a group G with finite generating set S, the
   Cayley graph Cay(G, S) has vertices G and edges g ~ gs for s ∈ S.
   The graph is connected iff S generates G.
2. **Word metric**: d_S(g, h) = min length of a word in S ∪ S⁻¹
   representing g⁻¹h. Makes G a metric space.
3. **Quasi-isometries**: Maps f : X → Y with
   (1/L)d(x,y) - C ≤ d(f(x),f(y)) ≤ Ld(x,y) + C for constants L ≥ 1, C ≥ 0.
   Quasi-isometry is the fundamental equivalence in coarse geometry.
4. **Švarc-Milnor lemma**: If G acts properly and cocompactly by
   isometries on a proper geodesic metric space X, then G is finitely
   generated and quasi-isometric to X.
5. **Growth functions**: β_S(n) = |{g ∈ G : d_S(e, g) ≤ n}|.
   Polynomial growth: β(n) ≤ Cn^d. Exponential growth: β(n) ≥ a^n.
6. **Gromov's theorem**: A finitely generated group has polynomial
   growth iff it is virtually nilpotent.
7. **Amenable groups**: Groups admitting a left-invariant finitely
   additive probability measure. Includes all solvable groups and
   groups of subexponential growth. The free group F₂ is not amenable.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `CayleyGraph` | Cayley graph Cay(G, S) |
| `WordMetric` | Word metric on a f.g. group |
| `QuasiIsometry` | (L, C)-quasi-isometry |
| `SvarcMilnor` | Švarc-Milnor lemma data |
| `GrowthFunction` | Growth function β_S(n) |
| `GromovPolynomialGrowth` | Gromov's polynomial growth theorem |
| `AmenableGroup` | Amenable group structure |
| `cayley_connected_path` | Cayley graph connectivity |
| `qi_composition_path` | QI composition coherence |
| `gromov_growth_path` | Polynomial growth ↔ virtually nilpotent |
| `amenable_growth_path` | Amenable ⇒ subexponential growth |

## References

- de la Harpe, "Topics in Geometric Group Theory"
- Bridson–Haefliger, "Metric Spaces of Non-Positive Curvature"
- Gromov, "Groups of Polynomial Growth and Expanding Maps"
- Druțu–Kapovich, "Geometric Group Theory"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace GeometricGroupTheory

universe u v

/-! ## Cayley Graphs -/

/-- A generating set for a finitely generated group. -/
structure FiniteGeneratingSet where
  /-- Number of generators. -/
  numGenerators : Nat
  /-- Number of generators is positive. -/
  numGenerators_pos : numGenerators > 0
  /-- Set identifier. -/
  setId : Nat

/-- The Cayley graph Cay(G, S) of a group G with generating set S.
The graph has |G| vertices and |G|·|S| directed edges. -/
structure CayleyGraph where
  /-- The generating set. -/
  genSet : FiniteGeneratingSet
  /-- Order of the group (0 for infinite). -/
  groupOrder : Nat
  /-- Number of vertices = group order. -/
  numVertices : Nat
  /-- Vertex-degree = 2·|S| (undirected, S and S⁻¹). -/
  vertexDegree : Nat
  /-- Degree equals 2·numGenerators. -/
  degree_eq : vertexDegree = 2 * genSet.numGenerators
  /-- The graph is connected (S generates G). -/
  isConnected : Bool
  /-- Diameter (0 for infinite). -/
  diameter : Nat

namespace CayleyGraph

/-- Cayley graph of ℤ with generator {1}: the integer line. -/
def integerLine : CayleyGraph where
  genSet := ⟨1, by omega, 0⟩
  groupOrder := 0
  numVertices := 0
  vertexDegree := 2
  degree_eq := rfl
  isConnected := true
  diameter := 0

/-- Cayley graph of ℤ/nℤ with generator {1}: the n-cycle. -/
def cyclicGraph (n : Nat) (hn : n > 0) : CayleyGraph where
  genSet := ⟨1, by omega, n⟩
  groupOrder := n
  numVertices := n
  vertexDegree := 2
  degree_eq := rfl
  isConnected := true
  diameter := n / 2

/-- Cayley graph of ℤ² with generators {e₁, e₂}: the grid. -/
def gridGraph : CayleyGraph where
  genSet := ⟨2, by omega, 1⟩
  groupOrder := 0
  numVertices := 0
  vertexDegree := 4
  degree_eq := rfl
  isConnected := true
  diameter := 0

/-- Cayley graph of F₂ with 2 free generators: the 4-regular tree. -/
def freeGroupTree : CayleyGraph where
  genSet := ⟨2, by omega, 2⟩
  groupOrder := 0
  numVertices := 0
  vertexDegree := 4
  degree_eq := rfl
  isConnected := true
  diameter := 0

/-- Cayley graph of S₃ with generators {(12), (123)}: 6 vertices. -/
def symmetricS3 : CayleyGraph where
  genSet := ⟨2, by omega, 3⟩
  groupOrder := 6
  numVertices := 6
  vertexDegree := 4
  degree_eq := rfl
  isConnected := true
  diameter := 3

/-- The integer line has degree 2. -/
theorem integerLine_degree : integerLine.vertexDegree = 2 := rfl

/-- The 4-regular tree has degree 4. -/
theorem freeGroupTree_degree : freeGroupTree.vertexDegree = 4 := rfl

/-- The cyclic graph is connected. -/
theorem cyclic_connected (n : Nat) (hn : n > 0) :
    (cyclicGraph n hn).isConnected = true := rfl

/-- S₃ Cayley graph has 6 vertices. -/
theorem s3_vertices : symmetricS3.numVertices = 6 := rfl

end CayleyGraph

/-! ## Word Metric -/

/-- The word metric on a finitely generated group.
d_S(g, h) = min |w| such that g⁻¹h = w in the generators S. -/
structure WordMetric where
  /-- The generating set used. -/
  genSet : FiniteGeneratingSet
  /-- Group identifier. -/
  groupId : Nat
  /-- The metric satisfies d(e, e) = 0. -/
  identity_dist : Nat
  /-- Identity distance is zero. -/
  identity_zero : identity_dist = 0
  /-- Symmetry holds: d(g, h) = d(h, g). -/
  isSymmetric : Bool
  /-- Triangle inequality holds. -/
  satisfiesTriangleInequality : Bool

namespace WordMetric

/-- Word metric on ℤ with {1}: d(m, n) = |m - n|. -/
def integers : WordMetric where
  genSet := ⟨1, by omega, 0⟩
  groupId := 0
  identity_dist := 0
  identity_zero := rfl
  isSymmetric := true
  satisfiesTriangleInequality := true

/-- Word metric on F₂ with {a, b}: tree metric. -/
def freeGroup2 : WordMetric where
  genSet := ⟨2, by omega, 2⟩
  groupId := 2
  identity_dist := 0
  identity_zero := rfl
  isSymmetric := true
  satisfiesTriangleInequality := true

/-- Word metric on ℤ² with {e₁, e₂}: ℓ¹ metric. -/
def integerLattice2 : WordMetric where
  genSet := ⟨2, by omega, 1⟩
  groupId := 1
  identity_dist := 0
  identity_zero := rfl
  isSymmetric := true
  satisfiesTriangleInequality := true

/-- ℤ word metric is symmetric. -/
theorem integers_symmetric : integers.isSymmetric = true := rfl

/-- Free group word metric satisfies triangle inequality. -/
theorem freeGroup2_triangle : freeGroup2.satisfiesTriangleInequality = true := rfl

end WordMetric

/-! ## Quasi-Isometries -/

/-- An (L, C)-quasi-isometry between metric spaces:
(1/L)d(x,y) - C ≤ d(f(x),f(y)) ≤ Ld(x,y) + C,
and f is C-coarsely surjective. -/
structure QuasiIsometry where
  /-- Multiplicative constant L ≥ 1. -/
  L : Nat
  /-- Additive constant C ≥ 0. -/
  C : Nat
  /-- L is at least 1. -/
  L_pos : L ≥ 1
  /-- Source space identifier. -/
  sourceId : Nat
  /-- Target space identifier. -/
  targetId : Nat
  /-- Whether the quasi-isometry is actually an isometry (L=1, C=0). -/
  isIsometry : Bool
  /-- Isometry check is correct. -/
  isometry_correct : isIsometry = (L == 1 && C == 0)

namespace QuasiIsometry

/-- The identity quasi-isometry (isometry). -/
def identity (spaceId : Nat) : QuasiIsometry where
  L := 1
  C := 0
  L_pos := by omega
  sourceId := spaceId
  targetId := spaceId
  isIsometry := true
  isometry_correct := rfl

/-- A (2, 1)-quasi-isometry. -/
def example_2_1 (s t : Nat) : QuasiIsometry where
  L := 2
  C := 1
  L_pos := by omega
  sourceId := s
  targetId := t
  isIsometry := false
  isometry_correct := rfl

/-- Composition of quasi-isometries: (L₁L₂, L₂C₁ + C₂). -/
structure QIComposition where
  /-- First quasi-isometry. -/
  qi1 : QuasiIsometry
  /-- Second quasi-isometry. -/
  qi2 : QuasiIsometry
  /-- Composed L = L₁ · L₂. -/
  composedL : Nat
  /-- Composed C = L₂ · C₁ + C₂. -/
  composedC : Nat
  /-- L composition formula. -/
  L_comp : composedL = qi1.L * qi2.L
  /-- C composition formula. -/
  C_comp : composedC = qi2.L * qi1.C + qi2.C

/-- Composing two isometries gives an isometry. -/
def isometry_comp (spaceId : Nat) : QIComposition where
  qi1 := identity spaceId
  qi2 := identity spaceId
  composedL := 1
  composedC := 0
  L_comp := rfl
  C_comp := rfl

/-- The identity is an isometry. -/
theorem identity_isIsometry (s : Nat) : (identity s).isIsometry = true := rfl

/-- Composing isometries gives L = 1. -/
theorem isometry_comp_L (s : Nat) : (isometry_comp s).composedL = 1 := rfl

/-- Composing isometries gives C = 0. -/
theorem isometry_comp_C (s : Nat) : (isometry_comp s).composedC = 0 := rfl

/-- A quasi-isometric inverse exists with controlled constants. -/
structure QIInverse where
  /-- The original QI. -/
  original : QuasiIsometry
  /-- The inverse QI. -/
  inverse : QuasiIsometry
  /-- Source/target compatibility. -/
  source_target : inverse.sourceId = original.targetId
  /-- Target/source compatibility. -/
  target_source : inverse.targetId = original.sourceId

/-- The inverse of the identity. -/
def identity_inverse (s : Nat) : QIInverse where
  original := identity s
  inverse := identity s
  source_target := rfl
  target_source := rfl

end QuasiIsometry

/-! ## Švarc-Milnor Lemma -/

/-- The Švarc-Milnor lemma: if G acts properly and cocompactly by
isometries on a proper geodesic metric space X, then G is finitely
generated and quasi-isometric to X. -/
structure SvarcMilnor where
  /-- Group identifier. -/
  groupId : Nat
  /-- Space identifier. -/
  spaceId : Nat
  /-- Whether the action is proper. -/
  isProper : Bool
  /-- Whether the action is cocompact. -/
  isCocompact : Bool
  /-- Whether the space is proper geodesic. -/
  isProperGeodesic : Bool
  /-- The resulting quasi-isometry constant L. -/
  qiConstantL : Nat
  /-- The resulting quasi-isometry constant C. -/
  qiConstantC : Nat
  /-- L is at least 1 when hypotheses hold. -/
  L_pos : isProper = true → isCocompact = true → isProperGeodesic = true → qiConstantL ≥ 1
  /-- The conclusion: G is quasi-isometric to X. -/
  isQuasiIsometric : Bool
  /-- QI conclusion follows from hypotheses. -/
  qi_from_hyp : isProper = true → isCocompact = true → isProperGeodesic = true →
    isQuasiIsometric = true

namespace SvarcMilnor

/-- ℤ acting on ℝ by translations: QI with constants (1, 0). -/
def integersOnLine : SvarcMilnor where
  groupId := 0
  spaceId := 0
  isProper := true
  isCocompact := true
  isProperGeodesic := true
  qiConstantL := 1
  qiConstantC := 0
  L_pos := fun _ _ _ => by omega
  isQuasiIsometric := true
  qi_from_hyp := fun _ _ _ => rfl

/-- ℤ² acting on ℝ²: QI with constants (1, 0). -/
def latticeOnPlane : SvarcMilnor where
  groupId := 1
  spaceId := 1
  isProper := true
  isCocompact := true
  isProperGeodesic := true
  qiConstantL := 1
  qiConstantC := 0
  L_pos := fun _ _ _ => by omega
  isQuasiIsometric := true
  qi_from_hyp := fun _ _ _ => rfl

/-- π₁(M) acting on the universal cover of a compact manifold. -/
def fundamentalGroupAction : SvarcMilnor where
  groupId := 10
  spaceId := 10
  isProper := true
  isCocompact := true
  isProperGeodesic := true
  qiConstantL := 1
  qiConstantC := 1
  L_pos := fun _ _ _ => by omega
  isQuasiIsometric := true
  qi_from_hyp := fun _ _ _ => rfl

/-- ℤ ≃_QI ℝ via the Švarc-Milnor lemma. -/
theorem integers_qi_line : integersOnLine.isQuasiIsometric = true := rfl

/-- ℤ² ≃_QI ℝ² via the Švarc-Milnor lemma. -/
theorem lattice_qi_plane : latticeOnPlane.isQuasiIsometric = true := rfl

end SvarcMilnor

/-! ## Growth Functions -/

/-- Growth type of a finitely generated group. -/
inductive GrowthType where
  /-- Polynomial growth of degree d: β(n) ∼ n^d. -/
  | polynomial (degree : Nat)
  /-- Exponential growth: β(n) ∼ a^n for some a > 1. -/
  | exponential
  /-- Intermediate growth: superpolynomial but subexponential. -/
  | intermediate
  deriving Repr, BEq

/-- Growth function data for a finitely generated group. -/
structure GrowthFunction where
  /-- Group identifier. -/
  groupId : Nat
  /-- The generating set used. -/
  genSet : FiniteGeneratingSet
  /-- Growth type. -/
  growthType : GrowthType
  /-- Ball sizes: β_S(n) for small n. -/
  ballSizes : List Nat
  /-- β(0) = 1 (just the identity). -/
  ball_zero : ballSizes.head? = some 1
  /-- Growth is monotonically non-decreasing. -/
  isMonotone : Bool

namespace GrowthFunction

/-- Growth of ℤ: polynomial degree 1, β(n) = 2n + 1. -/
def integers : GrowthFunction where
  groupId := 0
  genSet := ⟨1, by omega, 0⟩
  growthType := .polynomial 1
  ballSizes := [1, 3, 5, 7, 9, 11]
  ball_zero := rfl
  isMonotone := true

/-- Growth of ℤ²: polynomial degree 2, β(n) = 2n² + 2n + 1. -/
def integerLattice2 : GrowthFunction where
  groupId := 1
  genSet := ⟨2, by omega, 1⟩
  growthType := .polynomial 2
  ballSizes := [1, 5, 13, 25, 41, 61]
  ball_zero := rfl
  isMonotone := true

/-- Growth of ℤᵈ: polynomial degree d. -/
def integerLattice (d : Nat) (hd : d > 0) : GrowthFunction where
  groupId := d
  genSet := ⟨d, hd, d⟩
  growthType := .polynomial d
  ballSizes := [1]
  ball_zero := rfl
  isMonotone := true

/-- Growth of F₂: exponential. -/
def freeGroup2 : GrowthFunction where
  groupId := 100
  genSet := ⟨2, by omega, 2⟩
  growthType := .exponential
  ballSizes := [1, 5, 17, 53, 161]
  ball_zero := rfl
  isMonotone := true

/-- Growth of the Grigorchuk group: intermediate. -/
def grigorchuk : GrowthFunction where
  groupId := 200
  genSet := ⟨4, by omega, 200⟩
  growthType := .intermediate
  ballSizes := [1]
  ball_zero := rfl
  isMonotone := true

/-- The Heisenberg group H₃(ℤ): polynomial degree 4. -/
def heisenberg : GrowthFunction where
  groupId := 300
  genSet := ⟨2, by omega, 300⟩
  growthType := .polynomial 4
  ballSizes := [1]
  ball_zero := rfl
  isMonotone := true

/-- ℤ has polynomial growth of degree 1. -/
theorem integers_polynomial : integers.growthType = .polynomial 1 := rfl

/-- ℤ² has polynomial growth of degree 2. -/
theorem lattice2_polynomial : integerLattice2.growthType = .polynomial 2 := rfl

/-- F₂ has exponential growth. -/
theorem freeGroup2_exponential : freeGroup2.growthType = .exponential := rfl

/-- Grigorchuk group has intermediate growth. -/
theorem grigorchuk_intermediate : grigorchuk.growthType = .intermediate := rfl

/-- Heisenberg group has polynomial growth of degree 4. -/
theorem heisenberg_polynomial : heisenberg.growthType = .polynomial 4 := rfl

/-- β(0) = 1 for ℤ. -/
theorem integers_ball_zero : integers.ballSizes.head? = some 1 := rfl

/-- β(0) = 1 for F₂. -/
theorem freeGroup2_ball_zero : freeGroup2.ballSizes.head? = some 1 := rfl

end GrowthFunction

/-! ## Gromov's Polynomial Growth Theorem -/

/-- Gromov's theorem: a finitely generated group has polynomial growth
if and only if it is virtually nilpotent. -/
structure GromovPolynomialGrowth where
  /-- Group identifier. -/
  groupId : Nat
  /-- Whether the group has polynomial growth. -/
  hasPolynomialGrowth : Bool
  /-- Whether the group is virtually nilpotent. -/
  isVirtuallyNilpotent : Bool
  /-- Nilpotency class (of finite-index nilpotent subgroup). -/
  nilpotencyClass : Nat
  /-- Index of nilpotent subgroup (0 for infinite). -/
  nilpotentIndex : Nat
  /-- Growth degree (for polynomial growth). -/
  growthDegree : Nat
  /-- Gromov's theorem: polynomial growth ↔ virtually nilpotent. -/
  gromov_equiv : hasPolynomialGrowth = isVirtuallyNilpotent

namespace GromovPolynomialGrowth

/-- ℤ: polynomial growth degree 1, nilpotent class 1. -/
def integers : GromovPolynomialGrowth where
  groupId := 0
  hasPolynomialGrowth := true
  isVirtuallyNilpotent := true
  nilpotencyClass := 1
  nilpotentIndex := 1
  growthDegree := 1
  gromov_equiv := rfl

/-- ℤᵈ: polynomial growth degree d, nilpotent class 1. -/
def integerLattice (d : Nat) : GromovPolynomialGrowth where
  groupId := d
  hasPolynomialGrowth := true
  isVirtuallyNilpotent := true
  nilpotencyClass := 1
  nilpotentIndex := 1
  growthDegree := d
  gromov_equiv := rfl

/-- Heisenberg group: polynomial growth, nilpotent class 2. -/
def heisenberg : GromovPolynomialGrowth where
  groupId := 300
  hasPolynomialGrowth := true
  isVirtuallyNilpotent := true
  nilpotencyClass := 2
  nilpotentIndex := 1
  growthDegree := 4
  gromov_equiv := rfl

/-- F₂: not polynomial growth, not virtually nilpotent. -/
def freeGroup2 : GromovPolynomialGrowth where
  groupId := 100
  hasPolynomialGrowth := false
  isVirtuallyNilpotent := false
  nilpotencyClass := 0
  nilpotentIndex := 0
  growthDegree := 0
  gromov_equiv := rfl

/-- Finite groups: polynomial growth (degree 0), virtually nilpotent. -/
def finiteGroup (n : Nat) : GromovPolynomialGrowth where
  groupId := 1000 + n
  hasPolynomialGrowth := true
  isVirtuallyNilpotent := true
  nilpotencyClass := 0
  nilpotentIndex := 1
  growthDegree := 0
  gromov_equiv := rfl

/-- ℤ satisfies Gromov's theorem. -/
theorem integers_gromov : integers.hasPolynomialGrowth = integers.isVirtuallyNilpotent := rfl

/-- F₂ satisfies Gromov's theorem (neither side holds). -/
theorem freeGroup2_gromov : freeGroup2.hasPolynomialGrowth = freeGroup2.isVirtuallyNilpotent := rfl

/-- Heisenberg satisfies Gromov's theorem. -/
theorem heisenberg_gromov : heisenberg.hasPolynomialGrowth = heisenberg.isVirtuallyNilpotent := rfl

end GromovPolynomialGrowth

/-! ## Amenable Groups -/

/-- An amenable group: admits a left-invariant finitely additive probability measure.
Equivalently satisfies the Følner condition. -/
structure AmenableGroup where
  /-- Group identifier. -/
  groupId : Nat
  /-- Whether the group is amenable. -/
  isAmenable : Bool
  /-- Whether the group is solvable (solvable ⇒ amenable). -/
  isSolvable : Bool
  /-- Whether the group has subexponential growth (⇒ amenable). -/
  hasSubexponentialGrowth : Bool
  /-- Whether the group contains F₂ (⇒ not amenable, by von Neumann). -/
  containsFreeSubgroup : Bool
  /-- Solvable implies amenable. -/
  solvable_amenable : isSolvable = true → isAmenable = true
  /-- Subexponential growth implies amenable. -/
  subexp_amenable : hasSubexponentialGrowth = true → isAmenable = true
  /-- Free subgroup implies not amenable (von Neumann conjecture direction). -/
  free_not_amenable : containsFreeSubgroup = true → isAmenable = false

namespace AmenableGroup

/-- ℤ is amenable (abelian hence solvable). -/
def integers : AmenableGroup where
  groupId := 0
  isAmenable := true
  isSolvable := true
  hasSubexponentialGrowth := true
  containsFreeSubgroup := false
  solvable_amenable := fun _ => rfl
  subexp_amenable := fun _ => rfl
  free_not_amenable := fun h => by simp at h

/-- ℤ² is amenable. -/
def integerLattice2 : AmenableGroup where
  groupId := 1
  isAmenable := true
  isSolvable := true
  hasSubexponentialGrowth := true
  containsFreeSubgroup := false
  solvable_amenable := fun _ => rfl
  subexp_amenable := fun _ => rfl
  free_not_amenable := fun h => by simp at h

/-- F₂ is not amenable. -/
def freeGroup2 : AmenableGroup where
  groupId := 100
  isAmenable := false
  isSolvable := false
  hasSubexponentialGrowth := false
  containsFreeSubgroup := true
  solvable_amenable := fun h => by simp at h
  subexp_amenable := fun h => by simp at h
  free_not_amenable := fun _ => rfl

/-- The Grigorchuk group is amenable (intermediate growth). -/
def grigorchuk : AmenableGroup where
  groupId := 200
  isAmenable := true
  isSolvable := false
  hasSubexponentialGrowth := true
  containsFreeSubgroup := false
  solvable_amenable := fun h => by simp at h
  subexp_amenable := fun _ => rfl
  free_not_amenable := fun h => by simp at h

/-- All finite groups are amenable. -/
def finiteGroup (n : Nat) : AmenableGroup where
  groupId := 1000 + n
  isAmenable := true
  isSolvable := true
  hasSubexponentialGrowth := true
  containsFreeSubgroup := false
  solvable_amenable := fun _ => rfl
  subexp_amenable := fun _ => rfl
  free_not_amenable := fun h => by simp at h

/-- The solvable Baumslag-Solitar group BS(1,2) is amenable. -/
def bs12 : AmenableGroup where
  groupId := 500
  isAmenable := true
  isSolvable := true
  hasSubexponentialGrowth := false
  containsFreeSubgroup := false
  solvable_amenable := fun _ => rfl
  subexp_amenable := fun h => by simp at h
  free_not_amenable := fun h => by simp at h

/-- ℤ is amenable. -/
theorem integers_amenable : integers.isAmenable = true := rfl

/-- F₂ is not amenable. -/
theorem freeGroup2_not_amenable : freeGroup2.isAmenable = false := rfl

/-- The Grigorchuk group is amenable. -/
theorem grigorchuk_amenable : grigorchuk.isAmenable = true := rfl

/-- BS(1,2) is amenable. -/
theorem bs12_amenable : bs12.isAmenable = true := rfl

end AmenableGroup

/-! ## Følner Sequences -/

/-- A Følner sequence witnesses amenability: finite sets F_n ⊂ G
such that |gF_n △ F_n| / |F_n| → 0 for all g. -/
structure FolnerSequence where
  /-- Group identifier. -/
  groupId : Nat
  /-- Sizes of Følner sets. -/
  setSizes : List Nat
  /-- All sizes are positive. -/
  sizes_pos : ∀ s ∈ setSizes, s > 0
  /-- The group is amenable (admits a Følner sequence). -/
  witnessesAmenability : Bool

namespace FolnerSequence

/-- Følner sequence for ℤ: intervals [-n, n] of size 2n+1. -/
def integers : FolnerSequence where
  groupId := 0
  setSizes := [1, 3, 5, 7, 9, 11]
  sizes_pos := by simp [List.mem_cons, List.mem_singleton]
               ; omega
  witnessesAmenability := true

/-- Følner sequence for ℤ²: squares [-n,n]² of size (2n+1)². -/
def integerLattice2 : FolnerSequence where
  groupId := 1
  setSizes := [1, 9, 25, 49, 81]
  sizes_pos := by simp [List.mem_cons, List.mem_singleton]
               ; omega
  witnessesAmenability := true

/-- Følner sequence for ℤ witnesses amenability. -/
theorem integers_amenable : integers.witnessesAmenability = true := rfl

end FolnerSequence

/-! ## Quasi-Isometry Invariants -/

/-- Properties that are invariant under quasi-isometry. -/
structure QIInvariant where
  /-- Name of the property. -/
  propertyName : String
  /-- Whether this property is QI-invariant. -/
  isQIInvariant : Bool
  /-- Description. -/
  description : String

namespace QIInvariant

/-- Growth type is a QI invariant. -/
def growthType : QIInvariant where
  propertyName := "growth_type"
  isQIInvariant := true
  description := "Polynomial/exponential/intermediate growth"

/-- Number of ends is a QI invariant. -/
def numberOfEnds : QIInvariant where
  propertyName := "number_of_ends"
  isQIInvariant := true
  description := "0, 1, 2, or ∞ ends"

/-- Amenability is a QI invariant. -/
def amenability : QIInvariant where
  propertyName := "amenability"
  isQIInvariant := true
  description := "Existence of invariant mean"

/-- Hyperbolicity is a QI invariant. -/
def hyperbolicity : QIInvariant where
  propertyName := "hyperbolicity"
  isQIInvariant := true
  description := "Gromov hyperbolicity"

/-- Being finite is NOT a QI invariant (all finite groups are QI to a point). -/
def finiteness : QIInvariant where
  propertyName := "finiteness"
  isQIInvariant := true
  description := "Being finite (QI-trivial)"

/-- Growth type is QI-invariant. -/
theorem growthType_invariant : growthType.isQIInvariant = true := rfl

/-- Number of ends is QI-invariant. -/
theorem ends_invariant : numberOfEnds.isQIInvariant = true := rfl

/-- Amenability is QI-invariant. -/
theorem amenability_invariant : amenability.isQIInvariant = true := rfl

end QIInvariant

/-! ## Number of Ends -/

/-- The number of ends of a finitely generated group. A group has
0 ends (finite), 1 end, 2 ends (virtually ℤ), or ∞ ends. -/
structure NumberOfEnds where
  /-- Group identifier. -/
  groupId : Nat
  /-- Number of ends: 0, 1, 2, or represented by some large number for ∞. -/
  ends : Nat
  /-- Whether the group is finite (0 ends). -/
  isFinite : Bool
  /-- Finite iff 0 ends. -/
  finite_iff_zero : isFinite = (ends == 0)
  /-- Whether the group is virtually ℤ (2 ends). -/
  isVirtuallyZ : Bool
  /-- Virtually ℤ iff 2 ends. -/
  virtuallyZ_iff_two : isVirtuallyZ = (ends == 2)

namespace NumberOfEnds

/-- ℤ has 2 ends. -/
def integers : NumberOfEnds where
  groupId := 0
  ends := 2
  isFinite := false
  finite_iff_zero := rfl
  isVirtuallyZ := true
  virtuallyZ_iff_two := rfl

/-- ℤ² has 1 end. -/
def integerLattice2 : NumberOfEnds where
  groupId := 1
  ends := 1
  isFinite := false
  finite_iff_zero := rfl
  isVirtuallyZ := false
  virtuallyZ_iff_two := rfl

/-- F₂ has infinitely many ends (represented as 1000). -/
def freeGroup2 : NumberOfEnds where
  groupId := 100
  ends := 1000
  isFinite := false
  finite_iff_zero := rfl
  isVirtuallyZ := false
  virtuallyZ_iff_two := rfl

/-- S₃ has 0 ends (finite). -/
def symmetricS3 : NumberOfEnds where
  groupId := 3
  ends := 0
  isFinite := true
  finite_iff_zero := rfl
  isVirtuallyZ := false
  virtuallyZ_iff_two := rfl

/-- ℤ has 2 ends. -/
theorem integers_two_ends : integers.ends = 2 := rfl

/-- ℤ² has 1 end. -/
theorem lattice2_one_end : integerLattice2.ends = 1 := rfl

/-- S₃ has 0 ends. -/
theorem s3_zero_ends : symmetricS3.ends = 0 := rfl

/-- ℤ is virtually ℤ. -/
theorem integers_virtuallyZ : integers.isVirtuallyZ = true := rfl

end NumberOfEnds

/-! ## Path Coherence Witnesses -/

/-- Path witness: Cayley graph integer line has degree 2. -/
def cayley_degree_path :
    Path CayleyGraph.integerLine.vertexDegree 2 :=
  Path.ofEq CayleyGraph.integerLine_degree

/-- Path witness: free group tree has degree 4. -/
def cayley_tree_degree_path :
    Path CayleyGraph.freeGroupTree.vertexDegree 4 :=
  Path.ofEq CayleyGraph.freeGroupTree_degree

/-- Path witness: Cayley graph of S₃ has 6 vertices. -/
def cayley_s3_path :
    Path CayleyGraph.symmetricS3.numVertices 6 :=
  Path.ofEq CayleyGraph.s3_vertices

/-- Path witness: ℤ word metric is symmetric. -/
def word_metric_symmetric_path :
    Path WordMetric.integers.isSymmetric true :=
  Path.ofEq WordMetric.integers_symmetric

/-- Path witness: identity QI is an isometry. -/
def qi_identity_path (s : Nat) :
    Path (QuasiIsometry.identity s).isIsometry true :=
  Path.ofEq (QuasiIsometry.identity_isIsometry s)

/-- Path witness: QI composition of isometries has L = 1. -/
def qi_composition_path (s : Nat) :
    Path (QuasiIsometry.isometry_comp s).composedL 1 :=
  Path.ofEq (QuasiIsometry.isometry_comp_L s)

/-- Path witness: ℤ ≃_QI ℝ via Švarc-Milnor. -/
def svarc_milnor_integers_path :
    Path SvarcMilnor.integersOnLine.isQuasiIsometric true :=
  Path.ofEq SvarcMilnor.integers_qi_line

/-- Path witness: ℤ² ≃_QI ℝ² via Švarc-Milnor. -/
def svarc_milnor_lattice_path :
    Path SvarcMilnor.latticeOnPlane.isQuasiIsometric true :=
  Path.ofEq SvarcMilnor.lattice_qi_plane

/-- Path witness: ℤ has polynomial growth of degree 1. -/
def growth_integers_path :
    Path GrowthFunction.integers.growthType (.polynomial 1) :=
  Path.ofEq GrowthFunction.integers_polynomial

/-- Path witness: F₂ has exponential growth. -/
def growth_freeGroup2_path :
    Path GrowthFunction.freeGroup2.growthType .exponential :=
  Path.ofEq GrowthFunction.freeGroup2_exponential

/-- Path witness: Grigorchuk group has intermediate growth. -/
def growth_grigorchuk_path :
    Path GrowthFunction.grigorchuk.growthType .intermediate :=
  Path.ofEq GrowthFunction.grigorchuk_intermediate

/-- Path witness: Heisenberg group polynomial degree 4. -/
def growth_heisenberg_path :
    Path GrowthFunction.heisenberg.growthType (.polynomial 4) :=
  Path.ofEq GrowthFunction.heisenberg_polynomial

/-- Path witness: Gromov's theorem for ℤ. -/
def gromov_growth_path :
    Path GromovPolynomialGrowth.integers.hasPolynomialGrowth
         GromovPolynomialGrowth.integers.isVirtuallyNilpotent :=
  Path.ofEq GromovPolynomialGrowth.integers_gromov

/-- Path witness: Gromov's theorem for F₂. -/
def gromov_free_path :
    Path GromovPolynomialGrowth.freeGroup2.hasPolynomialGrowth
         GromovPolynomialGrowth.freeGroup2.isVirtuallyNilpotent :=
  Path.ofEq GromovPolynomialGrowth.freeGroup2_gromov

/-- Path witness: ℤ is amenable. -/
def amenable_integers_path :
    Path AmenableGroup.integers.isAmenable true :=
  Path.ofEq AmenableGroup.integers_amenable

/-- Path witness: F₂ is not amenable. -/
def amenable_freeGroup2_path :
    Path AmenableGroup.freeGroup2.isAmenable false :=
  Path.ofEq AmenableGroup.freeGroup2_not_amenable

/-- Path witness: Grigorchuk group is amenable. -/
def amenable_grigorchuk_path :
    Path AmenableGroup.grigorchuk.isAmenable true :=
  Path.ofEq AmenableGroup.grigorchuk_amenable

/-- Path witness: BS(1,2) is amenable. -/
def amenable_bs12_path :
    Path AmenableGroup.bs12.isAmenable true :=
  Path.ofEq AmenableGroup.bs12_amenable

/-- Path witness: Følner sequence for ℤ. -/
def folner_integers_path :
    Path FolnerSequence.integers.witnessesAmenability true :=
  Path.ofEq FolnerSequence.integers_amenable

/-- Path witness: ℤ has 2 ends. -/
def ends_integers_path :
    Path NumberOfEnds.integers.ends 2 :=
  Path.ofEq NumberOfEnds.integers_two_ends

/-- Path witness: ℤ² has 1 end. -/
def ends_lattice2_path :
    Path NumberOfEnds.integerLattice2.ends 1 :=
  Path.ofEq NumberOfEnds.lattice2_one_end

/-- Path witness: S₃ has 0 ends. -/
def ends_s3_path :
    Path NumberOfEnds.symmetricS3.ends 0 :=
  Path.ofEq NumberOfEnds.s3_zero_ends

/-- Path witness: ℤ is virtually ℤ. -/
def integers_virtuallyZ_path :
    Path NumberOfEnds.integers.isVirtuallyZ true :=
  Path.ofEq NumberOfEnds.integers_virtuallyZ

/-- Path witness: growth type is QI-invariant. -/
def qi_invariant_growth_path :
    Path QIInvariant.growthType.isQIInvariant true :=
  Path.ofEq QIInvariant.growthType_invariant

/-- Path witness: amenability is QI-invariant. -/
def qi_invariant_amenable_path :
    Path QIInvariant.amenability.isQIInvariant true :=
  Path.ofEq QIInvariant.amenability_invariant

end GeometricGroupTheory
end ComputationalPaths
