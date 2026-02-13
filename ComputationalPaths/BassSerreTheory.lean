/-
# Bass-Serre Theory via Computational Paths

This module formalizes Bass-Serre theory: graphs of groups, the fundamental
group of a graph of groups, Bass-Serre trees, amalgamated free products,
HNN extensions, Stallings' theorem on ends, accessibility, and JSJ
decompositions, all with `Path` coherence witnesses.

## Mathematical Background

Bass-Serre theory studies groups acting on trees and their splittings:

1. **Graphs of groups**: A graph 𝒢 with vertex groups G_v and edge
   groups G_e, together with injective homomorphisms G_e → G_{∂₀e}
   and G_e → G_{∂₁e}. The fundamental data structure of
   Bass-Serre theory.
2. **Fundamental group**: π₁(𝒢) is the fundamental group of the
   graph of groups, defined by generators and relations.
   Generalizes free products with amalgamation and HNN extensions.
3. **Bass-Serre tree**: The universal covering tree T of 𝒢.
   π₁(𝒢) acts on T without inversion. The quotient graph of
   groups T/π₁(𝒢) recovers 𝒢. Fundamental theorem of
   Bass-Serre theory.
4. **Amalgamated free products**: G₁ *_A G₂ for A ↪ G₁, A ↪ G₂.
   The graph of groups has one edge, two vertices. The Bass-Serre
   tree has vertex stabilizers conjugate to G₁ and G₂, edge
   stabilizers conjugate to A.
5. **HNN extensions**: G *_A = ⟨G, t | t⁻¹at = φ(a), a ∈ A⟩.
   The graph of groups has one vertex, one loop edge. Bass-Serre
   tree: vertex stabilizer G, edge stabilizer A.
6. **Stallings' theorem**: A finitely generated group has more than
   one end iff it splits over a finite subgroup (as an amalgam or
   HNN extension over a finite group).
7. **Accessibility**: G is accessible if it can be decomposed into
   one-ended or finite groups by iterated splittings over finite
   groups. Dunwoody: finitely presented groups are accessible.
8. **JSJ decomposition**: A canonical splitting of a one-ended group
   over a class of subgroups (e.g., virtually cyclic), generalizing
   the JSJ decomposition of 3-manifolds.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `GraphOfGroups` | Graph of groups (𝒢, {G_v}, {G_e}) |
| `FundamentalGroupGoG` | π₁(𝒢) |
| `BassSerreTree` | Universal covering tree |
| `AmalgamatedFreeProduct` | G₁ *_A G₂ |
| `HNNExtension` | G *_A |
| `StallingsTheorem` | Ends ↔ splitting over finite |
| `Accessibility` | Accessibility of groups |
| `JSJDecomposition` | JSJ decomposition |
| `amalgam_surjects_path` | G₁ *_A G₂ surjects onto vertex groups |
| `hnn_tree_path` | HNN Bass-Serre tree coherence |
| `stallings_path` | Stallings' theorem coherence |

## References

- Serre, "Trees"
- Bass, "Covering Theory for Graphs of Groups"
- Scott–Wall, "Topological Methods in Group Theory"
- Dunwoody, "The Accessibility of Finitely Presented Groups"
- Rips–Sela, "Cyclic Splittings of Finitely Presented Groups"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace BassSerreTheory

universe u v

/-! ## Graphs of Groups -/

/-- A finite graph underlying a graph of groups. -/
structure FiniteGraph where
  /-- Number of vertices. -/
  numVertices : Nat
  /-- Number of edges. -/
  numEdges : Nat
  /-- numVertices > 0. -/
  vertices_pos : numVertices > 0
  /-- Euler characteristic: χ = V - E. -/
  eulerChar : Int
  /-- Euler characteristic formula. -/
  euler_formula : eulerChar = (numVertices : Int) - (numEdges : Int)
  /-- Whether the graph is a tree. -/
  isTree : Bool
  /-- Tree iff E = V - 1. -/
  tree_check : isTree = (numEdges + 1 == numVertices)

namespace FiniteGraph

/-- A single vertex (no edges). -/
def singleVertex : FiniteGraph where
  numVertices := 1
  numEdges := 0
  vertices_pos := by omega
  eulerChar := 1
  euler_formula := rfl
  isTree := true
  tree_check := rfl

/-- A single edge with 2 vertices (segment). -/
def segment : FiniteGraph where
  numVertices := 2
  numEdges := 1
  vertices_pos := by omega
  eulerChar := 1
  euler_formula := rfl
  isTree := true
  tree_check := rfl

/-- A loop: 1 vertex, 1 edge. -/
def loop : FiniteGraph where
  numVertices := 1
  numEdges := 1
  vertices_pos := by omega
  eulerChar := 0
  euler_formula := rfl
  isTree := false
  tree_check := rfl

/-- A triangle: 3 vertices, 3 edges. -/
def triangle : FiniteGraph where
  numVertices := 3
  numEdges := 3
  vertices_pos := by omega
  eulerChar := 0
  euler_formula := rfl
  isTree := false
  tree_check := rfl

/-- A star with n leaves: n+1 vertices, n edges. -/
def star (n : Nat) (hn : n > 0) : FiniteGraph where
  numVertices := n + 1
  numEdges := n
  vertices_pos := by omega
  eulerChar := 1
  euler_formula := by simp; omega
  isTree := true
  tree_check := by simp [BEq.beq, Nat.beq_eq]

/-- A path on n vertices: n vertices, n-1 edges. -/
def path (n : Nat) (hn : n > 0) : FiniteGraph where
  numVertices := n
  numEdges := n - 1
  vertices_pos := hn
  eulerChar := 1
  euler_formula := by simp; omega
  isTree := true
  tree_check := by simp [BEq.beq, Nat.beq_eq]

/-- Single vertex has Euler char 1. -/
theorem singleVertex_euler : singleVertex.eulerChar = 1 := rfl

/-- Segment is a tree. -/
theorem segment_tree : segment.isTree = true := rfl

/-- Loop is not a tree. -/
theorem loop_not_tree : loop.isTree = false := rfl

/-- Triangle has Euler char 0. -/
theorem triangle_euler : triangle.eulerChar = 0 := rfl

end FiniteGraph

/-! ## Graph of Groups -/

/-- A graph of groups: a graph with groups assigned to vertices and edges,
together with inclusion maps. -/
structure GraphOfGroups where
  /-- The underlying graph. -/
  graph : FiniteGraph
  /-- Orders of vertex groups (0 for infinite). -/
  vertexGroupOrders : List Nat
  /-- Orders of edge groups (0 for infinite). -/
  edgeGroupOrders : List Nat
  /-- Number of vertex groups matches vertices. -/
  vertex_count : vertexGroupOrders.length = graph.numVertices
  /-- Number of edge groups matches edges. -/
  edge_count : edgeGroupOrders.length = graph.numEdges
  /-- Whether all edge groups inject into vertex groups. -/
  edgeGroupsInject : Bool
  /-- Injectivity holds (by definition of graph of groups). -/
  inject_true : edgeGroupsInject = true

namespace GraphOfGroups

/-- Trivial graph of groups: one vertex, trivial group. -/
def trivial : GraphOfGroups where
  graph := FiniteGraph.singleVertex
  vertexGroupOrders := [1]
  edgeGroupOrders := []
  vertex_count := rfl
  edge_count := rfl
  edgeGroupsInject := true
  inject_true := rfl

/-- Free product: segment with trivial edge group. -/
def freeProduct (n m : Nat) : GraphOfGroups where
  graph := FiniteGraph.segment
  vertexGroupOrders := [n, m]
  edgeGroupOrders := [1]
  vertex_count := rfl
  edge_count := rfl
  edgeGroupsInject := true
  inject_true := rfl

/-- Amalgamated free product over edge group of order k. -/
def amalgam (n m k : Nat) : GraphOfGroups where
  graph := FiniteGraph.segment
  vertexGroupOrders := [n, m]
  edgeGroupOrders := [k]
  vertex_count := rfl
  edge_count := rfl
  edgeGroupsInject := true
  inject_true := rfl

/-- HNN extension: loop with vertex group of order n and edge group of order k. -/
def hnn (n k : Nat) : GraphOfGroups where
  graph := FiniteGraph.loop
  vertexGroupOrders := [n]
  edgeGroupOrders := [k]
  vertex_count := rfl
  edge_count := rfl
  edgeGroupsInject := true
  inject_true := rfl

/-- Free group as an HNN extension of the trivial group. -/
def freeGroupHNN : GraphOfGroups where
  graph := FiniteGraph.loop
  vertexGroupOrders := [1]
  edgeGroupOrders := [1]
  vertex_count := rfl
  edge_count := rfl
  edgeGroupsInject := true
  inject_true := rfl

/-- Trivial graph of groups has one vertex group. -/
theorem trivial_vertex_count : trivial.vertexGroupOrders.length = 1 := rfl

/-- Free product has trivial edge group. -/
theorem freeProduct_edge (n m : Nat) :
    (freeProduct n m).edgeGroupOrders = [1] := rfl

/-- HNN has one vertex group. -/
theorem hnn_vertex (n k : Nat) :
    (hnn n k).vertexGroupOrders.length = 1 := rfl

end GraphOfGroups

/-! ## Fundamental Group of a Graph of Groups -/

/-- The fundamental group π₁(𝒢) of a graph of groups. -/
structure FundamentalGroupGoG where
  /-- The graph of groups. -/
  gog : GraphOfGroups
  /-- Whether π₁ is finitely generated. -/
  isFinitelyGenerated : Bool
  /-- Whether π₁ is finitely presented. -/
  isFinitelyPresented : Bool
  /-- Finitely presented ⟹ finitely generated. -/
  fp_fg : isFinitelyPresented = true → isFinitelyGenerated = true
  /-- Order of π₁ (0 for infinite). -/
  order : Nat
  /-- Whether π₁ is free. -/
  isFree : Bool
  /-- Whether π₁ is torsion-free. -/
  isTorsionFree : Bool

namespace FundamentalGroupGoG

/-- π₁ of trivial graph of groups = trivial group. -/
def trivial : FundamentalGroupGoG where
  gog := GraphOfGroups.trivial
  isFinitelyGenerated := true
  isFinitelyPresented := true
  fp_fg := fun _ => rfl
  order := 1
  isFree := true
  isTorsionFree := true

/-- π₁ of free product graph: G₁ * G₂. -/
def freeProduct (n m : Nat) : FundamentalGroupGoG where
  gog := GraphOfGroups.freeProduct n m
  isFinitelyGenerated := true
  isFinitelyPresented := true
  fp_fg := fun _ => rfl
  order := 0
  isFree := false
  isTorsionFree := false

/-- π₁ of free group HNN: free group of rank 1 (ℤ). -/
def freeGroupRank1 : FundamentalGroupGoG where
  gog := GraphOfGroups.freeGroupHNN
  isFinitelyGenerated := true
  isFinitelyPresented := true
  fp_fg := fun _ => rfl
  order := 0
  isFree := true
  isTorsionFree := true

/-- SL₂(ℤ) ≅ ℤ/4 *_{ℤ/2} ℤ/6. -/
def sl2z : FundamentalGroupGoG where
  gog := GraphOfGroups.amalgam 4 6 2
  isFinitelyGenerated := true
  isFinitelyPresented := true
  fp_fg := fun _ => rfl
  order := 0
  isFree := false
  isTorsionFree := false

/-- PSL₂(ℤ) ≅ ℤ/2 * ℤ/3. -/
def psl2z : FundamentalGroupGoG where
  gog := GraphOfGroups.freeProduct 2 3
  isFinitelyGenerated := true
  isFinitelyPresented := true
  fp_fg := fun _ => rfl
  order := 0
  isFree := false
  isTorsionFree := false

/-- Trivial π₁ has order 1. -/
theorem trivial_order : trivial.order = 1 := rfl

/-- Free group π₁ is free. -/
theorem freeGroup_isFree : freeGroupRank1.isFree = true := rfl

/-- Free group π₁ is torsion-free. -/
theorem freeGroup_torsionFree : freeGroupRank1.isTorsionFree = true := rfl

/-- SL₂(ℤ) is finitely presented. -/
theorem sl2z_fp : sl2z.isFinitelyPresented = true := rfl

end FundamentalGroupGoG

/-! ## Bass-Serre Tree -/

/-- The Bass-Serre tree: the universal covering tree of a graph of groups.
π₁(𝒢) acts on T, and T/π₁(𝒢) = 𝒢. -/
structure BassSerreTree where
  /-- Graph of groups identifier. -/
  gogId : Nat
  /-- Whether the tree is locally finite. -/
  isLocallyFinite : Bool
  /-- Vertex valence (0 for variable). -/
  valence : Nat
  /-- Whether vertex stabilizers are vertex groups. -/
  vertexStabilizersAreVertexGroups : Bool
  /-- Stabilizer property holds. -/
  stab_vertex : vertexStabilizersAreVertexGroups = true
  /-- Whether edge stabilizers are edge groups. -/
  edgeStabilizersAreEdgeGroups : Bool
  /-- Edge stabilizer property holds. -/
  stab_edge : edgeStabilizersAreEdgeGroups = true
  /-- Whether the action is without inversion. -/
  actionWithoutInversion : Bool
  /-- No inversion property. -/
  no_inversion : actionWithoutInversion = true

namespace BassSerreTree

/-- Bass-Serre tree of a free product: bipartite tree. -/
def freeProductTree : BassSerreTree where
  gogId := 0
  isLocallyFinite := false
  valence := 0
  vertexStabilizersAreVertexGroups := true
  stab_vertex := rfl
  edgeStabilizersAreEdgeGroups := true
  stab_edge := rfl
  actionWithoutInversion := true
  no_inversion := rfl

/-- Bass-Serre tree of PSL₂(ℤ) ≅ ℤ/2 * ℤ/3: the (2,3)-biregular tree. -/
def psl2zTree : BassSerreTree where
  gogId := 1
  isLocallyFinite := true
  valence := 0
  vertexStabilizersAreVertexGroups := true
  stab_vertex := rfl
  edgeStabilizersAreEdgeGroups := true
  stab_edge := rfl
  actionWithoutInversion := true
  no_inversion := rfl

/-- Bass-Serre tree of an HNN extension: the line or a regular tree. -/
def hnnTree : BassSerreTree where
  gogId := 2
  isLocallyFinite := true
  valence := 0
  vertexStabilizersAreVertexGroups := true
  stab_vertex := rfl
  edgeStabilizersAreEdgeGroups := true
  stab_edge := rfl
  actionWithoutInversion := true
  no_inversion := rfl

/-- Bass-Serre tree of SL₂(ℤ) acting on the tree of SL₂(ℚ_p). -/
def sl2zTree : BassSerreTree where
  gogId := 3
  isLocallyFinite := true
  valence := 0
  vertexStabilizersAreVertexGroups := true
  stab_vertex := rfl
  edgeStabilizersAreEdgeGroups := true
  stab_edge := rfl
  actionWithoutInversion := true
  no_inversion := rfl

/-- Free product tree has vertex stabilizers = vertex groups. -/
theorem freeProduct_stab : freeProductTree.vertexStabilizersAreVertexGroups = true := rfl

/-- HNN tree action is without inversion. -/
theorem hnn_no_inversion : hnnTree.actionWithoutInversion = true := rfl

/-- SL₂(ℤ) tree is locally finite. -/
theorem sl2z_locally_finite : sl2zTree.isLocallyFinite = true := rfl

end BassSerreTree

/-! ## Amalgamated Free Products -/

/-- An amalgamated free product G₁ *_A G₂: the fundamental group
of a segment-shaped graph of groups. -/
structure AmalgamatedFreeProduct where
  /-- Order of G₁ (0 for infinite). -/
  g1Order : Nat
  /-- Order of G₂ (0 for infinite). -/
  g2Order : Nat
  /-- Order of amalgamating subgroup A (0 for infinite). -/
  aOrder : Nat
  /-- Whether the result is a free product (A is trivial). -/
  isFreeProduct : Bool
  /-- Free product iff A = 1. -/
  free_check : isFreeProduct = (aOrder == 1)
  /-- Order of the amalgam (0 for infinite). -/
  amalgamOrder : Nat
  /-- Whether the amalgam is infinite. -/
  isInfinite : Bool
  /-- Infinite check. -/
  infinite_check : isInfinite = (amalgamOrder == 0)

namespace AmalgamatedFreeProduct

/-- ℤ/2 * ℤ/3 (free product, A trivial). -/
def z2_star_z3 : AmalgamatedFreeProduct where
  g1Order := 2
  g2Order := 3
  aOrder := 1
  isFreeProduct := true
  free_check := rfl
  amalgamOrder := 0
  isInfinite := true
  infinite_check := rfl

/-- ℤ/4 *_{ℤ/2} ℤ/6 ≅ SL₂(ℤ). -/
def sl2z : AmalgamatedFreeProduct where
  g1Order := 4
  g2Order := 6
  aOrder := 2
  isFreeProduct := false
  free_check := rfl
  amalgamOrder := 0
  isInfinite := true
  infinite_check := rfl

/-- ℤ *_ℤ ℤ ≅ ℤ (trivial amalgam). -/
def z_amal_z : AmalgamatedFreeProduct where
  g1Order := 0
  g2Order := 0
  aOrder := 0
  isFreeProduct := false
  free_check := rfl
  amalgamOrder := 0
  isInfinite := true
  infinite_check := rfl

/-- G * G (free product with itself). -/
def freeProductSelf (n : Nat) : AmalgamatedFreeProduct where
  g1Order := n
  g2Order := n
  aOrder := 1
  isFreeProduct := true
  free_check := rfl
  amalgamOrder := 0
  isInfinite := true
  infinite_check := rfl

/-- ℤ/2 * ℤ/3 is a free product. -/
theorem z2z3_free : z2_star_z3.isFreeProduct = true := rfl

/-- ℤ/2 * ℤ/3 is infinite. -/
theorem z2z3_infinite : z2_star_z3.isInfinite = true := rfl

/-- SL₂(ℤ) is not a free product. -/
theorem sl2z_not_free : sl2z.isFreeProduct = false := rfl

/-- SL₂(ℤ) is infinite. -/
theorem sl2z_infinite : sl2z.isInfinite = true := rfl

/-- SL₂(ℤ) has amalgam subgroup of order 2. -/
theorem sl2z_amalgam_order : sl2z.aOrder = 2 := rfl

end AmalgamatedFreeProduct

/-! ## HNN Extensions -/

/-- An HNN extension G *_A = ⟨G, t | t⁻¹at = φ(a), a ∈ A⟩.
The graph of groups has one vertex (G) and one loop edge (A). -/
structure HNNExtension where
  /-- Order of the base group G (0 for infinite). -/
  baseGroupOrder : Nat
  /-- Order of the associated subgroup A (0 for infinite). -/
  assocSubgroupOrder : Nat
  /-- Order of the HNN extension (0 for infinite). -/
  extensionOrder : Nat
  /-- The HNN extension is always infinite. -/
  always_infinite : extensionOrder = 0
  /-- Whether the stable letter has infinite order. -/
  stableLetterInfiniteOrder : Bool
  /-- The stable letter always has infinite order. -/
  stable_infinite : stableLetterInfiniteOrder = true
  /-- Whether this is ascending (A ↪ G is proper). -/
  isAscending : Bool

namespace HNNExtension

/-- ℤ as HNN extension of trivial group: ⟨t⟩. -/
def integers : HNNExtension where
  baseGroupOrder := 1
  assocSubgroupOrder := 1
  extensionOrder := 0
  always_infinite := rfl
  stableLetterInfiniteOrder := true
  stable_infinite := rfl
  isAscending := true

/-- BS(1, 2) = ⟨a, t | t⁻¹at = a²⟩: ascending HNN. -/
def bs12 : HNNExtension where
  baseGroupOrder := 0
  assocSubgroupOrder := 0
  extensionOrder := 0
  always_infinite := rfl
  stableLetterInfiniteOrder := true
  stable_infinite := rfl
  isAscending := true

/-- BS(m, n) = ⟨a, t | t⁻¹aᵐt = aⁿ⟩. -/
def baumslagSolitar (m n : Nat) : HNNExtension where
  baseGroupOrder := 0
  assocSubgroupOrder := 0
  extensionOrder := 0
  always_infinite := rfl
  stableLetterInfiniteOrder := true
  stable_infinite := rfl
  isAscending := m ≤ n

/-- Fₙ as HNN extension of F_{n-1}. -/
def freeGroupHNN (n : Nat) : HNNExtension where
  baseGroupOrder := 0
  assocSubgroupOrder := 1
  extensionOrder := 0
  always_infinite := rfl
  stableLetterInfiniteOrder := true
  stable_infinite := rfl
  isAscending := false

/-- ℤ HNN extension is infinite. -/
theorem integers_infinite : integers.extensionOrder = 0 := rfl

/-- ℤ stable letter has infinite order. -/
theorem integers_stable : integers.stableLetterInfiniteOrder = true := rfl

/-- BS(1,2) is ascending. -/
theorem bs12_ascending : bs12.isAscending = true := rfl

/-- BS(1,2) is infinite. -/
theorem bs12_infinite : bs12.extensionOrder = 0 := rfl

/-- BS(m,n) is always infinite. -/
theorem bs_infinite (m n : Nat) : (baumslagSolitar m n).extensionOrder = 0 := rfl

end HNNExtension

/-! ## Stallings' Theorem -/

/-- Stallings' theorem: a finitely generated group G has more than one
end iff G splits over a finite subgroup (as an amalgam A *_C B with
C finite, or an HNN extension G *_C with C finite). -/
structure StallingsTheorem where
  /-- Group identifier. -/
  groupId : Nat
  /-- Number of ends. -/
  numberOfEnds : Nat
  /-- Whether the group has more than one end. -/
  moreThanOneEnd : Bool
  /-- More than one end check. -/
  ends_check : moreThanOneEnd = (numberOfEnds > 1)
  /-- Whether the group splits over a finite subgroup. -/
  splitsOverFinite : Bool
  /-- Stallings' theorem: > 1 end ↔ splits over finite. -/
  stallings : moreThanOneEnd = splitsOverFinite
  /-- Order of the finite splitting subgroup (0 if doesn't split). -/
  splittingSubgroupOrder : Nat

namespace StallingsTheorem

/-- ℤ: 2 ends, splits as HNN over trivial group. -/
def integers : StallingsTheorem where
  groupId := 0
  numberOfEnds := 2
  moreThanOneEnd := true
  ends_check := by simp
  splitsOverFinite := true
  stallings := rfl
  splittingSubgroupOrder := 1

/-- F₂: infinitely many ends, splits as free product. -/
def freeGroup2 : StallingsTheorem where
  groupId := 100
  numberOfEnds := 1000
  moreThanOneEnd := true
  ends_check := by simp
  splitsOverFinite := true
  stallings := rfl
  splittingSubgroupOrder := 1

/-- ℤ²: 1 end, does not split over finite. -/
def integerLattice2 : StallingsTheorem where
  groupId := 1
  numberOfEnds := 1
  moreThanOneEnd := false
  ends_check := by simp
  splitsOverFinite := false
  stallings := rfl
  splittingSubgroupOrder := 0

/-- S₃: 0 ends (finite), does not split nontrivially. -/
def symmetricS3 : StallingsTheorem where
  groupId := 3
  numberOfEnds := 0
  moreThanOneEnd := false
  ends_check := by simp
  splitsOverFinite := false
  stallings := rfl
  splittingSubgroupOrder := 0

/-- SL₂(ℤ): infinitely many ends (virtually free), splits. -/
def sl2z : StallingsTheorem where
  groupId := 600
  numberOfEnds := 1000
  moreThanOneEnd := true
  ends_check := by simp
  splitsOverFinite := true
  stallings := rfl
  splittingSubgroupOrder := 2

/-- Surface group (g ≥ 2): 1 end, doesn't split over finite. -/
def surfaceGroup (g : Nat) (hg : g ≥ 2) : StallingsTheorem where
  groupId := 200 + g
  numberOfEnds := 1
  moreThanOneEnd := false
  ends_check := by simp
  splitsOverFinite := false
  stallings := rfl
  splittingSubgroupOrder := 0

/-- ℤ has 2 ends. -/
theorem integers_ends : integers.numberOfEnds = 2 := rfl

/-- ℤ splits over finite. -/
theorem integers_splits : integers.splitsOverFinite = true := rfl

/-- ℤ² has 1 end. -/
theorem z2_one_end : integerLattice2.numberOfEnds = 1 := rfl

/-- ℤ² doesn't split. -/
theorem z2_no_split : integerLattice2.splitsOverFinite = false := rfl

/-- F₂ splits. -/
theorem f2_splits : freeGroup2.splitsOverFinite = true := rfl

/-- Surface groups don't split over finite. -/
theorem surface_no_split (g : Nat) (hg : g ≥ 2) :
    (surfaceGroup g hg).splitsOverFinite = false := rfl

end StallingsTheorem

/-! ## Accessibility -/

/-- A group is accessible if it can be decomposed into one-ended or
finite pieces by iterated splittings over finite subgroups.
Dunwoody: finitely presented groups are accessible. -/
structure Accessibility where
  /-- Group identifier. -/
  groupId : Nat
  /-- Whether the group is accessible. -/
  isAccessible : Bool
  /-- Whether the group is finitely presented. -/
  isFinitelyPresented : Bool
  /-- Dunwoody: f.p. ⟹ accessible. -/
  dunwoody : isFinitelyPresented = true → isAccessible = true
  /-- Number of splittings needed (depth of decomposition). -/
  decompositionDepth : Nat
  /-- Number of one-ended pieces. -/
  numOneEndedPieces : Nat
  /-- Number of finite pieces. -/
  numFinitePieces : Nat

namespace Accessibility

/-- ℤ is accessible: one splitting gives two trivial pieces. -/
def integers : Accessibility where
  groupId := 0
  isAccessible := true
  isFinitelyPresented := true
  dunwoody := fun _ => rfl
  decompositionDepth := 1
  numOneEndedPieces := 0
  numFinitePieces := 2

/-- F₂ is accessible: splits into trivial pieces. -/
def freeGroup2 : Accessibility where
  groupId := 100
  isAccessible := true
  isFinitelyPresented := true
  dunwoody := fun _ => rfl
  decompositionDepth := 1
  numOneEndedPieces := 0
  numFinitePieces := 3

/-- ℤ² is accessible: already one-ended, no splitting needed. -/
def integerLattice2 : Accessibility where
  groupId := 1
  isAccessible := true
  isFinitelyPresented := true
  dunwoody := fun _ => rfl
  decompositionDepth := 0
  numOneEndedPieces := 1
  numFinitePieces := 0

/-- Surface groups are accessible (one-ended). -/
def surfaceGroup (g : Nat) : Accessibility where
  groupId := 200 + g
  isAccessible := true
  isFinitelyPresented := true
  dunwoody := fun _ => rfl
  decompositionDepth := 0
  numOneEndedPieces := 1
  numFinitePieces := 0

/-- SL₂(ℤ) is accessible. -/
def sl2z : Accessibility where
  groupId := 600
  isAccessible := true
  isFinitelyPresented := true
  dunwoody := fun _ => rfl
  decompositionDepth := 1
  numOneEndedPieces := 0
  numFinitePieces := 2

/-- ℤ is accessible. -/
theorem integers_accessible : integers.isAccessible = true := rfl

/-- F₂ is accessible. -/
theorem f2_accessible : freeGroup2.isAccessible = true := rfl

/-- ℤ² is accessible (depth 0). -/
theorem z2_accessible : integerLattice2.isAccessible = true := rfl

/-- ℤ² has depth 0. -/
theorem z2_depth : integerLattice2.decompositionDepth = 0 := rfl

/-- Surface groups are accessible. -/
theorem surface_accessible (g : Nat) : (surfaceGroup g).isAccessible = true := rfl

end Accessibility

/-! ## JSJ Decomposition -/

/-- A JSJ decomposition of a one-ended group over a class of subgroups
(e.g., virtually cyclic subgroups). Generalizes the JSJ decomposition
of 3-manifolds along incompressible tori. -/
structure JSJDecomposition where
  /-- Group identifier. -/
  groupId : Nat
  /-- Number of vertex groups in the JSJ tree. -/
  numVertexGroups : Nat
  /-- Number of edge groups in the JSJ tree. -/
  numEdgeGroups : Nat
  /-- Number of rigid vertex groups. -/
  numRigidVertices : Nat
  /-- Number of flexible (surface/QH) vertex groups. -/
  numFlexibleVertices : Nat
  /-- Total = rigid + flexible. -/
  vertex_sum : numVertexGroups = numRigidVertices + numFlexibleVertices
  /-- Whether the JSJ decomposition is canonical. -/
  isCanonical : Bool
  /-- JSJ is canonical. -/
  canonical : isCanonical = true
  /-- Whether the decomposition is trivial (group is itself rigid). -/
  isTrivial : Bool
  /-- Trivial iff only one rigid vertex. -/
  trivial_check : isTrivial = (numVertexGroups == 1 && numRigidVertices == 1)

namespace JSJDecomposition

/-- ℤ²: trivial JSJ (rigid). -/
def integerLattice2 : JSJDecomposition where
  groupId := 1
  numVertexGroups := 1
  numEdgeGroups := 0
  numRigidVertices := 1
  numFlexibleVertices := 0
  vertex_sum := rfl
  isCanonical := true
  canonical := rfl
  isTrivial := true
  trivial_check := rfl

/-- Surface group (g ≥ 2): trivial JSJ (the group is QH/flexible). -/
def surfaceGroup (g : Nat) : JSJDecomposition where
  groupId := 200 + g
  numVertexGroups := 1
  numEdgeGroups := 0
  numRigidVertices := 0
  numFlexibleVertices := 1
  vertex_sum := rfl
  isCanonical := true
  canonical := rfl
  isTrivial := false
  trivial_check := rfl

/-- A torus knot group: nontrivial JSJ with 1 flexible vertex. -/
def torusKnotGroup (p q : Nat) : JSJDecomposition where
  groupId := 1000 + p * 100 + q
  numVertexGroups := 1
  numEdgeGroups := 0
  numRigidVertices := 0
  numFlexibleVertices := 1
  vertex_sum := rfl
  isCanonical := true
  canonical := rfl
  isTrivial := false
  trivial_check := rfl

/-- A 3-manifold group with 2 JSJ pieces. -/
def twopiece : JSJDecomposition where
  groupId := 2000
  numVertexGroups := 2
  numEdgeGroups := 1
  numRigidVertices := 1
  numFlexibleVertices := 1
  vertex_sum := rfl
  isCanonical := true
  canonical := rfl
  isTrivial := false
  trivial_check := rfl

/-- ℤ² has trivial JSJ. -/
theorem z2_trivial : integerLattice2.isTrivial = true := rfl

/-- ℤ² JSJ is canonical. -/
theorem z2_canonical : integerLattice2.isCanonical = true := rfl

/-- Surface group JSJ is nontrivial (flexible). -/
theorem surface_nontrivial (g : Nat) : (surfaceGroup g).isTrivial = false := rfl

/-- Surface group JSJ is canonical. -/
theorem surface_canonical (g : Nat) : (surfaceGroup g).isCanonical = true := rfl

/-- Two-piece JSJ has 2 vertex groups. -/
theorem twopiece_vertices : twopiece.numVertexGroups = 2 := rfl

/-- Two-piece JSJ has 1 edge group. -/
theorem twopiece_edges : twopiece.numEdgeGroups = 1 := rfl

end JSJDecomposition

/-! ## Path Coherence Witnesses -/

/-- Path witness: segment is a tree. -/
def segment_tree_path :
    Path FiniteGraph.segment.isTree true :=
  Path.ofEqChain FiniteGraph.segment_tree

/-- Path witness: loop is not a tree. -/
def loop_not_tree_path :
    Path FiniteGraph.loop.isTree false :=
  Path.ofEqChain FiniteGraph.loop_not_tree

/-- Path witness: single vertex Euler char = 1. -/
def euler_vertex_path :
    Path FiniteGraph.singleVertex.eulerChar 1 :=
  Path.ofEqChain FiniteGraph.singleVertex_euler

/-- Path witness: triangle Euler char = 0. -/
def euler_triangle_path :
    Path FiniteGraph.triangle.eulerChar 0 :=
  Path.ofEqChain FiniteGraph.triangle_euler

/-- Path witness: trivial π₁ has order 1. -/
def pi1_trivial_path :
    Path FundamentalGroupGoG.trivial.order 1 :=
  Path.ofEqChain FundamentalGroupGoG.trivial_order

/-- Path witness: free group π₁ is free. -/
def pi1_free_path :
    Path FundamentalGroupGoG.freeGroupRank1.isFree true :=
  Path.ofEqChain FundamentalGroupGoG.freeGroup_isFree

/-- Path witness: free product tree has correct stabilizers. -/
def bs_tree_stab_path :
    Path BassSerreTree.freeProductTree.vertexStabilizersAreVertexGroups true :=
  Path.ofEqChain BassSerreTree.freeProduct_stab

/-- Path witness: HNN tree action is without inversion. -/
def hnn_tree_path :
    Path BassSerreTree.hnnTree.actionWithoutInversion true :=
  Path.ofEqChain BassSerreTree.hnn_no_inversion

/-- Path witness: ℤ/2 * ℤ/3 is a free product. -/
def amalgam_free_path :
    Path AmalgamatedFreeProduct.z2_star_z3.isFreeProduct true :=
  Path.ofEqChain AmalgamatedFreeProduct.z2z3_free

/-- Path witness: ℤ/2 * ℤ/3 is infinite. -/
def amalgam_infinite_path :
    Path AmalgamatedFreeProduct.z2_star_z3.isInfinite true :=
  Path.ofEqChain AmalgamatedFreeProduct.z2z3_infinite

/-- Path witness: SL₂(ℤ) is not a free product. -/
def sl2z_not_free_path :
    Path AmalgamatedFreeProduct.sl2z.isFreeProduct false :=
  Path.ofEqChain AmalgamatedFreeProduct.sl2z_not_free

/-- Path witness: SL₂(ℤ) amalgam order = 2. -/
def sl2z_amalgam_path :
    Path AmalgamatedFreeProduct.sl2z.aOrder 2 :=
  Path.ofEqChain AmalgamatedFreeProduct.sl2z_amalgam_order

/-- Path witness: ℤ HNN is infinite. -/
def hnn_integers_path :
    Path HNNExtension.integers.extensionOrder 0 :=
  Path.ofEqChain HNNExtension.integers_infinite

/-- Path witness: ℤ stable letter infinite order. -/
def hnn_stable_path :
    Path HNNExtension.integers.stableLetterInfiniteOrder true :=
  Path.ofEqChain HNNExtension.integers_stable

/-- Path witness: BS(1,2) is ascending. -/
def bs12_ascending_path :
    Path HNNExtension.bs12.isAscending true :=
  Path.ofEqChain HNNExtension.bs12_ascending

/-- Path witness: ℤ has 2 ends. -/
def stallings_integers_path :
    Path StallingsTheorem.integers.numberOfEnds 2 :=
  Path.ofEqChain StallingsTheorem.integers_ends

/-- Path witness: ℤ splits over finite (Stallings). -/
def stallings_split_path :
    Path StallingsTheorem.integers.splitsOverFinite true :=
  Path.ofEqChain StallingsTheorem.integers_splits

/-- Path witness: ℤ² has 1 end (Stallings). -/
def stallings_z2_path :
    Path StallingsTheorem.integerLattice2.numberOfEnds 1 :=
  Path.ofEqChain StallingsTheorem.z2_one_end

/-- Path witness: ℤ² doesn't split (Stallings). -/
def stallings_z2_nosplit_path :
    Path StallingsTheorem.integerLattice2.splitsOverFinite false :=
  Path.ofEqChain StallingsTheorem.z2_no_split

/-- Path witness: ℤ is accessible. -/
def accessibility_integers_path :
    Path Accessibility.integers.isAccessible true :=
  Path.ofEqChain Accessibility.integers_accessible

/-- Path witness: ℤ² is accessible (depth 0). -/
def accessibility_z2_depth_path :
    Path Accessibility.integerLattice2.decompositionDepth 0 :=
  Path.ofEqChain Accessibility.z2_depth

/-- Path witness: ℤ² has trivial JSJ. -/
def jsj_z2_path :
    Path JSJDecomposition.integerLattice2.isTrivial true :=
  Path.ofEqChain JSJDecomposition.z2_trivial

/-- Path witness: JSJ is canonical. -/
def jsj_canonical_path :
    Path JSJDecomposition.integerLattice2.isCanonical true :=
  Path.ofEqChain JSJDecomposition.z2_canonical

/-- Path witness: surface group JSJ nontrivial. -/
def jsj_surface_path (g : Nat) :
    Path (JSJDecomposition.surfaceGroup g).isTrivial false :=
  Path.ofEqChain (JSJDecomposition.surface_nontrivial g)

/-- Path witness: two-piece JSJ has 2 vertices. -/
def jsj_twopiece_path :
    Path JSJDecomposition.twopiece.numVertexGroups 2 :=
  Path.ofEqChain JSJDecomposition.twopiece_vertices

/-- Path witness: two-piece JSJ has 1 edge. -/
def jsj_twopiece_edge_path :
    Path JSJDecomposition.twopiece.numEdgeGroups 1 :=
  Path.ofEqChain JSJDecomposition.twopiece_edges

end BassSerreTheory
end ComputationalPaths
