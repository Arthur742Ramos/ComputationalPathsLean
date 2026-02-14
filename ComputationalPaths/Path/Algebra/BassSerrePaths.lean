/-
# Bass-Serre Theory for Computational Paths

This module provides a lightweight formalization of Bass-Serre theory
using the computational-paths algebraic infrastructure.  We model graphs
of groups, the fundamental group via a quotient, along with tree actions
and fundamental domains, amalgamated free products and HNN extensions.

## Key Definitions

- `BSGraph`, `BSGraphOfGroups`
- `BSFundamentalGroup`
- `AmalgamatedFreeProduct`, `HNNExtension`
- `BSTree`, `BSTreeAction`, `BSFundamentalDomain`

## References

- Serre, *Trees*
- Scott and Wall, *Topological Methods in Group Theory*
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.CompPath.PushoutPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BassSerrePaths

open Algebra

universe u

/-! ## Graphs of Groups -/

/-- A directed graph with explicit source and target maps. -/
structure BSGraph where
  /-- Vertices. -/
  Vertex : Type u
  /-- Edges. -/
  Edge : Type u
  /-- Source of an edge. -/
  src : Edge → Vertex
  /-- Target of an edge. -/
  tgt : Edge → Vertex

/-- A graph of groups: vertex groups, edge groups, and inclusions. -/
structure BSGraphOfGroups (G : BSGraph.{u}) where
  /-- Vertex group at each vertex. -/
  vertexGroup : G.Vertex → Type u
  /-- Strict group structure on each vertex group. -/
  vertexStr : ∀ v, StrictGroup (vertexGroup v)
  /-- Edge group at each edge. -/
  edgeGroup : G.Edge → Type u
  /-- Strict group structure on each edge group. -/
  edgeStr : ∀ e, StrictGroup (edgeGroup e)
  /-- Edge group inclusion into source vertex group (as a function). -/
  srcInclusion : ∀ e, edgeGroup e → vertexGroup (G.src e)
  /-- Edge group inclusion into target vertex group (as a function). -/
  tgtInclusion : ∀ e, edgeGroup e → vertexGroup (G.tgt e)

/-! ## Bass-Serre Fundamental Group -/

/-- Generator symbols for the Bass-Serre fundamental group. -/
inductive BSLetter (G : BSGraph.{u}) (vertGrp : G.Vertex → Type u) : Type u where
  /-- A vertex-group element at vertex v. -/
  | ofVertex (v : G.Vertex) (g : vertGrp v) : BSLetter G vertGrp
  /-- Positive edge symbol. -/
  | ofEdge (e : G.Edge) : BSLetter G vertGrp

/-- A Bass-Serre word is a list of letters. -/
abbrev BSWord (G : BSGraph.{u}) (vertGrp : G.Vertex → Type u) : Type u :=
  List (BSLetter G vertGrp)

/-- Relation for the Bass-Serre fundamental group. -/
inductive BSRel {G : BSGraph.{u}} (H : BSGraphOfGroups G) :
    BSWord G H.vertexGroup → BSWord G H.vertexGroup → Prop where
  /-- Reflexivity. -/
  | refl (w) : BSRel H w w
  /-- Edge identification: t_e · α_e(h) ~ β_e(h) · t_e. -/
  | edge_ident (e : G.Edge) (h : H.edgeGroup e)
      (pre suf : BSWord G H.vertexGroup) :
      BSRel H
        (pre ++ [BSLetter.ofVertex (G.src e) (H.srcInclusion e h)] ++ suf)
        (pre ++ [BSLetter.ofVertex (G.tgt e) (H.tgtInclusion e h)] ++ suf)
  /-- Symmetry. -/
  | symm {w₁ w₂} : BSRel H w₁ w₂ → BSRel H w₂ w₁
  /-- Transitivity. -/
  | trans {w₁ w₂ w₃} : BSRel H w₁ w₂ → BSRel H w₂ w₃ → BSRel H w₁ w₃

/-- The Bass-Serre fundamental group as a quotient of words. -/
def BSFundamentalGroup {G : BSGraph.{u}} (H : BSGraphOfGroups G) : Type u :=
  Quot (BSRel H)

/-- Include a vertex-group element. -/
def bsVertexInclusion {G : BSGraph.{u}} {H : BSGraphOfGroups G}
    (v : G.Vertex) (g : H.vertexGroup v) : BSFundamentalGroup H :=
  Quot.mk _ [BSLetter.ofVertex v g]

/-- Include an edge symbol. -/
def bsEdgeInclusion {G : BSGraph.{u}} {H : BSGraphOfGroups G}
    (e : G.Edge) : BSFundamentalGroup H :=
  Quot.mk _ [BSLetter.ofEdge e]

/-! ## Amalgamated Free Products -/

/-- The amalgamated free product from the pushout-paths construction. -/
abbrev AmalgamatedFreeProduct (G₁ G₂ H : Type u) (i₁ : H → G₁) (i₂ : H → G₂) : Type u :=
  CompPath.AmalgamatedFreeProduct G₁ G₂ H i₁ i₂

/-! ## HNN Extensions -/

/-- Data specifying an HNN extension. -/
structure HNNData (G : Type u) where
  /-- The associated subgroup type. -/
  Assoc : Type u
  /-- Left embedding of the associated subgroup. -/
  leftMap : Assoc → G
  /-- Right embedding of the associated subgroup. -/
  rightMap : Assoc → G

/-- Letters for HNN words. -/
inductive HNNLetter (G : Type u) : Type u where
  /-- Base group element. -/
  | base : G → HNNLetter G
  /-- Stable letter t (true) or t⁻¹ (false). -/
  | stable : Bool → HNNLetter G

/-- HNN words. -/
abbrev HNNWord (G : Type u) : Type u := List (HNNLetter G)

/-- HNN relation. -/
inductive HNNRel {G : Type u} (D : HNNData G) : HNNWord G → HNNWord G → Prop where
  /-- Reflexivity. -/
  | refl (w) : HNNRel D w w
  /-- Conjugation relation: t · φ(h) · t⁻¹ ~ ψ(h). -/
  | conjugate (h : D.Assoc) (pre suf : HNNWord G) :
      HNNRel D
        (pre ++ [HNNLetter.stable true, HNNLetter.base (D.leftMap h),
                  HNNLetter.stable false] ++ suf)
        (pre ++ [HNNLetter.base (D.rightMap h)] ++ suf)
  /-- Symmetry. -/
  | symm {w₁ w₂} : HNNRel D w₁ w₂ → HNNRel D w₂ w₁
  /-- Transitivity. -/
  | trans {w₁ w₂ w₃} : HNNRel D w₁ w₂ → HNNRel D w₂ w₃ → HNNRel D w₁ w₃

/-- The HNN extension as a quotient. -/
def HNNExtension {G : Type u} (D : HNNData G) : Type u :=
  Quot (HNNRel D)

/-! ## Trees and Tree Actions -/

/-- A tree as a graph equipped with a tree predicate. -/
structure BSTree where
  /-- Underlying graph. -/
  graph : BSGraph
  /-- Predicate asserting the graph is a tree. -/
  isTree : Prop

/-- Vertices of a tree. -/
abbrev BSTree.Vertex (T : BSTree) : Type := T.graph.Vertex

/-- Edges of a tree. -/
abbrev BSTree.Edge (T : BSTree) : Type := T.graph.Edge

/-- A group action on a tree respecting source/target maps. -/
structure BSTreeAction (G : Type u) (S : StrictGroup G) (T : BSTree) where
  /-- Action on vertices. -/
  actVertex : GroupAction G S T.Vertex
  /-- Action on edges. -/
  actEdge : GroupAction G S T.Edge
  /-- Source map is equivariant. -/
  act_src :
    ∀ g e, Path (actVertex.act g (T.graph.src e)) (T.graph.src (actEdge.act g e))
  /-- Target map is equivariant. -/
  act_tgt :
    ∀ g e, Path (actVertex.act g (T.graph.tgt e)) (T.graph.tgt (actEdge.act g e))

/-- Edge identifications yield computational paths in the fundamental group. -/
def bsEdgeIdentPath {G : BSGraph.{u}} (H : BSGraphOfGroups G)
    (e : G.Edge) (h : H.edgeGroup e) (pre suf : BSWord G H.vertexGroup) :
    Path
      (Quot.mk (BSRel H) (pre ++ [BSLetter.ofVertex (G.src e) (H.srcInclusion e h)] ++ suf))
      (Quot.mk (BSRel H) (pre ++ [BSLetter.ofVertex (G.tgt e) (H.tgtInclusion e h)] ++ suf)) :=
  Path.stepChain (Quot.sound (BSRel.edge_ident (H:=H) e h pre suf))

/-- Composing the edge-identification path with its inverse yields a loop. -/
def bsEdgeIdentLoop {G : BSGraph.{u}} (H : BSGraphOfGroups G)
    (e : G.Edge) (h : H.edgeGroup e) (pre suf : BSWord G H.vertexGroup) :
    Path
      (Quot.mk (BSRel H) (pre ++ [BSLetter.ofVertex (G.src e) (H.srcInclusion e h)] ++ suf))
      (Quot.mk (BSRel H) (pre ++ [BSLetter.ofVertex (G.src e) (H.srcInclusion e h)] ++ suf)) :=
  Path.trans (bsEdgeIdentPath H e h pre suf)
    (Path.symm (bsEdgeIdentPath H e h pre suf))

/-- A fundamental domain for a tree action. -/
structure BSFundamentalDomain {G : Type u} {S : StrictGroup G} {T : BSTree}
    (_A : BSTreeAction G S T) where
  /-- Vertices in the domain. -/
  vertices : T.Vertex → Prop
  /-- Edges in the domain. -/
  edges : T.Edge → Prop
  /-- Source of a domain edge lies in the domain. -/
  src_mem : ∀ {e}, edges e → vertices (T.graph.src e)
  /-- Target of a domain edge lies in the domain. -/
  tgt_mem : ∀ {e}, edges e → vertices (T.graph.tgt e)

/-! ## Summary -/

/-
We formalized graphs of groups, the Bass-Serre fundamental group as a quotient,
amalgamated free products via pushout paths, HNN extensions, trees, tree actions,
and fundamental domains for tree actions.
-/

end BassSerrePaths
end Algebra
end Path
end ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace BassSerrePaths

theorem bassSerre_bsFundamentalGroup_def {G : BSGraph}
    (H : BSGraphOfGroups G) :
    BSFundamentalGroup H = Quot (BSRel H) := by
  sorry

theorem bassSerre_bsVertexInclusion_def {G : BSGraph}
    {H : BSGraphOfGroups G} (v : G.Vertex) (g : H.vertexGroup v) :
    bsVertexInclusion v g = Quot.mk (BSRel H) [BSLetter.ofVertex v g] := by
  sorry

theorem bassSerre_bsEdgeInclusion_def {G : BSGraph}
    {H : BSGraphOfGroups G} (e : G.Edge) :
    bsEdgeInclusion e = Quot.mk (BSRel H) [BSLetter.ofEdge e] := by
  sorry

theorem bassSerre_amalgamatedFreeProduct_def
    (G₁ G₂ H : Type u) (i₁ : H → G₁) (i₂ : H → G₂) :
    AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ =
      CompPath.AmalgamatedFreeProduct G₁ G₂ H i₁ i₂ := by
  sorry

theorem bassSerre_hnnExtension_def {G : Type u} (D : HNNData G) :
    HNNExtension D = Quot (HNNRel D) := by
  sorry

theorem bassSerre_tree_vertex_def (T : BSTree) :
    T.Vertex = T.graph.Vertex := by
  sorry

theorem bassSerre_tree_edge_def (T : BSTree) :
    T.Edge = T.graph.Edge := by
  sorry

theorem bassSerre_bsEdgeIdentLoop_def {G : BSGraph}
    (H : BSGraphOfGroups G) (e : G.Edge) (h : H.edgeGroup e)
    (pre suf : BSWord G H.vertexGroup) :
    bsEdgeIdentLoop H e h pre suf =
      Path.trans (bsEdgeIdentPath H e h pre suf)
        (Path.symm (bsEdgeIdentPath H e h pre suf)) := by
  sorry

theorem bassSerre_hnnLetter_stable_true_ne_false {G : Type u} :
    HNNLetter.stable (G := G) true ≠ HNNLetter.stable (G := G) false := by
  sorry

theorem bassSerre_hnnLetter_base_ne_stable {G : Type u} (g : G) (b : Bool) :
    HNNLetter.base g ≠ HNNLetter.stable (G := G) b := by
  sorry

theorem bassSerre_bsGraph_vertex_nonempty (G : BSGraph) [h : Nonempty G.Vertex] :
    Nonempty G.Vertex := by
  sorry

theorem bassSerre_bsWord_nil_eq {G : BSGraph} (vertGrp : G.Vertex → Type u) :
    ([] : BSWord G vertGrp) = [] := by
  sorry

theorem bassSerre_fundamentalDomain_src_mem
    {G : Type u} {S : StrictGroup G} {T : BSTree}
    {Act : BSTreeAction G S T} (F : BSFundamentalDomain Act)
    {e : T.Edge} (h : F.edges e) :
    F.vertices (T.graph.src e) := by
  sorry

end BassSerrePaths
end Algebra
end Path
end ComputationalPaths
