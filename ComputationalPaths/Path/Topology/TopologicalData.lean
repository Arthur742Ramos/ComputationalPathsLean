/-
# Topological Data Analysis Structures via Computational Paths

This module formalizes TDA structures using the computational paths
framework. We define the Mapper algorithm, Reeb graphs, merge trees,
persistence landscapes, and Wasserstein distance on persistence diagrams,
all with Path-valued structural witnesses.

## Mathematical Background

Topological Data Analysis (TDA) combines topology and statistics:
- **Mapper**: a simplicial complex approximation of a Reeb graph, built
  from a filter function, cover, and clustering
- **Reeb graph**: quotient of a space by connected components of level sets
- **Merge trees**: tracking connected components as a sublevel set grows
- **Persistence landscapes**: functional summaries of persistence diagrams
- **Wasserstein distance**: Lp optimal transport distance between diagrams

## References

- Singh–Mémoli–Carlsson, "Topological Methods for the Analysis of High
  Dimensional Data Sets and 3D Object Recognition" (Mapper)
- Reeb, "Sur les points singuliers d'une forme de Pfaff"
- Bubenik, "Statistical Topological Data Analysis using Persistence Landscapes"
- Mileyko–Mukherjee–Harer, "Probability Measures on the Space of
  Persistence Diagrams"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace TopologicalData

open Algebra HomologicalAlgebra

universe u

/-! ## Filter Functions and Covers -/

/-- A filter function from a point cloud to ℤ (discretized reals). -/
structure FilterFunction where
  /-- Number of data points. -/
  numPoints : Nat
  /-- Filter value for each point index. -/
  value : Nat → Int

/-- An open cover of the filter range. -/
structure Cover where
  /-- Number of cover elements. -/
  numSets : Nat
  /-- Each cover element as an interval [low, high]. -/
  intervals : Nat → (Int × Int)
  /-- A nonempty cover exposes at least one indexed interval. -/
  nonempty_index : numSets > 0 → ∃ i, i < numSets

/-- A clustering of points within a cover element. -/
structure Clustering where
  /-- Number of clusters. -/
  numClusters : Nat
  /-- Cluster assignment for each point. -/
  assignment : Nat → Nat
  /-- Assignments either land in a cluster or the clustering is explicitly empty. -/
  valid : ∀ i, assignment i < numClusters ∨ numClusters = 0

/-! ## Mapper Construction -/

/-- The Mapper graph: a simplicial complex built from filter + cover + clustering. -/
structure MapperGraph where
  /-- Nodes: (cover index, cluster index) pairs. -/
  nodes : List (Nat × Nat)
  /-- Edges: pairs of node indices sharing points. -/
  edges : List (Nat × Nat)
  /-- Node count. -/
  numNodes : Nat
  /-- Node count matches. -/
  node_count : Path numNodes nodes.length

/-- The full Mapper construction pipeline. -/
structure MapperConstruction where
  /-- Input filter function. -/
  filter : FilterFunction
  /-- Cover of the range. -/
  cover : Cover
  /-- Clustering per cover element. -/
  clustering : Nat → Clustering
  /-- Resulting Mapper graph. -/
  result : MapperGraph

/-- Mapper is functorial: refinement of cover yields a simplicial map. -/
structure MapperFunctoriality where
  /-- Coarse Mapper. -/
  coarse : MapperGraph
  /-- Fine Mapper. -/
  fine : MapperGraph
  /-- Simplicial map (node mapping). -/
  simplicialMap : Nat → Nat
  /-- Each coarse edge maps to endpoints inside the fine Mapper graph. -/
  preserves_edges : ∀ e, e ∈ coarse.edges →
    simplicialMap e.1 < fine.numNodes ∧ simplicialMap e.2 < fine.numNodes

/-! ## Reeb Graphs -/

/-- A Reeb graph: vertices are connected components of level sets,
    edges connect components across adjacent levels. -/
structure ReebGraph where
  /-- Vertices (component id, level). -/
  vertices : List (Nat × Int)
  /-- Edges: pairs of vertex indices. -/
  edges : List (Nat × Nat)
  /-- Number of vertices. -/
  numVertices : Nat
  /-- Vertex count. -/
  vertex_count : Path numVertices vertices.length

/-- A Reeb graph morphism. -/
structure ReebMorphism (R₁ R₂ : ReebGraph) where
  /-- Vertex map. -/
  vertexMap : Nat → Nat
  /-- Edge endpoints land in the target vertex range. -/
  edge_preserving : ∀ e, e ∈ R₁.edges →
    vertexMap e.1 < R₂.numVertices ∧ vertexMap e.2 < R₂.numVertices

/-- The interleaving distance between two Reeb graphs. -/
structure ReebInterleavingDist where
  /-- First Reeb graph. -/
  r1 : ReebGraph
  /-- Second Reeb graph. -/
  r2 : ReebGraph
  /-- Interleaving parameter ε. -/
  epsilon : Nat
  /-- Forward map. -/
  forward : ReebMorphism r1 r2
  /-- Backward map. -/
  backward : ReebMorphism r2 r1

/-! ## Merge Trees -/

/-- A merge tree: a rooted tree tracking connected component merges
    as a sublevel set grows. -/
structure MergeTree where
  /-- Nodes: (component id, birth level). -/
  nodes : List (Nat × Int)
  /-- Parent pointers (index → parent index). -/
  parent : Nat → Nat
  /-- Root node index. -/
  root : Nat
  /-- Root is its own parent. -/
  root_fixed : Path (parent root) root

/-- A merge event: two components merge at a given level. -/
structure MergeEvent where
  /-- Component 1 index. -/
  comp1 : Nat
  /-- Component 2 index. -/
  comp2 : Nat
  /-- Merge level. -/
  level : Int
  /-- Surviving component. -/
  survivor : Nat

/-- The interleaving distance between merge trees. -/
structure MergeTreeDist where
  /-- First tree. -/
  t1 : MergeTree
  /-- Second tree. -/
  t2 : MergeTree
  /-- Distance value. -/
  distance : Nat

/-! ## Persistence Landscapes -/

/-- A persistence landscape: a sequence of piecewise-linear functions
    λₖ : ℝ → ℝ derived from a persistence diagram. -/
structure PersistenceLandscape where
  /-- Number of landscape functions. -/
  depth : Nat
  /-- Landscape function values at sample points. -/
  values : Nat → Nat → Int
  /-- Landscapes are ordered: λₖ ≥ λₖ₊₁ pointwise. -/
  ordered : ∀ k t, k + 1 < depth → values k t ≥ values (k + 1) t

/-- The Lp norm of a persistence landscape. -/
structure LandscapeNorm (p : Nat) where
  /-- The landscape. -/
  landscape : PersistenceLandscape
  /-- Norm value (discretized). -/
  norm : Nat

/-- Landscape distance between two persistence diagrams. -/
structure LandscapeDistance (p : Nat) where
  /-- First landscape. -/
  l1 : PersistenceLandscape
  /-- Second landscape. -/
  l2 : PersistenceLandscape
  /-- Distance value. -/
  distance : Nat

/-! ## Wasserstein Distance -/

/-- A transport plan between two persistence diagrams. -/
structure TransportPlan where
  /-- First diagram (birth, death) pairs. -/
  dgm1 : List (Nat × Nat)
  /-- Second diagram (birth, death) pairs. -/
  dgm2 : List (Nat × Nat)
  /-- Transport weights: (i, j, weight). -/
  weights : List (Nat × Nat × Nat)
  /-- Every transported mass references existing source and target points. -/
  marginals : ∀ w, w ∈ weights →
    w.1 < dgm1.length ∧ w.2.1 < dgm2.length

/-- The p-Wasserstein distance between persistence diagrams. -/
structure WassersteinDistance (p : Nat) where
  /-- First diagram. -/
  dgm1 : List (Nat × Nat)
  /-- Second diagram. -/
  dgm2 : List (Nat × Nat)
  /-- Optimal transport plan. -/
  plan : TransportPlan
  /-- Distance value. -/
  distance : Nat

/-- Wasserstein distance satisfies the triangle inequality. -/
structure WassersteinTriangle (p : Nat) where
  /-- Three diagrams. -/
  dgm1 : List (Nat × Nat)
  dgm2 : List (Nat × Nat)
  dgm3 : List (Nat × Nat)
  /-- Pairwise distances. -/
  d12 : WassersteinDistance p
  d23 : WassersteinDistance p
  d13 : WassersteinDistance p
  /-- Triangle inequality. -/
  triangle : d13.distance ≤ d12.distance + d23.distance

/-! ## TDAStep -/

/-- Rewrite steps for TDA computations. -/
inductive TDAStep : Type
  | mapper_refine : TDAStep
  | reeb_quotient : TDAStep
  | merge_event : TDAStep
  | landscape_sum : TDAStep
  | wasserstein_opt : TDAStep

/-- Local certificate carried by each TDA rewrite step. -/
structure TDAStepCertificate where
  /-- Size measure before the local rewrite. -/
  inputComplexity : Nat
  /-- Size measure after the local rewrite. -/
  outputComplexity : Nat
  /-- The rewrite does not increase the local size measure. -/
  output_le_input : outputComplexity ≤ inputComplexity
  /-- RwEq coherence for the step's normalized bookkeeping path. -/
  coherence :
    RwEq (Path.trans (Path.refl outputComplexity) (Path.refl outputComplexity))
      (Path.refl outputComplexity)

/-- TDAStep validity as a concrete local rewrite certificate. -/
noncomputable def tdaStep_valid : TDAStep → TDAStepCertificate
  | TDAStep.mapper_refine =>
      { inputComplexity := 2
        outputComplexity := 2
        output_le_input := by decide
        coherence := rweq_cmpA_refl_left (Path.refl 2) }
  | TDAStep.reeb_quotient =>
      { inputComplexity := 3
        outputComplexity := 2
        output_le_input := by decide
        coherence := rweq_cmpA_refl_left (Path.refl 2) }
  | TDAStep.merge_event =>
      { inputComplexity := 2
        outputComplexity := 1
        output_le_input := by decide
        coherence := rweq_cmpA_refl_left (Path.refl 1) }
  | TDAStep.landscape_sum =>
      { inputComplexity := 2
        outputComplexity := 2
        output_le_input := by decide
        coherence := rweq_cmpA_refl_left (Path.refl 2) }
  | TDAStep.wasserstein_opt =>
      { inputComplexity := 3
        outputComplexity := 1
        output_le_input := by decide
        coherence := rweq_cmpA_refl_left (Path.refl 1) }

/-- Merge tree root is a fixed point (Path witness). -/
noncomputable def mergeTree_root_fixed (t : MergeTree) :
    Path (t.parent t.root) t.root :=
  t.root_fixed

/-- Mapper node count consistency. -/
noncomputable def mapper_node_count (m : MapperGraph) :
    Path m.numNodes m.nodes.length :=
  m.node_count

/-! ## Additional Theorems -/

noncomputable def mapper_node_count_consistency_theorem
    (m : MapperGraph) : Path m.numNodes m.nodes.length :=
  m.node_count

theorem mapper_functoriality_refinement_theorem
    (M : MapperFunctoriality) :
    ∀ e, e ∈ M.coarse.edges →
      M.simplicialMap e.1 < M.fine.numNodes ∧
        M.simplicialMap e.2 < M.fine.numNodes :=
  M.preserves_edges

theorem reeb_interleaving_symmetry_theorem
    (R : ReebInterleavingDist) :
    ∀ e, e ∈ R.r2.edges →
      R.backward.vertexMap e.1 < R.r1.numVertices ∧
        R.backward.vertexMap e.2 < R.r1.numVertices :=
  R.backward.edge_preserving

noncomputable def merge_tree_root_fixed_theorem
    (t : MergeTree) : Path (t.parent t.root) t.root :=
  t.root_fixed

theorem merge_tree_distance_nonnegative_theorem
    (D : MergeTreeDist) : 0 ≤ D.distance :=
  Nat.zero_le D.distance

theorem landscape_order_monotone_theorem
    (L : PersistenceLandscape) :
    ∀ k t, k + 1 < L.depth → L.values k t ≥ L.values (k + 1) t :=
  L.ordered

theorem wasserstein_triangle_theorem
    (p : Nat) (W : WassersteinTriangle p) :
    W.d13.distance ≤ W.d12.distance + W.d23.distance :=
  W.triangle

theorem tda_step_validity_theorem
    (s : TDAStep) : (tdaStep_valid s).outputComplexity ≤ (tdaStep_valid s).inputComplexity :=
  (tdaStep_valid s).output_le_input

end TopologicalData
end Topology
end Path
end ComputationalPaths
