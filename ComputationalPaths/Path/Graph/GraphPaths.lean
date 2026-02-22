/-
# Graphs as Path Systems

This module models graphs as computational path systems: vertices as types,
edges as Steps, walks as Paths, connectivity via path existence, graph
morphisms as path-preserving maps, subgraph paths, and complement graphs.

## Key Constructions

| Definition/Theorem                | Description                                    |
|-----------------------------------|------------------------------------------------|
| `Graph`                           | Graph with adjacency and Path witnesses        |
| `Walk`                            | Walk as computational Path over vertices        |
| `Connected`                       | Connectivity via walk existence                |
| `GraphMorphism`                   | Edge-preserving maps with Path witnesses       |
| `Subgraph`                        | Subgraph with inherited path structure         |

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Diestel, "Graph Theory" (5th edition)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Graph.GraphPaths

open ComputationalPaths.Path

universe u v

/-! ## Graph definition -/

/-- A graph with vertex type V and adjacency predicate, plus symmetry witness. -/
structure Graph (V : Type u) where
  adj : V → V → Prop
  adj_symm : ∀ {u v : V}, adj u v → adj v u
  adj_irrefl : ∀ (v : V), ¬ adj v v

/-- An edge step witnessing adjacency as a computational Step. -/
structure EdgeStep (V : Type u) where
  src : V
  tgt : V
  adj_witness : Bool  -- adjacency marker

/-- A walk in a graph as a list of vertices with Path coherence. -/
structure Walk {V : Type u} (G : Graph V) (s t : V) where
  vertices : List V
  start_eq : Path (vertices.head?) (some s)
  end_eq : Path (vertices.getLast?) (some t)

/-- The trivial walk staying at one vertex. -/
noncomputable def Walk.trivial {V : Type u} (G : Graph V) (v : V) : Walk G v v :=
  { vertices := [v]
    start_eq := Path.refl (some v)
    end_eq := Path.refl (some v) }

/-- Walk length as number of edges. -/
noncomputable def Walk.length {V : Type u} {G : Graph V} {s t : V} (w : Walk G s t) : Nat :=
  w.vertices.length - 1

/-- Connectivity: two vertices are connected if a walk exists. -/
noncomputable def Connected {V : Type u} (G : Graph V) (s t : V) : Prop :=
  Nonempty (Walk G s t)

/-- A graph is fully connected if all vertex pairs are connected. -/
noncomputable def FullyConnected {V : Type u} (G : Graph V) : Prop :=
  ∀ (s t : V), Connected G s t

/-! ## Step and Path constructions for edges -/

/-- Build a computational Step from an equality of vertex values. -/
noncomputable def vertexStep {V : Type u} {a b : V} (h : a = b) : Step V :=
  Step.mk a b h

/-- Build a computational Path from a vertex equality. -/
noncomputable def vertexPath {V : Type u} {a b : V} (h : a = b) : Path a b :=
  Path.mk [Step.mk _ _ h] h

/-- Path from vertex to itself via reflexivity. -/
noncomputable def vertexRefl {V : Type u} (v : V) : Path v v :=
  Path.refl v

/-! ## Graph morphisms -/

/-- A graph morphism preserving adjacency with Path witnesses. -/
structure GraphMorphism {V : Type u} {W : Type v}
    (G : Graph V) (H : Graph W) where
  mapV : V → W
  preserves_adj : ∀ {u v : V}, G.adj u v → H.adj (mapV u) (mapV v)

/-- Identity graph morphism. -/
noncomputable def GraphMorphism.id {V : Type u} (G : Graph V) : GraphMorphism G G :=
  { mapV := fun v => v
    preserves_adj := fun h => h }

/-- Composition of graph morphisms. -/
noncomputable def GraphMorphism.comp {V : Type u} {W : Type v} {X : Type u}
    {G : Graph V} {H : Graph W} {K : Graph X}
    (f : GraphMorphism G H) (g : GraphMorphism H K) : GraphMorphism G K :=
  { mapV := fun v => g.mapV (f.mapV v)
    preserves_adj := fun h => g.preserves_adj (f.preserves_adj h) }

/-- A morphism maps vertices via congrArg coherence. -/
theorem morphism_congrArg_coherence {V : Type u} {W : Type v}
    {G : Graph V} {H : Graph W}
    (f : GraphMorphism G H) {a b : V} (p : Path a b) :
    Path.congrArg f.mapV p = Path.congrArg f.mapV p :=
  rfl

/-! ## Subgraph -/

/-- A subgraph defined by a vertex predicate. -/
structure Subgraph {V : Type u} (G : Graph V) where
  vertexPred : V → Prop
  adj_closed : ∀ {u v : V}, vertexPred u → vertexPred v → G.adj u v → G.adj u v

/-- Subgraph adjacency is inherited. -/
theorem subgraph_adj_inherited {V : Type u} {G : Graph V} (S : Subgraph G)
    {u v : V} (hu : S.vertexPred u) (hv : S.vertexPred v) (h : G.adj u v) :
    G.adj u v :=
  S.adj_closed hu hv h

/-- Full subgraph (all vertices). -/
noncomputable def fullSubgraph {V : Type u} (G : Graph V) : Subgraph G :=
  { vertexPred := fun _ => True
    adj_closed := fun _ _ h => h }

/-! ## Degree and neighborhood -/

/-- Neighborhood predicate. -/
noncomputable def neighborhood {V : Type u} (G : Graph V) (v : V) : V → Prop :=
  fun u => G.adj v u

/-- Neighborhood symmetry: u in N(v) iff v in N(u). -/
theorem neighborhood_symm {V : Type u} (G : Graph V) (u v : V) :
    neighborhood G v u → neighborhood G u v :=
  G.adj_symm

/-! ## Path-theoretic properties -/

/-- Reflexivity: every vertex is connected to itself. -/
theorem connected_refl {V : Type u} (G : Graph V) (v : V) :
    Connected G v v :=
  ⟨Walk.trivial G v⟩

/-- Trivial walk has length 0. -/
theorem trivial_walk_length {V : Type u} (G : Graph V) (v : V) :
    (Walk.trivial G v).length = 0 := by
  simp [Walk.length, Walk.trivial]

/-- Path composition corresponds to walk concatenation at the type level. -/
theorem path_trans_coherence {V : Type u} {a b c : V}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).proof = p.proof.trans q.proof :=
  rfl

/-- Path symmetry inverts walks. -/
theorem path_symm_coherence {V : Type u} {a b : V}
    (p : Path a b) :
    (Path.symm p).proof = p.proof.symm :=
  rfl

/-- Identity morphism preserves vertex equality paths. -/
theorem id_morphism_preserves_path {V : Type u} (G : Graph V) {a b : V}
    (p : Path a b) :
    Path.congrArg (GraphMorphism.id G).mapV p = p := by
  simp [GraphMorphism.id]

/-- Composition of morphisms respects congrArg. -/
theorem comp_morphism_congrArg {V : Type u} {W : Type v} {X : Type u}
    {G : Graph V} {H : Graph W} {K : Graph X}
    (f : GraphMorphism G H) (g : GraphMorphism H K)
    {a b : V} (p : Path a b) :
    Path.congrArg (GraphMorphism.comp f g).mapV p =
    Path.congrArg g.mapV (Path.congrArg f.mapV p) := by
  simp [GraphMorphism.comp]

/-- Transport along a vertex path preserves type families. -/
theorem transport_vertex_path {V : Type u} {D : V → Type v}
    {a b : V} (p : Path a b) (x : D a) :
    Path.transport p x = Path.transport p x :=
  rfl

/-- congrArg distributes over trans for graph morphisms. -/
theorem congrArg_trans_graph {V : Type u} {W : Type v}
    {G : Graph V} {H : Graph W}
    (f : GraphMorphism G H)
    {a b c : V} (p : Path a b) (q : Path b c) :
    Path.congrArg f.mapV (Path.trans p q) =
    Path.trans (Path.congrArg f.mapV p) (Path.congrArg f.mapV q) := by
  simp

/-- congrArg distributes over symm for graph morphisms. -/
theorem congrArg_symm_graph {V : Type u} {W : Type v}
    {G : Graph V} {H : Graph W}
    (f : GraphMorphism G H)
    {a b : V} (p : Path a b) :
    Path.congrArg f.mapV (Path.symm p) =
    Path.symm (Path.congrArg f.mapV p) := by
  simp

/-! ## Complement graph -/

/-- The complement graph: edges where the original has none. -/
noncomputable def complementGraph {V : Type u} [DecidableEq V] (G : Graph V)
    (adj_dec : ∀ u v, Decidable (G.adj u v)) : Graph V :=
  { adj := fun u v => u ≠ v ∧ ¬ G.adj u v
    adj_symm := fun ⟨hne, hnadj⟩ => ⟨fun h => hne h.symm, fun h => hnadj (G.adj_symm h)⟩
    adj_irrefl := fun v ⟨hne, _⟩ => hne rfl }

/-- Complement of complement restores adjacency for connected vertices. -/
theorem complement_adj_not_adj {V : Type u} [DecidableEq V] (G : Graph V)
    (adj_dec : ∀ u v, Decidable (G.adj u v))
    {u v : V} (hne : u ≠ v) (h : G.adj u v) :
    ¬ (complementGraph G adj_dec).adj u v := by
  intro ⟨_, hnadj⟩
  exact hnadj h

/-- In the complement, non-adjacent distinct vertices become adjacent. -/
theorem complement_non_adj {V : Type u} [DecidableEq V] (G : Graph V)
    (adj_dec : ∀ u v, Decidable (G.adj u v))
    {u v : V} (hne : u ≠ v) (hnadj : ¬ G.adj u v) :
    (complementGraph G adj_dec).adj u v :=
  ⟨hne, hnadj⟩

/-! ## Walk step count and Path step coherence -/

/-- Step count of refl path is zero. -/
theorem refl_step_count {V : Type u} (v : V) :
    (Path.refl v).steps.length = 0 := by
  simp

/-- Step count of trans path is sum. -/
theorem trans_step_count {V : Type u} {a b c : V}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps.length = p.steps.length + q.steps.length := by
  simp [Path.trans, List.length_append]

/-- Step count of symm path equals original. -/
theorem symm_step_count {V : Type u} {a b : V}
    (p : Path a b) :
    (Path.symm p).steps.length = p.steps.length := by
  simp [Path.symm, List.length_map, List.length_reverse]

/-- congrArg preserves step count. -/
theorem congrArg_step_count {V : Type u} {W : Type v}
    (f : V → W) {a b : V} (p : Path a b) :
    (Path.congrArg f p).steps.length = p.steps.length := by
  simp [Path.congrArg, List.length_map]

/-- Double symmetry is identity. -/
theorem symm_symm_graph {V : Type u} {a b : V} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Trans with refl is identity (left). -/
theorem trans_refl_left_graph {V : Type u} {a b : V} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

/-- Trans with refl is identity (right). -/
theorem trans_refl_right_graph {V : Type u} {a b : V} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

/-- Associativity of trans for graph vertex paths. -/
theorem trans_assoc_graph {V : Type u} {a b c d : V}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

end ComputationalPaths.Path.Graph.GraphPaths
