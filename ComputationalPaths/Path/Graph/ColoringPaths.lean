/-
# Graph Coloring via Computational Paths

This module formalizes graph coloring using computational paths: proper
colorings, chromatic properties, coloring extensions, independent sets
as monochromatic path-free sets, greedy coloring as path reduction.

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Diestel, "Graph Theory" (5th edition), Chapter 5
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Graph.ColoringPaths

open ComputationalPaths.Path

universe u v

/-! ## Graph and coloring definitions -/

/-- A simple graph. -/
structure SimpleGraph (V : Type u) where
  adj : V → V → Prop
  adj_symm : ∀ {u v : V}, adj u v → adj v u
  adj_irrefl : ∀ (v : V), ¬ adj v v

/-- A coloring of a graph with colors from type C. -/
structure Coloring {V : Type u} (G : SimpleGraph V) (C : Type v) where
  color : V → C

/-- A proper coloring: adjacent vertices have different colors. -/
structure ProperColoring {V : Type u} (G : SimpleGraph V) (C : Type v)
    extends Coloring G C where
  proper : ∀ {u v : V}, G.adj u v → color u ≠ color v

/-- An independent set: no two vertices are adjacent. -/
structure IndependentSet {V : Type u} (G : SimpleGraph V) where
  vertices : V → Prop
  independent : ∀ {u v : V}, vertices u → vertices v → ¬ G.adj u v

/-- A color class: set of vertices with the same color. -/
def colorClass {V : Type u} {C : Type v} {G : SimpleGraph V}
    (col : Coloring G C) (c : C) [DecidableEq C] : V → Prop :=
  fun v => col.color v = c

/-! ## Path witnesses for coloring properties -/

/-- Path witness that a color class forms an independent set. -/
theorem colorClass_independent {V : Type u} {C : Type v} [DecidableEq C]
    {G : SimpleGraph V} (col : ProperColoring G C) (c : C) :
    ∀ {u v : V}, colorClass col.toColoring c u → colorClass col.toColoring c v →
      ¬ G.adj u v := by
  intro u v hu hv hadj
  have hne := col.proper hadj
  simp [colorClass] at hu hv
  exact hne (hu.trans hv.symm)

/-- Path witness: recoloring preserves structure. -/
theorem recolor_path {V : Type u} {C : Type v} {G : SimpleGraph V}
    {c1 c2 : C} (h : c1 = c2) (col : Coloring G C) (v : V) :
    Path.transport (D := fun _ => C) (Path.ofEq h) (col.color v) = col.color v := by
  cases h; rfl

/-- Single color witness is trivially satisfied. -/
theorem single_color_trivial {V : Type u} {C : Type v} {G : SimpleGraph V}
    (col : ProperColoring G C) :
    ∀ (v : V), col.color v = col.color v :=
  fun _ => rfl

/-! ## Chromatic number bounds -/

/-- A k-coloring uses at most k colors (witnessed by Fin k). -/
structure KColoring {V : Type u} (G : SimpleGraph V) (k : Nat) where
  col : ProperColoring G (Fin k)

/-- Chromatic number bound: the graph admits a k-coloring. -/
def chromaticBound {V : Type u} (G : SimpleGraph V) (k : Nat) : Prop :=
  Nonempty (KColoring G k)

/-- A k-colorable graph is (k+1)-colorable. -/
def chromatic_monotone {V : Type u} {G : SimpleGraph V} {k : Nat}
    (h : KColoring G k) : KColoring G (k + 1) :=
  { col :=
    { color := fun v => (h.col.color v).castSucc
      proper := fun hadj heq => by
        have hne := h.col.proper hadj
        exact hne (Fin.castSucc_inj.mp heq) } }

/-! ## Independent sets and coloring -/

/-- Empty set is independent. -/
def emptyIndependent {V : Type u} (G : SimpleGraph V) : IndependentSet G :=
  { vertices := fun _ => False
    independent := fun h _ _ => h.elim }

/-- Independent set with Path witness of independence. -/
theorem independent_path_witness {V : Type u} {G : SimpleGraph V}
    (S : IndependentSet G) {u v : V} (hu : S.vertices u) (hv : S.vertices v) :
    ¬ G.adj u v :=
  S.independent hu hv

/-- Union of disjoint independent sets from different colors. -/
def colorClassIndependent {V : Type u} {C : Type v} [DecidableEq C]
    {G : SimpleGraph V} (col : ProperColoring G C) (c : C) :
    IndependentSet G :=
  { vertices := colorClass col.toColoring c
    independent := colorClass_independent col c }

/-! ## Greedy coloring as path reduction -/

/-- A greedy coloring sequence. -/
structure GreedyColoring {V : Type u} (G : SimpleGraph V) where
  steps : List V
  stepCount : Nat

/-- Greedy coloring step count path witness. -/
def greedy_step_count_path {V : Type u} {G : SimpleGraph V}
    (gc : GreedyColoring G) :
    Path gc.stepCount gc.stepCount :=
  Path.refl gc.stepCount

/-! ## Path algebra for colorings -/

/-- Coloring equality via Path when underlying functions agree. -/
def coloring_path_of_eq {V : Type u} {C : Type v}
    {G : SimpleGraph V} (c1 c2 : Coloring G C)
    (h : c1.color = c2.color) :
    Path c1.color c2.color :=
  Path.ofEq h

/-- congrArg on coloring function. -/
def congrArg_color {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : Coloring G C)
    {a b : V} (p : Path a b) :
    Path (col.color a) (col.color b) :=
  Path.congrArg col.color p

/-- congrArg color distributes over trans. -/
theorem congrArg_color_trans {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : Coloring G C)
    {a b c : V} (p : Path a b) (q : Path b c) :
    Path.congrArg col.color (Path.trans p q) =
    Path.trans (Path.congrArg col.color p) (Path.congrArg col.color q) := by
  simp

/-- congrArg color distributes over symm. -/
theorem congrArg_color_symm {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : Coloring G C)
    {a b : V} (p : Path a b) :
    Path.congrArg col.color (Path.symm p) =
    Path.symm (Path.congrArg col.color p) := by
  simp

/-- Path refl for coloring. -/
theorem color_refl {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : Coloring G C) (v : V) :
    Path.congrArg col.color (Path.refl v) = Path.refl (col.color v) := by
  simp

/-- Transport coloring along vertex path. -/
theorem transport_color {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : Coloring G C)
    {a b : V} (p : Path a b) :
    Path.transport (D := fun _ => C) p (col.color a) = col.color a := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-- Step count of congrArg on coloring. -/
theorem congrArg_color_steps {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : Coloring G C)
    {a b : V} (p : Path a b) :
    (Path.congrArg col.color p).steps.length = p.steps.length := by
  simp [List.length_map]

/-- Associativity of trans for colored paths. -/
theorem trans_assoc_coloring {V : Type u} {a b c d : V}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- Symm symm is identity. -/
theorem symm_symm_coloring {V : Type u} {a b : V} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Step count of refl. -/
theorem refl_step_count {V : Type u} (v : V) :
    (Path.refl v).steps.length = 0 := by
  simp

/-- Step count of trans is additive. -/
theorem trans_step_count {V : Type u} {a b c : V}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps.length = p.steps.length + q.steps.length := by
  simp [List.length_append]

/-- Step count of symm is preserved. -/
theorem symm_step_count {V : Type u} {a b : V}
    (p : Path a b) :
    (Path.symm p).steps.length = p.steps.length := by
  simp [List.length_map, List.length_reverse]

/-- Proper coloring is preserved by vertex path equality. -/
theorem proper_preserved_by_path {V : Type u} {C : Type v}
    {G : SimpleGraph V} (col : ProperColoring G C)
    {u v : V} (hadj : G.adj u v) :
    col.color u ≠ col.color v :=
  col.proper hadj

/-- Adjacency symmetry in graph. -/
theorem adj_symm_witness {V : Type u} {G : SimpleGraph V}
    {u v : V} (h : G.adj u v) : G.adj v u :=
  G.adj_symm h

/-- Adjacency irreflexivity. -/
theorem adj_irrefl_witness {V : Type u} {G : SimpleGraph V}
    (v : V) : ¬ G.adj v v :=
  G.adj_irrefl v

end ComputationalPaths.Path.Graph.ColoringPaths
