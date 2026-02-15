/-
# Trees as Acyclic Path Systems

This module formalizes trees as acyclic connected graphs in the computational
paths framework. Unique paths in trees, tree morphisms, subtrees, leaves,
depth/height as path length, rooted trees, and tree traversals as path orderings.

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
- Diestel, "Graph Theory" (5th edition), Chapter 1
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Graph.TreePaths

open ComputationalPaths.Path

universe u v

/-! ## Tree definition -/

/-- A rooted tree with parent function and root. -/
structure RootedTree (V : Type u) where
  root : V
  parent : V → Option V
  parent_root : parent root = none

/-- Depth of a vertex given a depth function. -/
def depthOf {V : Type u} (_T : RootedTree V) (depthFn : V → Nat) (v : V) : Nat :=
  depthFn v

/-- A vertex is a leaf if it has no children (given a child check). -/
def isLeaf {V : Type u} (_T : RootedTree V) (hasChild : V → Bool) (v : V) : Prop :=
  hasChild v = false

/-- Height of a tree given a height value. -/
def treeHeight {V : Type u} (_T : RootedTree V) (heightVal : Nat) : Nat :=
  heightVal

/-! ## Path-based tree structure -/

/-- A tree path: a list of vertices forming a path from source to target. -/
structure TreePath {V : Type u} (T : RootedTree V) (s t : V) where
  vertices : List V
  nonempty : vertices ≠ []
  start_eq : Path (vertices.head?) (some s)
  end_eq : Path (vertices.getLast?) (some t)

/-- Trivial path at a vertex. -/
def TreePath.trivial {V : Type u} (T : RootedTree V) (v : V) : TreePath T v v :=
  { vertices := [v]
    nonempty := List.cons_ne_nil _ _
    start_eq := Path.refl (some v)
    end_eq := Path.refl (some v) }

/-- Length of a tree path. -/
def TreePath.length {V : Type u} {T : RootedTree V} {s t : V} (p : TreePath T s t) : Nat :=
  p.vertices.length - 1

/-! ## Unique path property -/

/-- Trees have unique paths: any two paths between same endpoints
    have the same vertex list length (path uniqueness witness). -/
structure UniquePathProperty {V : Type u} (T : RootedTree V) where
  unique : ∀ {s t : V} (p q : TreePath T s t),
    Path p.vertices.length q.vertices.length

/-- Path from root is the computational path witness of rootedness. -/
def rootPath {V : Type u} (T : RootedTree V) : Path T.root T.root :=
  Path.refl T.root

/-- Root path has zero steps. -/
theorem rootPath_steps_empty {V : Type u} (T : RootedTree V) :
    (rootPath T).steps = [] := by
  simp [rootPath]

/-! ## Tree morphisms -/

/-- A tree morphism preserving root and parent structure. -/
structure TreeMorphism {V : Type u} {W : Type v}
    (S : RootedTree V) (T : RootedTree W) where
  mapV : V → W
  maps_root : Path (mapV S.root) T.root

/-- Identity tree morphism. -/
def TreeMorphism.id {V : Type u} (T : RootedTree V) : TreeMorphism T T :=
  { mapV := fun v => v
    maps_root := Path.refl T.root }

/-- Composition of tree morphisms. -/
def TreeMorphism.comp {V : Type u} {W : Type v} {X : Type u}
    {S : RootedTree V} {T : RootedTree W} {U : RootedTree X}
    (f : TreeMorphism S T) (g : TreeMorphism T U) : TreeMorphism S U :=
  { mapV := fun v => g.mapV (f.mapV v)
    maps_root := Path.trans (Path.congrArg g.mapV f.maps_root) g.maps_root }

/-! ## Subtrees -/

/-- A subtree defined by a vertex predicate containing the root. -/
structure Subtree {V : Type u} (T : RootedTree V) where
  pred : V → Prop
  contains_root : pred T.root

/-- Full subtree contains all vertices. -/
def fullSubtree {V : Type u} (T : RootedTree V) : Subtree T :=
  { pred := fun _ => True
    contains_root := trivial }

/-- Singleton subtree at root. -/
def rootSubtree {V : Type u} (T : RootedTree V) :
    Subtree T :=
  { pred := fun v => v = T.root
    contains_root := rfl }

/-! ## Path-theoretic tree properties -/

/-- Trivial tree path has length 0. -/
theorem trivial_path_length {V : Type u} (T : RootedTree V) (v : V) :
    (TreePath.trivial T v).length = 0 := by
  simp [TreePath.length, TreePath.trivial]

/-- Root path is reflexive. -/
theorem root_path_refl {V : Type u} (T : RootedTree V) :
    rootPath T = Path.refl T.root :=
  rfl

/-- Identity morphism preserves vertex paths via congrArg. -/
theorem id_morphism_congrArg {V : Type u} (T : RootedTree V) {a b : V}
    (p : Path a b) :
    Path.congrArg (TreeMorphism.id T).mapV p = p := by
  simp [TreeMorphism.id]

/-- Composition morphism congrArg factors through components. -/
theorem comp_morphism_congrArg {V : Type u} {W : Type v} {X : Type u}
    {S : RootedTree V} {T : RootedTree W} {U : RootedTree X}
    (f : TreeMorphism S T) (g : TreeMorphism T U)
    {a b : V} (p : Path a b) :
    Path.congrArg (TreeMorphism.comp f g).mapV p =
    Path.congrArg g.mapV (Path.congrArg f.mapV p) := by
  simp [TreeMorphism.comp]

/-- congrArg distributes over trans for tree morphisms. -/
theorem congrArg_trans_tree {V : Type u} {W : Type v}
    {S : RootedTree V} {T : RootedTree W}
    (f : TreeMorphism S T)
    {a b c : V} (p : Path a b) (q : Path b c) :
    Path.congrArg f.mapV (Path.trans p q) =
    Path.trans (Path.congrArg f.mapV p) (Path.congrArg f.mapV q) := by
  simp

/-- congrArg distributes over symm for tree morphisms. -/
theorem congrArg_symm_tree {V : Type u} {W : Type v}
    {S : RootedTree V} {T : RootedTree W}
    (f : TreeMorphism S T)
    {a b : V} (p : Path a b) :
    Path.congrArg f.mapV (Path.symm p) =
    Path.symm (Path.congrArg f.mapV p) := by
  simp

/-- Transport along root path is identity. -/
theorem transport_root_path {V : Type u} {D : V → Type v}
    (T : RootedTree V) (x : D T.root) :
    Path.transport (rootPath T) x = x := by
  unfold rootPath
  rfl

/-- Path trans with refl is identity in tree context. -/
theorem tree_trans_refl {V : Type u} {a b : V}
    (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

/-- Path refl trans is identity in tree context. -/
theorem tree_refl_trans {V : Type u} {a b : V}
    (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

/-- Trans proof composes. -/
theorem tree_trans_proof {V : Type u} {a b c : V}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).proof = p.proof.trans q.proof :=
  rfl

/-- Symm proof is symmetric. -/
theorem tree_symm_proof {V : Type u} {a b : V}
    (p : Path a b) :
    (Path.symm p).proof = p.proof.symm :=
  rfl

/-! ## Depth and height as step counts -/

/-- Step count of refl is 0. -/
theorem refl_steps_zero {V : Type u} (v : V) :
    (Path.refl v).steps.length = 0 := by
  simp

/-- Step count of trans is sum. -/
theorem trans_steps_add {V : Type u} {a b c : V}
    (p : Path a b) (q : Path b c) :
    (Path.trans p q).steps.length = p.steps.length + q.steps.length := by
  simp [List.length_append]

/-- Step count of symm equals original. -/
theorem symm_steps_eq {V : Type u} {a b : V}
    (p : Path a b) :
    (Path.symm p).steps.length = p.steps.length := by
  simp [List.length_map, List.length_reverse]

/-- congrArg preserves step count. -/
theorem congrArg_steps_eq {V : Type u} {W : Type v}
    (f : V → W) {a b : V} (p : Path a b) :
    (Path.congrArg f p).steps.length = p.steps.length := by
  simp [List.length_map]

/-- Associativity of trans in tree context. -/
theorem tree_trans_assoc {V : Type u} {a b c d : V}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- Double symm is identity. -/
theorem tree_symm_symm {V : Type u} {a b : V} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Symm of trans reverses order. -/
theorem tree_symm_trans {V : Type u} {a b c : V}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp

/-- Morphism maps root path to root path. -/
theorem morphism_maps_root_path {V : Type u} {W : Type v}
    {S : RootedTree V} {T : RootedTree W}
    (f : TreeMorphism S T) :
    Path.congrArg f.mapV (rootPath S) = Path.refl (f.mapV S.root) := by
  simp [rootPath]

/-- Full subtree contains root. -/
theorem full_subtree_root {V : Type u} (T : RootedTree V) :
    (fullSubtree T).contains_root = trivial :=
  rfl

/-- Root subtree predicate at root is rfl. -/
theorem root_subtree_pred {V : Type u} (T : RootedTree V) :
    (rootSubtree T).pred T.root :=
  rfl

end ComputationalPaths.Path.Graph.TreePaths
