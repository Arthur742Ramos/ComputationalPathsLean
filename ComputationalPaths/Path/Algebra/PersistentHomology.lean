/-
# Persistent Homology and Filtrations

This module provides lightweight data structures for persistent homology in the
computational paths framework. We record filtered simplicial complexes, view
persistence modules as functors from a poset (R, <=) to Vect, and package the
interval-decomposition interface together with birth-death pairs and diagrams.
We also add data for Vietoris-Rips and Cech filtrations.

## Key Definitions
- `Poset`, `posetCategory`
- `SimplicialComplex`, `FilteredComplex`
- `VectObj`, `vectCategory`, `PersistenceModule`
- `Interval`, `IntervalModule`, `IntervalDecomposition`
- `BirthDeathPair`, `PersistenceDiagram`
- `VietorisRipsFiltration`, `CechFiltration`

## References
- Edelsbrunner-Harer, "Computational Topology"
- Ghrist, "Barcodes: The Persistent Topology of Data"
- Zomorodian-Carlsson, "Computing Persistent Homology"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Homotopy.VectorBundle
import ComputationalPaths.Path.Homotopy.LocalizationTheory

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace PersistentHomology

open Homotopy.VectorBundle
open Homotopy.LocalizationTheory

universe u v w

/-! ## Posets and categories -/

/-- A minimal poset structure. -/
structure Poset (I : Type u) where
  /-- Order relation. -/
  le : I -> I -> Prop
  /-- Reflexivity. -/
  refl : forall i, le i i
  /-- Transitivity. -/
  trans : forall {i j k}, le i j -> le j k -> le i k
  /-- Antisymmetry. -/
  antisymm : forall {i j}, le i j -> le j i -> i = j

/-- The category associated to a poset. -/
def posetCategory {I : Type u} (P : Poset I) : Category where
  Obj := I
  Hom := fun i j => P.le i j
  id := fun i => P.refl i
  comp := fun {i j k} hij hjk => P.trans hij hjk
  id_comp := by
    intro X Y f
    apply Subsingleton.elim
  comp_id := by
    intro X Y f
    apply Subsingleton.elim
  assoc := by
    intro W X Y Z f g h
    apply Subsingleton.elim

/-! ## Simplicial complexes and filtrations -/

/-- Subsimplex relation: every vertex of tau appears in sigma. -/
def Subsimplex {V : Type v} (tau sigma : List V) : Prop :=
  forall v, List.Mem v tau -> List.Mem v sigma

/-- A simplicial complex as a downward-closed family of simplices. -/
structure SimplicialComplex (V : Type v) where
  /-- The simplices of the complex. -/
  simplices : List V -> Prop
  /-- Downward closure under faces. -/
  face_closed :
    forall {sigma tau}, Subsimplex tau sigma -> simplices sigma -> simplices tau

/-- A filtered simplicial complex indexed by a poset. -/
structure FilteredComplex (I : Type u) (V : Type v) where
  /-- Index poset. -/
  index : Poset I
  /-- Simplicial complex at each index. -/
  complex : I -> SimplicialComplex V
  /-- Monotonicity of simplices along the filtration. -/
  monotone :
    forall {i j} (h : index.le i j) {sigma},
      (complex i).simplices sigma -> (complex j).simplices sigma

/-! ## Vect category and linear maps -/

/-- A vector space packaged as an object of Vect. -/
structure VectObj (K : Type u) where
  /-- Underlying carrier. -/
  carrier : Type u
  /-- Vector space structure. -/
  vs : VectorSpace K carrier

/-- Linear maps between Vect objects. -/
abbrev VectHom {K : Type u} (V W : VectObj K) : Type u :=
  LinearMap V.vs W.vs

/-- Identity linear map. -/
def vectId {K : Type u} (V : VectObj K) : VectHom V V :=
  { toFun := fun x => x
    map_add := by intro v1 v2; rfl
    map_smul := by intro a v; rfl }

/-- Composition of linear maps. -/
def vectComp {K : Type u} {U V W : VectObj K}
    (f : VectHom U V) (g : VectHom V W) : VectHom U W :=
  { toFun := fun x => g.toFun (f.toFun x)
    map_add := by
      intro v1 v2
      calc
        g.toFun (f.toFun (U.vs.add v1 v2)) =
          g.toFun (V.vs.add (f.toFun v1) (f.toFun v2)) := by
            rw [f.map_add]
        _ = W.vs.add (g.toFun (f.toFun v1)) (g.toFun (f.toFun v2)) := by
            rw [g.map_add]
    map_smul := by
      intro a v
      calc
        g.toFun (f.toFun (U.vs.smul a v)) =
          g.toFun (V.vs.smul a (f.toFun v)) := by
            rw [f.map_smul]
        _ = W.vs.smul a (g.toFun (f.toFun v)) := by
            rw [g.map_smul] }

/-- Extensionality for linear maps. -/
theorem linearMap_ext {K V W : Type u} {vs : VectorSpace K V} {ws : VectorSpace K W}
    {f g : LinearMap vs ws} (h : forall v, f.toFun v = g.toFun v) : f = g := by
  cases f with
  | mk f_toFun f_map_add f_map_smul =>
    cases g with
    | mk g_toFun g_map_add g_map_smul =>
      have h_toFun : f_toFun = g_toFun := funext h
      cases h_toFun
      have h_add : f_map_add = g_map_add := by
        apply Subsingleton.elim
      have h_smul : f_map_smul = g_map_smul := by
        apply Subsingleton.elim
      cases h_add
      cases h_smul
      rfl

/-- The category of vector spaces over K. -/
def vectCategory (K : Type u) : Category where
  Obj := VectObj K
  Hom := fun V W => VectHom V W
  id := fun V => vectId V
  comp := fun f g => vectComp f g
  id_comp := by
    intro X Y f
    apply linearMap_ext
    intro v
    rfl
  comp_id := by
    intro X Y f
    apply linearMap_ext
    intro v
    rfl
  assoc := by
    intro W X Y Z f g h
    apply linearMap_ext
    intro v
    rfl

/-! ## Persistence modules -/

/-- A persistence module as a functor from a poset to Vect. -/
structure PersistenceModule (I : Type u) (K : Type v) where
  /-- The index poset. -/
  index : Poset I
  /-- The functor to Vect. -/
  functor : Functor (posetCategory index) (vectCategory K)

/-- The object at index i in a persistence module. -/
def PersistenceModule.obj {I : Type u} {K : Type v}
    (M : PersistenceModule I K) (i : I) : VectObj K :=
  M.functor.mapObj i

/-- The structure map associated to i <= j. -/
def PersistenceModule.map {I : Type u} {K : Type v}
    (M : PersistenceModule I K) {i j : I} (h : M.index.le i j) :
    VectHom (M.obj i) (M.obj j) :=
  M.functor.mapHom h

/-! ## Interval modules and structure theorem data -/

/-- An interval [b,d) in a poset, recorded by its endpoints. -/
structure Interval {I : Type u} (P : Poset I) where
  /-- Birth index. -/
  birth : I
  /-- Death index. -/
  death : I
  /-- Birth precedes death. -/
  birth_le_death : P.le birth death

/-- Birth-death pairs are the same data as intervals. -/
abbrev BirthDeathPair {I : Type u} (P : Poset I) : Type u :=
  Interval P

/-- An interval module: a persistence module supported on a single interval. -/
structure IntervalModule (I : Type u) (K : Type v) where
  /-- The underlying persistence module. -/
  module : PersistenceModule I K
  /-- The supporting interval. -/
  interval : Interval module.index
  /-- Support condition (placeholder). -/
  support : True

/-- Data of a decomposition into interval modules. -/
structure IntervalDecomposition (I : Type u) (K : Type v) where
  /-- The persistence module being decomposed. -/
  module : PersistenceModule I K
  /-- The list of intervals. -/
  intervals : List (Interval module.index)
  /-- Decomposition witness (placeholder). -/
  is_decomposition : True

/-- A persistence diagram: a finite multiset of birth-death pairs. -/
structure PersistenceDiagram {I : Type u} (P : Poset I) where
  /-- The list of pairs. -/
  pairs : List (BirthDeathPair P)
  /-- Finiteness witness. -/
  finite : True

/-- The diagram extracted from an interval decomposition. -/
def diagramOf {I : Type u} {K : Type v}
    (D : IntervalDecomposition I K) : PersistenceDiagram D.module.index :=
  { pairs := D.intervals, finite := trivial }

/-! ## Persistent homology -/

/-- Persistent homology data in degree n for a filtered complex. -/
structure PersistentHomology (I : Type u) (K : Type v) (X : Type w) where
  /-- Homological degree. -/
  degree : Nat
  /-- The filtered simplicial complex. -/
  filtered : FilteredComplex I X
  /-- The induced persistence module. -/
  module : PersistenceModule I K
  /-- Compatibility witness (placeholder). -/
  realizes : True

/-! ## Vietoris-Rips and Cech filtrations -/

/-- A minimal metric space structure with values in an index poset. -/
structure MetricSpace (I : Type u) (X : Type v) where
  /-- The index poset. -/
  index : Poset I
  /-- Distance function. -/
  dist : X -> X -> I
  /-- Reflexivity (encoded as order reflexivity). -/
  dist_self : forall x, index.le (dist x x) (dist x x)
  /-- Symmetry of the distance. -/
  symm : forall x y, dist x y = dist y x
  /-- Triangle inequality (placeholder). -/
  triangle : forall x y z, True

/-- Vietoris-Rips filtration data for a metric space. -/
structure VietorisRipsFiltration (I : Type u) (X : Type v) where
  /-- The ambient metric space. -/
  metric : MetricSpace I X
  /-- The filtered simplicial complex. -/
  complex : FilteredComplex I X
  /-- Rips condition (placeholder). -/
  rips_condition : True

/-- Cech filtration data for a metric space. -/
structure CechFiltration (I : Type u) (X : Type v) where
  /-- The ambient metric space. -/
  metric : MetricSpace I X
  /-- The filtered simplicial complex. -/
  complex : FilteredComplex I X
  /-- Cech condition (placeholder). -/
  cech_condition : True

/-! ## Summary -/

/-!
We defined lightweight data structures for persistent homology: filtered
simplicial complexes, persistence modules as functors from posets to Vect,
interval decomposition data with persistence diagrams, and Vietoris-Rips/Cech
filtrations over abstract metric spaces.
-/

end PersistentHomology
end Algebra
end Path
end ComputationalPaths
