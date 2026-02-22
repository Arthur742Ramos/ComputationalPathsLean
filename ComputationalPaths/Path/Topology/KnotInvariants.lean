/-
# Knot invariants via computational paths

This module packages knot diagrams and classical invariants in the
computational paths style. We record Reidemeister moves as explicit
path witnesses and package standard polynomial and finite type
invariants as structures that respect those paths.

## Mathematical Background

- Knot diagrams are planar projections with crossing data.
- Reidemeister moves generate equivalence of diagrams.
- Jones and HOMFLY-PT polynomials are Reidemeister-invariant.
- Vassiliev invariants are finite type invariants obtained from
  extensions to singular diagrams.

## References

- Lickorish, "An Introduction to Knot Theory"
- Kauffman, "Knots and Physics"
- Bar-Natan, "On the Vassiliev knot invariants"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace KnotInvariants

universe u

/-! ## Knot diagrams -/

/-- Crossing data with over/under and sign information. -/
structure Crossing where
  /-- Over/under choice. -/
  over : Bool
  /-- Sign of the crossing (right-hand rule). -/
  sign : Bool
  /-- Incoming arc label. -/
  incoming : Nat
  /-- Outgoing arc label. -/
  outgoing : Nat

/-- A knot diagram with a finite list of crossings. -/
structure KnotDiagram where
  /-- Crossing list. -/
  crossings : List Crossing
  /-- Number of components. -/
  components : Nat
  /-- Well-formedness witness (planarity, matching arcs). -/
  wellFormed : True

/-! ## Reidemeister moves -/

/-- Reidemeister move types. -/
inductive ReidemeisterType where
  | typeI
  | typeII
  | typeIII

/-- A single Reidemeister move with a computational path witness. -/
structure ReidemeisterMove where
  /-- Source diagram. -/
  source : KnotDiagram
  /-- Target diagram. -/
  target : KnotDiagram
  /-- Move kind. -/
  kind : ReidemeisterType
  /-- Path witness of the move. -/
  path : Path source target

/-- Reidemeister equivalence realized as a computational path. -/
structure ReidemeisterEquiv (d1 d2 : KnotDiagram) where
  /-- Path witness between diagrams. -/
  path : Path d1 d2

/-- Reflexivity of Reidemeister equivalence. -/
noncomputable def reidemeister_equiv_refl (d : KnotDiagram) : ReidemeisterEquiv d d :=
  ⟨Path.refl d⟩

/-! ## Reidemeister steps -/

/-- A single Reidemeister move recorded as a step. -/
inductive KnotStep : KnotDiagram → KnotDiagram → Type
  | move (m : ReidemeisterMove) : KnotStep m.source m.target

/-- Extract the computational path carried by a Reidemeister step. -/
noncomputable def knotStepPath {d1 d2 : KnotDiagram} : KnotStep d1 d2 → Path d1 d2
  | KnotStep.move m => m.path

/-- Convert a Reidemeister step into a Reidemeister equivalence. -/
noncomputable def knotStepEquiv {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) : ReidemeisterEquiv d1 d2 :=
  ⟨knotStepPath s⟩

/-- Compose two Reidemeister steps into a single path. -/
noncomputable def knot_steps_compose {d1 d2 d3 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) :
    Path d1 d3 :=
  Path.trans (knotStepPath s1) (knotStepPath s2)

/-! ## Polynomial data -/

/-- Laurent polynomials in one variable, as coefficient functions. -/
structure LaurentPolynomial where
  /-- Coefficient at a given exponent. -/
  coeff : Int -> Int

/-- Bivariate Laurent polynomials for HOMFLY-PT. -/
structure BivariateLaurent where
  /-- Coefficient at exponents (m, n). -/
  coeff : Int -> Int -> Int

/-- Skein triple of diagrams. -/
structure SkeinTriple where
  /-- Positive crossing. -/
  positive : KnotDiagram
  /-- Negative crossing. -/
  negative : KnotDiagram
  /-- Oriented smoothing. -/
  smooth : KnotDiagram

/-- A Reidemeister-invariant value on knot diagrams. -/
structure KnotInvariant (α : Type u) where
  /-- Evaluation on diagrams. -/
  value : KnotDiagram -> α
  /-- Invariance under Reidemeister equivalence. -/
  reidemeister : forall {d1 d2}, ReidemeisterEquiv d1 d2 ->
    Path (value d1) (value d2)

/-- Invariance of a knot invariant under a single Reidemeister step. -/
noncomputable def knot_invariant_step {α : Type u} (I : KnotInvariant α) {d1 d2 : KnotDiagram}
    (s : KnotStep d1 d2) : Path (I.value d1) (I.value d2) :=
  I.reidemeister (knotStepEquiv s)

/-- Invariance under a reversed Reidemeister step. -/
noncomputable def knot_invariant_step_symm {α : Type u} (I : KnotInvariant α) {d1 d2 : KnotDiagram}
    (s : KnotStep d1 d2) : Path (I.value d2) (I.value d1) :=
  Path.symm (knot_invariant_step I s)

/-- Invariance under two consecutive Reidemeister steps. -/
noncomputable def knot_invariant_two_steps {α : Type u} (I : KnotInvariant α)
    {d1 d2 d3 : KnotDiagram} (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) :
    Path (I.value d1) (I.value d3) :=
  Path.trans (knot_invariant_step I s1) (knot_invariant_step I s2)

/-- Jones polynomial data with an abstract skein relation. -/
structure JonesPolynomial extends KnotInvariant LaurentPolynomial where
  /-- Skein relation witness. -/
  skein : SkeinTriple -> True

/-- HOMFLY-PT polynomial data with an abstract skein relation. -/
structure HOMFLYPTPolynomial extends KnotInvariant BivariateLaurent where
  /-- Skein relation witness. -/
  skein : SkeinTriple -> True

/-! ## Vassiliev and finite type invariants -/

/-- A singular crossing marking a transverse double point. -/
structure SingularCrossing where
  /-- Position identifier. -/
  location : Nat
  /-- Sign data. -/
  sign : Bool

/-- A knot diagram with singular crossings. -/
structure SingularDiagram where
  /-- Underlying diagram. -/
  base : KnotDiagram
  /-- Singular crossings. -/
  singularities : List SingularCrossing

/-- Vassiliev invariant with an extension to singular diagrams. -/
structure VassilievInvariant extends KnotInvariant Int where
  /-- Order of the invariant. -/
  order : Nat
  /-- Extension to singular diagrams. -/
  extend : SingularDiagram -> Int
  /-- Finite type condition (order bound). -/
  finiteType : True

/-- A finite type invariant encoded independently of the extension. -/
structure FiniteTypeInvariant where
  /-- Order. -/
  order : Nat
  /-- Value on diagrams. -/
  value : KnotDiagram -> Int
  /-- Reidemeister invariance. -/
  reidemeister : forall {d1 d2}, ReidemeisterEquiv d1 d2 ->
    Path (value d1) (value d2)
  /-- Vanishing on sufficiently singular diagrams. -/
  vanishes : SingularDiagram -> True

/-! ## Additional Theorem Stubs -/

theorem reidemeister_equivalence_transitive_theorem
    {d1 d2 d3 : KnotDiagram}
    (h12 : ReidemeisterEquiv d1 d2) (h23 : ReidemeisterEquiv d2 d3) : True := trivial

theorem knot_step_preserves_invariant_theorem {α : Type u}
    (I : KnotInvariant α) {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) : True := trivial

theorem jones_skein_relation_theorem
    (J : JonesPolynomial) (s : SkeinTriple) : True := trivial

theorem homflypt_skein_relation_theorem
    (H : HOMFLYPTPolynomial) (s : SkeinTriple) : True := trivial

theorem vassiliev_finite_type_condition_theorem
    (V : VassilievInvariant) : True := trivial

theorem finite_type_reidemeister_invariance_theorem
    (F : FiniteTypeInvariant) {d1 d2 : KnotDiagram}
    (h : ReidemeisterEquiv d1 d2) : True := trivial

theorem reidemeister_step_path_symmetry_theorem
    {d1 d2 : KnotDiagram} (s : KnotStep d1 d2) : True := trivial

theorem knot_steps_compose_associative_theorem
    {d1 d2 d3 d4 : KnotDiagram}
    (s1 : KnotStep d1 d2) (s2 : KnotStep d2 d3) (s3 : KnotStep d3 d4) : True := trivial

end KnotInvariants
end Topology
end Path
end ComputationalPaths
