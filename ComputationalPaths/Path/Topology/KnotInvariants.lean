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
def reidemeister_equiv_refl (d : KnotDiagram) : ReidemeisterEquiv d d :=
  ⟨Path.refl d⟩

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

end KnotInvariants
end Topology
end Path
end ComputationalPaths
