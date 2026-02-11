/-
# Zigzag Persistence Interfaces

This module provides lightweight interfaces for zigzag persistence in the
computational paths library. We model zigzag persistence modules, interval
decompositions, levelset zigzags, the diamond principle, and extended
persistence data for closed manifolds together with Poincare duality.

## Key Definitions

- `ZigzagArrow`
- `ZigzagModule`
- `Interval`
- `IntervalDecomposition`
- `DiamondDiagram`
- `DiamondPrinciple`
- `LevelsetZigzag`
- `ClosedManifold`
- `ExtendedPersistence`
- `ExtendedPoincareDuality`

## References

- Carlsson and de Silva, "Zigzag Persistence"
- Cohen-Steiner, Edelsbrunner, Harer, "Extended Persistence"
- Bendich, Wang, Mukherjee, "Towards a Mathematical Theory of Levelset Zigzags"
- Edelsbrunner and Harer, "Computational Topology"
-/

import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ZigzagPersistence

universe u v

/-! ## Zigzag modules -/

/-- Direction of a zigzag arrow. -/
inductive ZigzagArrow where
  /-- Forward arrow from i to i+1. -/
  | forward
  /-- Backward arrow from i+1 to i. -/
  | backward

/-- A finite zigzag persistence module indexed by natural numbers. -/
structure ZigzagModule where
  /-- Number of arrows in the zigzag. -/
  length : Nat
  /-- Direction of the arrow from i to i+1. -/
  arrow : Nat -> ZigzagArrow
  /-- Objects at each index. -/
  obj : Nat -> Type u
  /-- Structure maps along the zigzag. -/
  map : (i : Nat) -> i < length ->
    match arrow i with
    | ZigzagArrow.forward => obj i -> obj (i + 1)
    | ZigzagArrow.backward => obj (i + 1) -> obj i

/-! ## Intervals and interval decomposition -/

/-- An interval [start, stop] in the index line. -/
structure Interval where
  /-- Left endpoint. -/
  start : Nat
  /-- Right endpoint. -/
  stop : Nat
  /-- Start is at most stop. -/
  start_le_stop : start <= stop

namespace Interval

/-- Membership of an index in an interval. -/
def contains (I : Interval) (i : Nat) : Prop :=
  And (I.start <= i) (i <= I.stop)

/-- The start index is contained in the interval. -/
theorem contains_start (I : Interval) : contains I I.start :=
  And.intro (Nat.le_refl _) I.start_le_stop

/-- The stop index is contained in the interval. -/
theorem contains_stop (I : Interval) : contains I I.stop :=
  And.intro I.start_le_stop (Nat.le_refl _)

end Interval

/-- Interval decomposition data for a zigzag module. -/
structure IntervalDecomposition (Z : ZigzagModule) where
  /-- Indexing type for intervals. -/
  intervals : Type u
  /-- Interval attached to each generator. -/
  interval : intervals -> Interval
  /-- Fiber attached to each interval. -/
  fiber : intervals -> Type v
  /-- Support predicate indicating when a fiber contributes. -/
  supports : intervals -> Nat -> Prop
  /-- Supports lie inside their intervals. -/
  supports_within :
    forall (j : intervals) (i : Nat), supports j i -> Interval.contains (interval j) i
  /-- Decomposition of each object into supported interval fibers. -/
  decompose : forall i : Nat,
    SimpleEquiv (Z.obj i)
      (Sigma (fun j : intervals => Subtype (fun _ : fiber j => supports j i)))

namespace IntervalDecomposition

variable {Z : ZigzagModule} (D : IntervalDecomposition Z)

/-- The sigma-type of supported fibers at index i. -/
def supportedFiber (i : Nat) : Type _ :=
  Sigma (fun j : D.intervals => Subtype (fun _ : D.fiber j => D.supports j i))

/-- The decomposition equivalence phrased using supported fibers. -/
def decomposeEquiv (i : Nat) :
    SimpleEquiv (Z.obj i) (D.supportedFiber i) :=
  D.decompose i

end IntervalDecomposition

/-! ## Diamond principle -/

/-- A commutative diamond diagram. -/
structure DiamondDiagram (A B C D : Type u) where
  /-- Left map. -/
  left : A -> B
  /-- Right map. -/
  right : A -> C
  /-- Down-left map. -/
  downLeft : B -> D
  /-- Down-right map. -/
  downRight : C -> D
  /-- Commutativity of the diamond. -/
  commutes : forall a : A, downLeft (left a) = downRight (right a)

/-- Fiber of a map at a point. -/
def Fiber {A B : Type u} (f : A -> B) (b : B) : Type u :=
  { a : A // f a = b }

/-- Diamond principle data: fiber-wise equivalences for a diamond diagram. -/
structure DiamondPrinciple {A B C D : Type u} (diagram : DiamondDiagram A B C D) where
  /-- Equivalence between fibers of the two legs over any d. -/
  fiberEquiv :
    forall d : D, SimpleEquiv (Fiber diagram.downLeft d) (Fiber diagram.downRight d)

/-! ## Levelset zigzag -/

/-- A levelset zigzag on a space X. -/
structure LevelsetZigzag (X : Type u) extends ZigzagModule where
  /-- Levelset at index i. -/
  levelset : Nat -> Type u
  /-- Identification between zigzag objects and levelsets. -/
  levelsetEquiv : forall i : Nat, SimpleEquiv (obj i) (levelset i)
  /-- Inclusion of each levelset into X. -/
  inclusion : forall i : Nat, levelset i -> X

/-! ## Extended persistence and duality -/

/-- Minimal data for a closed manifold. -/
structure ClosedManifold where
  /-- Underlying carrier type. -/
  carrier : Type u
  /-- Manifold dimension. -/
  dimension : Nat

/-- Extended persistence package for a closed manifold. -/
structure ExtendedPersistence (M : ClosedManifold) where
  /-- The levelset zigzag on the manifold. -/
  levelsetZigzag : LevelsetZigzag M.carrier
  /-- Interval decomposition of the resulting zigzag module. -/
  intervalDecomposition :
    IntervalDecomposition levelsetZigzag.toZigzagModule

namespace ExtendedPersistence

variable {M : ClosedManifold}

/-- The underlying zigzag module of an extended persistence package. -/
abbrev baseModule (E : ExtendedPersistence M) : ZigzagModule :=
  E.levelsetZigzag.toZigzagModule

end ExtendedPersistence

/-- Poincare duality data for extended persistence on a closed manifold. -/
structure ExtendedPoincareDuality (M : ClosedManifold) (E : ExtendedPersistence M) where
  /-- Complementary index in the extended persistence module. -/
  complement : Nat -> Nat
  /-- Poincare duality equivalence between complementary indices. -/
  duality : forall k : Nat,
    SimpleEquiv
      ((ExtendedPersistence.baseModule E).obj k)
      ((ExtendedPersistence.baseModule E).obj (complement k))
  /-- Complement is involutive. -/
  complement_involutive : forall k : Nat, complement (complement k) = k

/-! ## Summary

We introduced zigzag persistence modules, interval decomposition data, a diamond
principle interface, levelset zigzags, and extended persistence packages for
closed manifolds together with Poincare duality data.
-/

end ZigzagPersistence
end Algebra
end Path
end ComputationalPaths
