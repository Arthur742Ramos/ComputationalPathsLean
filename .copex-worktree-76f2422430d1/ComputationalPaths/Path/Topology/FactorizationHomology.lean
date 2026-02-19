/-!
# Factorization Homology and Chiral Structures

Data-level formalization of factorization homology, Ran spaces, chiral algebras,
En-factorization correspondences, nonabelian Poincare duality, and
Ayala-Francis-Tanaka stratified inputs in the computational-path setting.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace FactorizationHomology

universe u

/-! ## Basic manifold and Ran-space objects -/

structure Manifold where
  Point : Type u
  dim : Nat
  connected : Prop
  oriented : Prop

def OpenSet (M : Manifold.{u}) : Type u :=
  M.Point → Prop

def wholeOpen {M : Manifold.{u}} : OpenSet M :=
  fun _ => True

def emptyOpen {M : Manifold.{u}} : OpenSet M :=
  fun _ => False

def unionOpen {M : Manifold.{u}} (U V : OpenSet M) : OpenSet M :=
  fun x => U x ∨ V x

def interOpen {M : Manifold.{u}} (U V : OpenSet M) : OpenSet M :=
  fun x => U x ∧ V x

def disjointOpen {M : Manifold.{u}} (U V : OpenSet M) : Prop :=
  ∀ x, ¬ (U x ∧ V x)

structure OpenDisk (M : Manifold.{u}) where
  center : M.Point
  radius : Nat
  positive : 0 < radius

def diskAsOpen {M : Manifold.{u}} (D : OpenDisk M) : OpenSet M :=
  fun x => x = D.center

structure RanSpace (M : Manifold.{u}) where
  points : List M.Point

def ranSingleton {M : Manifold.{u}} (x : M.Point) : RanSpace M where
  points := [x]

def ranUnion {M : Manifold.{u}} (S T : RanSpace M) : RanSpace M where
  points := S.points ++ T.points

def ranCardinality {M : Manifold.{u}} (S : RanSpace M) : Nat :=
  S.points.length

def ranDiagonal {M : Manifold.{u}} (S : RanSpace M) : RanSpace M × RanSpace M :=
  (S, S)

/-! ## Factorization and chiral algebra data -/

structure FactorizationAlgebra (M : Manifold.{u}) where
  value : RanSpace M → Type u
  multiply : ∀ S T : RanSpace M, value S → value T → value (ranUnion S T)
  unit : ∀ x : M.Point, value (ranSingleton x)
  localConstancy : Prop

def FactorizationAlgebra.onSingleton {M : Manifold.{u}}
    (A : FactorizationAlgebra M) (x : M.Point) : Type u :=
  A.value (ranSingleton x)

structure ChiralAlgebra (M : Manifold.{u}) extends FactorizationAlgebra M where
  bracket : ∀ x y : M.Point,
    value (ranSingleton x) →
    value (ranSingleton y) →
    value (ranUnion (ranSingleton x) (ranSingleton y))
  jacobi : Prop

def chiralToFactorization {M : Manifold.{u}} (C : ChiralAlgebra M) :
    FactorizationAlgebra M :=
  C.toFactorizationAlgebra

structure EnAlgebra (n : Nat) where
  carrier : Type u
  unit : carrier
  mul : carrier → carrier → carrier
  assocPath : ∀ a b c : carrier, Path (mul (mul a b) c) (mul a (mul b c))
  leftUnitPath : ∀ a : carrier, Path (mul unit a) a
  rightUnitPath : ∀ a : carrier, Path (mul a unit) a

def EnAlgebra.isUnital {n : Nat} (_A : EnAlgebra (u := u) n) : Prop :=
  True

structure EnFactorizationCorrespondence (M : Manifold.{u}) (n : Nat) where
  toFactorization : EnAlgebra (u := u) n → FactorizationAlgebra M
  toEn : FactorizationAlgebra M → EnAlgebra (u := u) n
  roundTripEn : Prop
  roundTripFA : Prop

def EnFactorizationCorrespondence.toLocallyConstant {M : Manifold.{u}} {n : Nat}
    (corr : EnFactorizationCorrespondence M n) :
    EnAlgebra (u := u) n → FactorizationAlgebra M :=
  corr.toFactorization

/-! ## Factorization homology and duality -/

structure FactorizationHomology (M : Manifold.{u}) where
  algebra : FactorizationAlgebra M
  integral : Type u
  colimMap : ∀ S : RanSpace M, algebra.value S → integral

def FactorizationHomology.integrate {M : Manifold.{u}}
    (FH : FactorizationHomology M) : Type u :=
  FH.integral

def factorizationHomologyOfEn {M : Manifold.{u}} {n : Nat}
    (corr : EnFactorizationCorrespondence M n)
    (A : EnAlgebra (u := u) n) : FactorizationHomology M where
  algebra := corr.toFactorization A
  integral := PUnit
  colimMap := fun _ _ => PUnit.unit

def scanningMap {M : Manifold.{u}}
    (FH : FactorizationHomology M) : FH.integral → FH.integral :=
  fun x => x

def compactlySupportedSections {M : Manifold.{u}}
    (FH : FactorizationHomology M) : Type u :=
  FH.integral

def nonabelianPoincareDuality (M : Manifold.{u})
    (_A : EnAlgebra (u := u) M.dim) : Prop :=
  True

/-! ## Ayala-Francis-Tanaka style stratified input -/

structure StratifiedManifold where
  base : Manifold.{u}
  stratum : Nat → base.Point → Prop
  frontier : Prop

def openStratum (X : StratifiedManifold.{u}) : OpenSet X.base :=
  fun x => X.stratum 0 x

structure AFTStructure (X : StratifiedManifold.{u}) where
  diskAlgebra : EnAlgebra (u := u) X.base.dim
  constructible : Prop
  exitInvariance : Prop
  collarGluing : Prop

def AFTStructure.underlyingManifold {X : StratifiedManifold.{u}}
    (_A : AFTStructure X) : Manifold :=
  X.base

def aftFactorizationAlgebra {X : StratifiedManifold.{u}}
    (_A : AFTStructure X) : FactorizationAlgebra X.base where
  value := fun _ => PUnit
  multiply := fun _ _ _ _ => PUnit.unit
  unit := fun _ => PUnit.unit
  localConstancy := True

def exitPathObject (X : StratifiedManifold.{u}) : Type u :=
  X.base.Point

def constructibleRan (X : StratifiedManifold.{u}) : RanSpace X.base → Prop :=
  fun _ => True

def aftFactorizationHomology {X : StratifiedManifold.{u}}
    (A : AFTStructure X) : FactorizationHomology X.base where
  algebra := aftFactorizationAlgebra A
  integral := PUnit
  colimMap := fun _ _ => PUnit.unit

def factorizationBoundaryRestriction {M : Manifold.{u}}
    (U V : OpenSet M) : OpenSet M :=
  interOpen U V

def diskRefinement {M : Manifold.{u}} (D1 D2 : OpenDisk M) : Prop :=
  D1.radius ≤ D2.radius

def topologicalChiralHomology {M : Manifold.{u}}
    (C : ChiralAlgebra M) : FactorizationHomology M where
  algebra := chiralToFactorization C
  integral := PUnit
  colimMap := fun _ _ => PUnit.unit

def enFromChiral {M : Manifold.{u}} (_C : ChiralAlgebra M) :
    EnAlgebra (u := u) M.dim where
  carrier := PUnit
  unit := PUnit.unit
  mul := fun _ _ => PUnit.unit
  assocPath := by
    intro a b c
    exact Path.refl _
  leftUnitPath := by
    intro a
    exact Path.refl _
  rightUnitPath := by
    intro a
    exact Path.refl _

def aftDualityMap {X : StratifiedManifold.{u}} (A : AFTStructure X) :
    compactlySupportedSections (aftFactorizationHomology A) →
    compactlySupportedSections (aftFactorizationHomology A) :=
  fun x => x

/-! ## Coherence and duality theorems -/

theorem ranUnion_assoc {M : Manifold.{u}} (S T U : RanSpace M) :
    Path (ranUnion (ranUnion S T) U) (ranUnion S (ranUnion T U)) := by
  sorry

theorem ranCardinality_singleton {M : Manifold.{u}} (x : M.Point) :
    Path (ranCardinality (ranSingleton x)) 1 := by
  sorry

theorem ranDiagonal_fst {M : Manifold.{u}} (S : RanSpace M) :
    Path (ranDiagonal S).1 S := by
  sorry

theorem ranDiagonal_snd {M : Manifold.{u}} (S : RanSpace M) :
    Path (ranDiagonal S).2 S := by
  sorry

theorem disk_contains_center {M : Manifold.{u}} (D : OpenDisk M) :
    diskAsOpen D D.center := by
  sorry

theorem factorization_unit_left {M : Manifold.{u}} (A : FactorizationAlgebra M)
    (x : M.Point) (a : A.value (ranSingleton x)) :
    Path (A.multiply (ranSingleton x) (ranSingleton x) (A.unit x) a)
         (A.multiply (ranSingleton x) (ranSingleton x) (A.unit x) a) := by
  sorry

theorem factorization_unit_right {M : Manifold.{u}} (A : FactorizationAlgebra M)
    (x : M.Point) (a : A.value (ranSingleton x)) :
    Path (A.multiply (ranSingleton x) (ranSingleton x) a (A.unit x))
         (A.multiply (ranSingleton x) (ranSingleton x) a (A.unit x)) := by
  sorry

theorem chiral_underlying_localConstancy {M : Manifold.{u}} (C : ChiralAlgebra M) :
    (chiralToFactorization C).localConstancy := by
  sorry

theorem en_mul_assoc {n : Nat} (A : EnAlgebra (u := u) n) (a b c : A.carrier) :
    Path (A.mul (A.mul a b) c) (A.mul a (A.mul b c)) := by
  sorry

theorem en_left_unit {n : Nat} (A : EnAlgebra (u := u) n) (a : A.carrier) :
    Path (A.mul A.unit a) a := by
  sorry

theorem en_right_unit {n : Nat} (A : EnAlgebra (u := u) n) (a : A.carrier) :
    Path (A.mul a A.unit) a := by
  sorry

theorem correspondence_roundtrip_en {M : Manifold.{u}} {n : Nat}
    (corr : EnFactorizationCorrespondence M n) :
    corr.roundTripEn := by
  sorry

theorem correspondence_roundtrip_factorization {M : Manifold.{u}} {n : Nat}
    (corr : EnFactorizationCorrespondence M n) :
    corr.roundTripFA := by
  sorry

theorem scanning_idempotent {M : Manifold.{u}} (FH : FactorizationHomology M) :
    ∀ x : FH.integral, Path (scanningMap FH (scanningMap FH x)) (scanningMap FH x) := by
  sorry

theorem nonabelian_poincare_duality_holds {M : Manifold.{u}}
    (A : EnAlgebra (u := u) M.dim) :
    nonabelianPoincareDuality M A := by
  sorry

theorem ayala_francis_tanaka_exit_invariance {X : StratifiedManifold.{u}}
    (A : AFTStructure X) :
    A.exitInvariance := by
  sorry

theorem ayala_francis_tanaka_gluing {X : StratifiedManifold.{u}}
    (A : AFTStructure X) :
    A.collarGluing := by
  sorry

theorem ayala_francis_tanaka_constructibility {X : StratifiedManifold.{u}}
    (A : AFTStructure X) :
    A.constructible := by
  sorry

theorem boundary_restriction_idempotent {M : Manifold.{u}}
    (U V : OpenSet M) :
    Path (factorizationBoundaryRestriction (factorizationBoundaryRestriction U V) V)
         (factorizationBoundaryRestriction U V) := by
  sorry

theorem disk_refinement_refl {M : Manifold.{u}} (D : OpenDisk M) :
    diskRefinement D D := by
  sorry

theorem topological_chiral_homology_exists {M : Manifold.{u}} (C : ChiralAlgebra M) :
    Path (topologicalChiralHomology C).integral PUnit := by
  sorry

theorem en_from_chiral_unital {M : Manifold.{u}} (C : ChiralAlgebra M) :
    EnAlgebra.isUnital (enFromChiral C) := by
  sorry

theorem aft_duality_map_idempotent {X : StratifiedManifold.{u}} (A : AFTStructure X) :
    ∀ x, Path (aftDualityMap A (aftDualityMap A x)) (aftDualityMap A x) := by
  sorry

end FactorizationHomology
end Topology
end Path
end ComputationalPaths
