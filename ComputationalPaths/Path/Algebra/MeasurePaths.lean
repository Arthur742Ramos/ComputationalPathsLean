/-
# Measure Theory via Computational Paths

This module models measure-theoretic concepts using computational paths:
sigma algebras, measurable functions, measure additivity as path sums,
monotonicity, continuity from below/above, null sets, and outer measures.

## References

- Halmos, "Measure Theory"
- Billingsley, "Probability and Measure"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace MeasurePaths

universe u v

open ComputationalPaths.Path

/-! ## Sigma Algebras as Path Systems -/

/-- A sigma algebra with measurable sets and closure paths. -/
structure SigmaAlgebra (X : Type u) where
  measurable : (X → Prop) → Prop
  emptyMeas : measurable (fun _ => False)
  fullMeas : measurable (fun _ => True)

/-- A measurable function between sigma algebras. -/
structure MeasurableFunc (X Y : Type u) where
  func : X → Y
  sigmaX : SigmaAlgebra X
  sigmaY : SigmaAlgebra Y

/-- Identity is measurable. -/
def measurableId (X : Type u) (σ : SigmaAlgebra X) : MeasurableFunc X X where
  func := id
  sigmaX := σ
  sigmaY := σ

/-- Composition of measurable functions. -/
def measurableComp {X Y Z : Type u}
    (g : MeasurableFunc Y Z) (f : MeasurableFunc X Y) :
    MeasurableFunc X Z where
  func := g.func ∘ f.func
  sigmaX := f.sigmaX
  sigmaY := g.sigmaY

/-- Composition is associative at the function level. -/
theorem measurable_comp_assoc {X Y Z W : Type u}
    (h : MeasurableFunc Z W) (g : MeasurableFunc Y Z) (f : MeasurableFunc X Y) :
    (measurableComp h (measurableComp g f)).func =
    (measurableComp (measurableComp h g) f).func := rfl

/-- Identity composed is identity. -/
theorem measurable_id_comp {X Y : Type u} (f : MeasurableFunc X Y) :
    (measurableComp (measurableId Y f.sigmaY) f).func = f.func := rfl

/-! ## Measure with Path Witnesses -/

/-- A measure on a sigma algebra with path witnesses. -/
structure Measure (X : Type u) where
  sigma : SigmaAlgebra X
  meas : Nat → Nat  -- simplified: index → measure value
  emptyVal : Nat
  emptyPath : Path (meas 0) emptyVal

/-- Two measures are equivalent when they agree everywhere. -/
def measureEquiv {X : Type u} (m1 m2 : Measure X) : Prop :=
  ∀ n : Nat, m1.meas n = m2.meas n

/-- Measure equivalence is reflexive. -/
theorem measureEquiv_refl {X : Type u} (m : Measure X) :
    measureEquiv m m :=
  fun _ => rfl

/-- Measure equivalence is symmetric. -/
theorem measureEquiv_symm {X : Type u}
    {m1 m2 : Measure X} (h : measureEquiv m1 m2) :
    measureEquiv m2 m1 :=
  fun n => (h n).symm

/-- Measure equivalence is transitive. -/
theorem measureEquiv_trans {X : Type u}
    {m1 m2 m3 : Measure X}
    (h1 : measureEquiv m1 m2) (h2 : measureEquiv m2 m3) :
    measureEquiv m1 m3 :=
  fun n => (h1 n).trans (h2 n)

/-! ## Measure Additivity as Path Sums -/

/-- Additivity data: μ(A ∪ B) = μ(A) + μ(B) for disjoint sets. -/
structure AdditivityData where
  measA : Nat
  measB : Nat
  measUnion : Nat
  sumVal : Nat
  sumPath : Path sumVal (measA + measB)
  additivePath : Path measUnion sumVal

/-- Composed additivity path: union measure = sum of individual measures. -/
def additivity_path (d : AdditivityData) : Path d.measUnion (d.measA + d.measB) :=
  Path.trans d.additivePath d.sumPath

/-- Additivity path trans refl. -/
theorem additivity_trans_refl (d : AdditivityData) :
    Path.trans d.additivePath (Path.refl d.sumVal) = d.additivePath := by
  simp

/-- Additivity symmetry distributes. -/
theorem additivity_symm_trans (d : AdditivityData) :
    Path.symm (additivity_path d) =
    Path.trans (Path.symm d.sumPath) (Path.symm d.additivePath) := by
  simp [additivity_path]

/-- RwEq: additivity path trans refl. -/
theorem additivity_rweq_trans_refl (d : AdditivityData) :
    RwEq
      (Path.trans d.additivePath (Path.refl d.sumVal))
      d.additivePath :=
  rweq_of_step (Step.trans_refl_right d.additivePath)

/-- RwEq: additivity inv cancel right. -/
theorem additivity_rweq_inv_right (d : AdditivityData) :
    RwEq
      (Path.trans d.additivePath (Path.symm d.additivePath))
      (Path.refl d.measUnion) :=
  rweq_cmpA_inv_right d.additivePath

/-- RwEq: additivity inv cancel left. -/
theorem additivity_rweq_inv_left (d : AdditivityData) :
    RwEq
      (Path.trans (Path.symm d.additivePath) d.additivePath)
      (Path.refl d.sumVal) :=
  rweq_cmpA_inv_left d.additivePath

/-- RwEq: additivity symm_symm. -/
theorem additivity_rweq_symm_symm (d : AdditivityData) :
    RwEq
      (Path.symm (Path.symm d.additivePath))
      d.additivePath :=
  rweq_of_step (Step.symm_symm d.additivePath)

/-! ## Monotonicity -/

/-- Monotonicity data: A ⊆ B implies μ(A) ≤ μ(B). -/
structure MonoData where
  measA : Nat
  measB : Nat
  diff : Nat
  monoPath : Path (measA + diff) measB

/-- Monotonicity path trans refl. -/
theorem mono_trans_refl (d : MonoData) :
    Path.trans d.monoPath (Path.refl d.measB) = d.monoPath := by
  simp

/-- RwEq: monotonicity trans refl. -/
theorem mono_rweq_trans_refl (d : MonoData) :
    RwEq
      (Path.trans d.monoPath (Path.refl d.measB))
      d.monoPath :=
  rweq_of_step (Step.trans_refl_right d.monoPath)

/-- RwEq: monotonicity inv cancel. -/
theorem mono_rweq_inv_right (d : MonoData) :
    RwEq
      (Path.trans d.monoPath (Path.symm d.monoPath))
      (Path.refl (d.measA + d.diff)) :=
  rweq_cmpA_inv_right d.monoPath

/-! ## Continuity from Below -/

/-- Continuity from below: μ(⋃ Aₙ) = lim μ(Aₙ). -/
structure ContFromBelow where
  measures : List Nat
  limitVal : Nat
  unionMeas : Nat
  limitPath : Path unionMeas limitVal

/-- Continuity from below trans refl. -/
theorem cont_below_trans_refl (d : ContFromBelow) :
    Path.trans d.limitPath (Path.refl d.limitVal) = d.limitPath := by
  simp

/-- RwEq: continuity from below inv cancel. -/
theorem cont_below_rweq_inv_right (d : ContFromBelow) :
    RwEq
      (Path.trans d.limitPath (Path.symm d.limitPath))
      (Path.refl d.unionMeas) :=
  rweq_cmpA_inv_right d.limitPath

/-- RwEq: continuity from below trans refl. -/
theorem cont_below_rweq_trans_refl (d : ContFromBelow) :
    RwEq
      (Path.trans d.limitPath (Path.refl d.limitVal))
      d.limitPath :=
  rweq_of_step (Step.trans_refl_right d.limitPath)

/-- RwEq: continuity from below symm_symm. -/
theorem cont_below_rweq_symm_symm (d : ContFromBelow) :
    RwEq
      (Path.symm (Path.symm d.limitPath))
      d.limitPath :=
  rweq_of_step (Step.symm_symm d.limitPath)

/-! ## Continuity from Above -/

/-- Continuity from above: μ(⋂ Aₙ) = lim μ(Aₙ) when finite. -/
structure ContFromAbove where
  measures : List Nat
  limitVal : Nat
  interMeas : Nat
  limitPath : Path interMeas limitVal

/-- RwEq: continuity from above inv cancel. -/
theorem cont_above_rweq_inv_right (d : ContFromAbove) :
    RwEq
      (Path.trans d.limitPath (Path.symm d.limitPath))
      (Path.refl d.interMeas) :=
  rweq_cmpA_inv_right d.limitPath

/-- RwEq: continuity from above trans refl. -/
theorem cont_above_rweq_trans_refl (d : ContFromAbove) :
    RwEq
      (Path.trans d.limitPath (Path.refl d.limitVal))
      d.limitPath :=
  rweq_of_step (Step.trans_refl_right d.limitPath)

/-! ## Null Sets -/

/-- Null set data: a set with measure zero. -/
structure NullSetData where
  measVal : Nat
  nullPath : Path measVal 0

/-- Null set path trans refl. -/
theorem null_trans_refl (d : NullSetData) :
    Path.trans d.nullPath (Path.refl 0) = d.nullPath := by
  simp

/-- RwEq: null set inv cancel. -/
theorem null_rweq_inv_right (d : NullSetData) :
    RwEq
      (Path.trans d.nullPath (Path.symm d.nullPath))
      (Path.refl d.measVal) :=
  rweq_cmpA_inv_right d.nullPath

/-- RwEq: null set symm_symm. -/
theorem null_rweq_symm_symm (d : NullSetData) :
    RwEq
      (Path.symm (Path.symm d.nullPath))
      d.nullPath :=
  rweq_of_step (Step.symm_symm d.nullPath)

/-! ## Outer Measure -/

/-- Outer measure data: subadditivity witness. -/
structure OuterMeasureData where
  measA : Nat
  measB : Nat
  outerVal : Nat
  sumVal : Nat
  subaddPath : Path outerVal sumVal
  sumPath : Path sumVal (measA + measB)

/-- Outer measure subadditivity composed path. -/
def outer_subadd_path (d : OuterMeasureData) : Path d.outerVal (d.measA + d.measB) :=
  Path.trans d.subaddPath d.sumPath

/-- Outer measure associativity. -/
theorem outer_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-- RwEq: outer measure trans refl. -/
theorem outer_rweq_trans_refl (d : OuterMeasureData) :
    RwEq
      (Path.trans d.subaddPath (Path.refl d.sumVal))
      d.subaddPath :=
  rweq_of_step (Step.trans_refl_right d.subaddPath)

/-- RwEq: outer measure inv cancel. -/
theorem outer_rweq_inv_right (d : OuterMeasureData) :
    RwEq
      (Path.trans d.subaddPath (Path.symm d.subaddPath))
      (Path.refl d.outerVal) :=
  rweq_cmpA_inv_right d.subaddPath

/-! ## CongrArg and Transport -/

/-- CongrArg for measure values. -/
theorem meas_congrArg {X : Type u} (m : Measure X) {n1 n2 : Nat}
    (h : n1 = n2) : m.meas n1 = m.meas n2 :=
  _root_.congrArg m.meas h

/-- Path from congrArg on measure. -/
def meas_congrArg_path {X : Type u} (m : Measure X) {n1 n2 : Nat}
    (h : n1 = n2) : Path (m.meas n1) (m.meas n2) :=
  Path.ofEq (_root_.congrArg m.meas h)

/-- Transport of measure data along index equality. -/
def meas_transport {P : Nat → Type v} {n1 n2 : Nat}
    (h : n1 = n2) (x : P n1) : P n2 :=
  Path.transport (Path.ofEq h) x

/-- Transport along refl is identity. -/
theorem meas_transport_refl {P : Nat → Type v} (n : Nat) (x : P n) :
    meas_transport (rfl : n = n) x = x := rfl

/-! ## Trivial Instances -/

/-- Trivial sigma algebra on Unit. -/
def trivialSigma : SigmaAlgebra Unit where
  measurable := fun _ => True
  emptyMeas := trivial
  fullMeas := trivial

/-- Trivial measure on Unit. -/
def trivialMeasure : Measure Unit where
  sigma := trivialSigma
  meas := fun _ => 0
  emptyVal := 0
  emptyPath := Path.refl 0

/-- Trivial additivity data. -/
def trivialAdditivity : AdditivityData where
  measA := 0
  measB := 0
  measUnion := 0
  sumVal := 0
  sumPath := Path.refl 0
  additivePath := Path.refl 0

/-- Trivial null set. -/
def trivialNull : NullSetData where
  measVal := 0
  nullPath := Path.refl 0

end MeasurePaths
end Algebra
end Path
end ComputationalPaths
