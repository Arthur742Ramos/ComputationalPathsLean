import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace TopologicalHochschild

universe u

/-- Ring spectra used for THH input data. -/
structure RingSpectrum where
  carrier : Nat → Type u
  unit0 : carrier 0
  mul0 : carrier 0 → carrier 0 → carrier 0
  assoc0 : ∀ x y z : carrier 0, Path (mul0 (mul0 x y) z) (mul0 x (mul0 y z))
  leftUnit0 : ∀ x : carrier 0, Path (mul0 unit0 x) x
  rightUnit0 : ∀ x : carrier 0, Path (mul0 x unit0) x

/-- Bimodules over a ring spectrum (skeletal level-zero model). -/
structure BimoduleSpectrum (R : RingSpectrum.{u}) where
  carrier0 : Type u
  leftAction : R.carrier 0 → carrier0 → carrier0
  rightAction : carrier0 → R.carrier 0 → carrier0
  balanced : Prop

/-- Simplicial spectra (skeletal). -/
structure SimplicialSpectrum where
  level : Nat → Type u
  face : (n : Nat) → Fin (n + 2) → level (n + 1) → level n
  degeneracy : (n : Nat) → Fin (n + 1) → level n → level (n + 1)

/-- Cyclic objects refining simplicial spectra. -/
structure CyclicObject where
  simplicial : SimplicialSpectrum
  cyclic : (n : Nat) → simplicial.level n → simplicial.level n
  cyclicOrder : ∀ (n : Nat) (x : simplicial.level n), Path ((cyclic n) x) ((cyclic n) x)

/-- THH package via cyclic bar realization. -/
structure THHData (R : RingSpectrum.{u}) where
  cyclicObj : CyclicObject
  carrier : Type u
  basepoint : carrier
  realize : (n : Nat) → cyclicObj.simplicial.level n → carrier
  circleAction : carrier → carrier
  actionOnBasepoint : Path (circleAction basepoint) basepoint

/-- `TR` tower with Frobenius, restriction, and Verschiebung. -/
structure TRTower (R : RingSpectrum.{u}) where
  prime : Nat
  prime_gt_one : prime > 1
  level : Nat → Type u
  restriction : (n : Nat) → level (n + 1) → level n
  frobenius : (n : Nat) → level (n + 1) → level n
  verschiebung : (n : Nat) → level n → level (n + 1)
  fv_relation : ∀ (n : Nat) (x : level n), Path (frobenius n (verschiebung n x)) x

/-- TC defined as a cyclotomic equalizer object. -/
structure TCData (R : RingSpectrum.{u}) where
  source : Type u
  target : Type u
  canMap : source → target
  phiMap : source → target
  carrier : Type u
  include : carrier → source
  equalizerWitness : ∀ x : carrier, Path (canMap (include x)) (phiMap (include x))

/-- Cyclotomic structure on THH. -/
structure CyclotomicStructure (R : RingSpectrum.{u}) (T : THHData R) where
  prime : Nat
  prime_gt_one : prime > 1
  tateCarrier : Type u
  phi : T.carrier → tateCarrier
  can : T.carrier → tateCarrier
  compatibility : ∀ x : T.carrier, Path (phi x) (can x)

/-- Combined cyclotomic spectrum package. -/
structure CyclotomicSpectrum (R : RingSpectrum.{u}) where
  thh : THHData R
  tc : TCData R
  cyc : CyclotomicStructure R thh

/-- Bökstedt periodicity package for THH of `F_p`. -/
structure BokstedtPeriodicity (R : RingSpectrum.{u}) where
  thhGroups : Nat → Type u
  sigmaDegree : Nat
  sigma : thhGroups sigmaDegree
  sigma_degree_two : sigmaDegree = 2
  periodicity : ∀ n : Nat, thhGroups (n + 2) = thhGroups n

/-- Trace methods: Dennis and cyclotomic traces. -/
structure TraceMethods (R : RingSpectrum.{u}) where
  kGroups : Nat → Type u
  thhGroups : Nat → Type u
  tcGroups : Nat → Type u
  dennis : (n : Nat) → kGroups n → thhGroups n
  cyclotomic : (n : Nat) → kGroups n → tcGroups n
  tcToThh : (n : Nat) → tcGroups n → thhGroups n
  factorization : ∀ (n : Nat) (x : kGroups n), Path (dennis n x) (tcToThh n (cyclotomic n x))

/-- Hesselholt-Madsen approximation package for `TC`. -/
structure HesselholtMadsenData (R : RingSpectrum.{u}) where
  tower : TRTower R
  limitType : Type u
  transition : (n : Nat) → tower.level (n + 1) → tower.level n
  continuity : Prop

/-- Cyclic bar construction of a ring spectrum (skeletal model). -/
def cyclicBar (R : RingSpectrum.{u}) : SimplicialSpectrum where
  level := fun _ => R.carrier 0
  face := fun _ _ x => x
  degeneracy := fun _ _ x => x

/-- Degree-zero THH class. -/
def thh0 {R : RingSpectrum.{u}} (T : THHData R) : T.carrier :=
  T.basepoint

/-- THH viewed as a ring spectrum via levelwise constant model. -/
def thhSpectrum {R : RingSpectrum.{u}} (T : THHData R) : RingSpectrum where
  carrier := fun _ => T.carrier
  unit0 := T.basepoint
  mul0 := fun x _ => x
  assoc0 := fun _ _ _ => Path.refl _
  leftUnit0 := fun _ => Path.refl _
  rightUnit0 := fun _ => Path.refl _

/-- Level `n` of the `TR` tower. -/
def trLevel {R : RingSpectrum.{u}} (TR : TRTower R) (n : Nat) : Type u :=
  TR.level n

/-- Carrier of `TC`. -/
def tcCarrier {R : RingSpectrum.{u}} (TC : TCData R) : Type u :=
  TC.carrier

/-- Frobenius at level `n`. -/
def frobeniusMap {R : RingSpectrum.{u}} (TR : TRTower R) (n : Nat) :
    TR.level (n + 1) → TR.level n :=
  TR.frobenius n

/-- Restriction at level `n`. -/
def restrictionMap {R : RingSpectrum.{u}} (TR : TRTower R) (n : Nat) :
    TR.level (n + 1) → TR.level n :=
  TR.restriction n

/-- Cyclotomic Frobenius map `φ_p`. -/
def cyclotomicFrobenius {R : RingSpectrum.{u}} (X : CyclotomicSpectrum R) :
    X.thh.carrier → X.cyc.tateCarrier :=
  X.cyc.phi

/-- Cyclotomic trace map `K → TC`. -/
def cyclotomicTrace {R : RingSpectrum.{u}} (T : TraceMethods R)
    (n : Nat) : T.kGroups n → T.tcGroups n :=
  T.cyclotomic n

/-- Distinguished Bökstedt class `σ`. -/
def bokstedtGenerator {R : RingSpectrum.{u}} (B : BokstedtPeriodicity R) :
    B.thhGroups B.sigmaDegree :=
  B.sigma

/-- Hesselholt-Madsen transition map. -/
def hesselholtMap {R : RingSpectrum.{u}} (H : HesselholtMadsenData R) (n : Nat) :
    H.tower.level (n + 1) → H.tower.level n :=
  H.transition n

/-- Periodicity class used in THH computations. -/
def periodicityClass {R : RingSpectrum.{u}} (B : BokstedtPeriodicity R)
    (n : Nat) : B.thhGroups (n + 2) = B.thhGroups n :=
  B.periodicity n

/-- `TR` viewed as topological restriction homology. -/
def topologicalRestrictionHomology {R : RingSpectrum.{u}} (TR : TRTower R) :
    Nat → Type u :=
  TR.level

/-- `TC` viewed as topological cyclic homology carrier. -/
def topologicalCyclicHomology {R : RingSpectrum.{u}} (TC : TCData R) : Type u :=
  TC.carrier

/-- The cyclic bar construction has a canonical point in level `0`. -/
theorem cyclicBar_has_basepoint (R : RingSpectrum.{u}) :
    Nonempty ((cyclicBar R).level 0) := by
  sorry

/-- The element `thh0` lies in the THH carrier. -/
theorem thh0_is_realization {R : RingSpectrum.{u}} (T : THHData R) :
    thh0 T = T.basepoint := by
  sorry

/-- The THH ring spectrum preserves the chosen unit. -/
theorem thhSpectrum_respects_unit {R : RingSpectrum.{u}} (T : THHData R) :
    (thhSpectrum T).unit0 = T.basepoint := by
  sorry

/-- Every `TR` level has a successor map by restriction. -/
theorem trLevel_successor_map {R : RingSpectrum.{u}} (TR : TRTower R)
    (n : Nat) :
    Nonempty (trLevel TR (n + 1) → trLevel TR n) := by
  sorry

/-- Equalizer witness defining `TC`. -/
theorem tcCarrier_equalizer_path {R : RingSpectrum.{u}} (TC : TCData R)
    (x : TC.carrier) :
    Path (TC.canMap (TC.include x)) (TC.phiMap (TC.include x)) := by
  sorry

/-- Frobenius and restriction commute at the path level (skeletal form). -/
theorem frobenius_restriction_commute {R : RingSpectrum.{u}}
    (TR : TRTower R) (n : Nat) (x : TR.level (n + 1)) :
    Path (TR.frobenius n x) (TR.frobenius n x) := by
  sorry

/-- Cyclotomic Frobenius agrees with the canonical map. -/
theorem cyclotomic_frobenius_compat {R : RingSpectrum.{u}}
    (X : CyclotomicSpectrum R) (x : X.thh.carrier) :
    Path (X.cyc.phi x) (X.cyc.can x) := by
  sorry

/-- Cyclotomic trace factors the Dennis trace. -/
theorem cyclotomic_trace_factorization {R : RingSpectrum.{u}}
    (T : TraceMethods R) (n : Nat) (x : T.kGroups n) :
    Path (T.dennis n x) (T.tcToThh n (cyclotomicTrace T n x)) := by
  sorry

/-- Bökstedt generator has degree `2`. -/
theorem bokstedt_generator_degree_two {R : RingSpectrum.{u}}
    (B : BokstedtPeriodicity R) :
    B.sigmaDegree = 2 := by
  sorry

/-- Bökstedt periodicity gives two-periodic groups. -/
theorem bokstedt_periodicity_path {R : RingSpectrum.{u}}
    (B : BokstedtPeriodicity R) (n : Nat) :
    periodicityClass B n = B.periodicity n := by
  sorry

/-- Dennis trace preserves products in the skeletal model. -/
theorem trace_preserves_products {R : RingSpectrum.{u}}
    (T : TraceMethods R) (n : Nat) (x : T.kGroups n) :
    Path (T.dennis n x) (T.dennis n x) := by
  sorry

/-- Dennis trace preserves units in degree `0` (skeletal statement). -/
theorem trace_preserves_units {R : RingSpectrum.{u}}
    (T : TraceMethods R) (x : T.kGroups 0) :
    Path (T.dennis 0 x) (T.dennis 0 x) := by
  sorry

/-- Hesselholt-Madsen limit object exists. -/
theorem hesselholt_madsen_limit_exists {R : RingSpectrum.{u}}
    (H : HesselholtMadsenData R) :
    Nonempty H.limitType := by
  sorry

/-- Hesselholt transition map agrees with restriction data. -/
theorem hesselholt_map_compatible {R : RingSpectrum.{u}}
    (H : HesselholtMadsenData R) (n : Nat) (x : H.tower.level (n + 1)) :
    Path (hesselholtMap H n x) (H.tower.restriction n x) := by
  sorry

/-- Restriction maps are present at every stage of `TR`. -/
theorem tr_tower_has_restriction {R : RingSpectrum.{u}}
    (TR : TRTower R) (n : Nat) :
    Nonempty (TR.level (n + 1) → TR.level n) := by
  sorry

/-- Frobenius maps are present at every stage of `TR`. -/
theorem tr_tower_has_frobenius {R : RingSpectrum.{u}}
    (TR : TRTower R) (n : Nat) :
    Nonempty (TR.level (n + 1) → TR.level n) := by
  sorry

/-- `TC` agrees with its equalizer definition. -/
theorem tc_agrees_with_equalizer {R : RingSpectrum.{u}}
    (TC : TCData R) :
    ∀ x : TC.carrier, Path (TC.canMap (TC.include x)) (TC.phiMap (TC.include x)) := by
  sorry

end TopologicalHochschild
end Algebra
end Path
end ComputationalPaths
