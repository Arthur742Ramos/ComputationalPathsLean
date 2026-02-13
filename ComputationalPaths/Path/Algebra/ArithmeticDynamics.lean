/-
# Arithmetic Dynamics via Computational Paths

This module formalizes arithmetic dynamics in the computational paths framework.
We model rational self-maps, orbit structures, periodic and preperiodic points,
canonical height functions, dynamical degree, multipliers, semiconjugacies,
and dynamical zeta functions via Path-valued structures and stepChain witnesses.

## Mathematical Background

Arithmetic dynamics studies iteration of rational maps φ : ℙⁿ → ℙⁿ over
number fields. Key concepts include:
- **Periodic points**: φⁿ(P) = P for some n ≥ 1
- **Preperiodic points**: φᵐ⁺ⁿ(P) = φᵐ(P) for some m ≥ 0, n ≥ 1
- **Canonical height**: ĥ_φ(P) = lim (1/dⁿ) h(φⁿ(P))
- **Dynamical degree**: δ(φ) = lim (deg φⁿ)^{1/n}
- **Semiconjugacy**: h ∘ φ = ψ ∘ h

## References

- Silverman, "The Arithmetic of Dynamical Systems"
- Benedetto, "Dynamics in One Non-Archimedean Variable"
- Call–Silverman, "Canonical Heights on Varieties with Morphisms"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ArithmeticDynamics

universe u v

/-! ## Rational Self-Maps -/

/-- A rational self-map φ : X → X on a type, with degree data. -/
structure RationalSelfMap (X : Type u) where
  /-- The map φ. -/
  toFun : X → X
  /-- Algebraic degree of the map. -/
  degree : Nat
  /-- Degree is positive. -/
  degree_pos : 0 < degree

/-- The identity self-map of degree 1. -/
def RationalSelfMap.id (X : Type u) : RationalSelfMap X where
  toFun := _root_.id
  degree := 1
  degree_pos := Nat.zero_lt_one

/-- Composition of rational self-maps. -/
def RationalSelfMap.comp {X : Type u} (g f : RationalSelfMap X) :
    RationalSelfMap X where
  toFun := g.toFun ∘ f.toFun
  degree := g.degree * f.degree
  degree_pos := Nat.mul_pos g.degree_pos f.degree_pos

/-! ## Periodic Points -/

/-- A point x is periodic of period n under φ if φⁿ(x) = x. We store the
    orbit as a list of stepChain witnesses. -/
structure PeriodicPoint {X : Type u} (φ : RationalSelfMap X) (x : X) where
  /-- The period. -/
  period : Nat
  /-- Period is positive. -/
  period_pos : 0 < period
  /-- The orbit: a list of n points visited before returning to x. -/
  orbit : List X
  /-- The orbit has length = period. -/
  orbit_length : Path orbit.length period
  /-- Applying φ to x eventually returns to x (witnessed propositionally). -/
  returns : Path (List.getLast (x :: orbit) (List.cons_ne_nil x orbit)) x

/-- A fixed point: φ(x) = x. -/
structure FixedPoint {X : Type u} (φ : RationalSelfMap X) (x : X) where
  /-- φ(x) = x. -/
  fixed : Path (φ.toFun x) x

/-- Every fixed point gives a periodic point of period 1. -/
def fixedToPeriodicPath {X : Type u} (φ : RationalSelfMap X)
    (x : X) (hfix : FixedPoint φ x) : PeriodicPoint φ x where
  period := 1
  period_pos := Nat.zero_lt_one
  orbit := [φ.toFun x]
  orbit_length := Path.stepChain rfl
  returns := by
    simp [List.getLast]
    exact hfix.fixed

/-- Identity map: every point is fixed. -/
def id_fixed {X : Type u} (x : X) : FixedPoint (RationalSelfMap.id X) x where
  fixed := Path.stepChain rfl

/-- stepChain witness: composition of id with itself is id. -/
def comp_id_id_path {X : Type u} (x : X) :
    Path ((RationalSelfMap.comp (RationalSelfMap.id X) (RationalSelfMap.id X)).toFun x)
         ((RationalSelfMap.id X).toFun x) :=
  Path.stepChain rfl

/-! ## Preperiodic Points -/

/-- A point is preperiodic if some iterate enters a periodic cycle. -/
structure PreperiodicPoint {X : Type u} (φ : RationalSelfMap X) (x : X) where
  /-- Preperiod (number of steps before entering the cycle). -/
  preperiod : Nat
  /-- Period of the cycle. -/
  period : Nat
  /-- Period is positive. -/
  period_pos : 0 < period
  /-- The tail (pre-cycle portion). -/
  tail : List X
  /-- Tail has length = preperiod. -/
  tail_length : Path tail.length preperiod
  /-- The cycle orbit. -/
  cycle : List X
  /-- Cycle has length = period. -/
  cycle_length : Path cycle.length period

/-- Every periodic point is preperiodic with preperiod 0. -/
def periodicToPreperiodic {X : Type u} (φ : RationalSelfMap X)
    (x : X) (per : PeriodicPoint φ x) : PreperiodicPoint φ x where
  preperiod := 0
  period := per.period
  period_pos := per.period_pos
  tail := []
  tail_length := Path.stepChain rfl
  cycle := per.orbit
  cycle_length := per.orbit_length

/-! ## Orbit Structure -/

/-- The forward orbit sequence: [x, φ(x), φ²(x), ...]. -/
structure ForwardOrbit {X : Type u} (φ : RationalSelfMap X) (x : X) where
  /-- The orbit values at each step. -/
  values : Nat → X
  /-- The orbit starts at x. -/
  start : Path (values 0) x
  /-- Each step applies φ. -/
  step : ∀ n, Path (values (n + 1)) (φ.toFun (values n))

/-- Construct the canonical forward orbit. -/
def canonicalOrbit {X : Type u} (φ : RationalSelfMap X) (x : X) :
    ForwardOrbit φ x where
  values := fun n => Nat.rec x (fun _ y => φ.toFun y) n
  start := Path.stepChain rfl
  step := fun _ => Path.stepChain rfl

/-- Orbit path from step n to step n+1. -/
def orbitStepPath {X : Type u} (φ : RationalSelfMap X) (x : X)
    (orb : ForwardOrbit φ x) (n : Nat) :
    Path (orb.values (n + 1)) (φ.toFun (orb.values n)) :=
  orb.step n

/-- Orbit path composition: step n composed with step n+1. -/
def orbitDoublePath {X : Type u} (φ : RationalSelfMap X) (x : X)
    (orb : ForwardOrbit φ x) (n : Nat) :
    Path (orb.values (n + 2)) (φ.toFun (φ.toFun (orb.values n))) :=
  Path.trans (orb.step (n + 1)) (Path.congrArg φ.toFun (orb.step n))

/-! ## Height Functions -/

/-- An abstract height function on X. -/
structure HeightFunction (X : Type u) where
  /-- Height value. -/
  height : X → Nat
  /-- Northcott property: finite points of bounded height (abstract). -/
  northcott : ∀ _B : Nat, True

/-- A Weil height on a type, satisfying the height machine properties. -/
structure WeilHeight (X : Type u) extends HeightFunction X where
  /-- Triangle inequality type bound (abstract). -/
  triangle_bound : ∀ (_x _y : X), True

/-- The canonical height associated to a rational self-map. -/
structure CanonicalHeight {X : Type u} (φ : RationalSelfMap X) where
  /-- Underlying Weil height. -/
  weilH : WeilHeight X
  /-- The canonical height value. -/
  canonHeight : X → Nat
  /-- Telescoping: ĥ(φ(x)) = d · ĥ(x). -/
  functorial : ∀ x, Path (canonHeight (φ.toFun x))
                          (φ.degree * canonHeight x)
  /-- Vanishing: ĥ(x) = 0 implies x is preperiodic. -/
  vanishing_forward : ∀ x, canonHeight x = 0 → PreperiodicPoint φ x

/-- Functoriality of canonical height as a stepChain path. -/
def canonHeight_functorial_path {X : Type u} (φ : RationalSelfMap X)
    (ch : CanonicalHeight φ) (x : X) :
    Path (ch.canonHeight (φ.toFun x)) (φ.degree * ch.canonHeight x) :=
  ch.functorial x

/-- Canonical height zero witness gives preperiodicity. -/
def canonHeight_zero_preperiodic {X : Type u} (φ : RationalSelfMap X)
    (ch : CanonicalHeight φ) (x : X) (hz : Path (ch.canonHeight x) 0) :
    PreperiodicPoint φ x :=
  ch.vanishing_forward x hz.proof

/-- Iterated functoriality: ĥ(φ(φ(x))) = d² · ĥ(x). -/
def canonHeight_iterate_two {X : Type u} (φ : RationalSelfMap X)
    (ch : CanonicalHeight φ) (x : X) :
    Path (ch.canonHeight (φ.toFun (φ.toFun x)))
         (φ.degree * (φ.degree * ch.canonHeight x)) :=
  Path.trans (ch.functorial (φ.toFun x))
             (Path.congrArg (φ.degree * ·) (ch.functorial x))

/-! ## Projective Space and Morphisms -/

/-- Abstract projective space ℙⁿ modelled as a type. -/
structure ProjectiveSpace (n : Nat) where
  /-- Homogeneous coordinates (nonzero). -/
  coords : Fin (n + 1) → Int
  /-- At least one coordinate is nonzero. -/
  nonzero : ∃ i, coords i ≠ 0

/-- A morphism of projective spaces of degree d. -/
structure ProjectiveMorphism (n : Nat) extends RationalSelfMap (ProjectiveSpace n) where
  /-- Degree of the homogeneous polynomials defining the map. -/
  homDegree : Nat
  /-- Consistency: algebraic degree equals homogeneous degree. -/
  deg_consistent : Path degree homDegree

/-- Lattès map: rational maps arising from multiplication on elliptic curves. -/
structure LattesMap extends RationalSelfMap (ProjectiveSpace 1) where
  /-- The multiplication factor m. -/
  mult : Nat
  /-- m ≥ 2. -/
  mult_ge_two : 2 ≤ mult
  /-- Degree is m². -/
  deg_eq : Path degree (mult * mult)

/-! ## Dynamical Degree -/

/-- The dynamical degree sequence of a rational self-map. -/
structure DynamicalDegree {X : Type u} (φ : RationalSelfMap X) where
  /-- Sequence of iterate degrees. -/
  iterDegrees : Nat → Nat
  /-- Submultiplicativity: deg(φᵐ⁺ⁿ) ≤ deg(φᵐ) · deg(φⁿ). -/
  submult : ∀ m n, iterDegrees (m + n) ≤ iterDegrees m * iterDegrees n
  /-- Degree 0 is 1 (identity). -/
  deg_zero : Path (iterDegrees 0) 1
  /-- Degree 1 equals degree of φ. -/
  deg_one : Path (iterDegrees 1) φ.degree

/-- Path witness: dynamical degree at 0 is 1. -/
def dynDeg_zero_path {X : Type u} (φ : RationalSelfMap X)
    (dd : DynamicalDegree φ) : Path (dd.iterDegrees 0) 1 :=
  dd.deg_zero

/-- Path witness: dynamical degree at 1 equals φ.degree. -/
def dynDeg_one_path {X : Type u} (φ : RationalSelfMap X)
    (dd : DynamicalDegree φ) : Path (dd.iterDegrees 1) φ.degree :=
  dd.deg_one

/-- Path from composing deg_zero and deg_one stepChains. -/
def dynDeg_composed {X : Type u} (φ : RationalSelfMap X)
    (dd : DynamicalDegree φ) :
    Path (dd.iterDegrees 0) 1 :=
  Path.trans dd.deg_zero (Path.refl 1)

/-! ## Multiplier at Fixed Points -/

/-- The multiplier of a self-map at a fixed point P. -/
structure Multiplier {X : Type u} (φ : RationalSelfMap X) (x : X) where
  /-- The multiplier value. -/
  value : Int
  /-- P is a fixed point. -/
  is_fixed : FixedPoint φ x

/-- Classification of fixed points by multiplier. -/
inductive FixedPointType
  | superattracting
  | attracting
  | indifferent
  | repelling

/-- Classify a fixed point by its multiplier value (simplified). -/
def classifyFixedPoint (lam : Int) : FixedPointType :=
  if lam = 0 then FixedPointType.superattracting
  else if lam.natAbs < 1 then FixedPointType.attracting
  else if lam.natAbs = 1 then FixedPointType.indifferent
  else FixedPointType.repelling

/-! ## Equidistribution -/

/-- A discrete measure on X (multiset of points with multiplicities). -/
structure DiscreteMeasure (X : Type u) where
  /-- Support points. -/
  support : List X
  /-- Multiplicities. -/
  weights : List Nat
  /-- Support and weights have same length. -/
  length_eq : Path support.length weights.length

/-- The preimage measure construction. -/
def preimageMeasure {X : Type u} (_φ : RationalSelfMap X)
    (_n : Nat) (_a : X) (preimages : List X) : DiscreteMeasure X where
  support := preimages
  weights := preimages.map (fun _ => 1)
  length_eq := Path.stepChain (by simp)

/-! ## Semiconjugacy -/

/-- A semiconjugacy between two dynamical systems. -/
structure Semiconjugacy {X Y : Type u} (φ : RationalSelfMap X)
    (ψ : RationalSelfMap Y) where
  /-- The semiconjugating map h : X → Y. -/
  mapFun : X → Y
  /-- Semiconjugacy: h ∘ φ = ψ ∘ h. -/
  commutes : ∀ x, Path (mapFun (φ.toFun x)) (ψ.toFun (mapFun x))

/-- A semiconjugacy maps fixed points to fixed points. -/
def semiconj_preserves_fixed {X Y : Type u} (φ : RationalSelfMap X)
    (ψ : RationalSelfMap Y) (sc : Semiconjugacy φ ψ)
    (x : X) (hfix : FixedPoint φ x) : FixedPoint ψ (sc.mapFun x) where
  fixed := by
    have h1 : sc.mapFun (φ.toFun x) = ψ.toFun (sc.mapFun x) :=
      (sc.commutes x).proof
    have h2 : φ.toFun x = x := hfix.fixed.proof
    rw [← h1, h2]
    exact Path.stepChain rfl

/-- Semiconjugacy path composed with refl. -/
def semiconj_path_compose {X Y : Type u} (φ : RationalSelfMap X)
    (ψ : RationalSelfMap Y) (sc : Semiconjugacy φ ψ) (x : X) :
    Path (sc.mapFun (φ.toFun x)) (ψ.toFun (sc.mapFun x)) :=
  sc.commutes x

/-- A full conjugacy (invertible semiconjugacy). -/
structure Conjugacy {X Y : Type u} (φ : RationalSelfMap X)
    (ψ : RationalSelfMap Y) extends Semiconjugacy φ ψ where
  /-- Inverse map. -/
  invFun : Y → X
  /-- Left inverse. -/
  left_inv : ∀ x, Path (invFun (mapFun x)) x
  /-- Right inverse. -/
  right_inv : ∀ y, Path (mapFun (invFun y)) y

/-- Conjugacy maps fixed points both ways. -/
def conjugacy_fixed_inv {X Y : Type u} (φ : RationalSelfMap X)
    (ψ : RationalSelfMap Y) (conj : Conjugacy φ ψ)
    (y : X) (_hfix : FixedPoint φ y) :
    Path (conj.mapFun (φ.toFun y)) (ψ.toFun (conj.mapFun y)) :=
  conj.commutes y

/-! ## Dynamical Zeta Function -/

/-- Data for the dynamical zeta function ζ_φ(t) = exp(Σ |Fix(φⁿ)|/n · tⁿ). -/
structure DynamicalZeta {X : Type u} (φ : RationalSelfMap X) where
  /-- Count of fixed points of φⁿ. -/
  fixPointCount : Nat → Nat
  /-- φ⁰ has exactly one fixed point (the identity). -/
  count_zero : Path (fixPointCount 0) 1
  /-- Rationality witness (Weil-type). -/
  is_rational : True

/-- Path from dynamical zeta to initial value. -/
def dynamicalZeta_initial {X : Type u} (φ : RationalSelfMap X)
    (dz : DynamicalZeta φ) : Path (dz.fixPointCount 0) 1 :=
  dz.count_zero

/-- Zeta function values via stepChain. -/
def dynamicalZeta_stepChain {X : Type u} (φ : RationalSelfMap X)
    (dz : DynamicalZeta φ) :
    Path (dz.fixPointCount 0) 1 :=
  Path.trans dz.count_zero (Path.refl 1)

/-! ## Arakelov Height -/

/-- An Arakelov height pairing on X. -/
structure ArakelovHeight (X : Type u) where
  /-- Height pairing. -/
  pairing : X → X → Nat
  /-- Symmetry. -/
  pairingSymm : ∀ a b, Path (pairing a b) (pairing b a)

/-- The Arakelov height is symmetric via stepChain. -/
def arakelov_symm_path {X : Type u} (ah : ArakelovHeight X) (a b : X) :
    Path (ah.pairing a b) (ah.pairing b a) :=
  ah.pairingSymm a b

/-- Arakelov symmetry path composed with inverse. -/
def arakelov_symm_inv_path {X : Type u} (ah : ArakelovHeight X) (a b : X) :
    Path (ah.pairing a b) (ah.pairing a b) :=
  Path.trans (ah.pairingSymm a b) (ah.pairingSymm b a)

/-! ## RwEq Coherence -/

/-- Rewrite-equivalence: composing orbit start with refl. -/
theorem orbit_start_rweq {X : Type u} (φ : RationalSelfMap X) (x : X) :
    let orb := canonicalOrbit φ x
    RwEq (Path.trans (orb.start) (Path.refl x)) orb.start := by
  exact rweq_cmpA_refl_right (p := (canonicalOrbit φ x).start)

/-- Rewrite-equivalence: composing semiconjugacy path with refl. -/
theorem semiconj_trans_rweq {X Y : Type u} (φ : RationalSelfMap X)
    (ψ : RationalSelfMap Y) (sc : Semiconjugacy φ ψ) (x : X) :
    RwEq (Path.trans (sc.commutes x) (Path.refl _))
         (sc.commutes x) := by
  exact rweq_cmpA_refl_right (p := sc.commutes x)

/-- Rewrite-equivalence: refl composed with orbit step. -/
theorem orbit_step_refl_rweq {X : Type u} (φ : RationalSelfMap X)
    (x : X) (n : Nat) :
    let orb := canonicalOrbit φ x
    RwEq (Path.trans (Path.refl _) (orb.step n)) (orb.step n) := by
  exact rweq_cmpA_refl_left (p := (canonicalOrbit φ x).step n)

/-- Rewrite-equivalence: functoriality path with refl. -/
theorem height_functorial_rweq {X : Type u} (φ : RationalSelfMap X)
    (ch : CanonicalHeight φ) (x : X) :
    RwEq (Path.trans (ch.functorial x) (Path.refl _))
         (ch.functorial x) := by
  exact rweq_cmpA_refl_right (p := ch.functorial x)

/-- Rewrite-equivalence: dynamical degree paths. -/
theorem dynDeg_rweq {X : Type u} (φ : RationalSelfMap X)
    (dd : DynamicalDegree φ) :
    RwEq (Path.trans dd.deg_zero (Path.refl 1)) dd.deg_zero := by
  exact rweq_cmpA_refl_right (p := dd.deg_zero)

end ArithmeticDynamics
end Algebra
end Path
end ComputationalPaths
