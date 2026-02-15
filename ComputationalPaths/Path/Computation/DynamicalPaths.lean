/-
# Dynamical Systems via Computational Paths

Deep constructions modeling dynamical systems through computational paths:
state spaces, orbits, fixed points, periodic orbits, stability analysis,
Lyapunov functions, attractors, repellers, conjugacy, semiconjugacy,
invariant measures, omega-limit sets, bifurcation cascades, and ergodic paths.

## References

- Strogatz, "Nonlinear Dynamics and Chaos"
- Katok & Hasselblatt, "Introduction to the Modern Theory of Dynamical Systems"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace DynamicalPaths

universe u v

open ComputationalPaths.Path

/-! ## State Spaces and Orbit Composition -/

/-- A discrete dynamical system on a type. -/
structure DynSystem (S : Type u) where
  evolve : S → S

/-- An orbit segment connecting a state to its successor. -/
structure OrbitSegment (S : Type u) where
  state : S
  nextState : S
  step : Path state nextState

/-- Compose orbit paths via trans. -/
def orbitCompose {S : Type u} {a b c : S}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Orbit composition is associative. -/
theorem orbitCompose_assoc {S : Type u} {a b c d : S}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    orbitCompose (orbitCompose p q) r = orbitCompose p (orbitCompose q r) := by
  simp [orbitCompose]

/-- Orbit composition with refl on right is identity. -/
theorem orbitCompose_refl_right {S : Type u} {a b : S} (p : Path a b) :
    orbitCompose p (Path.refl b) = p := by
  simp [orbitCompose]

/-- Orbit composition with refl on left is identity. -/
theorem orbitCompose_refl_left {S : Type u} {a b : S} (p : Path a b) :
    orbitCompose (Path.refl a) p = p := by
  simp [orbitCompose]

/-! ## Fixed Points -/

/-- Fixed point data: f(x) = x witnessed by a path. -/
structure FixedPointData (S : Type u) where
  point : S
  image : S
  fixedPath : Path image point

/-- Fixed point path trans refl. -/
theorem fixedPoint_trans_refl {S : Type u} (d : FixedPointData S) :
    Path.trans d.fixedPath (Path.refl d.point) = d.fixedPath := by
  simp

/-- RwEq: fixed point trans refl. -/
theorem fixedPoint_rweq_trans_refl {S : Type u} (d : FixedPointData S) :
    RwEq (Path.trans d.fixedPath (Path.refl d.point)) d.fixedPath :=
  rweq_of_step (Step.trans_refl_right d.fixedPath)

/-- RwEq: fixed point inv cancel right. -/
theorem fixedPoint_rweq_inv_right {S : Type u} (d : FixedPointData S) :
    RwEq
      (Path.trans d.fixedPath (Path.symm d.fixedPath))
      (Path.refl d.image) :=
  rweq_cmpA_inv_right d.fixedPath

/-- RwEq: fixed point symm_symm. -/
theorem fixedPoint_rweq_symm_symm {S : Type u} (d : FixedPointData S) :
    RwEq (Path.symm (Path.symm d.fixedPath)) d.fixedPath :=
  rweq_of_step (Step.symm_symm d.fixedPath)

/-- RwEq: fixed point inv cancel left. -/
theorem fixedPoint_rweq_inv_left {S : Type u} (d : FixedPointData S) :
    RwEq
      (Path.trans (Path.symm d.fixedPath) d.fixedPath)
      (Path.refl d.point) :=
  rweq_cmpA_inv_left d.fixedPath

/-! ## Periodic Orbits -/

/-- Periodic orbit data: f^n(x) = x witnessed by a path. -/
structure PeriodicOrbitData (S : Type u) where
  basePoint : S
  iterateImage : S
  period : Nat
  periodicPath : Path iterateImage basePoint

/-- Periodic orbit path trans refl. -/
theorem periodic_trans_refl {S : Type u} (d : PeriodicOrbitData S) :
    Path.trans d.periodicPath (Path.refl d.basePoint) = d.periodicPath := by
  simp

/-- RwEq: periodic inv cancel right. -/
theorem periodic_rweq_inv_right {S : Type u} (d : PeriodicOrbitData S) :
    RwEq
      (Path.trans d.periodicPath (Path.symm d.periodicPath))
      (Path.refl d.iterateImage) :=
  rweq_cmpA_inv_right d.periodicPath

/-- RwEq: periodic symm_symm. -/
theorem periodic_rweq_symm_symm {S : Type u} (d : PeriodicOrbitData S) :
    RwEq (Path.symm (Path.symm d.periodicPath)) d.periodicPath :=
  rweq_of_step (Step.symm_symm d.periodicPath)

/-- RwEq: periodic inv cancel left. -/
theorem periodic_rweq_inv_left {S : Type u} (d : PeriodicOrbitData S) :
    RwEq
      (Path.trans (Path.symm d.periodicPath) d.periodicPath)
      (Path.refl d.basePoint) :=
  rweq_cmpA_inv_left d.periodicPath

/-! ## Lyapunov Functions -/

/-- Lyapunov function data: V(f(x)) relates to V(x) via a path. -/
structure LyapunovData where
  vAtState : Nat
  vAtNext : Nat
  lyapunovPath : Path vAtNext vAtState

/-- Lyapunov path trans refl. -/
theorem lyapunov_trans_refl (d : LyapunovData) :
    Path.trans d.lyapunovPath (Path.refl d.vAtState) = d.lyapunovPath := by
  simp

/-- RwEq: Lyapunov inv cancel right. -/
theorem lyapunov_rweq_inv_right (d : LyapunovData) :
    RwEq
      (Path.trans d.lyapunovPath (Path.symm d.lyapunovPath))
      (Path.refl d.vAtNext) :=
  rweq_cmpA_inv_right d.lyapunovPath

/-- RwEq: Lyapunov trans refl. -/
theorem lyapunov_rweq_trans_refl (d : LyapunovData) :
    RwEq
      (Path.trans d.lyapunovPath (Path.refl d.vAtState))
      d.lyapunovPath :=
  rweq_of_step (Step.trans_refl_right d.lyapunovPath)

/-! ## Conjugacy -/

/-- Conjugacy data: h ∘ f = g ∘ h witnessed as a path. -/
structure ConjugacyData (A B : Type u) where
  hfVal : B
  ghVal : B
  conjugacyPath : Path hfVal ghVal

/-- Conjugacy path trans refl. -/
theorem conjugacy_trans_refl {A B : Type u} (d : ConjugacyData A B) :
    Path.trans d.conjugacyPath (Path.refl d.ghVal) = d.conjugacyPath := by
  simp

/-- RwEq: conjugacy inv cancel right. -/
theorem conjugacy_rweq_inv_right {A B : Type u} (d : ConjugacyData A B) :
    RwEq
      (Path.trans d.conjugacyPath (Path.symm d.conjugacyPath))
      (Path.refl d.hfVal) :=
  rweq_cmpA_inv_right d.conjugacyPath

/-- RwEq: conjugacy symm_symm. -/
theorem conjugacy_rweq_symm_symm {A B : Type u} (d : ConjugacyData A B) :
    RwEq (Path.symm (Path.symm d.conjugacyPath)) d.conjugacyPath :=
  rweq_of_step (Step.symm_symm d.conjugacyPath)

/-! ## Semiconjugacy -/

/-- Semiconjugacy: h ∘ f = g ∘ h where h is a surjection, witnessed as a path. -/
structure SemiconjugacyData (A B : Type u) where
  hfVal : B
  ghVal : B
  semiconjPath : Path hfVal ghVal

/-- Semiconjugacy composed with orbit yields valid path. -/
theorem semiconj_orbit_compose {A B : Type u}
    (d : SemiconjugacyData A B) {c : B} (orb : Path d.ghVal c) :
    orbitCompose d.semiconjPath orb =
    Path.trans d.semiconjPath orb := by
  simp [orbitCompose]

/-- RwEq: semiconjugacy refl trans. -/
theorem semiconj_rweq_refl_trans {A B : Type u} (d : SemiconjugacyData A B) :
    RwEq
      (Path.trans (Path.refl d.hfVal) d.semiconjPath)
      d.semiconjPath :=
  rweq_of_step (Step.trans_refl_left d.semiconjPath)

/-! ## Attractors -/

/-- Attractor data: orbit converges to attractor, witnessed as path. -/
structure AttractorData (S : Type u) where
  orbitVal : S
  attractorVal : S
  convergePath : Path orbitVal attractorVal

/-- Attractor convergence path trans refl. -/
theorem attractor_trans_refl {S : Type u} (d : AttractorData S) :
    Path.trans d.convergePath (Path.refl d.attractorVal) = d.convergePath := by
  simp

/-- RwEq: attractor inv cancel right. -/
theorem attractor_rweq_inv_right {S : Type u} (d : AttractorData S) :
    RwEq
      (Path.trans d.convergePath (Path.symm d.convergePath))
      (Path.refl d.orbitVal) :=
  rweq_cmpA_inv_right d.convergePath

/-- RwEq: attractor refl trans. -/
theorem attractor_rweq_refl_trans {S : Type u} (d : AttractorData S) :
    RwEq
      (Path.trans (Path.refl d.orbitVal) d.convergePath)
      d.convergePath :=
  rweq_of_step (Step.trans_refl_left d.convergePath)

/-! ## Repellers -/

/-- Repeller data: orbit diverges from repeller, witnessed as reversed path. -/
structure RepellerData (S : Type u) where
  repellerVal : S
  orbitVal : S
  divergePath : Path repellerVal orbitVal

/-- The reverse path from orbit back to repeller. -/
def repellerReturn {S : Type u} (d : RepellerData S) : Path d.orbitVal d.repellerVal :=
  Path.symm d.divergePath

/-- Repeller diverge-return cancels. -/
theorem repeller_rweq_diverge_return {S : Type u} (d : RepellerData S) :
    RwEq
      (Path.trans d.divergePath (repellerReturn d))
      (Path.refl d.repellerVal) :=
  rweq_cmpA_inv_right d.divergePath

/-- RwEq: repeller symm_symm. -/
theorem repeller_rweq_symm_symm {S : Type u} (d : RepellerData S) :
    RwEq (Path.symm (Path.symm d.divergePath)) d.divergePath :=
  rweq_of_step (Step.symm_symm d.divergePath)

/-! ## Omega-Limit Sets -/

/-- Omega-limit data: orbit approaches limit set element. -/
structure OmegaLimitData (S : Type u) where
  orbitVal : S
  limitVal : S
  approachPath : Path orbitVal limitVal

/-- Omega-limit approach composed with return gives identity. -/
theorem omegaLimit_rweq_approach_return {S : Type u} (d : OmegaLimitData S) :
    RwEq
      (Path.trans d.approachPath (Path.symm d.approachPath))
      (Path.refl d.orbitVal) :=
  rweq_cmpA_inv_right d.approachPath

/-- RwEq: omega-limit refl trans. -/
theorem omegaLimit_rweq_refl_trans {S : Type u} (d : OmegaLimitData S) :
    RwEq
      (Path.trans (Path.refl d.orbitVal) d.approachPath)
      d.approachPath :=
  rweq_of_step (Step.trans_refl_left d.approachPath)

/-! ## Bifurcation Cascades -/

/-- Bifurcation data: system behavior changes at parameter value. -/
structure BifurcationData where
  preVal : Nat
  postVal : Nat
  bifurcPath : Path preVal postVal

/-- Composing two bifurcation transitions. -/
def bifurcationCascade (d1 : BifurcationData) (d2 : BifurcationData)
    (h : d1.postVal = d2.preVal) : Path d1.preVal d2.postVal :=
  Path.trans d1.bifurcPath (Path.trans (Path.ofEq h) d2.bifurcPath)

/-- Bifurcation symm_symm. -/
theorem bifurcation_rweq_symm_symm (d : BifurcationData) :
    RwEq (Path.symm (Path.symm d.bifurcPath)) d.bifurcPath :=
  rweq_of_step (Step.symm_symm d.bifurcPath)

/-- Bifurcation trans refl. -/
theorem bifurcation_trans_refl (d : BifurcationData) :
    Path.trans d.bifurcPath (Path.refl d.postVal) = d.bifurcPath := by
  simp

/-! ## Invariant Sets -/

/-- Invariant set data: f(S) ⊆ S witnessed as membership path. -/
structure InvariantSetData (S : Type u) where
  memberVal : S
  imageVal : S
  invariantPath : Path imageVal memberVal

/-- Invariant set path trans refl. -/
theorem invariant_trans_refl {S : Type u} (d : InvariantSetData S) :
    Path.trans d.invariantPath (Path.refl d.memberVal) = d.invariantPath := by
  simp

/-- RwEq: invariant set inv cancel left. -/
theorem invariant_rweq_inv_left {S : Type u} (d : InvariantSetData S) :
    RwEq
      (Path.trans (Path.symm d.invariantPath) d.invariantPath)
      (Path.refl d.memberVal) :=
  rweq_cmpA_inv_left d.invariantPath

/-! ## Topological Conjugacy via congrArg -/

/-- Applying a conjugacy map h to a dynamical path via congrArg. -/
theorem congrArg_conjugacy {A B : Type u} (h : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg h (Path.trans p (Path.refl y)) =
    Path.congrArg h p := by
  simp

/-- congrArg preserves orbit composition. -/
theorem congrArg_orbitCompose {A B : Type u} (h : A → B)
    {x y z : A} (p : Path x y) (q : Path y z) :
    Path.congrArg h (orbitCompose p q) =
    orbitCompose (Path.congrArg h p) (Path.congrArg h q) := by
  simp [orbitCompose]

/-- congrArg preserves symm of orbit paths. -/
theorem congrArg_orbit_symm {A B : Type u} (h : A → B)
    {x y : A} (p : Path x y) :
    Path.congrArg h (Path.symm p) = Path.symm (Path.congrArg h p) := by
  simp

/-! ## Ergodic Paths -/

/-- Ergodic data: time average equals space average, witnessed as a path. -/
structure ErgodicData where
  timeAvg : Nat
  spaceAvg : Nat
  ergodicPath : Path timeAvg spaceAvg

/-- Ergodic path trans refl. -/
theorem ergodic_trans_refl (d : ErgodicData) :
    Path.trans d.ergodicPath (Path.refl d.spaceAvg) = d.ergodicPath := by
  simp

/-- RwEq: ergodic inv cancel. -/
theorem ergodic_rweq_inv_right (d : ErgodicData) :
    RwEq
      (Path.trans d.ergodicPath (Path.symm d.ergodicPath))
      (Path.refl d.timeAvg) :=
  rweq_cmpA_inv_right d.ergodicPath

/-- RwEq: ergodic symm_symm. -/
theorem ergodic_rweq_symm_symm (d : ErgodicData) :
    RwEq (Path.symm (Path.symm d.ergodicPath)) d.ergodicPath :=
  rweq_of_step (Step.symm_symm d.ergodicPath)

/-! ## Orbit Equivalence -/

/-- Two orbit paths that agree propositionally are RwEq. -/
theorem orbit_rweq_of_eq {S : Type u} {a b : S}
    (p q : Path a b) (h : p = q) : RwEq p q := by
  subst h; exact rweq_refl p

/-- Orbit symm trans cancel. -/
theorem orbit_rweq_symm_trans {S : Type u} {a b : S} (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_cmpA_inv_left p

/-- Orbit trans symm cancel. -/
theorem orbit_rweq_trans_symm {S : Type u} {a b : S} (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right p

/-! ## Iterated Maps and Orbit Chains -/

/-- Iterated orbit: chain of n orbit segments. -/
def iteratedOrbit {S : Type u} {a : S} (p : Path a a) : Nat → Path a a
  | 0 => Path.refl a
  | n + 1 => Path.trans (iteratedOrbit p n) p

/-- Iterated orbit 0 is refl. -/
theorem iteratedOrbit_zero {S : Type u} {a : S} (p : Path a a) :
    iteratedOrbit p 0 = Path.refl a := rfl

/-- Iterated orbit 1 is identity with trans refl. -/
theorem iteratedOrbit_one {S : Type u} {a : S} (p : Path a a) :
    iteratedOrbit p 1 = Path.trans (Path.refl a) p := rfl

/-- RwEq: iterated orbit 1 simplifies. -/
theorem iteratedOrbit_one_rweq {S : Type u} {a : S} (p : Path a a) :
    RwEq (iteratedOrbit p 1) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Mapping a dynamical path through a function preserves orbit structure. -/
theorem congrArg_iterated_zero {S T : Type u} (f : S → T) {a : S} (p : Path a a) :
    Path.congrArg f (iteratedOrbit p 0) = Path.refl (f a) := by
  simp [iteratedOrbit]

end DynamicalPaths
end Computation
end Path
end ComputationalPaths
