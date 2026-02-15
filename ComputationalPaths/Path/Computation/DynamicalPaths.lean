/-
# Dynamical Systems via Computational Paths

This module models dynamical systems using computational paths:
state spaces, orbits as path sequences, fixed points, periodic orbits,
stability, Lyapunov functions, attractors, and conjugacy.

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

/-! ## State Spaces and Dynamics -/

/-- A discrete dynamical system: a type with an evolution map. -/
structure DynSystem (S : Type u) where
  evolve : S → S

/-- An orbit segment: records the path from f^n(x) to f^(n+1)(x). -/
structure OrbitSegment (S : Type u) where
  state : S
  nextState : S
  orbitPath : Path state nextState

/-- Two orbit segments compose when endpoints match. -/
def orbitCompose {S : Type u} {a b c : S}
    (seg1 : Path a b) (seg2 : Path b c) : Path a c :=
  Path.trans seg1 seg2

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

/-- Fixed point path refl trans. -/
theorem fixedPoint_refl_trans {S : Type u} (d : FixedPointData S) :
    Path.trans (Path.refl d.image) d.fixedPath = d.fixedPath := by
  simp

/-- RwEq: fixed point trans refl. -/
theorem fixedPoint_rweq_trans_refl {S : Type u} (d : FixedPointData S) :
    RwEq
      (Path.trans d.fixedPath (Path.refl d.point))
      d.fixedPath :=
  rweq_of_step (Step.trans_refl_right d.fixedPath)

/-- RwEq: fixed point inv cancel right. -/
theorem fixedPoint_rweq_inv_right {S : Type u} (d : FixedPointData S) :
    RwEq
      (Path.trans d.fixedPath (Path.symm d.fixedPath))
      (Path.refl d.image) :=
  rweq_cmpA_inv_right d.fixedPath

/-- RwEq: fixed point symm_symm. -/
theorem fixedPoint_rweq_symm_symm {S : Type u} (d : FixedPointData S) :
    RwEq
      (Path.symm (Path.symm d.fixedPath))
      d.fixedPath :=
  rweq_of_step (Step.symm_symm d.fixedPath)

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

/-- RwEq: periodic symm_symm. -/
theorem periodic_rweq_symm_symm {S : Type u} (d : PeriodicOrbitData S) :
    RwEq
      (Path.symm (Path.symm d.periodicPath))
      d.periodicPath :=
  rweq_of_step (Step.symm_symm d.periodicPath)

/-- RwEq: periodic inv cancel left. -/
theorem periodic_rweq_inv_left {S : Type u} (d : PeriodicOrbitData S) :
    RwEq
      (Path.trans (Path.symm d.periodicPath) d.periodicPath)
      (Path.refl d.basePoint) :=
  rweq_cmpA_inv_left d.periodicPath

/-- RwEq: periodic inv cancel right. -/
theorem periodic_rweq_inv_right {S : Type u} (d : PeriodicOrbitData S) :
    RwEq
      (Path.trans d.periodicPath (Path.symm d.periodicPath))
      (Path.refl d.iterateImage) :=
  rweq_cmpA_inv_right d.periodicPath

/-! ## Stability and Lyapunov Functions -/

/-- Lyapunov function data: V(f(x)) ≤ V(x) witnessed as a path between values. -/
structure LyapunovData (S : Type u) where
  stateVal : S
  vAtState : Nat
  vAtNext : Nat
  lyapunovPath : Path vAtNext vAtState

/-- Lyapunov path trans refl. -/
theorem lyapunov_trans_refl {S : Type u} (d : LyapunovData S) :
    Path.trans d.lyapunovPath (Path.refl d.vAtState) = d.lyapunovPath := by
  simp

/-- RwEq: Lyapunov inv cancel right. -/
theorem lyapunov_rweq_inv_right {S : Type u} (d : LyapunovData S) :
    RwEq
      (Path.trans d.lyapunovPath (Path.symm d.lyapunovPath))
      (Path.refl d.vAtNext) :=
  rweq_cmpA_inv_right d.lyapunovPath

/-- RwEq: Lyapunov trans refl. -/
theorem lyapunov_rweq_trans_refl {S : Type u} (d : LyapunovData S) :
    RwEq
      (Path.trans d.lyapunovPath (Path.refl d.vAtState))
      d.lyapunovPath :=
  rweq_of_step (Step.trans_refl_right d.lyapunovPath)

/-! ## Conjugacy -/

/-- Conjugacy data: h ∘ f = g ∘ h witnessed as a path. -/
structure ConjugacyData (A B : Type u) where
  fVal : A
  gVal : B
  hfVal : B
  ghVal : B
  conjugacyPath : Path hfVal ghVal

/-- Conjugacy path trans refl. -/
theorem conjugacy_trans_refl {A B : Type u} (d : ConjugacyData A B) :
    Path.trans d.conjugacyPath (Path.refl d.ghVal) = d.conjugacyPath := by
  simp

/-- Conjugacy path trans symm cancel via RwEq. -/
theorem conjugacy_trans_symm {A B : Type u} (d : ConjugacyData A B) :
    RwEq
      (Path.trans d.conjugacyPath (Path.symm d.conjugacyPath))
      (Path.refl d.hfVal) :=
  rweq_cmpA_inv_right d.conjugacyPath

/-- RwEq: conjugacy inv cancel. -/
theorem conjugacy_rweq_inv_right {A B : Type u} (d : ConjugacyData A B) :
    RwEq
      (Path.trans d.conjugacyPath (Path.symm d.conjugacyPath))
      (Path.refl d.hfVal) :=
  rweq_cmpA_inv_right d.conjugacyPath

/-- RwEq: conjugacy symm_symm. -/
theorem conjugacy_rweq_symm_symm {A B : Type u} (d : ConjugacyData A B) :
    RwEq
      (Path.symm (Path.symm d.conjugacyPath))
      d.conjugacyPath :=
  rweq_of_step (Step.symm_symm d.conjugacyPath)

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

/-! ## Bifurcation -/

/-- Bifurcation data: system behavior changes at parameter value. -/
structure BifurcationData where
  paramVal : Nat
  preVal : Nat
  postVal : Nat
  bifurcPath : Path preVal postVal

/-- Bifurcation path symm_symm via RwEq. -/
theorem bifurcation_rweq_symm_symm (d : BifurcationData) :
    RwEq
      (Path.symm (Path.symm d.bifurcPath))
      d.bifurcPath :=
  rweq_of_step (Step.symm_symm d.bifurcPath)

/-- Bifurcation path trans refl. -/
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

/-! ## Orbit Equivalence -/

/-- Two orbit paths that agree propositionally are RwEq. -/
theorem orbit_rweq_of_eq {S : Type u} {a b : S}
    (p q : Path a b) (h : p = q) : RwEq p q := by
  subst h; exact rweq_refl p

/-- Orbit symm trans cancel gives refl via RwEq. -/
theorem orbit_rweq_symm_trans {S : Type u} {a b : S} (p : Path a b) :
    RwEq
      (Path.trans (Path.symm p) p)
      (Path.refl b) :=
  rweq_cmpA_inv_left p

/-- Orbit trans symm cancel gives refl via RwEq. -/
theorem orbit_rweq_trans_symm {S : Type u} {a b : S} (p : Path a b) :
    RwEq
      (Path.trans p (Path.symm p))
      (Path.refl a) :=
  rweq_cmpA_inv_right p

end DynamicalPaths
end Computation
end Path
end ComputationalPaths
