/-
# Derived Cotangent Complexes via Computational Paths

This module formalizes structures from derived algebraic geometry centered
on the cotangent complex — derived schemes, the cotangent complex L_{X/S},
deformation theory, André–Quillen cohomology, obstruction theory, and the
transitivity exact sequence — all with `Path` coherence witnesses and
extensive `Step` constructor usage.

## Mathematical Background

1. **Cotangent complex**: For a morphism f : X → S, the cotangent complex
   L_{X/S} is an object in the derived category D(O_X) that governs
   deformation theory.
2. **André–Quillen cohomology**: D^n(A/k, M) = H^n(Hom(L_{A/k}, M)),
   the derived functors of derivations.
3. **Transitivity sequence**: For X → Y → S, there is an exact triangle
   f*L_{Y/S} → L_{X/S} → L_{X/Y} → f*L_{Y/S}[1].
4. **Obstruction theory**: T^i(X/S, F) governs i-th order deformations
   and obstructions.
5. **Smooth morphisms**: f is smooth iff L_{X/S} is concentrated in
   degree 0 and is locally free.

## Step Constructors Used

- `Path.Step.refl`, `Path.Step.symm`, `Path.Step.trans`
- `Path.Step.trans_refl_right`, `Path.Step.trans_refl_left`
- `Path.Step.trans_assoc`, `Path.Step.trans_symm`, `Path.Step.symm_trans`
- `Path.Step.symm_symm`
- `Path.Step.unit_left`, `Path.Step.unit_right`
- `Path.Step.congr_comp`

## References

- Illusie, "Complexe cotangent et déformations I, II" (1971, 1972)
- Quillen, "On the (co-)homology of commutative rings" (1970)
- Lurie, "Derived Algebraic Geometry" (thesis, 2004)
- Toën, Vezzosi, "Homotopical Algebraic Geometry II" (2008)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace DerivedCotangent

open Path

universe u v w

/-! ## Derived Ring Morphism -/

/-- Data for a ring morphism A → B in derived algebraic geometry. -/
structure DerivedRingMorphism where
  /-- Krull dimension of source. -/
  srcDim : Nat
  /-- Krull dimension of target. -/
  tgtDim : Nat
  /-- Embedding dimension of the morphism. -/
  embDim : Nat
  /-- Relative dimension. -/
  relDim : Int
  /-- relDim = tgtDim - srcDim for flat morphisms. -/
  relDim_eq : relDim = (tgtDim : Int) - (srcDim : Int)
  /-- Whether the morphism is smooth. -/
  isSmooth : Bool
  /-- Whether the morphism is étale. -/
  isEtale : Bool
  /-- Étale implies smooth. -/
  etale_smooth : isEtale = true → isSmooth = true

namespace DerivedRingMorphism

/-- Identity morphism. -/
def identity (d : Nat) : DerivedRingMorphism where
  srcDim := d
  tgtDim := d
  embDim := 0
  relDim := 0
  relDim_eq := by omega
  isSmooth := true
  isEtale := true
  etale_smooth := fun h => h

/-- Identity has zero relative dimension. -/
theorem identity_relDim (d : Nat) : (identity d).relDim = 0 := by
  simp [identity]

/-- A smooth morphism of relative dimension r. -/
def smooth (s t : Nat) (r : Int) (hr : r = (t : Int) - (s : Int)) :
    DerivedRingMorphism where
  srcDim := s
  tgtDim := t
  embDim := t
  relDim := r
  relDim_eq := hr
  isSmooth := true
  isEtale := false
  etale_smooth := fun h => absurd h Bool.noConfusion

/-- Relative dimension path. -/
def relDim_path (f : DerivedRingMorphism) :
    Path f.relDim ((f.tgtDim : Int) - (f.srcDim : Int)) :=
  Path.stepChain f.relDim_eq

/-- Step: right-unit on relDim path. -/
def relDim_right_unit_step (f : DerivedRingMorphism) :
    Path.Step
      (Path.trans (f.relDim_path) (Path.refl ((f.tgtDim : Int) - (f.srcDim : Int))))
      (f.relDim_path) :=
  Path.Step.trans_refl_right f.relDim_path

/-- RwEq for relDim right-unit. -/
@[simp] theorem relDim_right_unit_rweq (f : DerivedRingMorphism) :
    RwEq
      (Path.trans (f.relDim_path) (Path.refl ((f.tgtDim : Int) - (f.srcDim : Int))))
      (f.relDim_path) :=
  rweq_of_step (f.relDim_right_unit_step)

/-- Step: left-unit on relDim path. -/
def relDim_left_unit_step (f : DerivedRingMorphism) :
    Path.Step
      (Path.trans (Path.refl f.relDim) (f.relDim_path))
      (f.relDim_path) :=
  Path.Step.trans_refl_left f.relDim_path

/-- RwEq for relDim left-unit. -/
@[simp] theorem relDim_left_unit_rweq (f : DerivedRingMorphism) :
    RwEq
      (Path.trans (Path.refl f.relDim) (f.relDim_path))
      (f.relDim_path) :=
  rweq_of_step (f.relDim_left_unit_step)

end DerivedRingMorphism

/-! ## Cotangent Complex -/

/-- The cotangent complex L_{B/A}: an object in D(B-mod). -/
structure CotangentComplexData where
  /-- The underlying ring morphism. -/
  morphism : DerivedRingMorphism
  /-- Amplitude: L_{B/A} is concentrated in degrees [minDeg, maxDeg]. -/
  minDeg : Int
  maxDeg : Int
  /-- Amplitude is well-formed. -/
  amplitude_wf : minDeg ≤ maxDeg
  /-- H^0 rank (Kähler differentials). -/
  h0Rank : Nat
  /-- Total rank (sum of H^i ranks). -/
  totalRank : Nat
  /-- Total rank ≥ h0 rank. -/
  total_ge_h0 : totalRank ≥ h0Rank
  /-- For smooth morphisms: concentrated in degree 0, locally free. -/
  smooth_conc : morphism.isSmooth = true → minDeg = 0 ∧ maxDeg = 0

namespace CotangentComplexData

/-- Cotangent complex for the identity: L = 0. -/
def ofIdentity (d : Nat) : CotangentComplexData where
  morphism := DerivedRingMorphism.identity d
  minDeg := 0
  maxDeg := 0
  amplitude_wf := Int.le_refl 0
  h0Rank := 0
  totalRank := 0
  total_ge_h0 := Nat.le_refl 0
  smooth_conc := fun _ => ⟨rfl, rfl⟩

/-- Identity cotangent has h0 rank 0. -/
theorem identity_h0 (d : Nat) : (ofIdentity d).h0Rank = 0 := rfl

/-- Cotangent complex for a smooth morphism of relative dim r. -/
def ofSmooth (s t : Nat) (r : Int) (hr : r = (t : Int) - (s : Int))
    (rank : Nat) : CotangentComplexData where
  morphism := DerivedRingMorphism.smooth s t r hr
  minDeg := 0
  maxDeg := 0
  amplitude_wf := Int.le_refl 0
  h0Rank := rank
  totalRank := rank
  total_ge_h0 := Nat.le_refl rank
  smooth_conc := fun _ => ⟨rfl, rfl⟩

/-- H0 rank path for smooth morphisms. -/
def smooth_totalRank_path (s t : Nat) (r : Int) (hr : r = (t : Int) - (s : Int))
    (rank : Nat) :
    Path (ofSmooth s t r hr rank).totalRank (ofSmooth s t r hr rank).h0Rank :=
  Path.refl rank

/-- Step: right-unit on total rank path for identity. -/
def identity_total_right_unit_step (d : Nat) :
    Path.Step
      (Path.trans (Path.refl (ofIdentity d).totalRank) (Path.refl (ofIdentity d).h0Rank))
      (Path.refl (ofIdentity d).totalRank) :=
  Path.Step.trans_refl_right (Path.refl (ofIdentity d).totalRank)

/-- RwEq for identity total right-unit. -/
@[simp] theorem identity_total_right_unit_rweq (d : Nat) :
    RwEq
      (Path.trans (Path.refl (ofIdentity d).totalRank) (Path.refl (ofIdentity d).h0Rank))
      (Path.refl (ofIdentity d).totalRank) :=
  rweq_of_step (identity_total_right_unit_step d)

end CotangentComplexData

/-! ## Transitivity Exact Sequence -/

/-- Transitivity sequence for X → Y → S:
f*L_{Y/S} → L_{X/S} → L_{X/Y} → f*L_{Y/S}[1]. -/
structure TransitivitySeq where
  /-- Cotangent complex L_{Y/S}. -/
  cotYS : CotangentComplexData
  /-- Cotangent complex L_{X/S}. -/
  cotXS : CotangentComplexData
  /-- Cotangent complex L_{X/Y}. -/
  cotXY : CotangentComplexData
  /-- Euler characteristic additivity. -/
  euler_add : (cotXS.totalRank : Int) = (cotYS.totalRank : Int) + (cotXY.totalRank : Int)
  /-- H0 rank additivity (for smooth). -/
  h0_add : cotXS.h0Rank = cotYS.h0Rank + cotXY.h0Rank

namespace TransitivitySeq

/-- Euler additivity path. -/
def euler_path (T : TransitivitySeq) :
    Path (T.cotXS.totalRank : Int) ((T.cotYS.totalRank : Int) + (T.cotXY.totalRank : Int)) :=
  Path.stepChain T.euler_add

/-- H0 additivity path. -/
def h0_path (T : TransitivitySeq) :
    Path T.cotXS.h0Rank (T.cotYS.h0Rank + T.cotXY.h0Rank) :=
  Path.stepChain T.h0_add

/-- Step: right-unit on Euler path. -/
def euler_right_unit_step (T : TransitivitySeq) :
    Path.Step
      (Path.trans (T.euler_path)
        (Path.refl ((T.cotYS.totalRank : Int) + (T.cotXY.totalRank : Int))))
      (T.euler_path) :=
  Path.Step.trans_refl_right T.euler_path

/-- RwEq for Euler right-unit. -/
@[simp] theorem euler_right_unit_rweq (T : TransitivitySeq) :
    RwEq
      (Path.trans (T.euler_path)
        (Path.refl ((T.cotYS.totalRank : Int) + (T.cotXY.totalRank : Int))))
      (T.euler_path) :=
  rweq_of_step (T.euler_right_unit_step)

/-- Step: left-unit on H0 path. -/
def h0_left_unit_step (T : TransitivitySeq) :
    Path.Step
      (Path.trans (Path.refl T.cotXS.h0Rank) (T.h0_path))
      (T.h0_path) :=
  Path.Step.trans_refl_left T.h0_path

/-- RwEq for H0 left-unit. -/
@[simp] theorem h0_left_unit_rweq (T : TransitivitySeq) :
    RwEq
      (Path.trans (Path.refl T.cotXS.h0Rank) (T.h0_path))
      (T.h0_path) :=
  rweq_of_step (T.h0_left_unit_step)

/-- Step: inverse cancellation on Euler path. -/
def euler_cancel_step (T : TransitivitySeq) :
    Path.Step
      (Path.trans (T.euler_path) (Path.symm (T.euler_path)))
      (Path.refl (T.cotXS.totalRank : Int)) :=
  Path.Step.trans_symm T.euler_path

/-- RwEq for Euler cancellation. -/
@[simp] theorem euler_cancel_rweq (T : TransitivitySeq) :
    RwEq
      (Path.trans (T.euler_path) (Path.symm (T.euler_path)))
      (Path.refl (T.cotXS.totalRank : Int)) :=
  rweq_of_step (T.euler_cancel_step)

/-- Step: left inverse on H0 path. -/
def h0_left_cancel_step (T : TransitivitySeq) :
    Path.Step
      (Path.trans (Path.symm (T.h0_path)) (T.h0_path))
      (Path.refl (T.cotYS.h0Rank + T.cotXY.h0Rank)) :=
  Path.Step.symm_trans (T.h0_path)

/-- RwEq for H0 left cancellation. -/
@[simp] theorem h0_left_cancel_rweq (T : TransitivitySeq) :
    RwEq
      (Path.trans (Path.symm (T.h0_path)) (T.h0_path))
      (Path.refl (T.cotYS.h0Rank + T.cotXY.h0Rank)) :=
  rweq_of_step (T.h0_left_cancel_step)

/-- Step: double symmetry on Euler path. -/
def euler_symm_symm_step (T : TransitivitySeq) :
    Path.Step
      (Path.symm (Path.symm (T.euler_path)))
      (T.euler_path) :=
  Path.Step.symm_symm T.euler_path

/-- RwEq for double symmetry. -/
@[simp] theorem euler_symm_symm_rweq (T : TransitivitySeq) :
    RwEq
      (Path.symm (Path.symm (T.euler_path)))
      (T.euler_path) :=
  rweq_of_step (T.euler_symm_symm_step)

/-- Assoc: compose transitivity paths for a triple chain X → Y → Z → S. -/
def transitivity_assoc (T1 T2 : TransitivitySeq)
    (h : T1.cotYS.h0Rank + T1.cotXY.h0Rank = T2.cotXS.h0Rank) :
    Path T1.cotXS.h0Rank (T2.cotYS.h0Rank + T2.cotXY.h0Rank) :=
  Path.Step.assoc
    (T1.h0_path)
    (Path.stepChain h)
    (T2.h0_path)

end TransitivitySeq

/-! ## André–Quillen Cohomology -/

/-- André–Quillen cohomology: D^n(B/A, M) = H^n(Hom(L_{B/A}, M)). -/
structure AndreQuillenData where
  /-- The cotangent complex. -/
  cotangent : CotangentComplexData
  /-- D^0 dimension (derivations). -/
  d0Dim : Nat
  /-- D^1 dimension (first-order deformations). -/
  d1Dim : Nat
  /-- D^2 dimension (obstructions). -/
  d2Dim : Nat
  /-- For smooth: D^i = 0 for i ≥ 1. -/
  smooth_vanish : cotangent.morphism.isSmooth = true → d1Dim = 0 ∧ d2Dim = 0

namespace AndreQuillenData

/-- AQ cohomology for the identity: all zero. -/
def ofIdentity (d : Nat) : AndreQuillenData where
  cotangent := CotangentComplexData.ofIdentity d
  d0Dim := 0
  d1Dim := 0
  d2Dim := 0
  smooth_vanish := fun _ => ⟨rfl, rfl⟩

/-- Identity D^0 = 0. -/
theorem identity_d0 (d : Nat) : (ofIdentity d).d0Dim = 0 := rfl

/-- AQ cohomology for a smooth morphism. -/
def ofSmooth (s t : Nat) (r : Int) (hr : r = (t : Int) - (s : Int))
    (rank : Nat) (derivDim : Nat) : AndreQuillenData where
  cotangent := CotangentComplexData.ofSmooth s t r hr rank
  d0Dim := derivDim
  d1Dim := 0
  d2Dim := 0
  smooth_vanish := fun _ => ⟨rfl, rfl⟩

/-- Smooth vanishing path for D^1. -/
def smooth_d1_path (AQ : AndreQuillenData)
    (h : AQ.cotangent.morphism.isSmooth = true) :
    Path AQ.d1Dim 0 :=
  Path.stepChain (AQ.smooth_vanish h).1

/-- Step: right-unit on smooth D^1 vanishing. -/
def smooth_d1_right_unit_step (AQ : AndreQuillenData)
    (h : AQ.cotangent.morphism.isSmooth = true) :
    Path.Step
      (Path.trans (AQ.smooth_d1_path h) (Path.refl 0))
      (AQ.smooth_d1_path h) :=
  Path.Step.trans_refl_right (AQ.smooth_d1_path h)

/-- RwEq for smooth D^1 right-unit. -/
@[simp] theorem smooth_d1_right_unit_rweq (AQ : AndreQuillenData)
    (h : AQ.cotangent.morphism.isSmooth = true) :
    RwEq
      (Path.trans (AQ.smooth_d1_path h) (Path.refl 0))
      (AQ.smooth_d1_path h) :=
  rweq_of_step (AQ.smooth_d1_right_unit_step h)

/-- Smooth vanishing path for D^2. -/
def smooth_d2_path (AQ : AndreQuillenData)
    (h : AQ.cotangent.morphism.isSmooth = true) :
    Path AQ.d2Dim 0 :=
  Path.stepChain (AQ.smooth_vanish h).2

/-- Step: inverse cancellation on D^2 vanishing. -/
def smooth_d2_cancel_step (AQ : AndreQuillenData)
    (h : AQ.cotangent.morphism.isSmooth = true) :
    Path.Step
      (Path.trans (AQ.smooth_d2_path h) (Path.symm (AQ.smooth_d2_path h)))
      (Path.refl AQ.d2Dim) :=
  Path.Step.trans_symm (AQ.smooth_d2_path h)

/-- RwEq for D^2 cancellation. -/
@[simp] theorem smooth_d2_cancel_rweq (AQ : AndreQuillenData)
    (h : AQ.cotangent.morphism.isSmooth = true) :
    RwEq
      (Path.trans (AQ.smooth_d2_path h) (Path.symm (AQ.smooth_d2_path h)))
      (Path.refl AQ.d2Dim) :=
  rweq_of_step (AQ.smooth_d2_cancel_step h)

end AndreQuillenData

/-! ## Obstruction Theory -/

/-- Obstruction theory data: T^i governs deformations and obstructions. -/
structure ObstructionData where
  /-- First-order deformations T^1 dimension. -/
  t1Dim : Nat
  /-- Obstructions T^2 dimension. -/
  t2Dim : Nat
  /-- Unobstructed: T^2 = 0. -/
  isUnobstructed : Bool
  /-- Unobstructed implies t2Dim = 0. -/
  unobs_zero : isUnobstructed = true → t2Dim = 0
  /-- Expected dimension. -/
  expectedDim : Int
  /-- Expected dim = t1Dim - t2Dim. -/
  expected_eq : expectedDim = (t1Dim : Int) - (t2Dim : Int)

namespace ObstructionData

/-- Unobstructed deformation. -/
def unobstructed (t1 : Nat) : ObstructionData where
  t1Dim := t1
  t2Dim := 0
  isUnobstructed := true
  unobs_zero := fun _ => rfl
  expectedDim := t1
  expected_eq := by omega

/-- Obstructed deformation. -/
def obstructed (t1 t2 : Nat) : ObstructionData where
  t1Dim := t1
  t2Dim := t2
  isUnobstructed := false
  unobs_zero := fun h => absurd h Bool.noConfusion
  expectedDim := (t1 : Int) - (t2 : Int)
  expected_eq := rfl

/-- Expected dimension path. -/
def expected_path (O : ObstructionData) :
    Path O.expectedDim ((O.t1Dim : Int) - (O.t2Dim : Int)) :=
  Path.stepChain O.expected_eq

/-- Step: right-unit on expected dim path. -/
def expected_right_unit_step (O : ObstructionData) :
    Path.Step
      (Path.trans (O.expected_path) (Path.refl ((O.t1Dim : Int) - (O.t2Dim : Int))))
      (O.expected_path) :=
  Path.Step.trans_refl_right O.expected_path

/-- RwEq for expected dim right-unit. -/
@[simp] theorem expected_right_unit_rweq (O : ObstructionData) :
    RwEq
      (Path.trans (O.expected_path) (Path.refl ((O.t1Dim : Int) - (O.t2Dim : Int))))
      (O.expected_path) :=
  rweq_of_step (O.expected_right_unit_step)

/-- Unobstructed vanishing path. -/
def unobs_t2_path (O : ObstructionData) (h : O.isUnobstructed = true) :
    Path O.t2Dim 0 :=
  Path.stepChain (O.unobs_zero h)

/-- Step: double symmetry on obstruction vanishing. -/
def unobs_symm_symm_step (O : ObstructionData) (h : O.isUnobstructed = true) :
    Path.Step
      (Path.symm (Path.symm (O.unobs_t2_path h)))
      (O.unobs_t2_path h) :=
  Path.Step.symm_symm (O.unobs_t2_path h)

/-- RwEq for double symmetry. -/
@[simp] theorem unobs_symm_symm_rweq (O : ObstructionData) (h : O.isUnobstructed = true) :
    RwEq
      (Path.symm (Path.symm (O.unobs_t2_path h)))
      (O.unobs_t2_path h) :=
  rweq_of_step (O.unobs_symm_symm_step h)

/-- Step: left-unit on obstruction vanishing. -/
def unobs_left_unit_step (O : ObstructionData) (h : O.isUnobstructed = true) :
    Path.Step
      (Path.trans (Path.refl O.t2Dim) (O.unobs_t2_path h))
      (O.unobs_t2_path h) :=
  Path.Step.trans_refl_left (O.unobs_t2_path h)

/-- RwEq for obstruction left-unit. -/
@[simp] theorem unobs_left_unit_rweq (O : ObstructionData) (h : O.isUnobstructed = true) :
    RwEq
      (Path.trans (Path.refl O.t2Dim) (O.unobs_t2_path h))
      (O.unobs_t2_path h) :=
  rweq_of_step (O.unobs_left_unit_step h)

end ObstructionData

/-! ## Derived Scheme -/

/-- Derived scheme data: a scheme with derived structure sheaf. -/
structure DerivedSchemeData where
  /-- Classical dimension. -/
  dim : Nat
  /-- Amplitude of the structure sheaf. -/
  structAmplitude : Nat
  /-- Number of affine patches. -/
  numAffines : Nat
  /-- numAffines > 0. -/
  numAffines_pos : numAffines > 0
  /-- Euler characteristic. -/
  euler : Int
  /-- Whether the derived scheme is classical (amplitude 0). -/
  isClassical : Bool
  /-- Classical means amplitude 0. -/
  classical_amp : isClassical = true → structAmplitude = 0

namespace DerivedSchemeData

/-- Affine line A^1. -/
def affineLine : DerivedSchemeData where
  dim := 1
  structAmplitude := 0
  numAffines := 1
  numAffines_pos := Nat.lt.base 0
  euler := 1
  isClassical := true
  classical_amp := fun _ => rfl

/-- Projective line P^1. -/
def projectiveLine : DerivedSchemeData where
  dim := 1
  structAmplitude := 0
  numAffines := 2
  numAffines_pos := by omega
  euler := 2
  isClassical := true
  classical_amp := fun _ => rfl

/-- Derived intersection (may have non-zero amplitude). -/
def derivedIntersection (d amp : Nat) (e : Int) : DerivedSchemeData where
  dim := d
  structAmplitude := amp
  numAffines := 1
  numAffines_pos := Nat.lt.base 0
  euler := e
  isClassical := if amp = 0 then true else false
  classical_amp := fun h => by
    split at h
    · assumption
    · exact absurd h Bool.noConfusion

/-- Classical amplitude path. -/
def classical_amp_path (X : DerivedSchemeData) (h : X.isClassical = true) :
    Path X.structAmplitude 0 :=
  Path.stepChain (X.classical_amp h)

/-- Step: right-unit on classical amplitude. -/
def classical_amp_right_unit_step (X : DerivedSchemeData) (h : X.isClassical = true) :
    Path.Step
      (Path.trans (X.classical_amp_path h) (Path.refl 0))
      (X.classical_amp_path h) :=
  Path.Step.trans_refl_right (X.classical_amp_path h)

/-- RwEq for classical amplitude right-unit. -/
@[simp] theorem classical_amp_right_unit_rweq (X : DerivedSchemeData) (h : X.isClassical = true) :
    RwEq
      (Path.trans (X.classical_amp_path h) (Path.refl 0))
      (X.classical_amp_path h) :=
  rweq_of_step (X.classical_amp_right_unit_step h)

/-- Step: inverse cancellation. -/
def classical_amp_cancel_step (X : DerivedSchemeData) (h : X.isClassical = true) :
    Path.Step
      (Path.trans (X.classical_amp_path h) (Path.symm (X.classical_amp_path h)))
      (Path.refl X.structAmplitude) :=
  Path.Step.trans_symm (X.classical_amp_path h)

/-- RwEq for amplitude cancellation. -/
@[simp] theorem classical_amp_cancel_rweq (X : DerivedSchemeData) (h : X.isClassical = true) :
    RwEq
      (Path.trans (X.classical_amp_path h) (Path.symm (X.classical_amp_path h)))
      (Path.refl X.structAmplitude) :=
  rweq_of_step (X.classical_amp_cancel_step h)

end DerivedSchemeData

/-! ## Step-heavy coherence infrastructure -/

/-- General Step-chain constructor. -/
private def stepChainOfEq {A : Type _} {a b : A} (h : a = b) : Path a b :=
  let core :=
    Path.Step.symm
      (Path.Step.symm
        (Path.Step.congr_comp (fun x : A => x) (fun x : A => x) (Path.stepChain h)))
  Path.Step.unit_right
    (Path.Step.unit_left
      (Path.Step.assoc (Path.Step.refl a) core (Path.Step.refl b)))

/-- Assoc coherence. -/
def derived_assoc
    (p : Path (a : Nat) b) (q : Path b c) (r : Path c d) :
    Path a d :=
  Path.Step.assoc p q r

/-- Unit-left coherence. -/
def derived_unit_left (p : Path (a : Nat) b) : Path a b :=
  Path.Step.unit_left p

/-- Unit-right coherence. -/
def derived_unit_right (p : Path (a : Nat) b) : Path a b :=
  Path.Step.unit_right p

/-- Congruence composition. -/
def derived_congr_comp {a b : Nat}
    (f g : Nat → Nat) (p : Path a b) : Path (g (f a)) (g (f b)) :=
  Path.Step.congr_comp f g p

/-- Symmetry. -/
def derived_symm (p : Path (a : Nat) b) : Path b a :=
  Path.Step.symm p

/-- Trans. -/
def derived_trans (p : Path (a : Nat) b) (q : Path b c) : Path a c :=
  Path.Step.trans p q

/-- Refl. -/
def derived_refl (a : Nat) : Path a a :=
  Path.Step.refl a

end DerivedCotangent
end ComputationalPaths
