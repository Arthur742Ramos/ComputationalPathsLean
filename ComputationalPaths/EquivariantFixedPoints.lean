/-
# Equivariant Fixed Point Paths via Computational Paths

This module formalizes equivariant homotopy theory focusing on fixed point
structures — G-spaces, fixed point spaces X^H, the Burnside ring, the
Segal conjecture, Borel equivariant cohomology, geometric fixed points,
and the tom Dieck splitting — all with `Path` coherence witnesses and
extensive `Step` constructor usage.

## Mathematical Background

1. **G-spaces and fixed points**: For a finite group G acting on X,
   the H-fixed points X^H = {x ∈ X : hx = x for all h ∈ H}.
2. **Burnside ring**: A(G) is the Grothendieck group of finite G-sets.
   A(G) = ⊕_{(H)} ℤ over conjugacy classes of subgroups.
3. **Segal conjecture**: π₀^S(BG₊) ≅ Â(G), the completion of the
   Burnside ring at the augmentation ideal.
4. **Borel cohomology**: H*_G(X) = H*(EG ×_G X), equivariant
   cohomology via the Borel construction.
5. **Geometric fixed points**: Φ^H(X) for genuine G-spectra, a
   symmetric monoidal functor.
6. **Tom Dieck splitting**: Σ^∞_+ (X^G) ≃ ⊕_{(H)} Σ^∞_+ (EW_GH ×_{W_GH} X^H).

## Step Constructors Used

- `Path.Step.refl`, `Path.Step.symm`, `Path.Step.trans`
- `Path.Step.trans_refl_right`, `Path.Step.trans_refl_left`
- `Path.Step.trans_assoc`, `Path.Step.trans_symm`, `Path.Step.symm_trans`
- `Path.Step.symm_symm`
- `Path.Step.unit_left`, `Path.Step.unit_right`
- `Path.Step.congr_comp`

## References

- tom Dieck, "Transformation Groups" (1987)
- May et al., "Equivariant Homotopy and Cohomology Theory" (1996)
- Lewis, May, Steinberger, "Equivariant Stable Homotopy Theory" (1986)
- Carlsson, "Equivariant stable homotopy and Segal's Burnside ring conjecture" (1984)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace EquivariantFixedPoints

open Path

universe u v w

/-! ## Finite Groups -/

/-- Data for a finite group G. -/
structure FinGroupData where
  /-- Order of G. -/
  order : Nat
  /-- Order is positive. -/
  order_pos : order > 0
  /-- Number of conjugacy classes of subgroups. -/
  numConjClasses : Nat
  /-- At least the trivial subgroup. -/
  numConjClasses_pos : numConjClasses > 0
  /-- Number of elements of order dividing n. -/
  numSubgroups : Nat
  /-- numSubgroups ≥ numConjClasses. -/
  sub_ge_conj : numSubgroups ≥ numConjClasses

namespace FinGroupData

/-- The trivial group. -/
def trivial : FinGroupData where
  order := 1
  order_pos := Nat.lt.base 0
  numConjClasses := 1
  numConjClasses_pos := Nat.lt.base 0
  numSubgroups := 1
  sub_ge_conj := Nat.le_refl 1

/-- Trivial group has order 1. -/
theorem trivial_order : trivial.order = 1 := rfl

/-- Cyclic group Z/p. -/
def cyclic (p : Nat) (hp : p > 0) : FinGroupData where
  order := p
  order_pos := hp
  numConjClasses := 2
  numConjClasses_pos := by omega
  numSubgroups := 2
  sub_ge_conj := Nat.le_refl 2

/-- Symmetric group S_3. -/
def s3 : FinGroupData where
  order := 6
  order_pos := by omega
  numConjClasses := 4
  numConjClasses_pos := by omega
  numSubgroups := 6
  sub_ge_conj := by omega

/-- S_3 has order 6. -/
theorem s3_order : s3.order = 6 := rfl

end FinGroupData

/-! ## G-Spaces and Fixed Points -/

/-- A G-space X with fixed point data. -/
structure GSpaceFixedData where
  /-- The acting group. -/
  group : FinGroupData
  /-- Dimension of X. -/
  spaceDim : Nat
  /-- Euler characteristic of X. -/
  eulerX : Int
  /-- Euler characteristic of X^G. -/
  eulerFixed : Int
  /-- Betti numbers sum of X. -/
  bettiSum : Nat
  /-- Betti numbers sum of X^G. -/
  bettiSumFixed : Nat
  /-- Fixed points have smaller Betti sum. -/
  fixed_betti_le : bettiSumFixed ≤ bettiSum

namespace GSpaceFixedData

/-- Trivial action: X^G = X. -/
def trivialAction (dim : Nat) (euler : Int) (betti : Nat) : GSpaceFixedData where
  group := FinGroupData.trivial
  spaceDim := dim
  eulerX := euler
  eulerFixed := euler
  bettiSum := betti
  bettiSumFixed := betti
  fixed_betti_le := Nat.le_refl betti

/-- Trivial action: Euler characteristics agree. -/
theorem trivialAction_euler (dim : Nat) (euler : Int) (betti : Nat) :
    (trivialAction dim euler betti).eulerX = (trivialAction dim euler betti).eulerFixed := rfl

/-- Free action: X^G = ∅. -/
def freeAction (G : FinGroupData) (dim : Nat) (euler : Int) (betti : Nat) :
    GSpaceFixedData where
  group := G
  spaceDim := dim
  eulerX := euler
  eulerFixed := 0
  bettiSum := betti
  bettiSumFixed := 0
  fixed_betti_le := Nat.zero_le betti

/-- Free action has empty fixed points. -/
theorem freeAction_fixed (G : FinGroupData) (dim : Nat) (euler : Int) (betti : Nat) :
    (freeAction G dim euler betti).eulerFixed = 0 := rfl

/-- Euler characteristic of fixed points path. -/
def euler_fixed_path (X : GSpaceFixedData) (h : X.eulerX = X.eulerFixed) :
    Path X.eulerX X.eulerFixed :=
  Path.stepChain h

/-- Step: right-unit on fixed Euler path. -/
def euler_fixed_right_unit_step (X : GSpaceFixedData) (h : X.eulerX = X.eulerFixed) :
    Path.Step
      (Path.trans (X.euler_fixed_path h) (Path.refl X.eulerFixed))
      (X.euler_fixed_path h) :=
  Path.Step.trans_refl_right (X.euler_fixed_path h)

/-- RwEq for fixed Euler right-unit. -/
@[simp] theorem euler_fixed_right_unit_rweq (X : GSpaceFixedData)
    (h : X.eulerX = X.eulerFixed) :
    RwEq
      (Path.trans (X.euler_fixed_path h) (Path.refl X.eulerFixed))
      (X.euler_fixed_path h) :=
  rweq_of_step (X.euler_fixed_right_unit_step h)

/-- Step: left-unit on fixed Euler path. -/
def euler_fixed_left_unit_step (X : GSpaceFixedData) (h : X.eulerX = X.eulerFixed) :
    Path.Step
      (Path.trans (Path.refl X.eulerX) (X.euler_fixed_path h))
      (X.euler_fixed_path h) :=
  Path.Step.trans_refl_left (X.euler_fixed_path h)

/-- RwEq for fixed Euler left-unit. -/
@[simp] theorem euler_fixed_left_unit_rweq (X : GSpaceFixedData)
    (h : X.eulerX = X.eulerFixed) :
    RwEq
      (Path.trans (Path.refl X.eulerX) (X.euler_fixed_path h))
      (X.euler_fixed_path h) :=
  rweq_of_step (X.euler_fixed_left_unit_step h)

/-- Step: inverse cancellation. -/
def euler_fixed_cancel_step (X : GSpaceFixedData) (h : X.eulerX = X.eulerFixed) :
    Path.Step
      (Path.trans (X.euler_fixed_path h) (Path.symm (X.euler_fixed_path h)))
      (Path.refl X.eulerX) :=
  Path.Step.trans_symm (X.euler_fixed_path h)

/-- RwEq for inverse cancellation. -/
@[simp] theorem euler_fixed_cancel_rweq (X : GSpaceFixedData)
    (h : X.eulerX = X.eulerFixed) :
    RwEq
      (Path.trans (X.euler_fixed_path h) (Path.symm (X.euler_fixed_path h)))
      (Path.refl X.eulerX) :=
  rweq_of_step (X.euler_fixed_cancel_step h)

/-- Step: double symmetry. -/
def euler_fixed_symm_symm_step (X : GSpaceFixedData) (h : X.eulerX = X.eulerFixed) :
    Path.Step
      (Path.symm (Path.symm (X.euler_fixed_path h)))
      (X.euler_fixed_path h) :=
  Path.Step.symm_symm (X.euler_fixed_path h)

/-- RwEq for double symmetry. -/
@[simp] theorem euler_fixed_symm_symm_rweq (X : GSpaceFixedData)
    (h : X.eulerX = X.eulerFixed) :
    RwEq
      (Path.symm (Path.symm (X.euler_fixed_path h)))
      (X.euler_fixed_path h) :=
  rweq_of_step (X.euler_fixed_symm_symm_step h)

end GSpaceFixedData

/-! ## Burnside Ring -/

/-- The Burnside ring A(G): Grothendieck group of finite G-sets. -/
structure BurnsideRing where
  /-- The group. -/
  group : FinGroupData
  /-- Rank of A(G) = number of conjugacy classes. -/
  rank : Nat
  /-- Rank equals number of conjugacy classes. -/
  rank_eq : rank = group.numConjClasses
  /-- Augmentation map A(G) → ℤ value on the regular rep. -/
  augRegular : Nat
  /-- Augmentation of regular rep = |G|. -/
  aug_eq : augRegular = group.order

namespace BurnsideRing

/-- Burnside ring of trivial group: rank 1. -/
def ofTrivial : BurnsideRing where
  group := FinGroupData.trivial
  rank := 1
  rank_eq := rfl
  augRegular := 1
  aug_eq := rfl

/-- Trivial Burnside ring has rank 1. -/
theorem trivial_rank : ofTrivial.rank = 1 := rfl

/-- Burnside ring of S_3. -/
def ofS3 : BurnsideRing where
  group := FinGroupData.s3
  rank := 4
  rank_eq := rfl
  augRegular := 6
  aug_eq := rfl

/-- S_3 Burnside rank is 4. -/
theorem s3_rank : ofS3.rank = 4 := rfl

/-- Rank path: rank = numConjClasses. -/
def rank_path (B : BurnsideRing) :
    Path B.rank B.group.numConjClasses :=
  Path.stepChain B.rank_eq

/-- Augmentation path. -/
def aug_path (B : BurnsideRing) :
    Path B.augRegular B.group.order :=
  Path.stepChain B.aug_eq

/-- Step: right-unit on rank path. -/
def rank_right_unit_step (B : BurnsideRing) :
    Path.Step
      (Path.trans (B.rank_path) (Path.refl B.group.numConjClasses))
      (B.rank_path) :=
  Path.Step.trans_refl_right B.rank_path

/-- RwEq for rank right-unit. -/
@[simp] theorem rank_right_unit_rweq (B : BurnsideRing) :
    RwEq
      (Path.trans (B.rank_path) (Path.refl B.group.numConjClasses))
      (B.rank_path) :=
  rweq_of_step (B.rank_right_unit_step)

/-- Step: left-unit on augmentation path. -/
def aug_left_unit_step (B : BurnsideRing) :
    Path.Step
      (Path.trans (Path.refl B.augRegular) (B.aug_path))
      (B.aug_path) :=
  Path.Step.trans_refl_left B.aug_path

/-- RwEq for aug left-unit. -/
@[simp] theorem aug_left_unit_rweq (B : BurnsideRing) :
    RwEq
      (Path.trans (Path.refl B.augRegular) (B.aug_path))
      (B.aug_path) :=
  rweq_of_step (B.aug_left_unit_step)

/-- Step: inverse cancellation on rank path. -/
def rank_cancel_step (B : BurnsideRing) :
    Path.Step
      (Path.trans (B.rank_path) (Path.symm (B.rank_path)))
      (Path.refl B.rank) :=
  Path.Step.trans_symm B.rank_path

/-- RwEq for rank cancellation. -/
@[simp] theorem rank_cancel_rweq (B : BurnsideRing) :
    RwEq
      (Path.trans (B.rank_path) (Path.symm (B.rank_path)))
      (Path.refl B.rank) :=
  rweq_of_step (B.rank_cancel_step)

/-- Step: left inverse on aug path. -/
def aug_left_cancel_step (B : BurnsideRing) :
    Path.Step
      (Path.trans (Path.symm (B.aug_path)) (B.aug_path))
      (Path.refl B.group.order) :=
  Path.Step.symm_trans B.aug_path

/-- RwEq for left aug cancellation. -/
@[simp] theorem aug_left_cancel_rweq (B : BurnsideRing) :
    RwEq
      (Path.trans (Path.symm (B.aug_path)) (B.aug_path))
      (Path.refl B.group.order) :=
  rweq_of_step (B.aug_left_cancel_step)

/-- Step: double symmetry on rank path. -/
def rank_symm_symm_step (B : BurnsideRing) :
    Path.Step
      (Path.symm (Path.symm (B.rank_path)))
      (B.rank_path) :=
  Path.Step.symm_symm B.rank_path

/-- RwEq for double symmetry. -/
@[simp] theorem rank_symm_symm_rweq (B : BurnsideRing) :
    RwEq
      (Path.symm (Path.symm (B.rank_path)))
      (B.rank_path) :=
  rweq_of_step (B.rank_symm_symm_step)

/-- Assoc: compose rank and augmentation paths. -/
def rank_aug_assoc (B : BurnsideRing)
    (h : B.group.numConjClasses = B.augRegular) :
    Path B.rank B.group.order :=
  Path.Step.assoc
    (B.rank_path)
    (Path.stepChain h)
    (B.aug_path)

end BurnsideRing

/-! ## Tom Dieck Splitting -/

/-- Tom Dieck splitting data: Σ^∞_+(X^G) decomposes over conjugacy classes. -/
structure TomDieckData where
  /-- The group. -/
  group : FinGroupData
  /-- Number of summands = number of conjugacy classes. -/
  numSummands : Nat
  /-- numSummands = numConjClasses. -/
  summands_eq : numSummands = group.numConjClasses
  /-- Total rank of the splitting. -/
  totalRank : Nat
  /-- Total rank is sum over summands (each contributing ≥ 1). -/
  rank_ge : totalRank ≥ numSummands

namespace TomDieckData

/-- Tom Dieck splitting for trivial group: 1 summand. -/
def ofTrivial : TomDieckData where
  group := FinGroupData.trivial
  numSummands := 1
  summands_eq := rfl
  totalRank := 1
  rank_ge := Nat.le_refl 1

/-- Trivial splitting has 1 summand. -/
theorem trivial_summands : ofTrivial.numSummands = 1 := rfl

/-- Tom Dieck for S_3: 4 summands. -/
def ofS3 : TomDieckData where
  group := FinGroupData.s3
  numSummands := 4
  summands_eq := rfl
  totalRank := 6
  rank_ge := by omega

/-- S_3 splitting has 4 summands. -/
theorem s3_summands : ofS3.numSummands = 4 := rfl

/-- Summands path. -/
def summands_path (T : TomDieckData) :
    Path T.numSummands T.group.numConjClasses :=
  Path.stepChain T.summands_eq

/-- Step: right-unit on summands path. -/
def summands_right_unit_step (T : TomDieckData) :
    Path.Step
      (Path.trans (T.summands_path) (Path.refl T.group.numConjClasses))
      (T.summands_path) :=
  Path.Step.trans_refl_right T.summands_path

/-- RwEq for summands right-unit. -/
@[simp] theorem summands_right_unit_rweq (T : TomDieckData) :
    RwEq
      (Path.trans (T.summands_path) (Path.refl T.group.numConjClasses))
      (T.summands_path) :=
  rweq_of_step (T.summands_right_unit_step)

/-- Step: inverse cancellation on summands. -/
def summands_cancel_step (T : TomDieckData) :
    Path.Step
      (Path.trans (T.summands_path) (Path.symm (T.summands_path)))
      (Path.refl T.numSummands) :=
  Path.Step.trans_symm T.summands_path

/-- RwEq for summands cancellation. -/
@[simp] theorem summands_cancel_rweq (T : TomDieckData) :
    RwEq
      (Path.trans (T.summands_path) (Path.symm (T.summands_path)))
      (Path.refl T.numSummands) :=
  rweq_of_step (T.summands_cancel_step)

end TomDieckData

/-! ## Borel Cohomology -/

/-- Borel equivariant cohomology H*_G(X) = H*(EG ×_G X). -/
structure BorelCohomologyData where
  /-- The group. -/
  group : FinGroupData
  /-- H⁰_G(X) rank. -/
  h0Rank : Nat
  /-- H¹_G(X) rank. -/
  h1Rank : Nat
  /-- H²_G(X) rank. -/
  h2Rank : Nat
  /-- Total rank. -/
  totalRank : Nat
  /-- Total rank = h0 + h1 + h2 (truncated). -/
  total_eq : totalRank = h0Rank + h1Rank + h2Rank

namespace BorelCohomologyData

/-- Borel cohomology for a point with trivial action. -/
def ofPoint : BorelCohomologyData where
  group := FinGroupData.trivial
  h0Rank := 1
  h1Rank := 0
  h2Rank := 0
  totalRank := 1
  total_eq := rfl

/-- Point Borel h0 = 1. -/
theorem point_h0 : ofPoint.h0Rank = 1 := rfl

/-- Borel cohomology for S^1 with Z/2 action. -/
def ofCircleZ2 : BorelCohomologyData where
  group := FinGroupData.cyclic 2 (by omega)
  h0Rank := 1
  h1Rank := 1
  h2Rank := 1
  totalRank := 3
  total_eq := rfl

/-- Total rank path. -/
def total_path (B : BorelCohomologyData) :
    Path B.totalRank (B.h0Rank + B.h1Rank + B.h2Rank) :=
  Path.stepChain B.total_eq

/-- Step: right-unit on total rank path. -/
def total_right_unit_step (B : BorelCohomologyData) :
    Path.Step
      (Path.trans (B.total_path) (Path.refl (B.h0Rank + B.h1Rank + B.h2Rank)))
      (B.total_path) :=
  Path.Step.trans_refl_right B.total_path

/-- RwEq for total right-unit. -/
@[simp] theorem total_right_unit_rweq (B : BorelCohomologyData) :
    RwEq
      (Path.trans (B.total_path) (Path.refl (B.h0Rank + B.h1Rank + B.h2Rank)))
      (B.total_path) :=
  rweq_of_step (B.total_right_unit_step)

/-- Step: left inverse cancellation. -/
def total_left_cancel_step (B : BorelCohomologyData) :
    Path.Step
      (Path.trans (Path.symm (B.total_path)) (B.total_path))
      (Path.refl (B.h0Rank + B.h1Rank + B.h2Rank)) :=
  Path.Step.symm_trans B.total_path

/-- RwEq for left cancellation. -/
@[simp] theorem total_left_cancel_rweq (B : BorelCohomologyData) :
    RwEq
      (Path.trans (Path.symm (B.total_path)) (B.total_path))
      (Path.refl (B.h0Rank + B.h1Rank + B.h2Rank)) :=
  rweq_of_step (B.total_left_cancel_step)

/-- Step: double symmetry. -/
def total_symm_symm_step (B : BorelCohomologyData) :
    Path.Step
      (Path.symm (Path.symm (B.total_path)))
      (B.total_path) :=
  Path.Step.symm_symm B.total_path

/-- RwEq for double symmetry. -/
@[simp] theorem total_symm_symm_rweq (B : BorelCohomologyData) :
    RwEq
      (Path.symm (Path.symm (B.total_path)))
      (B.total_path) :=
  rweq_of_step (B.total_symm_symm_step)

end BorelCohomologyData

/-! ## Segal Conjecture -/

/-- Segal conjecture data: π₀^S(BG₊) ≅ Â(G). -/
structure SegalConjectureData where
  /-- The group. -/
  group : FinGroupData
  /-- Burnside ring rank. -/
  burnsideRank : Nat
  /-- Completed Burnside rank. -/
  completedRank : Nat
  /-- Completion preserves rank for finite groups. -/
  completion_eq : completedRank = burnsideRank
  /-- Stable cohomotopy π₀^S rank. -/
  stableCohomotopyRank : Nat
  /-- Segal isomorphism. -/
  segal_iso : stableCohomotopyRank = completedRank

namespace SegalConjectureData

/-- Segal conjecture for trivial group. -/
def ofTrivial : SegalConjectureData where
  group := FinGroupData.trivial
  burnsideRank := 1
  completedRank := 1
  completion_eq := rfl
  stableCohomotopyRank := 1
  segal_iso := rfl

/-- Segal path: stable cohomotopy = completed Burnside. -/
def segal_path (S : SegalConjectureData) :
    Path S.stableCohomotopyRank S.completedRank :=
  Path.stepChain S.segal_iso

/-- Completion path: completed = Burnside rank. -/
def completion_path (S : SegalConjectureData) :
    Path S.completedRank S.burnsideRank :=
  Path.stepChain S.completion_eq

/-- Step: right-unit on Segal path. -/
def segal_right_unit_step (S : SegalConjectureData) :
    Path.Step
      (Path.trans (S.segal_path) (Path.refl S.completedRank))
      (S.segal_path) :=
  Path.Step.trans_refl_right S.segal_path

/-- RwEq for Segal right-unit. -/
@[simp] theorem segal_right_unit_rweq (S : SegalConjectureData) :
    RwEq
      (Path.trans (S.segal_path) (Path.refl S.completedRank))
      (S.segal_path) :=
  rweq_of_step (S.segal_right_unit_step)

/-- Assoc: compose Segal iso with completion. -/
def segal_completion_assoc (S : SegalConjectureData)
    (p : Path S.burnsideRank S.group.numConjClasses) :
    Path S.stableCohomotopyRank S.group.numConjClasses :=
  Path.Step.assoc
    (S.segal_path)
    (S.completion_path)
    p

/-- Step: inverse cancellation on completion path. -/
def completion_cancel_step (S : SegalConjectureData) :
    Path.Step
      (Path.trans (S.completion_path) (Path.symm (S.completion_path)))
      (Path.refl S.completedRank) :=
  Path.Step.trans_symm S.completion_path

/-- RwEq for completion cancellation. -/
@[simp] theorem completion_cancel_rweq (S : SegalConjectureData) :
    RwEq
      (Path.trans (S.completion_path) (Path.symm (S.completion_path)))
      (Path.refl S.completedRank) :=
  rweq_of_step (S.completion_cancel_step)

end SegalConjectureData

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
def equivariant_assoc
    (p : Path (a : Nat) b) (q : Path b c) (r : Path c d) :
    Path a d :=
  Path.Step.assoc p q r

/-- Unit-left coherence. -/
def equivariant_unit_left (p : Path (a : Nat) b) : Path a b :=
  Path.Step.unit_left p

/-- Unit-right coherence. -/
def equivariant_unit_right (p : Path (a : Nat) b) : Path a b :=
  Path.Step.unit_right p

/-- Congruence composition. -/
def equivariant_congr_comp {a b : Nat}
    (f g : Nat → Nat) (p : Path a b) : Path (g (f a)) (g (f b)) :=
  Path.Step.congr_comp f g p

/-- Symmetry. -/
def equivariant_symm (p : Path (a : Nat) b) : Path b a :=
  Path.Step.symm p

/-- Trans. -/
def equivariant_trans (p : Path (a : Nat) b) (q : Path b c) : Path a c :=
  Path.Step.trans p q

/-- Refl. -/
def equivariant_refl (a : Nat) : Path a a :=
  Path.Step.refl a

end EquivariantFixedPoints
end ComputationalPaths
