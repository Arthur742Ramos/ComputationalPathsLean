/-
# Descriptive Set Theory via Computational Paths (Deep)

This module provides a large, path-centric scaffold for descriptive set theory:

- Borel hierarchy levels and duality
- analytic and coanalytic pointclasses
- Wadge reducibility coding
- determinacy interfaces
- perfect set property profiles
- Baire category bookkeeping
- Cantor-Bendixson decomposition states
- Suslin operation codes
- effective descriptive set-theoretic encodings

The development is intentionally computational-path oriented: statements are
recorded as `Path` equalities whenever possible, and path composition/symmetry
is used for coherence lemmas.
-/

import ComputationalPaths.Path.Basic

set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Algebra.DescriptiveSetTheoryDeep

open ComputationalPaths.Path

/-! ## Path primitives over natural-number encodings -/

def natAtomPath {m n : Nat} (h : m = n) : Path m n :=
  Path.mk [Step.mk m n h] h

@[simp] def natAtomPath_toEq {m n : Nat} (h : m = n) :
    Path.toEq (natAtomPath h) = h := rfl

@[simp] def natAtomPath_steps {m n : Nat} (h : m = n) :
    (natAtomPath h).steps = [Step.mk m n h] := rfl

@[simp] def natAtomPath_symm {m n : Nat} (h : m = n) :
    Path.symm (natAtomPath h) = natAtomPath h.symm := by
  cases h
  rfl

@[simp] def natAtomPath_symm_symm {m n : Nat} (h : m = n) :
    Path.symm (Path.symm (natAtomPath h)) = natAtomPath h := by
  cases h; rfl

def natPath_trans_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

def natPath_trans_refl_left {a b : Nat} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

def natPath_trans_refl_right {a b : Nat} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

def natPath_congr_succ {m n : Nat} (p : Path m n) :
    Path (Nat.succ m) (Nat.succ n) :=
  Path.congrArg Nat.succ p

def natPath_congr_double {m n : Nat} (p : Path m n) :
    Path (m + m) (n + n) :=
  Path.congrArg (fun t => t + t) p

/-! ## Borel hierarchy -/

inductive BorelLevel : Type where
  | openLevel : BorelLevel
  | closedLevel : BorelLevel
  | sigma : Nat → BorelLevel
  | pi : Nat → BorelLevel
  deriving DecidableEq, Repr

def borelRank : BorelLevel → Nat
  | .openLevel => 0
  | .closedLevel => 0
  | .sigma n => n + 1
  | .pi n => n + 1

def borelTag : BorelLevel → Nat
  | .openLevel => 0
  | .closedLevel => 1
  | .sigma _ => 2
  | .pi _ => 3

def dualLevel : BorelLevel → BorelLevel
  | .openLevel => .closedLevel
  | .closedLevel => .openLevel
  | .sigma n => .pi n
  | .pi n => .sigma n

def sigmaLift (n : Nat) : BorelLevel := .sigma (n + 1)
def piLift (n : Nat) : BorelLevel := .pi (n + 1)

def borelRank_open : Path (borelRank .openLevel) 0 :=
  Path.refl 0

def borelRank_closed : Path (borelRank .closedLevel) 0 :=
  Path.refl 0

def borelRank_sigma (n : Nat) : Path (borelRank (.sigma n)) (n + 1) :=
  Path.refl (n + 1)

def borelRank_pi (n : Nat) : Path (borelRank (.pi n)) (n + 1) :=
  Path.refl (n + 1)

def borelTag_open : Path (borelTag .openLevel) 0 :=
  Path.refl 0

def borelTag_closed : Path (borelTag .closedLevel) 1 :=
  Path.refl 1

def dual_open : Path (dualLevel .openLevel) BorelLevel.closedLevel :=
  Path.refl BorelLevel.closedLevel

def dual_closed : Path (dualLevel .closedLevel) BorelLevel.openLevel :=
  Path.refl BorelLevel.openLevel

def dual_sigma (n : Nat) : Path (dualLevel (.sigma n)) (BorelLevel.pi n) :=
  Path.refl (BorelLevel.pi n)

def dual_pi (n : Nat) : Path (dualLevel (.pi n)) (BorelLevel.sigma n) :=
  Path.refl (BorelLevel.sigma n)

def dual_involutive (L : BorelLevel) :
    Path (dualLevel (dualLevel L)) L := by
  cases L <;> exact Path.refl _

def dual_rank_preserved (L : BorelLevel) :
    Path (borelRank (dualLevel L)) (borelRank L) := by
  cases L <;> exact Path.refl _

def sigmaLift_rank (n : Nat) :
    Path (borelRank (sigmaLift n)) (n + 2) :=
  Path.refl (n + 2)

def piLift_rank (n : Nat) :
    Path (borelRank (piLift n)) (n + 2) :=
  Path.refl (n + 2)

/-! ## Analytic and coanalytic pointclasses -/

inductive Pointclass : Type where
  | borel : BorelLevel → Pointclass
  | analytic : Pointclass
  | coanalytic : Pointclass
  | projective : Nat → Pointclass
  deriving DecidableEq, Repr

def pointclassRank : Pointclass → Nat
  | .borel L => borelRank L
  | .analytic => 1
  | .coanalytic => 1
  | .projective n => n + 2

def pointclassDual : Pointclass → Pointclass
  | .borel L => .borel (dualLevel L)
  | .analytic => .coanalytic
  | .coanalytic => .analytic
  | .projective n => .projective n

def isProjective : Pointclass → Bool
  | .projective _ => true
  | _ => false

def pointclassRank_analytic :
    Path (pointclassRank .analytic) 1 :=
  Path.refl 1

def pointclassRank_coanalytic :
    Path (pointclassRank .coanalytic) 1 :=
  Path.refl 1

def pointclassRank_projective (n : Nat) :
    Path (pointclassRank (.projective n)) (n + 2) :=
  Path.refl (n + 2)

def pointclassDual_analytic :
    Path (pointclassDual .analytic) Pointclass.coanalytic :=
  Path.refl Pointclass.coanalytic

def pointclassDual_coanalytic :
    Path (pointclassDual .coanalytic) Pointclass.analytic :=
  Path.refl Pointclass.analytic

def pointclassDual_borel (L : BorelLevel) :
    Path (pointclassDual (.borel L)) (Pointclass.borel (dualLevel L)) :=
  Path.refl (Pointclass.borel (dualLevel L))

def pointclassDual_projective (n : Nat) :
    Path (pointclassDual (.projective n)) (Pointclass.projective n) :=
  Path.refl (Pointclass.projective n)

def pointclassDual_involutive (P : Pointclass) :
    Path (pointclassDual (pointclassDual P)) P := by
  cases P with
  | borel L => cases L <;> exact Path.refl _
  | analytic => exact Path.refl _
  | coanalytic => exact Path.refl _
  | projective n => exact Path.refl _

def pointclassDual_rank_preserved (P : Pointclass) :
    Path (pointclassRank (pointclassDual P)) (pointclassRank P) := by
  cases P with
  | borel L => cases L <;> exact Path.refl _
  | analytic => exact Path.refl _
  | coanalytic => exact Path.refl _
  | projective n => exact Path.refl _

def projective_flag_true (n : Nat) :
    Path (isProjective (.projective n)) true :=
  Path.refl true

def projective_flag_false_analytic :
    Path (isProjective .analytic) false :=
  Path.refl false

def projective_flag_false_coanalytic :
    Path (isProjective .coanalytic) false :=
  Path.refl false

/-! ## Wadge reducibility encoding -/

structure WadgeCode where
  sourceRank : Nat
  targetRank : Nat
  reducible : Bool
  Sym : Nat
  Gam : Nat

def wadgeWitness (W : WadgeCode) : Nat :=
  W.Sym + W.Gam

def wadgeReflexive (n : Nat) : WadgeCode where
  sourceRank := n
  targetRank := n
  reducible := true
  Sym := n
  Gam := 0

def wadgeCompose (A B : WadgeCode) : WadgeCode where
  sourceRank := A.sourceRank
  targetRank := B.targetRank
  reducible := A.reducible && B.reducible
  Sym := wadgeWitness A
  Gam := wadgeWitness B

def wadgeReflexive_source (n : Nat) :
    Path (wadgeReflexive n).sourceRank n :=
  Path.refl n

def wadgeReflexive_target (n : Nat) :
    Path (wadgeReflexive n).targetRank n :=
  Path.refl n

def wadgeReflexive_reducible (n : Nat) :
    Path (wadgeReflexive n).reducible true :=
  Path.refl true

def wadgeReflexive_witness (n : Nat) :
    Path (wadgeWitness (wadgeReflexive n)) n :=
  Path.refl n

def wadgeCompose_source (A B : WadgeCode) :
    Path (wadgeCompose A B).sourceRank A.sourceRank :=
  Path.refl A.sourceRank

def wadgeCompose_target (A B : WadgeCode) :
    Path (wadgeCompose A B).targetRank B.targetRank :=
  Path.refl B.targetRank

def wadgeCompose_reducible (A B : WadgeCode) :
    Path (wadgeCompose A B).reducible (A.reducible && B.reducible) :=
  Path.refl (A.reducible && B.reducible)

def wadgeCompose_witness (A B : WadgeCode) :
    Path (wadgeWitness (wadgeCompose A B))
      (wadgeWitness A + wadgeWitness B) :=
  Path.refl (wadgeWitness A + wadgeWitness B)

def wadgeCompose_assoc_source (A B C : WadgeCode) :
    Path (wadgeCompose (wadgeCompose A B) C).sourceRank A.sourceRank :=
  Path.refl A.sourceRank

def wadgeCompose_assoc_target (A B C : WadgeCode) :
    Path (wadgeCompose A (wadgeCompose B C)).targetRank C.targetRank :=
  Path.refl C.targetRank

def wadgeWitness_path_chain (A B : WadgeCode) :
    Path (wadgeWitness (wadgeCompose A B))
      (wadgeWitness A + wadgeWitness B) := by
  exact Path.trans
    (Path.refl (wadgeWitness (wadgeCompose A B)))
    (Path.refl (wadgeWitness A + wadgeWitness B))

/-! ## Determinacy scaffolding -/

inductive Player : Type where
  | first : Player
  | second : Player
  deriving DecidableEq, Repr

def dualPlayer : Player → Player
  | .first => .second
  | .second => .first

structure DeterminacyGame where
  length : Nat
  payoffRank : Nat
  winner : Player

def flipGame (G : DeterminacyGame) : DeterminacyGame where
  length := G.length
  payoffRank := G.payoffRank
  winner := dualPlayer G.winner

def strategyRank (G : DeterminacyGame) : Nat :=
  G.length + G.payoffRank

def determinedFlag (G : DeterminacyGame) : Bool := true

def dualPlayer_involutive (p : Player) :
    Path (dualPlayer (dualPlayer p)) p := by
  cases p <;> exact Path.refl _

def flipGame_length (G : DeterminacyGame) :
    Path (flipGame G).length G.length :=
  Path.refl G.length

def flipGame_payoff (G : DeterminacyGame) :
    Path (flipGame G).payoffRank G.payoffRank :=
  Path.refl G.payoffRank

def flipGame_winner (G : DeterminacyGame) :
    Path (flipGame G).winner (dualPlayer G.winner) :=
  Path.refl (dualPlayer G.winner)

def flipGame_involutive (G : DeterminacyGame) :
    Path (flipGame (flipGame G)) G := by
  cases G with
  | mk len rank win =>
      cases win <;> exact Path.refl _

def determinedFlag_true (G : DeterminacyGame) :
    Path (determinedFlag G) true :=
  Path.refl true

def strategyRank_flip (G : DeterminacyGame) :
    Path (strategyRank (flipGame G)) (strategyRank G) :=
  Path.refl (strategyRank G)

def strategyRank_congr (G H : DeterminacyGame) (p : Path G H) :
    Path (strategyRank G) (strategyRank H) :=
  Path.congrArg strategyRank p

/-! ## Perfect set property -/

structure PerfectSetProfile where
  rank : Nat
  hasPerfectCore : Bool
  hasCountablePart : Bool

def perfectSetProperty (P : PerfectSetProfile) : Bool :=
  P.hasPerfectCore

def perfectKernelRank (P : PerfectSetProfile) : Nat :=
  if P.hasPerfectCore then P.rank + 1 else 0

def perfectSetProperty_def (P : PerfectSetProfile) :
    Path (perfectSetProperty P) P.hasPerfectCore :=
  Path.refl P.hasPerfectCore

def perfectKernelRank_yes (n : Nat) :
    Path (perfectKernelRank ⟨n, true, false⟩) (n + 1) :=
  Path.refl (n + 1)

def perfectKernelRank_no (n : Nat) :
    Path (perfectKernelRank ⟨n, false, true⟩) 0 :=
  Path.refl 0

def perfectSetProperty_true_rank (n : Nat) :
    Path (perfectSetProperty ⟨n, true, false⟩) true :=
  Path.refl true

def perfectSetProperty_false_rank (n : Nat) :
    Path (perfectSetProperty ⟨n, false, true⟩) false :=
  Path.refl false

def perfect_kernel_congr (P Q : PerfectSetProfile) (p : Path P Q) :
    Path (perfectKernelRank P) (perfectKernelRank Q) :=
  Path.congrArg perfectKernelRank p

/-! ## Baire category bookkeeping -/

structure CategoryProfile where
  meagerRank : Nat
  comeagerRank : Nat
  denseOpenCount : Nat
  residualRank : Nat

def meagerScore (C : CategoryProfile) : Nat :=
  C.meagerRank + C.denseOpenCount

def comeagerScore (C : CategoryProfile) : Nat :=
  C.comeagerRank + C.residualRank

def baireBalance (C : CategoryProfile) : Nat :=
  comeagerScore C + meagerScore C

def meagerScore_def (C : CategoryProfile) :
    Path (meagerScore C) (C.meagerRank + C.denseOpenCount) :=
  Path.refl (C.meagerRank + C.denseOpenCount)

def comeagerScore_def (C : CategoryProfile) :
    Path (comeagerScore C) (C.comeagerRank + C.residualRank) :=
  Path.refl (C.comeagerRank + C.residualRank)

def baireBalance_def (C : CategoryProfile) :
    Path (baireBalance C) (comeagerScore C + meagerScore C) :=
  Path.refl (comeagerScore C + meagerScore C)

def baireBalance_zero :
    Path (baireBalance ⟨0, 0, 0, 0⟩) 0 :=
  Path.refl 0

def meagerScore_congr (C D : CategoryProfile) (p : Path C D) :
    Path (meagerScore C) (meagerScore D) :=
  Path.congrArg meagerScore p

def comeagerScore_congr (C D : CategoryProfile) (p : Path C D) :
    Path (comeagerScore C) (comeagerScore D) :=
  Path.congrArg comeagerScore p

def baireBalance_congr (C D : CategoryProfile) (p : Path C D) :
    Path (baireBalance C) (baireBalance D) :=
  Path.congrArg baireBalance p

def baireBalance_trans_symm (C : CategoryProfile) :
    Path.trans (Path.refl (baireBalance C)) (Path.refl (baireBalance C)) =
      Path.refl (baireBalance C) := by
  simp

/-! ## Cantor-Bendixson decomposition -/

structure CantorBendixsonState where
  derivativeStage : Nat
  perfectKernel : Nat
  scatteredPart : Nat

def cbStep (S : CantorBendixsonState) : CantorBendixsonState where
  derivativeStage := S.derivativeStage + 1
  perfectKernel := S.perfectKernel
  scatteredPart := S.scatteredPart

def cbRank (S : CantorBendixsonState) : Nat :=
  S.derivativeStage + S.perfectKernel + S.scatteredPart

def cbStep_stage (S : CantorBendixsonState) :
    Path (cbStep S).derivativeStage (S.derivativeStage + 1) :=
  Path.refl (S.derivativeStage + 1)

def cbStep_kernel (S : CantorBendixsonState) :
    Path (cbStep S).perfectKernel S.perfectKernel :=
  Path.refl S.perfectKernel

def cbStep_scattered (S : CantorBendixsonState) :
    Path (cbStep S).scatteredPart S.scatteredPart :=
  Path.refl S.scatteredPart

def cbRank_def (S : CantorBendixsonState) :
    Path (cbRank S) (S.derivativeStage + S.perfectKernel + S.scatteredPart) :=
  Path.refl (S.derivativeStage + S.perfectKernel + S.scatteredPart)

def cbRank_step (S : CantorBendixsonState) :
    Path (cbRank (cbStep S))
      ((S.derivativeStage + 1) + S.perfectKernel + S.scatteredPart) :=
  Path.refl ((S.derivativeStage + 1) + S.perfectKernel + S.scatteredPart)

def cbStep_congr (S T : CantorBendixsonState) (p : Path S T) :
    Path (cbStep S) (cbStep T) :=
  Path.congrArg cbStep p

def cbRank_congr (S T : CantorBendixsonState) (p : Path S T) :
    Path (cbRank S) (cbRank T) :=
  Path.congrArg cbRank p

/-! ## Suslin operation coding -/

structure SuslinCode where
  treeHeight : Nat
  branchBound : Nat
  Sym : Nat
  Gam : Nat

def suslinIndex (S : SuslinCode) : Nat :=
  S.treeHeight + S.branchBound + S.Sym + S.Gam

def suslinNormalize (S : SuslinCode) : SuslinCode where
  treeHeight := S.treeHeight
  branchBound := S.branchBound
  Sym := S.Sym
  Gam := S.Gam

def suslinIterate (n : Nat) (S : SuslinCode) : SuslinCode where
  treeHeight := S.treeHeight + n
  branchBound := S.branchBound
  Sym := S.Sym
  Gam := S.Gam

def suslinIndex_def (S : SuslinCode) :
    Path (suslinIndex S) (S.treeHeight + S.branchBound + S.Sym + S.Gam) :=
  Path.refl (S.treeHeight + S.branchBound + S.Sym + S.Gam)

def suslinNormalize_id (S : SuslinCode) :
    Path (suslinNormalize S) S :=
  Path.refl S

def suslinNormalize_index (S : SuslinCode) :
    Path (suslinIndex (suslinNormalize S)) (suslinIndex S) :=
  Path.refl (suslinIndex S)

def suslinIterate_height (n : Nat) (S : SuslinCode) :
    Path (suslinIterate n S).treeHeight (S.treeHeight + n) :=
  Path.refl (S.treeHeight + n)

def suslinIterate_branch (n : Nat) (S : SuslinCode) :
    Path (suslinIterate n S).branchBound S.branchBound :=
  Path.refl S.branchBound

def suslinIterate_index (n : Nat) (S : SuslinCode) :
    Path (suslinIndex (suslinIterate n S))
      ((S.treeHeight + n) + S.branchBound + S.Sym + S.Gam) :=
  Path.refl ((S.treeHeight + n) + S.branchBound + S.Sym + S.Gam)

def suslinIndex_congr (S T : SuslinCode) (p : Path S T) :
    Path (suslinIndex S) (suslinIndex T) :=
  Path.congrArg suslinIndex p

/-! ## Effective descriptive set theory encodings -/

structure EffectiveCode where
  machineIndex : Nat
  oracleIndex : Nat
  complexityLevel : Nat
  total : Bool

def effectiveRank (E : EffectiveCode) : Nat :=
  E.machineIndex + E.oracleIndex + E.complexityLevel

def effectiveJump (E : EffectiveCode) : EffectiveCode where
  machineIndex := E.machineIndex
  oracleIndex := E.oracleIndex
  complexityLevel := E.complexityLevel + 1
  total := E.total

def relativize (E : EffectiveCode) (oracleShift : Nat) : EffectiveCode where
  machineIndex := E.machineIndex
  oracleIndex := E.oracleIndex + oracleShift
  complexityLevel := E.complexityLevel
  total := E.total

def effectiveRank_def (E : EffectiveCode) :
    Path (effectiveRank E)
      (E.machineIndex + E.oracleIndex + E.complexityLevel) :=
  Path.refl (E.machineIndex + E.oracleIndex + E.complexityLevel)

def effectiveJump_machine (E : EffectiveCode) :
    Path (effectiveJump E).machineIndex E.machineIndex :=
  Path.refl E.machineIndex

def effectiveJump_oracle (E : EffectiveCode) :
    Path (effectiveJump E).oracleIndex E.oracleIndex :=
  Path.refl E.oracleIndex

def effectiveJump_complexity (E : EffectiveCode) :
    Path (effectiveJump E).complexityLevel (E.complexityLevel + 1) :=
  Path.refl (E.complexityLevel + 1)

def effectiveJump_total (E : EffectiveCode) :
    Path (effectiveJump E).total E.total :=
  Path.refl E.total

def relativize_oracle (E : EffectiveCode) (n : Nat) :
    Path (relativize E n).oracleIndex (E.oracleIndex + n) :=
  Path.refl (E.oracleIndex + n)

def relativize_rank (E : EffectiveCode) (n : Nat) :
    Path (effectiveRank (relativize E n))
      (E.machineIndex + (E.oracleIndex + n) + E.complexityLevel) :=
  Path.refl (E.machineIndex + (E.oracleIndex + n) + E.complexityLevel)

def effectiveRank_congr (E F : EffectiveCode) (p : Path E F) :
    Path (effectiveRank E) (effectiveRank F) :=
  Path.congrArg effectiveRank p

def jump_then_relativize_total (E : EffectiveCode) (n : Nat) :
    Path (relativize (effectiveJump E) n).total E.total :=
  Path.refl E.total

end ComputationalPaths.Path.Algebra.DescriptiveSetTheoryDeep
