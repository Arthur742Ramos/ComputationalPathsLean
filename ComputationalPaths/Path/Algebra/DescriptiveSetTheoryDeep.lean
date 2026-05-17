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
import ComputationalPaths.Path.Rewrite.RwEq

set_option linter.unusedVariables false

namespace ComputationalPaths.Path.Algebra.DescriptiveSetTheoryDeep

open ComputationalPaths.Path

private inductive DSTCertificateKind where
  | definitional
  | borel
  | wadge
  | determinacy
  | category
  | effective
  deriving DecidableEq, Repr

private structure DSTCertificate {A : Type _} (lhs rhs : A) where
  kind : DSTCertificateKind
  witness : Path lhs rhs
  nonemptySteps : witness.steps ≠ []

private noncomputable def mkDSTCertificate {A : Type _}
    (kind : DSTCertificateKind) {lhs rhs : A} (h : lhs = rhs) :
    DSTCertificate lhs rhs :=
  { kind := kind
    witness := Path.stepChain h
    nonemptySteps := by simp [Path.stepChain] }

private noncomputable def dstCertPath {A : Type _}
    (anchor : A) (kind : DSTCertificateKind := .definitional) :
    Path anchor anchor :=
  (mkDSTCertificate kind (lhs := anchor) (rhs := anchor) rfl).witness

/-! ## Path primitives over natural-number encodings -/

noncomputable def natAtomPath {m n : Nat} (h : m = n) : Path m n :=
  Path.mk [Step.mk m n h] h

@[simp] noncomputable def natAtomPath_toEq {m n : Nat} (h : m = n) :
    Path.toEq (natAtomPath h) = h := rfl

@[simp] noncomputable def natAtomPath_steps {m n : Nat} (h : m = n) :
    (natAtomPath h).steps = [Step.mk m n h] := rfl

@[simp] noncomputable def natAtomPath_symm {m n : Nat} (h : m = n) :
    Path.symm (natAtomPath h) = natAtomPath h.symm := by
  cases h
  rfl

@[simp] noncomputable def natAtomPath_symm_symm {m n : Nat} (h : m = n) :
    Path.symm (Path.symm (natAtomPath h)) = natAtomPath h := by
  cases h; rfl

noncomputable def natPath_trans_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

noncomputable def natPath_trans_refl_left {a b : Nat} (p : Path a b) :
    Path.trans (Path.refl a) p = p := by
  simp

noncomputable def natPath_trans_refl_right {a b : Nat} (p : Path a b) :
    Path.trans p (Path.refl b) = p := by
  simp

noncomputable def natPath_congr_succ {m n : Nat} (p : Path m n) :
    Path (Nat.succ m) (Nat.succ n) :=
  Path.congrArg Nat.succ p

noncomputable def natPath_congr_double {m n : Nat} (p : Path m n) :
    Path (m + m) (n + n) :=
  Path.congrArg (fun t => t + t) p

/-! ## Borel hierarchy -/

inductive BorelLevel : Type where
  | openLevel : BorelLevel
  | closedLevel : BorelLevel
  | sigma : Nat → BorelLevel
  | pi : Nat → BorelLevel
  deriving DecidableEq, Repr

noncomputable def borelRank : BorelLevel → Nat
  | .openLevel => 0
  | .closedLevel => 0
  | .sigma n => n + 1
  | .pi n => n + 1

noncomputable def borelTag : BorelLevel → Nat
  | .openLevel => 0
  | .closedLevel => 1
  | .sigma _ => 2
  | .pi _ => 3

noncomputable def dualLevel : BorelLevel → BorelLevel
  | .openLevel => .closedLevel
  | .closedLevel => .openLevel
  | .sigma n => .pi n
  | .pi n => .sigma n

noncomputable def sigmaLift (n : Nat) : BorelLevel := .sigma (n + 1)
noncomputable def piLift (n : Nat) : BorelLevel := .pi (n + 1)

noncomputable def borelRank_open : Path (borelRank .openLevel) 0 :=
  dstCertPath 0 .borel

noncomputable def borelRank_closed : Path (borelRank .closedLevel) 0 :=
  dstCertPath 0

noncomputable def borelRank_sigma (n : Nat) : Path (borelRank (.sigma n)) (n + 1) :=
  dstCertPath (n + 1)

noncomputable def borelRank_pi (n : Nat) : Path (borelRank (.pi n)) (n + 1) :=
  dstCertPath (n + 1)

noncomputable def borelTag_open : Path (borelTag .openLevel) 0 :=
  dstCertPath 0

noncomputable def borelTag_closed : Path (borelTag .closedLevel) 1 :=
  dstCertPath 1

noncomputable def dual_open : Path (dualLevel .openLevel) BorelLevel.closedLevel :=
  dstCertPath BorelLevel.closedLevel

noncomputable def dual_closed : Path (dualLevel .closedLevel) BorelLevel.openLevel :=
  dstCertPath BorelLevel.openLevel

noncomputable def dual_sigma (n : Nat) : Path (dualLevel (.sigma n)) (BorelLevel.pi n) :=
  dstCertPath (BorelLevel.pi n)

noncomputable def dual_pi (n : Nat) : Path (dualLevel (.pi n)) (BorelLevel.sigma n) :=
  dstCertPath (BorelLevel.sigma n)

noncomputable def dual_involutive (L : BorelLevel) :
    Path (dualLevel (dualLevel L)) L := by
  cases L <;> exact dstCertPath _

noncomputable def dual_rank_preserved (L : BorelLevel) :
    Path (borelRank (dualLevel L)) (borelRank L) := by
  cases L <;> exact dstCertPath _

noncomputable def sigmaLift_rank (n : Nat) :
    Path (borelRank (sigmaLift n)) (n + 2) :=
  dstCertPath (n + 2)

noncomputable def piLift_rank (n : Nat) :
    Path (borelRank (piLift n)) (n + 2) :=
  dstCertPath (n + 2)

/-! ## Analytic and coanalytic pointclasses -/

inductive Pointclass : Type where
  | borel : BorelLevel → Pointclass
  | analytic : Pointclass
  | coanalytic : Pointclass
  | projective : Nat → Pointclass
  deriving DecidableEq, Repr

noncomputable def pointclassRank : Pointclass → Nat
  | .borel L => borelRank L
  | .analytic => 1
  | .coanalytic => 1
  | .projective n => n + 2

noncomputable def pointclassDual : Pointclass → Pointclass
  | .borel L => .borel (dualLevel L)
  | .analytic => .coanalytic
  | .coanalytic => .analytic
  | .projective n => .projective n

noncomputable def isProjective : Pointclass → Bool
  | .projective _ => true
  | _ => false

noncomputable def pointclassRank_analytic :
    Path (pointclassRank .analytic) 1 :=
  dstCertPath 1

noncomputable def pointclassRank_coanalytic :
    Path (pointclassRank .coanalytic) 1 :=
  dstCertPath 1

noncomputable def pointclassRank_projective (n : Nat) :
    Path (pointclassRank (.projective n)) (n + 2) :=
  dstCertPath (n + 2)

noncomputable def pointclassDual_analytic :
    Path (pointclassDual .analytic) Pointclass.coanalytic :=
  dstCertPath Pointclass.coanalytic

noncomputable def pointclassDual_coanalytic :
    Path (pointclassDual .coanalytic) Pointclass.analytic :=
  dstCertPath Pointclass.analytic

noncomputable def pointclassDual_borel (L : BorelLevel) :
    Path (pointclassDual (.borel L)) (Pointclass.borel (dualLevel L)) :=
  dstCertPath (Pointclass.borel (dualLevel L))

noncomputable def pointclassDual_projective (n : Nat) :
    Path (pointclassDual (.projective n)) (Pointclass.projective n) :=
  dstCertPath (Pointclass.projective n)

noncomputable def pointclassDual_involutive (P : Pointclass) :
    Path (pointclassDual (pointclassDual P)) P := by
  cases P with
  | borel L => cases L <;> exact dstCertPath _
  | analytic => exact dstCertPath _
  | coanalytic => exact dstCertPath _
  | projective n => exact dstCertPath _

noncomputable def pointclassDual_rank_preserved (P : Pointclass) :
    Path (pointclassRank (pointclassDual P)) (pointclassRank P) := by
  cases P with
  | borel L => cases L <;> exact dstCertPath _
  | analytic => exact dstCertPath _
  | coanalytic => exact dstCertPath _
  | projective n => exact dstCertPath _

noncomputable def projective_flag_true (n : Nat) :
    Path (isProjective (.projective n)) true :=
  dstCertPath true

noncomputable def projective_flag_false_analytic :
    Path (isProjective .analytic) false :=
  dstCertPath false

noncomputable def projective_flag_false_coanalytic :
    Path (isProjective .coanalytic) false :=
  dstCertPath false

/-! ## Wadge reducibility encoding -/

structure WadgeCode where
  sourceRank : Nat
  targetRank : Nat
  reducible : Bool
  Sym : Nat
  Gam : Nat

noncomputable def wadgeWitness (W : WadgeCode) : Nat :=
  W.Sym + W.Gam

noncomputable def wadgeReflexive (n : Nat) : WadgeCode where
  sourceRank := n
  targetRank := n
  reducible := true
  Sym := n
  Gam := 0

noncomputable def wadgeCompose (A B : WadgeCode) : WadgeCode where
  sourceRank := A.sourceRank
  targetRank := B.targetRank
  reducible := A.reducible && B.reducible
  Sym := wadgeWitness A
  Gam := wadgeWitness B

noncomputable def wadgeReflexive_source (n : Nat) :
    Path (wadgeReflexive n).sourceRank n :=
  dstCertPath n .wadge

noncomputable def wadgeReflexive_target (n : Nat) :
    Path (wadgeReflexive n).targetRank n :=
  dstCertPath n

noncomputable def wadgeReflexive_reducible (n : Nat) :
    Path (wadgeReflexive n).reducible true :=
  dstCertPath true

noncomputable def wadgeReflexive_witness (n : Nat) :
    Path (wadgeWitness (wadgeReflexive n)) n :=
  dstCertPath n

noncomputable def wadgeCompose_source (A B : WadgeCode) :
    Path (wadgeCompose A B).sourceRank A.sourceRank :=
  dstCertPath A.sourceRank

noncomputable def wadgeCompose_target (A B : WadgeCode) :
    Path (wadgeCompose A B).targetRank B.targetRank :=
  dstCertPath B.targetRank

noncomputable def wadgeCompose_reducible (A B : WadgeCode) :
    Path (wadgeCompose A B).reducible (A.reducible && B.reducible) :=
  dstCertPath (A.reducible && B.reducible)

noncomputable def wadgeCompose_witness (A B : WadgeCode) :
    Path (wadgeWitness (wadgeCompose A B))
      (wadgeWitness A + wadgeWitness B) :=
  dstCertPath (wadgeWitness A + wadgeWitness B)

noncomputable def wadgeCompose_assoc_source (A B C : WadgeCode) :
    Path (wadgeCompose (wadgeCompose A B) C).sourceRank A.sourceRank :=
  dstCertPath A.sourceRank

noncomputable def wadgeCompose_assoc_target (A B C : WadgeCode) :
    Path (wadgeCompose A (wadgeCompose B C)).targetRank C.targetRank :=
  dstCertPath C.targetRank

noncomputable def wadgeWitness_path_chain (A B : WadgeCode) :
    Path (wadgeWitness (wadgeCompose A B))
      (wadgeWitness A + wadgeWitness B) := by
  exact Path.trans
    (dstCertPath (wadgeWitness (wadgeCompose A B)))
    (dstCertPath (wadgeWitness A + wadgeWitness B))

/-! ## Determinacy scaffolding -/

inductive Player : Type where
  | first : Player
  | second : Player
  deriving DecidableEq, Repr

noncomputable def dualPlayer : Player → Player
  | .first => .second
  | .second => .first

structure DeterminacyGame where
  length : Nat
  payoffRank : Nat
  winner : Player

noncomputable def flipGame (G : DeterminacyGame) : DeterminacyGame where
  length := G.length
  payoffRank := G.payoffRank
  winner := dualPlayer G.winner

noncomputable def strategyRank (G : DeterminacyGame) : Nat :=
  G.length + G.payoffRank

noncomputable def determinedFlag (G : DeterminacyGame) : Bool := true

noncomputable def dualPlayer_involutive (p : Player) :
    Path (dualPlayer (dualPlayer p)) p := by
  cases p <;> exact dstCertPath _ .determinacy

noncomputable def flipGame_length (G : DeterminacyGame) :
    Path (flipGame G).length G.length :=
  dstCertPath G.length

noncomputable def flipGame_payoff (G : DeterminacyGame) :
    Path (flipGame G).payoffRank G.payoffRank :=
  dstCertPath G.payoffRank

noncomputable def flipGame_winner (G : DeterminacyGame) :
    Path (flipGame G).winner (dualPlayer G.winner) :=
  dstCertPath (dualPlayer G.winner)

noncomputable def flipGame_involutive (G : DeterminacyGame) :
    Path (flipGame (flipGame G)) G := by
  cases G with
  | mk len rank win =>
      cases win <;> exact dstCertPath _

noncomputable def determinedFlag_true (G : DeterminacyGame) :
    Path (determinedFlag G) true :=
  dstCertPath true

noncomputable def strategyRank_flip (G : DeterminacyGame) :
    Path (strategyRank (flipGame G)) (strategyRank G) :=
  dstCertPath (strategyRank G)

noncomputable def strategyRank_congr (G H : DeterminacyGame) (p : Path G H) :
    Path (strategyRank G) (strategyRank H) :=
  Path.congrArg strategyRank p

/-! ## Perfect set property -/

structure PerfectSetProfile where
  rank : Nat
  hasPerfectCore : Bool
  hasCountablePart : Bool

noncomputable def perfectSetProperty (P : PerfectSetProfile) : Bool :=
  P.hasPerfectCore

noncomputable def perfectKernelRank (P : PerfectSetProfile) : Nat :=
  if P.hasPerfectCore then P.rank + 1 else 0

noncomputable def perfectSetProperty_def (P : PerfectSetProfile) :
    Path (perfectSetProperty P) P.hasPerfectCore :=
  dstCertPath P.hasPerfectCore

noncomputable def perfectKernelRank_yes (n : Nat) :
    Path (perfectKernelRank ⟨n, true, false⟩) (n + 1) :=
  dstCertPath (n + 1)

noncomputable def perfectKernelRank_no (n : Nat) :
    Path (perfectKernelRank ⟨n, false, true⟩) 0 :=
  dstCertPath 0

noncomputable def perfectSetProperty_true_rank (n : Nat) :
    Path (perfectSetProperty ⟨n, true, false⟩) true :=
  dstCertPath true

noncomputable def perfectSetProperty_false_rank (n : Nat) :
    Path (perfectSetProperty ⟨n, false, true⟩) false :=
  dstCertPath false

noncomputable def perfect_kernel_congr (P Q : PerfectSetProfile) (p : Path P Q) :
    Path (perfectKernelRank P) (perfectKernelRank Q) :=
  Path.congrArg perfectKernelRank p

/-! ## Baire category bookkeeping -/

structure CategoryProfile where
  meagerRank : Nat
  comeagerRank : Nat
  denseOpenCount : Nat
  residualRank : Nat

noncomputable def meagerScore (C : CategoryProfile) : Nat :=
  C.meagerRank + C.denseOpenCount

noncomputable def comeagerScore (C : CategoryProfile) : Nat :=
  C.comeagerRank + C.residualRank

noncomputable def baireBalance (C : CategoryProfile) : Nat :=
  comeagerScore C + meagerScore C

noncomputable def meagerScore_def (C : CategoryProfile) :
    Path (meagerScore C) (C.meagerRank + C.denseOpenCount) :=
  dstCertPath (C.meagerRank + C.denseOpenCount) .category

noncomputable def comeagerScore_def (C : CategoryProfile) :
    Path (comeagerScore C) (C.comeagerRank + C.residualRank) :=
  dstCertPath (C.comeagerRank + C.residualRank)

noncomputable def baireBalance_def (C : CategoryProfile) :
    Path (baireBalance C) (comeagerScore C + meagerScore C) :=
  dstCertPath (comeagerScore C + meagerScore C)

noncomputable def baireBalance_zero :
    Path (baireBalance ⟨0, 0, 0, 0⟩) 0 :=
  dstCertPath 0

noncomputable def meagerScore_congr (C D : CategoryProfile) (p : Path C D) :
    Path (meagerScore C) (meagerScore D) :=
  Path.congrArg meagerScore p

noncomputable def comeagerScore_congr (C D : CategoryProfile) (p : Path C D) :
    Path (comeagerScore C) (comeagerScore D) :=
  Path.congrArg comeagerScore p

noncomputable def baireBalance_congr (C D : CategoryProfile) (p : Path C D) :
    Path (baireBalance C) (baireBalance D) :=
  Path.congrArg baireBalance p

noncomputable def baireBalance_trans_symm (C : CategoryProfile) :
    Path.trans (Path.refl (baireBalance C)) (Path.refl (baireBalance C)) =
      Path.refl (baireBalance C) := by
  simp

/-! ## Cantor-Bendixson decomposition -/

structure CantorBendixsonState where
  derivativeStage : Nat
  perfectKernel : Nat
  scatteredPart : Nat

noncomputable def cbStep (S : CantorBendixsonState) : CantorBendixsonState where
  derivativeStage := S.derivativeStage + 1
  perfectKernel := S.perfectKernel
  scatteredPart := S.scatteredPart

noncomputable def cbRank (S : CantorBendixsonState) : Nat :=
  S.derivativeStage + S.perfectKernel + S.scatteredPart

noncomputable def cbStep_stage (S : CantorBendixsonState) :
    Path (cbStep S).derivativeStage (S.derivativeStage + 1) :=
  dstCertPath (S.derivativeStage + 1)

noncomputable def cbStep_kernel (S : CantorBendixsonState) :
    Path (cbStep S).perfectKernel S.perfectKernel :=
  dstCertPath S.perfectKernel

noncomputable def cbStep_scattered (S : CantorBendixsonState) :
    Path (cbStep S).scatteredPart S.scatteredPart :=
  dstCertPath S.scatteredPart

noncomputable def cbRank_def (S : CantorBendixsonState) :
    Path (cbRank S) (S.derivativeStage + S.perfectKernel + S.scatteredPart) :=
  dstCertPath (S.derivativeStage + S.perfectKernel + S.scatteredPart)

noncomputable def cbRank_step (S : CantorBendixsonState) :
    Path (cbRank (cbStep S))
      ((S.derivativeStage + 1) + S.perfectKernel + S.scatteredPart) :=
  dstCertPath ((S.derivativeStage + 1) + S.perfectKernel + S.scatteredPart)

noncomputable def cbStep_congr (S T : CantorBendixsonState) (p : Path S T) :
    Path (cbStep S) (cbStep T) :=
  Path.congrArg cbStep p

noncomputable def cbRank_congr (S T : CantorBendixsonState) (p : Path S T) :
    Path (cbRank S) (cbRank T) :=
  Path.congrArg cbRank p

/-! ## Suslin operation coding -/

structure SuslinCode where
  treeHeight : Nat
  branchBound : Nat
  Sym : Nat
  Gam : Nat

noncomputable def suslinIndex (S : SuslinCode) : Nat :=
  S.treeHeight + S.branchBound + S.Sym + S.Gam

noncomputable def suslinNormalize (S : SuslinCode) : SuslinCode where
  treeHeight := S.treeHeight
  branchBound := S.branchBound
  Sym := S.Sym
  Gam := S.Gam

noncomputable def suslinIterate (n : Nat) (S : SuslinCode) : SuslinCode where
  treeHeight := S.treeHeight + n
  branchBound := S.branchBound
  Sym := S.Sym
  Gam := S.Gam

noncomputable def suslinIndex_def (S : SuslinCode) :
    Path (suslinIndex S) (S.treeHeight + S.branchBound + S.Sym + S.Gam) :=
  dstCertPath (S.treeHeight + S.branchBound + S.Sym + S.Gam)

noncomputable def suslinNormalize_id (S : SuslinCode) :
    Path (suslinNormalize S) S :=
  dstCertPath S

noncomputable def suslinNormalize_index (S : SuslinCode) :
    Path (suslinIndex (suslinNormalize S)) (suslinIndex S) :=
  dstCertPath (suslinIndex S)

noncomputable def suslinIterate_height (n : Nat) (S : SuslinCode) :
    Path (suslinIterate n S).treeHeight (S.treeHeight + n) :=
  dstCertPath (S.treeHeight + n)

noncomputable def suslinIterate_branch (n : Nat) (S : SuslinCode) :
    Path (suslinIterate n S).branchBound S.branchBound :=
  dstCertPath S.branchBound

noncomputable def suslinIterate_index (n : Nat) (S : SuslinCode) :
    Path (suslinIndex (suslinIterate n S))
      ((S.treeHeight + n) + S.branchBound + S.Sym + S.Gam) :=
  dstCertPath ((S.treeHeight + n) + S.branchBound + S.Sym + S.Gam)

noncomputable def suslinIndex_congr (S T : SuslinCode) (p : Path S T) :
    Path (suslinIndex S) (suslinIndex T) :=
  Path.congrArg suslinIndex p

/-! ## Effective descriptive set theory encodings -/

structure EffectiveCode where
  machineIndex : Nat
  oracleIndex : Nat
  complexityLevel : Nat
  total : Bool

noncomputable def effectiveRank (E : EffectiveCode) : Nat :=
  E.machineIndex + E.oracleIndex + E.complexityLevel

noncomputable def effectiveJump (E : EffectiveCode) : EffectiveCode where
  machineIndex := E.machineIndex
  oracleIndex := E.oracleIndex
  complexityLevel := E.complexityLevel + 1
  total := E.total

noncomputable def relativize (E : EffectiveCode) (oracleShift : Nat) : EffectiveCode where
  machineIndex := E.machineIndex
  oracleIndex := E.oracleIndex + oracleShift
  complexityLevel := E.complexityLevel
  total := E.total

noncomputable def effectiveRank_def (E : EffectiveCode) :
    Path (effectiveRank E)
      (E.machineIndex + E.oracleIndex + E.complexityLevel) :=
  dstCertPath (E.machineIndex + E.oracleIndex + E.complexityLevel) .effective

noncomputable def effectiveJump_machine (E : EffectiveCode) :
    Path (effectiveJump E).machineIndex E.machineIndex :=
  dstCertPath E.machineIndex

noncomputable def effectiveJump_oracle (E : EffectiveCode) :
    Path (effectiveJump E).oracleIndex E.oracleIndex :=
  dstCertPath E.oracleIndex

noncomputable def effectiveJump_complexity (E : EffectiveCode) :
    Path (effectiveJump E).complexityLevel (E.complexityLevel + 1) :=
  dstCertPath (E.complexityLevel + 1)

noncomputable def effectiveJump_total (E : EffectiveCode) :
    Path (effectiveJump E).total E.total :=
  dstCertPath E.total

noncomputable def relativize_oracle (E : EffectiveCode) (n : Nat) :
    Path (relativize E n).oracleIndex (E.oracleIndex + n) :=
  dstCertPath (E.oracleIndex + n)

noncomputable def relativize_rank (E : EffectiveCode) (n : Nat) :
    Path (effectiveRank (relativize E n))
      (E.machineIndex + (E.oracleIndex + n) + E.complexityLevel) :=
  dstCertPath (E.machineIndex + (E.oracleIndex + n) + E.complexityLevel)

noncomputable def effectiveRank_congr (E F : EffectiveCode) (p : Path E F) :
    Path (effectiveRank E) (effectiveRank F) :=
  Path.congrArg effectiveRank p

noncomputable def jump_then_relativize_total (E : EffectiveCode) (n : Nat) :
    Path (relativize (effectiveJump E) n).total E.total :=
  dstCertPath E.total

/-- Rewrite coherence: right unit law on Wadge witness composition chain. -/
noncomputable def wadgeWitness_chain_right_unit_rweq (A B : WadgeCode) :
    RwEq (Path.trans (wadgeWitness_path_chain A B) (Path.refl _))
      (wadgeWitness_path_chain A B) :=
  rweq_cmpA_refl_right (wadgeWitness_path_chain A B)

/-- Rewrite coherence: left unit law on Borel dual involution certificate. -/
noncomputable def dual_involutive_left_unit_rweq (L : BorelLevel) :
    RwEq (Path.trans (Path.refl _) (dual_involutive L)) (dual_involutive L) :=
  rweq_cmpA_refl_left (dual_involutive L)

end ComputationalPaths.Path.Algebra.DescriptiveSetTheoryDeep
