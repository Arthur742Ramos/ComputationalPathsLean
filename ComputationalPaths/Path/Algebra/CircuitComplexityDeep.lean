/-
  Circuit Complexity via Computational Paths
  =========================================

  This module gives a computational-path formalization scaffold for core circuit
  complexity themes:

  - Boolean gates and fan-in structure
  - Circuit size/depth profiles
  - NC/AC/TC hierarchy tags
  - P/poly advice families
  - Lower-bound witness schemas
  - Razborov-Smolensky style bookkeeping
  - Natural proofs barrier metadata
  - Monotone and threshold layers
  - Circuit transformations as explicit paths
-/

import ComputationalPaths.Path.Basic

namespace CircuitComplexityDeep

open ComputationalPaths

/-! ## Section 1: Boolean gate signatures -/

inductive GateKind : Type where
  | input
  | const0
  | const1
  | andGate
  | orGate
  | notGate
  | xorGate
  | nandGate
  | norGate
  | xnorGate
  | majGate
  | thresholdGate (k n : Nat)
  deriving DecidableEq, Repr

def GateKind.fanIn : GateKind → Nat
  | .input => 0
  | .const0 => 0
  | .const1 => 0
  | .andGate => 2
  | .orGate => 2
  | .notGate => 1
  | .xorGate => 2
  | .nandGate => 2
  | .norGate => 2
  | .xnorGate => 2
  | .majGate => 3
  | .thresholdGate _ n => n

def GateKind.isMonotone : GateKind → Bool
  | .notGate => false
  | .xorGate => false
  | .nandGate => false
  | .norGate => false
  | .xnorGate => false
  | _ => true

def GateKind.isThreshold : GateKind → Bool
  | .thresholdGate _ _ => true
  | _ => false

def GateKind.isSymmetric : GateKind → Bool
  | .andGate => true
  | .orGate => true
  | .xorGate => true
  | .nandGate => true
  | .norGate => true
  | .xnorGate => true
  | .majGate => true
  | .thresholdGate _ _ => true
  | _ => false

def thm01_fanIn_input : Path (GateKind.fanIn GateKind.input) 0 :=
  Path.refl 0

def thm02_fanIn_and : Path (GateKind.fanIn GateKind.andGate) 2 :=
  Path.refl 2

def thm03_fanIn_not : Path (GateKind.fanIn GateKind.notGate) 1 :=
  Path.refl 1

def thm04_fanIn_maj : Path (GateKind.fanIn GateKind.majGate) 3 :=
  Path.refl 3

def thm05_fanIn_threshold (k n : Nat) :
    Path (GateKind.fanIn (.thresholdGate k n)) n :=
  Path.refl n

def thm06_monotone_and : Path (GateKind.isMonotone GateKind.andGate) true :=
  Path.refl true

def thm07_monotone_not : Path (GateKind.isMonotone GateKind.notGate) false :=
  Path.refl false

def thm08_threshold_true (k n : Nat) :
    Path (GateKind.isThreshold (.thresholdGate k n)) true :=
  Path.refl true

def thm09_threshold_false_and : Path (GateKind.isThreshold GateKind.andGate) false :=
  Path.refl false

def thm10_symmetric_xor : Path (GateKind.isSymmetric GateKind.xorGate) true :=
  Path.refl true

def thm11_symmetric_input : Path (GateKind.isSymmetric GateKind.input) false :=
  Path.refl false

def thm12_fanIn_roundtrip (g : GateKind) :
    Path (GateKind.fanIn g) (GateKind.fanIn g) :=
  Path.trans (Path.refl (GateKind.fanIn g)) (Path.refl (GateKind.fanIn g))

def thm13_monotone_roundtrip (g : GateKind) :
    Path (GateKind.isMonotone g) (GateKind.isMonotone g) :=
  Path.symm (Path.refl (GateKind.isMonotone g))

def thm14_fanIn_shift_congr (g : GateKind) :
    Path (GateKind.fanIn g + 1) (GateKind.fanIn g + 1) :=
  Path.congrArg (fun n => n + 1) (Path.refl (GateKind.fanIn g))

/-! ## Section 2: Circuit profiles for size/depth bookkeeping -/

structure CircuitProfile where
  inputs : Nat
  size : Nat
  depth : Nat
  fanInBound : Nat
  unboundedFanIn : Bool
  hasParity : Bool
  hasThreshold : Bool
  symBudget : Nat
  gamContext : Nat
  deriving DecidableEq, Repr

def Sym (p : CircuitProfile) : Nat := p.symBudget
def Gam (p : CircuitProfile) : Nat := p.gamContext

def ncProfile (k n : Nat) : CircuitProfile :=
  { inputs := n
    size := n * (k + 1)
    depth := k + 1
    fanInBound := 2
    unboundedFanIn := false
    hasParity := false
    hasThreshold := false
    symBudget := k
    gamContext := n }

def acProfile (k n : Nat) : CircuitProfile :=
  { inputs := n
    size := n * (k + 2)
    depth := k + 1
    fanInBound := n + 1
    unboundedFanIn := true
    hasParity := false
    hasThreshold := false
    symBudget := k + 1
    gamContext := n + 1 }

def tcProfile (k n : Nat) : CircuitProfile :=
  { inputs := n
    size := n * (k + 3)
    depth := k + 1
    fanInBound := n + 1
    unboundedFanIn := true
    hasParity := false
    hasThreshold := true
    symBudget := k + 2
    gamContext := n + 2 }

def ppolyProfile (n advice : Nat) : CircuitProfile :=
  { inputs := n
    size := n * n + advice + 1
    depth := n + 1
    fanInBound := n + 1
    unboundedFanIn := true
    hasParity := true
    hasThreshold := false
    symBudget := advice
    gamContext := n }

def CircuitProfile.work (p : CircuitProfile) : Nat :=
  p.size + p.depth

def CircuitProfile.signature (p : CircuitProfile) : Nat :=
  p.inputs + p.fanInBound + Sym p + Gam p

def thm15_nc_inputs (k n : Nat) : Path (ncProfile k n).inputs n :=
  Path.refl n

def thm16_nc_fanIn : Path (ncProfile 0 0).fanInBound 2 :=
  Path.refl 2

def thm17_nc_unbounded (k n : Nat) :
    Path (ncProfile k n).unboundedFanIn false :=
  Path.refl false

def thm18_ac_unbounded (k n : Nat) :
    Path (acProfile k n).unboundedFanIn true :=
  Path.refl true

def thm19_ac_threshold (k n : Nat) :
    Path (acProfile k n).hasThreshold false :=
  Path.refl false

def thm20_tc_threshold (k n : Nat) :
    Path (tcProfile k n).hasThreshold true :=
  Path.refl true

def thm21_tc_unbounded (k n : Nat) :
    Path (tcProfile k n).unboundedFanIn true :=
  Path.refl true

def thm22_ppoly_parity (n advice : Nat) :
    Path (ppolyProfile n advice).hasParity true :=
  Path.refl true

def thm23_ppoly_sym (n advice : Nat) :
    Path (Sym (ppolyProfile n advice)) advice :=
  Path.refl advice

def thm24_ppoly_gam (n advice : Nat) :
    Path (Gam (ppolyProfile n advice)) n :=
  Path.refl n

def thm25_nc_sym (k n : Nat) :
    Path (Sym (ncProfile k n)) k :=
  Path.refl k

def thm26_nc_gam (k n : Nat) :
    Path (Gam (ncProfile k n)) n :=
  Path.refl n

def thm27_work_def (p : CircuitProfile) :
    Path p.work (p.size + p.depth) :=
  Path.refl (p.size + p.depth)

def thm28_signature_def (p : CircuitProfile) :
    Path p.signature (p.inputs + p.fanInBound + Sym p + Gam p) :=
  Path.refl (p.inputs + p.fanInBound + Sym p + Gam p)

def thm29_profile_work_roundtrip (p : CircuitProfile) :
    Path p.work p.work :=
  Path.trans (Path.refl p.work) (Path.refl p.work)

def thm30_sym_gam_ascii (Sym Gam : Nat) :
    Path (Sym + Gam) (Sym + Gam) :=
  Path.refl (Sym + Gam)

/-! ## Section 3: NC/AC/TC and nonuniform hierarchy tags -/

inductive CircuitClass : Type where
  | nc : Nat → CircuitClass
  | ac : Nat → CircuitClass
  | tc : Nat → CircuitClass
  | ppoly
  | lowerBound
  deriving DecidableEq, Repr

def CircuitClass.level : CircuitClass → Nat
  | .nc k => k + 1
  | .ac k => k + 1
  | .tc k => k + 1
  | .ppoly => 100
  | .lowerBound => 200

def CircuitClass.allowsUnbounded : CircuitClass → Bool
  | .nc _ => false
  | .ac _ => true
  | .tc _ => true
  | .ppoly => true
  | .lowerBound => false

def CircuitClass.usesThreshold : CircuitClass → Bool
  | .tc _ => true
  | _ => false

def CircuitClass.isNonuniform : CircuitClass → Bool
  | .ppoly => true
  | _ => false

def thm31_nc_level (k : Nat) :
    Path (CircuitClass.level (.nc k)) (k + 1) :=
  Path.refl (k + 1)

def thm32_ac_level (k : Nat) :
    Path (CircuitClass.level (.ac k)) (k + 1) :=
  Path.refl (k + 1)

def thm33_tc_level (k : Nat) :
    Path (CircuitClass.level (.tc k)) (k + 1) :=
  Path.refl (k + 1)

def thm34_ppoly_level :
    Path (CircuitClass.level .ppoly) 100 :=
  Path.refl 100

def thm35_nc_unbounded (k : Nat) :
    Path (CircuitClass.allowsUnbounded (.nc k)) false :=
  Path.refl false

def thm36_ac_unbounded (k : Nat) :
    Path (CircuitClass.allowsUnbounded (.ac k)) true :=
  Path.refl true

def thm37_tc_threshold (k : Nat) :
    Path (CircuitClass.usesThreshold (.tc k)) true :=
  Path.refl true

def thm38_ac_threshold (k : Nat) :
    Path (CircuitClass.usesThreshold (.ac k)) false :=
  Path.refl false

def thm39_ppoly_nonuniform :
    Path (CircuitClass.isNonuniform .ppoly) true :=
  Path.refl true

def thm40_nc_nonuniform (k : Nat) :
    Path (CircuitClass.isNonuniform (.nc k)) false :=
  Path.refl false

def thm41_class_level_roundtrip (c : CircuitClass) :
    Path (CircuitClass.level c) (CircuitClass.level c) :=
  Path.trans (Path.refl (CircuitClass.level c)) (Path.refl (CircuitClass.level c))

def thm42_class_level_symm (c : CircuitClass) :
    Path (CircuitClass.level c) (CircuitClass.level c) :=
  Path.symm (Path.refl (CircuitClass.level c))

def thm43_class_level_shift (c : CircuitClass) :
    Path (CircuitClass.level c + 1) (CircuitClass.level c + 1) :=
  Path.congrArg (fun n => n + 1) (Path.refl (CircuitClass.level c))

def thm44_nc_level_chain (k : Nat) :
    Path (CircuitClass.level (.nc k)) (k + 1) :=
  Path.trans (Path.refl (k + 1)) (Path.refl (k + 1))

/-! ## Section 4: P/poly advice systems -/

structure AdviceSystem where
  inputLen : Nat
  adviceLen : Nat
  circuitSize : Nat
  depthBound : Nat
  symToken : Nat
  gamToken : Nat
  deriving DecidableEq, Repr

def AdviceSystem.Sym (a : AdviceSystem) : Nat := a.symToken
def AdviceSystem.Gam (a : AdviceSystem) : Nat := a.gamToken

def polyAdviceBound (n : Nat) : Nat :=
  n * n + 1

def mkPPolyAdvice (n : Nat) : AdviceSystem :=
  { inputLen := n
    adviceLen := polyAdviceBound n
    circuitSize := n * n + polyAdviceBound n
    depthBound := n + 1
    symToken := n
    gamToken := polyAdviceBound n }

def AdviceSystem.description (a : AdviceSystem) : Nat :=
  a.inputLen + a.adviceLen + a.circuitSize + a.depthBound + a.Sym + a.Gam

def thm45_polyAdvice_def (n : Nat) :
    Path (polyAdviceBound n) (n * n + 1) :=
  Path.refl (n * n + 1)

def thm46_mkAdvice_input (n : Nat) :
    Path (mkPPolyAdvice n).inputLen n :=
  Path.refl n

def thm47_mkAdvice_len (n : Nat) :
    Path (mkPPolyAdvice n).adviceLen (polyAdviceBound n) :=
  Path.refl (polyAdviceBound n)

def thm48_mkAdvice_depth (n : Nat) :
    Path (mkPPolyAdvice n).depthBound (n + 1) :=
  Path.refl (n + 1)

def thm49_mkAdvice_sym (n : Nat) :
    Path (mkPPolyAdvice n).Sym n :=
  Path.refl n

def thm50_mkAdvice_gam (n : Nat) :
    Path (mkPPolyAdvice n).Gam (polyAdviceBound n) :=
  Path.refl (polyAdviceBound n)

def thm51_advice_description_def (a : AdviceSystem) :
    Path a.description
      (a.inputLen + a.adviceLen + a.circuitSize + a.depthBound + a.Sym + a.Gam) :=
  Path.refl (a.inputLen + a.adviceLen + a.circuitSize + a.depthBound + a.Sym + a.Gam)

def thm52_advice_description_roundtrip (n : Nat) :
    Path (mkPPolyAdvice n).description (mkPPolyAdvice n).description :=
  Path.trans (Path.refl (mkPPolyAdvice n).description) (Path.refl (mkPPolyAdvice n).description)

def thm53_advice_description_symm (n : Nat) :
    Path (mkPPolyAdvice n).description (mkPPolyAdvice n).description :=
  Path.symm (Path.refl (mkPPolyAdvice n).description)

def thm54_advice_description_shift (n : Nat) :
    Path ((mkPPolyAdvice n).description + 1) ((mkPPolyAdvice n).description + 1) :=
  Path.congrArg (fun m => m + 1) (Path.refl (mkPPolyAdvice n).description)

/-! ## Section 5: Lower-bound witness schemas and Razborov-Smolensky data -/

structure LowerBoundWitness where
  targetClass : CircuitClass
  modulus : Nat
  polynomialDegree : Nat
  witnessSize : Nat
  monotoneOnly : Bool
  symMarker : Nat
  gamMarker : Nat
  deriving DecidableEq, Repr

def LowerBoundWitness.Sym (w : LowerBoundWitness) : Nat := w.symMarker
def LowerBoundWitness.Gam (w : LowerBoundWitness) : Nat := w.gamMarker

def LowerBoundWitness.score (w : LowerBoundWitness) : Nat :=
  w.witnessSize + w.polynomialDegree + w.Sym + w.Gam

def razborovSmolenskyWitness (m d n : Nat) : LowerBoundWitness :=
  { targetClass := CircuitClass.ac d
    modulus := m
    polynomialDegree := d
    witnessSize := n * (d + 1)
    monotoneOnly := false
    symMarker := m
    gamMarker := n }

def monotoneCliqueWitness (n : Nat) : LowerBoundWitness :=
  { targetClass := CircuitClass.lowerBound
    modulus := 0
    polynomialDegree := n
    witnessSize := n * n
    monotoneOnly := true
    symMarker := n
    gamMarker := n + 1 }

def thm55_rs_target (m d n : Nat) :
    Path (razborovSmolenskyWitness m d n).targetClass (CircuitClass.ac d) :=
  Path.refl (CircuitClass.ac d)

def thm56_rs_modulus (m d n : Nat) :
    Path (razborovSmolenskyWitness m d n).modulus m :=
  Path.refl m

def thm57_rs_degree (m d n : Nat) :
    Path (razborovSmolenskyWitness m d n).polynomialDegree d :=
  Path.refl d

def thm58_rs_monotone_false (m d n : Nat) :
    Path (razborovSmolenskyWitness m d n).monotoneOnly false :=
  Path.refl false

def thm59_rs_sym (m d n : Nat) :
    Path (razborovSmolenskyWitness m d n).Sym m :=
  Path.refl m

def thm60_rs_gam (m d n : Nat) :
    Path (razborovSmolenskyWitness m d n).Gam n :=
  Path.refl n

def thm61_monotone_clique_true (n : Nat) :
    Path (monotoneCliqueWitness n).monotoneOnly true :=
  Path.refl true

def thm62_monotone_clique_target (n : Nat) :
    Path (monotoneCliqueWitness n).targetClass CircuitClass.lowerBound :=
  Path.refl CircuitClass.lowerBound

def thm63_lower_score_def (w : LowerBoundWitness) :
    Path w.score (w.witnessSize + w.polynomialDegree + w.Sym + w.Gam) :=
  Path.refl (w.witnessSize + w.polynomialDegree + w.Sym + w.Gam)

def thm64_lower_score_roundtrip (w : LowerBoundWitness) :
    Path w.score w.score :=
  Path.trans (Path.refl w.score) (Path.refl w.score)

/-! ## Section 6: Natural proofs barrier metadata -/

structure NaturalProofRecord where
  large : Bool
  constructive : Bool
  useful : Bool
  againstPseudoRandom : Bool
  symIndex : Nat
  gamIndex : Nat
  deriving DecidableEq, Repr

def NaturalProofRecord.Sym (r : NaturalProofRecord) : Nat := r.symIndex
def NaturalProofRecord.Gam (r : NaturalProofRecord) : Nat := r.gamIndex

def NaturalProofRecord.isNatural (r : NaturalProofRecord) : Bool :=
  r.large && r.constructive && r.useful

def NaturalProofRecord.barrierActive (r : NaturalProofRecord) : Bool :=
  r.isNatural && r.againstPseudoRandom

def canonicalBarrier : NaturalProofRecord :=
  { large := true
    constructive := true
    useful := true
    againstPseudoRandom := true
    symIndex := 1
    gamIndex := 2 }

def thm65_barrier_large :
    Path canonicalBarrier.large true :=
  Path.refl true

def thm66_barrier_constructive :
    Path canonicalBarrier.constructive true :=
  Path.refl true

def thm67_barrier_useful :
    Path canonicalBarrier.useful true :=
  Path.refl true

def thm68_barrier_isNatural :
    Path canonicalBarrier.isNatural true :=
  Path.refl true

def thm69_barrier_active :
    Path canonicalBarrier.barrierActive true :=
  Path.refl true

def thm70_barrier_sym :
    Path canonicalBarrier.Sym 1 :=
  Path.refl 1

def thm71_barrier_gam :
    Path canonicalBarrier.Gam 2 :=
  Path.refl 2

def thm72_barrier_roundtrip :
    Path canonicalBarrier.barrierActive canonicalBarrier.barrierActive :=
  Path.trans (Path.refl canonicalBarrier.barrierActive) (Path.refl canonicalBarrier.barrierActive)

/-! ## Section 7: Monotone and threshold layer parameters -/

structure MonotoneLayer where
  vars : Nat
  andCount : Nat
  orCount : Nat
  depth : Nat
  symLoad : Nat
  gamLoad : Nat
  deriving DecidableEq, Repr

def MonotoneLayer.Sym (m : MonotoneLayer) : Nat := m.symLoad
def MonotoneLayer.Gam (m : MonotoneLayer) : Nat := m.gamLoad

def MonotoneLayer.size (m : MonotoneLayer) : Nat :=
  m.andCount + m.orCount

def thresholdCost (k n : Nat) : Nat :=
  k + n + 1

def majorityCost (n : Nat) : Nat :=
  n + 1

def monotoneDepthBound (m : MonotoneLayer) : Nat :=
  m.depth + 1

def thm73_monotone_size_def (m : MonotoneLayer) :
    Path m.size (m.andCount + m.orCount) :=
  Path.refl (m.andCount + m.orCount)

def thm74_threshold_cost_def (k n : Nat) :
    Path (thresholdCost k n) (k + n + 1) :=
  Path.refl (k + n + 1)

def thm75_majority_cost_def (n : Nat) :
    Path (majorityCost n) (n + 1) :=
  Path.refl (n + 1)

def thm76_monotone_depth_bound (m : MonotoneLayer) :
    Path (monotoneDepthBound m) (m.depth + 1) :=
  Path.refl (m.depth + 1)

def thm77_monotone_sym (m : MonotoneLayer) :
    Path m.Sym m.symLoad :=
  Path.refl m.symLoad

def thm78_monotone_gam (m : MonotoneLayer) :
    Path m.Gam m.gamLoad :=
  Path.refl m.gamLoad

def thm79_monotone_size_roundtrip (m : MonotoneLayer) :
    Path m.size m.size :=
  Path.trans (Path.refl m.size) (Path.refl m.size)

def thm80_threshold_cost_shift (k n : Nat) :
    Path (thresholdCost k n + 1) (thresholdCost k n + 1) :=
  Path.congrArg (fun t => t + 1) (Path.refl (thresholdCost k n))

/-! ## Section 8: Circuit transformations as explicit computational paths -/

structure CircuitTransform where
  before : CircuitProfile
  after : CircuitProfile
  tag : Nat
  symTag : Nat
  gamTag : Nat
  deriving DecidableEq, Repr

def CircuitTransform.Sym (t : CircuitTransform) : Nat := t.symTag
def CircuitTransform.Gam (t : CircuitTransform) : Nat := t.gamTag

def identityTransform (p : CircuitProfile) : CircuitTransform :=
  { before := p
    after := p
    tag := 0
    symTag := Sym p
    gamTag := Gam p }

def composeTransform (x y : CircuitTransform) : CircuitTransform :=
  { before := x.before
    after := y.after
    tag := x.tag + y.tag
    symTag := x.symTag + y.symTag
    gamTag := x.gamTag + y.gamTag }

def depthBalanceTransform (p : CircuitProfile) : CircuitTransform :=
  { before := p
    after := p
    tag := 1
    symTag := Sym p + 1
    gamTag := Gam p }

def deMorganTransform (p : CircuitProfile) : CircuitTransform :=
  { before := p
    after := p
    tag := 2
    symTag := Sym p
    gamTag := Gam p + 1 }

def thresholdLiftTransform (p : CircuitProfile) : CircuitTransform :=
  { before := p
    after := p
    tag := 3
    symTag := Sym p + 2
    gamTag := Gam p }

def monotoneProjectionTransform (p : CircuitProfile) : CircuitTransform :=
  { before := p
    after := p
    tag := 4
    symTag := Sym p
    gamTag := Gam p + 2 }

def CircuitTransform.cost (t : CircuitTransform) : Nat :=
  t.tag + t.Sym + t.Gam

def thm81_id_before (p : CircuitProfile) :
    Path (identityTransform p).before p :=
  Path.refl p

def thm82_id_after (p : CircuitProfile) :
    Path (identityTransform p).after p :=
  Path.refl p

def thm83_id_tag (p : CircuitProfile) :
    Path (identityTransform p).tag 0 :=
  Path.refl 0

def thm84_id_sym (p : CircuitProfile) :
    Path (identityTransform p).Sym (Sym p) :=
  Path.refl (Sym p)

def thm85_id_gam (p : CircuitProfile) :
    Path (identityTransform p).Gam (Gam p) :=
  Path.refl (Gam p)

def thm86_compose_before (x y : CircuitTransform) :
    Path (composeTransform x y).before x.before :=
  Path.refl x.before

def thm87_compose_after (x y : CircuitTransform) :
    Path (composeTransform x y).after y.after :=
  Path.refl y.after

def thm88_compose_tag (x y : CircuitTransform) :
    Path (composeTransform x y).tag (x.tag + y.tag) :=
  Path.refl (x.tag + y.tag)

def thm89_compose_sym (x y : CircuitTransform) :
    Path (composeTransform x y).Sym (x.Sym + y.Sym) :=
  Path.refl (x.Sym + y.Sym)

def thm90_compose_gam (x y : CircuitTransform) :
    Path (composeTransform x y).Gam (x.Gam + y.Gam) :=
  Path.refl (x.Gam + y.Gam)

def thm91_depth_balance_before (p : CircuitProfile) :
    Path (depthBalanceTransform p).before p :=
  Path.refl p

def thm92_demorgan_after (p : CircuitProfile) :
    Path (deMorganTransform p).after p :=
  Path.refl p

def thm93_threshold_lift_inputs (p : CircuitProfile) :
    Path (thresholdLiftTransform p).after.inputs p.inputs :=
  Path.refl p.inputs

def thm94_monotone_projection_size (p : CircuitProfile) :
    Path (monotoneProjectionTransform p).after.size p.size :=
  Path.refl p.size

def thm95_transform_cost_def (t : CircuitTransform) :
    Path t.cost (t.tag + t.Sym + t.Gam) :=
  Path.refl (t.tag + t.Sym + t.Gam)

def thm96_transform_cost_identity (p : CircuitProfile) :
    Path (identityTransform p).cost (Sym p + Gam p) := by
  let h : (identityTransform p).cost = Sym p + Gam p := by
    simp [CircuitTransform.cost, identityTransform, CircuitTransform.Sym, CircuitTransform.Gam]
  exact Path.mk [Step.mk _ _ h] h

def thm97_compose_tag_roundtrip (x y : CircuitTransform) :
    Path (composeTransform x y).tag (composeTransform x y).tag :=
  Path.trans (Path.refl (composeTransform x y).tag) (Path.refl (composeTransform x y).tag)

def thm98_compose_tag_symm (x y : CircuitTransform) :
    Path (x.tag + y.tag) (composeTransform x y).tag :=
  Path.symm (thm88_compose_tag x y)

def thm99_compose_tag_shift (x y : CircuitTransform) :
    Path ((composeTransform x y).tag + 1) ((x.tag + y.tag) + 1) :=
  Path.congrArg (fun n => n + 1) (thm88_compose_tag x y)

def thm100_compose_tag_assoc (x y z : CircuitTransform) :
    Path (composeTransform (composeTransform x y) z).tag
      (composeTransform x (composeTransform y z)).tag := by
  let h :
      (composeTransform (composeTransform x y) z).tag =
        (composeTransform x (composeTransform y z)).tag := by
    simp [composeTransform, Nat.add_assoc]
  exact Path.mk [Step.mk _ _ h] h

def thm101_compose_tag_assoc_symm (x y z : CircuitTransform) :
    Path (composeTransform x (composeTransform y z)).tag
      (composeTransform (composeTransform x y) z).tag :=
  Path.symm (thm100_compose_tag_assoc x y z)

def thm102_compose_tag_assoc_trans (x y z : CircuitTransform) :
    Path (composeTransform (composeTransform x y) z).tag
      (composeTransform x (composeTransform y z)).tag :=
  Path.trans (thm100_compose_tag_assoc x y z)
    (Path.refl (composeTransform x (composeTransform y z)).tag)

def thm103_compose_sym_assoc (x y z : CircuitTransform) :
    Path (composeTransform (composeTransform x y) z).Sym
      (composeTransform x (composeTransform y z)).Sym := by
  let h :
      (composeTransform (composeTransform x y) z).Sym =
        (composeTransform x (composeTransform y z)).Sym := by
    simp [composeTransform, CircuitTransform.Sym, Nat.add_assoc]
  exact Path.mk [Step.mk _ _ h] h

def thm104_compose_gam_assoc (x y z : CircuitTransform) :
    Path (composeTransform (composeTransform x y) z).Gam
      (composeTransform x (composeTransform y z)).Gam := by
  let h :
      (composeTransform (composeTransform x y) z).Gam =
        (composeTransform x (composeTransform y z)).Gam := by
    simp [composeTransform, CircuitTransform.Gam, Nat.add_assoc]
  exact Path.mk [Step.mk _ _ h] h

def thm105_balance_demorgan_tag (p : CircuitProfile) :
    Path (composeTransform (depthBalanceTransform p) (deMorganTransform p)).tag 3 :=
  Path.refl 3

def thm106_balance_demorgan_threshold_tag (p : CircuitProfile) :
    Path
      (composeTransform
        (composeTransform (depthBalanceTransform p) (deMorganTransform p))
        (thresholdLiftTransform p)).tag
      6 :=
  Path.refl 6

def thm107_projection_chain_tag (p : CircuitProfile) :
    Path
      (composeTransform
        (thresholdLiftTransform p)
        (monotoneProjectionTransform p)).tag
      7 :=
  Path.refl 7

def thm108_transform_chain_roundtrip (p : CircuitProfile) :
    Path
      (composeTransform
        (thresholdLiftTransform p)
        (monotoneProjectionTransform p)).tag
      (composeTransform
        (thresholdLiftTransform p)
        (monotoneProjectionTransform p)).tag :=
  Path.trans
    (Path.refl
      (composeTransform
        (thresholdLiftTransform p)
        (monotoneProjectionTransform p)).tag)
    (Path.refl
      (composeTransform
        (thresholdLiftTransform p)
        (monotoneProjectionTransform p)).tag)

end CircuitComplexityDeep
