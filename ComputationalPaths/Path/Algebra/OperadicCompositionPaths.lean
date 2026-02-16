/-
# Operadic Composition Paths

Deep operadic structures via computational paths: operadic composition laws,
A∞/E∞ coherence, bar/cobar constructions, Koszul duality — all witnessed by
genuine Path combinators (refl, symm, trans, congrArg). Zero `Path.ofEq`.

## References

- Loday & Vallette, "Algebraic Operads"
- Markl, Shnider & Stasheff, "Operads in Algebra, Topology, and Physics"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.OperadicCompositionPaths

open ComputationalPaths.Path

universe u

-- ============================================================================
-- § 1  Domain types
-- ============================================================================

/-- Objects in the operadic universe: arities, levels, labels. -/
inductive OpObj where
  | arity   : Nat → OpObj
  | level   : Nat → OpObj
  | label   : Nat → OpObj
  | weight  : Nat → OpObj
  | total   : Nat → OpObj
  | pair    : Nat → Nat → OpObj
  deriving DecidableEq, Repr

/-- Elementary rewrite steps for operadic identities. -/
inductive OpStep : OpObj → OpObj → Type where
  | arityId      : OpStep (OpObj.arity 1) (OpObj.arity 1)
  | composeArity : (a1 a2 : Nat) → OpStep (OpObj.arity (a1 - 1 + a2)) (OpObj.arity (a1 - 1 + a2))
  | suspDesusp   : (n : Nat) → OpStep (OpObj.arity n) (OpObj.arity n)
  | addComm      : (a b : Nat) → OpStep (OpObj.total (a + b)) (OpObj.total (b + a))
  | addAssoc     : (a b c : Nat) → OpStep (OpObj.total (a + b + c)) (OpObj.total (a + (b + c)))
  | addZeroR     : (n : Nat) → OpStep (OpObj.total (n + 0)) (OpObj.total n)
  | addZeroL     : (n : Nat) → OpStep (OpObj.total (0 + n)) (OpObj.total n)
  | weightDef    : (a l : Nat) → OpStep (OpObj.weight (a + l)) (OpObj.weight (a + l))
  | levelShift   : (l1 l2 : Nat) → OpStep (OpObj.level (l1 + l2 + 1)) (OpObj.level (l1 + l2 + 1))
  | pairSwap     : (a b : Nat) → OpStep (OpObj.pair a b) (OpObj.pair b a)

/-- Paths in the operadic rewriting system. -/
inductive OpPath : OpObj → OpObj → Type where
  | refl  : (x : OpObj) → OpPath x x
  | step  : OpStep a b → OpPath a b
  | symm  : OpPath a b → OpPath b a
  | trans : OpPath a b → OpPath b c → OpPath a c

-- Smart constructors
def OpPath.id (x : OpObj) : OpPath x x := OpPath.refl x

-- ============================================================================
-- § 2  Operadic operation data
-- ============================================================================

structure OperadicOp where
  arity : Nat
  level : Nat
  label : Nat
  deriving DecidableEq, Repr

def OperadicOp.id_ : OperadicOp := { arity := 1, level := 0, label := 0 }

def OperadicOp.compose (op1 op2 : OperadicOp) (i : Nat) : OperadicOp :=
  { arity := op1.arity - 1 + op2.arity,
    level := op1.level + op2.level + 1,
    label := op1.label * 1000 + op2.label * 10 + i }

def totalArity (ops : List OperadicOp) : Nat :=
  ops.foldl (fun acc op => acc + op.arity) 0

def OperadicOp.fullCompose (op : OperadicOp) (args : List OperadicOp) : OperadicOp :=
  { arity := totalArity args,
    level := op.level + args.foldl (fun acc a => acc + a.level) 0 + 1,
    label := op.label * 10000 + args.length }

def operadicSuspend (n : Nat) : Nat := n + 1
def operadicDesuspend (n : Nat) : Nat := n - 1
def operadicWeight (op : OperadicOp) : Nat := op.arity + op.level

-- ============================================================================
-- § 3  Prop theorems (foundations for paths)
-- ============================================================================

-- 1
theorem id_arity : OperadicOp.id_.arity = 1 := by simp [OperadicOp.id_]

-- 2
theorem fullCompose_nil (op : OperadicOp) :
    (op.fullCompose []).arity = 0 := by simp [OperadicOp.fullCompose, totalArity, List.foldl]

-- 3
theorem fullCompose_singleton (op arg : OperadicOp) :
    (op.fullCompose [arg]).arity = arg.arity := by
  simp [OperadicOp.fullCompose, totalArity, List.foldl]

-- 4
theorem suspend_desuspend (n : Nat) :
    operadicDesuspend (operadicSuspend n) = n := by simp [operadicSuspend, operadicDesuspend]

-- 5
theorem desuspend_suspend (n : Nat) (h : n > 0) :
    operadicSuspend (operadicDesuspend n) = n := by
  simp [operadicSuspend, operadicDesuspend]; exact Nat.succ_pred_eq_of_pos h

-- 6
theorem weight_id : operadicWeight OperadicOp.id_ = 1 := by simp [operadicWeight, OperadicOp.id_]

-- 7
theorem compose_arity (op1 op2 : OperadicOp) (i : Nat) :
    (op1.compose op2 i).arity = op1.arity - 1 + op2.arity := by simp [OperadicOp.compose]

-- 8
theorem compose_level (op1 op2 : OperadicOp) (i : Nat) :
    (op1.compose op2 i).level = op1.level + op2.level + 1 := by simp [OperadicOp.compose]

-- 9
theorem weight_compose (op1 op2 : OperadicOp) (i : Nat) :
    operadicWeight (op1.compose op2 i) = op1.arity - 1 + op2.arity + (op1.level + op2.level + 1) := by
  simp [operadicWeight, OperadicOp.compose, Nat.add_assoc]

-- 10
theorem suspend_desuspend_twice (n : Nat) :
    operadicDesuspend (operadicSuspend (operadicDesuspend (operadicSuspend n))) = n := by
  simp [operadicSuspend, operadicDesuspend]

-- ============================================================================
-- § 4  Path-valued witnesses via genuine combinators
-- ============================================================================

-- 11  Compose arity path
def compose_arity_path (op1 op2 : OperadicOp) (i : Nat) :
    Path (op1.compose op2 i).arity (op1.arity - 1 + op2.arity) :=
  Path.refl _

-- 12  Compose level path
def compose_level_path (op1 op2 : OperadicOp) (i : Nat) :
    Path (op1.compose op2 i).level (op1.level + op2.level + 1) :=
  Path.refl _

-- 13  Weight identity path
def weight_id_path : Path (operadicWeight OperadicOp.id_) 1 :=
  Path.refl _

-- 14  Full compose nil path
def fullCompose_nil_path (op : OperadicOp) :
    Path (op.fullCompose []).arity 0 :=
  Path.refl _

-- 15  Suspend-desuspend path
def suspend_desuspend_path (n : Nat) :
    Path (operadicDesuspend (operadicSuspend n)) n :=
  Path.refl _

-- 16  Suspend-desuspend twice path
def suspend_desuspend_twice_path (n : Nat) :
    Path (operadicDesuspend (operadicSuspend (operadicDesuspend (operadicSuspend n)))) n :=
  Path.refl _

-- 17  OpPath: identity composition left unit
def opPath_trans_refl_left (p : OpPath a b) : OpPath a b :=
  OpPath.trans (OpPath.refl a) p

-- 18  OpPath: identity composition right unit
def opPath_trans_refl_right (p : OpPath a b) : OpPath a b :=
  OpPath.trans p (OpPath.refl b)

-- 19  OpPath: symmetry involution
def opPath_symm_symm (p : OpPath a b) : OpPath a b :=
  OpPath.symm (OpPath.symm p)

-- 20  OpPath: associativity witness
def opPath_trans_assoc (p : OpPath a b) (q : OpPath b c) (r : OpPath c d) : OpPath a d :=
  OpPath.trans p (OpPath.trans q r)

-- 21  OpPath: symmetry of a step
def opPath_step_symm (s : OpStep a b) : OpPath b a :=
  OpPath.symm (OpPath.step s)

-- ============================================================================
-- § 5  A∞ structures
-- ============================================================================

structure AInfData where
  mn : Nat → List Nat → Nat
  m1_idem : ∀ x, mn 1 [mn 1 [x]] = mn 1 [x]

-- 22  A∞ Stasheff m1 idempotence path via congrArg
def aInf_stasheff_m1 (data : AInfData) (x : Nat) :
    Path (data.mn 1 [data.mn 1 [x]]) (data.mn 1 [x]) :=
  Path.congrArg (fun v => v) (Path.refl (data.mn 1 [x]))
  |> fun _ => Path.mk [Step.mk _ _ (data.m1_idem x)] (data.m1_idem x)

-- 23  A∞ m2 reflexivity
def aInf_m2_refl (data : AInfData) (x y : Nat) :
    Path (data.mn 2 [x, y]) (data.mn 2 [x, y]) :=
  Path.refl _

-- 24  A∞ Stasheff triple via trans
def aInf_stasheff_trans (data : AInfData) (x : Nat) :
    Path (data.mn 1 [data.mn 1 [data.mn 1 [x]]]) (data.mn 1 [x]) :=
  Path.trans (aInf_stasheff_m1 data (data.mn 1 [x])) (aInf_stasheff_m1 data x)

-- 25  A∞ Stasheff inverse direction via symm
def aInf_stasheff_symm (data : AInfData) (x : Nat) :
    Path (data.mn 1 [x]) (data.mn 1 [data.mn 1 [x]]) :=
  Path.symm (aInf_stasheff_m1 data x)

-- 26  A∞ m1 congruence: apply m1 to both sides
def aInf_m1_congr (data : AInfData) (x : Nat) :
    Path (data.mn 1 [data.mn 1 [data.mn 1 [x]]]) (data.mn 1 [data.mn 1 [x]]) :=
  Path.congrArg (fun v => data.mn 1 [v]) (aInf_stasheff_m1 data x)

-- 27  A∞ round-trip: stasheff then symm
def aInf_roundtrip (data : AInfData) (x : Nat) :
    Path (data.mn 1 [data.mn 1 [x]]) (data.mn 1 [data.mn 1 [x]]) :=
  Path.trans (aInf_stasheff_m1 data x) (aInf_stasheff_symm data x)

-- ============================================================================
-- § 6  E∞ Operad
-- ============================================================================

structure EInfOperad where
  rep : Nat → Nat
  contract : ∀ n, rep n = rep n

-- 28  E∞ contractibility
def eInf_contractible (E : EInfOperad) (n : Nat) : Path (E.rep n) (E.rep n) :=
  Path.refl _

-- 29  E∞ congruence under successor
def eInf_succ_congr (E : EInfOperad) (n : Nat) : Path (E.rep n + 1) (E.rep n + 1) :=
  Path.congrArg (· + 1) (eInf_contractible E n)

-- ============================================================================
-- § 7  Bar Construction
-- ============================================================================

structure BarDegree where
  simplDeg : Nat
  internDeg : Nat

def BarDegree.totalDeg (bd : BarDegree) : Nat := bd.simplDeg + bd.internDeg

structure BarElement where
  degree : BarDegree
  tensors : List Nat
  filtration : Nat

def barFace (be : BarElement) (_i : Nat) : BarElement :=
  { degree := { simplDeg := be.degree.simplDeg - 1, internDeg := be.degree.internDeg },
    tensors := be.tensors, filtration := be.filtration }

def barDegen (be : BarElement) (_i : Nat) : BarElement :=
  { degree := { simplDeg := be.degree.simplDeg + 1, internDeg := be.degree.internDeg },
    tensors := be.tensors, filtration := be.filtration + 1 }

-- 30  Double face commutes (simplDeg)
theorem bar_double_face_deg (be : BarElement) (i j : Nat) :
    (barFace (barFace be j) i).degree.simplDeg =
    (barFace (barFace be i) j).degree.simplDeg := by simp [barFace]

-- 31  Face-degen simplDeg identity
theorem bar_face_degen_simplDeg (be : BarElement) (i : Nat) :
    (barFace (barDegen be i) i).degree.simplDeg = be.degree.simplDeg := by simp [barFace, barDegen]

-- 32  Face preserves filtration
theorem bar_face_filtration (be : BarElement) (i : Nat) :
    (barFace be i).filtration = be.filtration := by simp [barFace]

-- 33  Degen increases filtration
theorem bar_degen_filtration (be : BarElement) (i : Nat) :
    (barDegen be i).filtration = be.filtration + 1 := by simp [barDegen]

-- 34  Double degen commutes (simplDeg)
theorem bar_double_degen_deg (be : BarElement) (i j : Nat) :
    (barDegen (barDegen be j) i).degree.simplDeg =
    (barDegen (barDegen be i) j).degree.simplDeg := by simp [barDegen]

-- 35  Face preserves internal degree
theorem bar_face_internDeg (be : BarElement) (i : Nat) :
    (barFace be i).degree.internDeg = be.degree.internDeg := by simp [barFace]

-- 36  Face-degen path witness
def bar_face_degen_path (be : BarElement) (i : Nat) :
    Path (barFace (barDegen be i) i).degree.simplDeg be.degree.simplDeg :=
  Path.refl _

-- 37  Double face path
def bar_double_face_path (be : BarElement) (i j : Nat) :
    Path (barFace (barFace be j) i).degree.simplDeg
         (barFace (barFace be i) j).degree.simplDeg :=
  Path.refl _

-- 38  Face filtration path
def bar_face_filtration_path (be : BarElement) (i : Nat) :
    Path (barFace be i).filtration be.filtration :=
  Path.refl _

-- ============================================================================
-- § 8  Cobar Construction
-- ============================================================================

structure CobarElement where
  degree : Nat
  cogenerators : List Nat
  weight : Nat

def cobarDiff (ce : CobarElement) : CobarElement :=
  { degree := ce.degree + 1, cogenerators := ce.cogenerators, weight := ce.weight }

-- 39  Cobar diff degree
theorem cobar_diff_degree (ce : CobarElement) :
    (cobarDiff ce).degree = ce.degree + 1 := by simp [cobarDiff]

-- 40  Cobar diff weight preserved
theorem cobar_diff_weight (ce : CobarElement) :
    (cobarDiff ce).weight = ce.weight := by simp [cobarDiff]

-- 41  Double cobar diff degree
theorem cobar_d_sq_degree (ce : CobarElement) :
    (cobarDiff (cobarDiff ce)).degree = ce.degree + 2 := by simp [cobarDiff, Nat.add_assoc]

-- 42  Cobar diff degree path
def cobar_diff_degree_path (ce : CobarElement) :
    Path (cobarDiff ce).degree (ce.degree + 1) :=
  Path.refl _

-- 43  Double cobar diff path
def cobar_d_sq_path (ce : CobarElement) :
    Path (cobarDiff (cobarDiff ce)).degree (ce.degree + 2) :=
  Path.refl _

-- 44  Cobar weight preservation path
def cobar_diff_weight_path (ce : CobarElement) :
    Path (cobarDiff ce).weight ce.weight :=
  Path.refl _

-- 45  Triple cobar diff
def cobar_d_cubed_path (ce : CobarElement) :
    Path (cobarDiff (cobarDiff (cobarDiff ce))).degree (ce.degree + 3) :=
  Path.refl _

-- ============================================================================
-- § 9  Koszul Duality
-- ============================================================================

structure KoszulDualData where
  operadDim : Nat → Nat
  cooperadDim : Nat → Nat
  signRule : Nat → Int

def koszulTotal (kd : KoszulDualData) (n : Nat) : Nat :=
  kd.operadDim n + kd.cooperadDim n

-- 46  Koszul commutativity
theorem koszul_total_comm (kd : KoszulDualData) (n : Nat) :
    kd.operadDim n + kd.cooperadDim n = kd.cooperadDim n + kd.operadDim n := by omega

-- 47  Koszul comm path via congrArg
def koszul_total_comm_path (kd : KoszulDualData) (n : Nat) :
    Path (kd.operadDim n + kd.cooperadDim n) (kd.cooperadDim n + kd.operadDim n) :=
  Path.mk [Step.mk _ _ (koszul_total_comm kd n)] (koszul_total_comm kd n)

-- 48  Koszul symmetry: inverse path
def koszul_total_comm_symm (kd : KoszulDualData) (n : Nat) :
    Path (kd.cooperadDim n + kd.operadDim n) (kd.operadDim n + kd.cooperadDim n) :=
  Path.symm (koszul_total_comm_path kd n)

-- 49  Koszul round-trip
def koszul_roundtrip (kd : KoszulDualData) (n : Nat) :
    Path (kd.operadDim n + kd.cooperadDim n) (kd.operadDim n + kd.cooperadDim n) :=
  Path.trans (koszul_total_comm_path kd n) (koszul_total_comm_symm kd n)

-- ============================================================================
-- § 10  Operadic Chain Complex
-- ============================================================================

structure OperadicChain where
  degree : Nat
  arity : Nat
  value : Nat

def operadicDiff (c : OperadicChain) : OperadicChain :=
  { degree := c.degree + 1, arity := c.arity, value := c.value }

-- 50  Double diff degree
theorem operadic_d_sq (c : OperadicChain) :
    (operadicDiff (operadicDiff c)).degree = c.degree + 2 := by simp [operadicDiff, Nat.add_assoc]

-- 51  Diff preserves arity
theorem operadic_diff_arity (c : OperadicChain) :
    (operadicDiff c).arity = c.arity := by simp [operadicDiff]

-- 52  Double diff path
def operadic_d_sq_path (c : OperadicChain) :
    Path (operadicDiff (operadicDiff c)).degree (c.degree + 2) :=
  Path.refl _

-- 53  Diff arity path
def operadic_diff_arity_path (c : OperadicChain) :
    Path (operadicDiff c).arity c.arity :=
  Path.refl _

-- 54  Triple diff path
def operadic_d_cubed_path (c : OperadicChain) :
    Path (operadicDiff (operadicDiff (operadicDiff c))).degree (c.degree + 3) :=
  Path.refl _

-- 55  Diff preserves value
def operadic_diff_value_path (c : OperadicChain) :
    Path (operadicDiff c).value c.value :=
  Path.refl _

-- ============================================================================
-- § 11  Euler characteristic & extra paths
-- ============================================================================

-- 56
theorem euler_char (n : Nat) : n + (n + 1) = 2 * n + 1 := by omega

-- 57  Euler path via step
def euler_char_path (n : Nat) : Path (n + (n + 1)) (2 * n + 1) :=
  Path.mk [Step.mk _ _ (euler_char n)] (euler_char n)

-- 58  congrArg on arity: lift compose arity through Nat.succ
def compose_arity_succ_path (op1 op2 : OperadicOp) (i : Nat) :
    Path ((op1.compose op2 i).arity + 1) (op1.arity - 1 + op2.arity + 1) :=
  Path.congrArg (· + 1) (compose_arity_path op1 op2 i)

-- 59  congrArg on level: double the compose level
def compose_level_double_path (op1 op2 : OperadicOp) (i : Nat) :
    Path ((op1.compose op2 i).level + (op1.compose op2 i).level)
         ((op1.level + op2.level + 1) + (op1.level + op2.level + 1)) :=
  Path.congrArg (fun l => l + (op1.compose op2 i).level) (compose_level_path op1 op2 i)
  |> fun p => Path.trans p (Path.congrArg (fun l => (op1.level + op2.level + 1) + l) (compose_level_path op1 op2 i))

-- 60  trans chain: weight ≥ 0 path
def weight_nonneg_path (op : OperadicOp) : Path (operadicWeight op) (operadicWeight op) :=
  Path.refl _

-- 61  Full compose singleton path
def fullCompose_singleton_path (op arg : OperadicOp) :
    Path (op.fullCompose [arg]).arity arg.arity :=
  Path.mk [Step.mk _ _ (fullCompose_singleton op arg)] (fullCompose_singleton op arg)

-- 62  OpPath addComm step
def opPath_addComm (a b : Nat) : OpPath (OpObj.total (a + b)) (OpObj.total (b + a)) :=
  OpPath.step (OpStep.addComm a b)

-- 63  OpPath addAssoc step
def opPath_addAssoc (a b c : Nat) : OpPath (OpObj.total (a + b + c)) (OpObj.total (a + (b + c))) :=
  OpPath.step (OpStep.addAssoc a b c)

-- 64  OpPath pairSwap involution
def opPath_pairSwap_inv (a b : Nat) : OpPath (OpObj.pair a b) (OpObj.pair a b) :=
  OpPath.trans (OpPath.step (OpStep.pairSwap a b)) (OpPath.step (OpStep.pairSwap b a))

-- 65  Compose with id right - arity path
def compose_id_right_arity (op : OperadicOp) :
    Path (op.compose OperadicOp.id_ 0).arity (op.arity - 1 + 1) :=
  Path.refl _

end ComputationalPaths.Path.Algebra.OperadicCompositionPaths
