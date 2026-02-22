/-
  ComputationalPaths/Path/Rewriting/TreeAutomataDeep.lean

  Tree Automata and Term Recognition via Computational Paths

  We model ranked alphabets, ground terms as trees, bottom-up and top-down
  tree automata, runs, regular tree languages, closure properties,
  pumping, transducers, determinism, and Myhill-Nerode — all connected
  through computational paths (Path.trans, Path.symm, Path.congrArg).
-/

import ComputationalPaths.Path.Basic

namespace TreeAutomataDeep

open ComputationalPaths

/-! ## Ranked Alphabet and Ground Terms -/

/-- A ranked symbol: a name together with its arity. -/
structure RankedSym where
  name : Nat
  arity : Nat
  deriving DecidableEq, Repr

/-- Ground terms (trees) over a ranked alphabet. -/
inductive GTerm : Type where
  | node : RankedSym → List GTerm → GTerm
  deriving Repr

/-- The root symbol of a ground term. -/
noncomputable def GTerm.rootSym : GTerm → RankedSym
  | .node f _ => f

/-- The children (subtrees) of a ground term. -/
noncomputable def GTerm.children : GTerm → List GTerm
  | .node _ cs => cs

/-- Depth of a ground term. -/
noncomputable def GTerm.depth : GTerm → Nat
  | .node _ [] => 0
  | .node _ cs => 1 + cs.foldl (fun acc c => max acc c.depth) 0

/-- Size (number of nodes) of a ground term. -/
noncomputable def GTerm.size : GTerm → Nat
  | .node _ cs => 1 + cs.foldl (fun acc c => acc + c.size) 0

/-- A leaf is a node with no children. -/
noncomputable def GTerm.isLeaf : GTerm → Bool
  | .node _ [] => true
  | .node _ (_ :: _) => false

/-! ## States and Bottom-Up Tree Automaton (BUTA) -/

/-- State type for tree automata. -/
structure TAState where
  id : Nat
  deriving DecidableEq, Repr

/-- A bottom-up tree automaton transition. -/
structure BUTransition where
  symbol : RankedSym
  inputStates : List TAState
  outputState : TAState
  deriving DecidableEq, Repr

/-- Bottom-Up Tree Automaton. -/
structure BUTA where
  states : List TAState
  alphabet : List RankedSym
  transitions : List BUTransition
  finalStates : List TAState

/-- Check if a transition matches a symbol and input states. -/
noncomputable def BUTransition.matches (tr : BUTransition) (f : RankedSym) (qs : List TAState) : Bool :=
  tr.symbol == f && tr.inputStates == qs

/-- Find applicable transitions in a BUTA. -/
noncomputable def BUTA.findTransitions (aut : BUTA) (f : RankedSym) (qs : List TAState) : List TAState :=
  (aut.transitions.filter (fun tr => tr.matches f qs)).map BUTransition.outputState

/-- Whether a state is final. -/
noncomputable def BUTA.isFinal (aut : BUTA) (q : TAState) : Bool :=
  aut.finalStates.any (· == q)

/-! ## Top-Down Tree Automaton (TDTA) -/

/-- A top-down tree automaton transition. -/
structure TDTransition where
  inputState : TAState
  symbol : RankedSym
  outputStates : List TAState
  deriving DecidableEq, Repr

/-- Top-Down Tree Automaton. -/
structure TDTA where
  states : List TAState
  alphabet : List RankedSym
  transitions : List TDTransition
  initialStates : List TAState

/-- Find applicable top-down transitions. -/
noncomputable def TDTA.findTransitions (aut : TDTA) (q : TAState) (f : RankedSym) : List (List TAState) :=
  (aut.transitions.filter (fun tr => tr.inputState == q && tr.symbol == f)).map TDTransition.outputStates

/-! ## Run of a Tree Automaton as a Path -/

/-- A run configuration: a term paired with its state assignment. -/
structure RunConfig where
  term : GTerm
  state : TAState
  deriving Repr

/-- A partial run step in the bottom-up run. -/
noncomputable def RunConfig.step (rc : RunConfig) (q' : TAState) : RunConfig :=
  { rc with state := q' }

/-! ## Recognition Witness -/

/-- A recognition witness: evidence that a BUTA accepts a term. -/
inductive BUWitness : BUTA → GTerm → TAState → Type where
  | leaf : (aut : BUTA) → (f : RankedSym) →
           (q : TAState) → q ∈ aut.findTransitions f [] →
           BUWitness aut (.node f []) q
  | step : (aut : BUTA) → (f : RankedSym) →
           (cs : List GTerm) → (qs : List TAState) →
           (q : TAState) → q ∈ aut.findTransitions f qs →
           BUWitness aut (.node f cs) q

/-- Acceptance means reaching a final state. -/
structure BUAccepts (aut : BUTA) (t : GTerm) where
  state : TAState
  witness : BUWitness aut t state
  isFinal : aut.isFinal state = true

/-! ## Regular Tree Languages -/

/-- A tree language is a set of ground terms. -/
noncomputable def TreeLang := GTerm → Prop

/-- The language accepted by a BUTA. -/
noncomputable def BUTA.lang (aut : BUTA) : TreeLang :=
  fun t => ∃ q, q ∈ aut.finalStates ∧ (aut.findTransitions t.rootSym []).any (· == q) = true

/-- A tree language is regular if recognized by some BUTA. -/
noncomputable def IsRegularTreeLang (L : TreeLang) : Prop :=
  ∃ aut : BUTA, ∀ t, L t ↔ BUTA.lang aut t

/-! ## Path-based reasoning about automaton configurations -/

/-- Configuration of a tree automaton. -/
structure AutoConfig where
  currentStates : List TAState
  processed : Nat
  deriving DecidableEq, Repr

/-- Identity path on an automaton configuration. -/
noncomputable def autoConfigRefl (cfg : AutoConfig) : Path cfg cfg :=
  Path.refl cfg

/-- Transitivity of configuration paths. -/
noncomputable def autoConfigTrans {a b c : AutoConfig}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Symmetry of configuration paths. -/
noncomputable def autoConfigSymm {a b : AutoConfig}
    (p : Path a b) : Path b a :=
  Path.symm p

/-! ## Theorems: Path composition for automata runs -/

/-- Theorem 1: Reflexivity composes trivially. -/
theorem run_path_refl (cfg : AutoConfig) :
    autoConfigTrans (autoConfigRefl cfg) (autoConfigRefl cfg) =
    autoConfigRefl cfg := by
  unfold autoConfigTrans autoConfigRefl
  simp [Path.trans_refl_left]

/-- Theorem 2: Associativity of run path composition. -/
theorem run_path_assoc {a b c d : AutoConfig}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    autoConfigTrans (autoConfigTrans p q) r =
    autoConfigTrans p (autoConfigTrans q r) := by
  unfold autoConfigTrans
  simp [Path.trans_assoc]

/-- Theorem 3: Symm distributes over trans for run paths. -/
theorem run_path_symm_trans {a b c : AutoConfig}
    (p : Path a b) (q : Path b c) :
    autoConfigSymm (autoConfigTrans p q) =
    autoConfigTrans (autoConfigSymm q) (autoConfigSymm p) := by
  unfold autoConfigSymm autoConfigTrans
  simp [Path.symm_trans]

/-! ## Product Construction for Intersection -/

/-- Product state of two automata. -/
structure ProdState where
  fst : TAState
  snd : TAState
  deriving DecidableEq, Repr

/-- Encode product state as single state. -/
noncomputable def encodeProd (p : ProdState) : TAState :=
  ⟨p.fst.id * 1000 + p.snd.id⟩

/-- Product transition. -/
noncomputable def prodTransition (tr1 : BUTransition) (tr2 : BUTransition) : Option BUTransition :=
  if tr1.symbol == tr2.symbol && tr1.inputStates.length == tr2.inputStates.length then
    some {
      symbol := tr1.symbol
      inputStates := List.zipWith (fun a b => (⟨a.id * 1000 + b.id⟩ : TAState))
                       tr1.inputStates tr2.inputStates
      outputState := ⟨tr1.outputState.id * 1000 + tr2.outputState.id⟩
    }
  else
    none

/-- The product automaton for intersection. -/
noncomputable def BUTA.product (a1 a2 : BUTA) : BUTA where
  states := Id.run do
    let mut res : List TAState := []
    for s1 in a1.states do
      for s2 in a2.states do
        res := ⟨s1.id * 1000 + s2.id⟩ :: res
    return res
  alphabet := a1.alphabet
  transitions := Id.run do
    let mut res : List BUTransition := []
    for t1 in a1.transitions do
      for t2 in a2.transitions do
        match prodTransition t1 t2 with
        | some t => res := t :: res
        | none => pure ()
    return res
  finalStates := Id.run do
    let mut res : List TAState := []
    for f1 in a1.finalStates do
      for f2 in a2.finalStates do
        res := ⟨f1.id * 1000 + f2.id⟩ :: res
    return res

/-! ## Union Construction -/

/-- Disjoint union of states. -/
noncomputable def disjointState (side : Bool) (q : TAState) : TAState :=
  ⟨if side then q.id * 2 + 1 else q.id * 2⟩

/-- Shift a transition to a side of the disjoint union. -/
noncomputable def shiftTransition (side : Bool) (tr : BUTransition) : BUTransition where
  symbol := tr.symbol
  inputStates := tr.inputStates.map (disjointState side)
  outputState := disjointState side tr.outputState

/-- The union automaton. -/
noncomputable def BUTA.union (a1 a2 : BUTA) : BUTA where
  states := a1.states.map (disjointState false) ++ a2.states.map (disjointState true)
  alphabet := a1.alphabet ++ a2.alphabet
  transitions := a1.transitions.map (shiftTransition false) ++
                 a2.transitions.map (shiftTransition true)
  finalStates := a1.finalStates.map (disjointState false) ++
                 a2.finalStates.map (disjointState true)

/-! ## Complement Construction -/

/-- Complement automaton (assumes deterministic and complete). -/
noncomputable def BUTA.complement (aut : BUTA) : BUTA where
  states := aut.states
  alphabet := aut.alphabet
  transitions := aut.transitions
  finalStates := aut.states.filter (fun q => !aut.isFinal q)

/-! ## Path-lifted function application -/

/-- Apply a function on TAState through a path. -/
noncomputable def liftStateFun (f : TAState → TAState) {a b : TAState}
    (p : Path a b) : Path (f a) (f b) :=
  Path.congrArg f p

/-- Theorem 4: Lifting preserves transitivity. -/
theorem lift_state_trans (f : TAState → TAState) {a b c : TAState}
    (p : Path a b) (q : Path b c) :
    liftStateFun f (Path.trans p q) =
    Path.trans (liftStateFun f p) (liftStateFun f q) := by
  unfold liftStateFun
  simp [Path.congrArg_trans]

/-- Theorem 5: Lifting preserves symmetry. -/
theorem lift_state_symm (f : TAState → TAState) {a b : TAState}
    (p : Path a b) :
    liftStateFun f (Path.symm p) =
    Path.symm (liftStateFun f p) := by
  unfold liftStateFun
  simp [Path.congrArg_symm]

/-- Theorem 6: Lifting refl is refl. -/
theorem lift_state_refl (f : TAState → TAState) (a : TAState) :
    liftStateFun f (Path.refl a) = Path.refl (f a) := by
  unfold liftStateFun
  rfl

/-! ## Run Composition Paths -/

/-- A run segment: evidence of processing part of a tree. -/
structure RunSegment where
  startState : TAState
  endState : TAState
  depth : Nat
  deriving DecidableEq, Repr

/-- Identity run segment. -/
noncomputable def RunSegment.idSeg (q : TAState) : RunSegment :=
  ⟨q, q, 0⟩

/-- Compose two run segments. -/
noncomputable def RunSegment.compose (s1 s2 : RunSegment) : RunSegment :=
  ⟨s1.startState, s2.endState, s1.depth + s2.depth⟩

/-! ## Deterministic Bottom-Up Tree Automaton -/

/-- A BUTA is deterministic if each (symbol, input-states) pair has at most one transition. -/
noncomputable def BUTA.isDeterministic (aut : BUTA) : Prop :=
  ∀ f qs, (aut.findTransitions f qs).length ≤ 1

/-- A complete BUTA has at least one transition for every (symbol, input-states). -/
noncomputable def BUTA.isComplete (aut : BUTA) : Prop :=
  ∀ f qs, (aut.findTransitions f qs).length ≥ 1

/-! ## State Equivalence and Myhill-Nerode -/

/-- A context is a term with a hole. -/
inductive Context : Type where
  | hole : Context
  | node : RankedSym → List Context → Context

/-- Plug a term into a context. -/
noncomputable def Context.plug : Context → GTerm → GTerm
  | .hole, t => t
  | .node f cs, t => .node f (cs.map (·.plug t))

/-- Myhill-Nerode equivalence for trees. -/
noncomputable def mnEquiv (L : TreeLang) (t1 t2 : GTerm) : Prop :=
  ∀ c : Context, L (c.plug t1) ↔ L (c.plug t2)

/-- Theorem 7: MN equivalence is reflexive. -/
theorem mnEquiv_refl (L : TreeLang) (t : GTerm) : mnEquiv L t t := by
  intro c; exact Iff.rfl

/-- Theorem 8: MN equivalence is symmetric. -/
theorem mnEquiv_symm (L : TreeLang) {t1 t2 : GTerm}
    (h : mnEquiv L t1 t2) : mnEquiv L t2 t1 := by
  intro c; exact (h c).symm

/-- Theorem 9: MN equivalence is transitive. -/
theorem mnEquiv_trans (L : TreeLang) {t1 t2 t3 : GTerm}
    (h1 : mnEquiv L t1 t2) (h2 : mnEquiv L t2 t3) : mnEquiv L t1 t3 := by
  intro c; exact (h1 c).trans (h2 c)

/-! ## Path-Witnessed State Equivalence -/

/-- Two states are equivalent if they accept the same trees. -/
noncomputable def stateEquiv (aut : BUTA) (q1 q2 : TAState) : Prop :=
  ∀ t : GTerm, (q1 ∈ aut.findTransitions t.rootSym []) ↔
               (q2 ∈ aut.findTransitions t.rootSym [])

/-- Theorem 10: State equivalence is reflexive. -/
theorem stateEquiv_refl (aut : BUTA) (q : TAState) :
    stateEquiv aut q q := by
  intro _; exact Iff.rfl

/-- Theorem 11: State equivalence is symmetric. -/
theorem stateEquiv_symm (aut : BUTA) {q1 q2 : TAState}
    (h : stateEquiv aut q1 q2) : stateEquiv aut q2 q1 := by
  intro t; exact (h t).symm

/-- Theorem 12: State equivalence is transitive. -/
theorem stateEquiv_trans (aut : BUTA) {q1 q2 q3 : TAState}
    (h1 : stateEquiv aut q1 q2) (h2 : stateEquiv aut q2 q3) :
    stateEquiv aut q1 q3 := by
  intro t; exact (h1 t).trans (h2 t)

/-! ## Tree Transducers -/

/-- A bottom-up tree transducer rule. -/
structure BUTransducerRule where
  inputSym : RankedSym
  inputStates : List TAState
  outputState : TAState
  outputTerm : GTerm

/-- Bottom-up tree transducer. -/
structure BUTransducer where
  states : List TAState
  inputAlphabet : List RankedSym
  outputAlphabet : List RankedSym
  rules : List BUTransducerRule
  finalStates : List TAState

/-- Top-down tree transducer rule. -/
structure TDTransducerRule where
  inputState : TAState
  inputSym : RankedSym
  outputStates : List TAState
  outputTerm : GTerm

/-- Top-down tree transducer. -/
structure TDTransducer where
  states : List TAState
  inputAlphabet : List RankedSym
  outputAlphabet : List RankedSym
  rules : List TDTransducerRule
  initialState : TAState

/-! ## Path Structure on Transducer Configs -/

/-- Transducer configuration. -/
structure TransConfig where
  state : TAState
  inputRemaining : GTerm
  outputSoFar : GTerm
  deriving Repr

/-- Theorem 13: Transducer path composition with refl right. -/
theorem trans_config_compose {a b c : TransConfig}
    (p : Path a b) (q : Path b c) :
    Path.trans (Path.trans p q) (Path.refl c) = Path.trans p q := by
  simp [Path.trans_refl_right]

/-- Theorem 14: Transducer path symm distributes over trans. -/
theorem trans_config_symm_dist {a b c : TransConfig}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp [Path.symm_trans]

/-! ## Pumping for Tree Languages -/

/-- A context decomposition of a tree: C[C'[t]]. -/
structure TreeDecomp where
  outer : Context
  inner : Context
  core : GTerm

/-- Pump the inner context n times. -/
noncomputable def pumpContext : Nat → Context → Context → Context
  | 0, _, inner => inner
  | n + 1, outer, inner =>
    match outer with
    | .hole => pumpContext n outer inner
    | .node f cs => .node f (cs.map (fun c => pumpContext n c inner))

/-- The pumping property for tree languages. -/
noncomputable def TreePumpingProp (L : TreeLang) (n : Nat) : Prop :=
  ∀ t : GTerm, t.size > n → L t →
    ∃ d : TreeDecomp,
      L (d.outer.plug (d.inner.plug d.core)) ∧
      L (d.outer.plug d.core)

/-! ## Path Coherence Theorems -/

/-- Theorem 15: Double symmetry is identity. -/
theorem path_symm_symm_auto {a b : AutoConfig}
    (p : Path a b) : Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-- Theorem 16: refl is left identity of trans. -/
theorem path_refl_trans_auto {a b : AutoConfig}
    (p : Path a b) : Path.trans (Path.refl a) p = p := by
  simp [Path.trans_refl_left]

/-- Theorem 17: refl is right identity of trans. -/
theorem path_trans_refl_auto {a b : AutoConfig}
    (p : Path a b) : Path.trans p (Path.refl b) = p := by
  simp [Path.trans_refl_right]

/-- Theorem 18: congrArg distributes over trans on AutoConfig. -/
theorem path_congrArg_trans_auto (f : AutoConfig → AutoConfig)
    {a b c : AutoConfig} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) := by
  simp [Path.congrArg_trans]

/-- Theorem 19: congrArg distributes over symm on AutoConfig. -/
theorem path_congrArg_symm_auto (f : AutoConfig → AutoConfig)
    {a b : AutoConfig} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) := by
  simp [Path.congrArg_symm]

/-! ## Closure Under Homomorphism -/

/-- A tree homomorphism. -/
structure TreeHom where
  mapSym : RankedSym → RankedSym
  preserveArity : ∀ f, (mapSym f).arity = f.arity

/-- Apply a tree homomorphism. -/
noncomputable def TreeHom.apply (h : TreeHom) : GTerm → GTerm
  | .node f cs => .node (h.mapSym f) (cs.map h.apply)

/-- Image of a tree language under a homomorphism. -/
noncomputable def TreeLang.image (L : TreeLang) (h : TreeHom) : TreeLang :=
  fun t => ∃ t', L t' ∧ h.apply t' = t

/-- Preimage of a tree language under a homomorphism. -/
noncomputable def TreeLang.preimage (L : TreeLang) (h : TreeHom) : TreeLang :=
  fun t => L (h.apply t)

/-! ## Path Lifting Through Tree Hom -/

/-- Theorem 20: Hom preserves path on root sym. -/
theorem hom_preserves_rootSym (h : TreeHom) (f : RankedSym) (cs : List GTerm) :
    (h.apply (.node f cs)).rootSym = h.mapSym f := by
  simp [TreeHom.apply, GTerm.rootSym]

/-- Lift a path through tree hom application. -/
noncomputable def liftHomPath (h : TreeHom) {t1 t2 : GTerm}
    (p : Path t1 t2) : Path (h.apply t1) (h.apply t2) :=
  Path.congrArg h.apply p

/-- Theorem 21: Lifting hom preserves trans. -/
theorem liftHom_trans (h : TreeHom) {t1 t2 t3 : GTerm}
    (p : Path t1 t2) (q : Path t2 t3) :
    liftHomPath h (Path.trans p q) =
    Path.trans (liftHomPath h p) (liftHomPath h q) := by
  unfold liftHomPath
  simp [Path.congrArg_trans]

/-- Theorem 22: Lifting hom preserves symm. -/
theorem liftHom_symm (h : TreeHom) {t1 t2 : GTerm}
    (p : Path t1 t2) :
    liftHomPath h (Path.symm p) =
    Path.symm (liftHomPath h p) := by
  unfold liftHomPath
  simp [Path.congrArg_symm]

/-- Theorem 23: Lifting hom preserves refl. -/
theorem liftHom_refl (h : TreeHom) (t : GTerm) :
    liftHomPath h (Path.refl t) = Path.refl (h.apply t) := by
  unfold liftHomPath
  rfl

/-! ## State Mapping and Minimization -/

/-- A state mapping between automata. -/
structure StateMap where
  map : TAState → TAState

/-- Apply state map to a transition. -/
noncomputable def StateMap.applyTransition (sm : StateMap) (tr : BUTransition) : BUTransition where
  symbol := tr.symbol
  inputStates := tr.inputStates.map sm.map
  outputState := sm.map tr.outputState

/-- Apply state map to a BUTA. -/
noncomputable def StateMap.applyBUTA (sm : StateMap) (aut : BUTA) : BUTA where
  states := aut.states.map sm.map
  alphabet := aut.alphabet
  transitions := aut.transitions.map sm.applyTransition
  finalStates := aut.finalStates.map sm.map

/-- Path witnessing state map coherence. -/
noncomputable def stateMapPath (sm : StateMap) {q1 q2 : TAState}
    (p : Path q1 q2) : Path (sm.map q1) (sm.map q2) :=
  Path.congrArg sm.map p

/-- Theorem 24: State map path preserves trans. -/
theorem stateMap_trans (sm : StateMap) {q1 q2 q3 : TAState}
    (p : Path q1 q2) (r : Path q2 q3) :
    stateMapPath sm (Path.trans p r) =
    Path.trans (stateMapPath sm p) (stateMapPath sm r) := by
  unfold stateMapPath
  simp [Path.congrArg_trans]

/-- Theorem 25: State map path preserves symm. -/
theorem stateMap_symm (sm : StateMap) {q1 q2 : TAState}
    (p : Path q1 q2) :
    stateMapPath sm (Path.symm p) =
    Path.symm (stateMapPath sm p) := by
  unfold stateMapPath
  simp [Path.congrArg_symm]

/-! ## Congruence Closure -/

/-- A congruence on states. -/
structure StateCong where
  rel : TAState → TAState → Prop
  isRefl : ∀ q, rel q q
  isSym : ∀ {q1 q2}, rel q1 q2 → rel q2 q1
  isTrans : ∀ {q1 q2 q3}, rel q1 q2 → rel q2 q3 → rel q1 q3

/-- Theorem 26: Path implies congruence. -/
theorem path_implies_cong (sc : StateCong) {q1 q2 : TAState}
    (p : Path q1 q2) : sc.rel q1 q2 := by
  have h := p.toEq
  subst h
  exact sc.isRefl q1

/-! ## Path Algebra on RunSegment -/

/-- Theorem 27: RunSegment paths compose associatively. -/
theorem runSeg_assoc {a b c d : RunSegment}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp [Path.trans_assoc]

/-- Theorem 28: Symm distributes over trans for RunSegment. -/
theorem runSeg_symm_trans {a b c : RunSegment}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) := by
  simp [Path.symm_trans]

/-- Theorem 29: Double symm for RunSegment. -/
theorem runSeg_symm_symm {a b : RunSegment}
    (p : Path a b) : Path.symm (Path.symm p) = p :=
  Path.symm_symm p

/-! ## Tree Language Operations -/

/-- Union of tree languages. -/
noncomputable def TreeLang.union (L1 L2 : TreeLang) : TreeLang :=
  fun t => L1 t ∨ L2 t

/-- Intersection of tree languages. -/
noncomputable def TreeLang.inter (L1 L2 : TreeLang) : TreeLang :=
  fun t => L1 t ∧ L2 t

/-- Complement of a tree language. -/
noncomputable def TreeLang.compl (L : TreeLang) : TreeLang :=
  fun t => ¬ L t

/-- Theorem 30: Double complement is identity. -/
theorem treeLang_compl_compl (L : TreeLang) (t : GTerm) :
    TreeLang.compl (TreeLang.compl L) t ↔ L t := by
  unfold TreeLang.compl
  constructor
  · intro h; exact Classical.byContradiction (fun hn => h hn)
  · intro h hn; exact hn h

/-- Theorem 31: Union is commutative. -/
theorem treeLang_union_comm (L1 L2 : TreeLang) (t : GTerm) :
    TreeLang.union L1 L2 t ↔ TreeLang.union L2 L1 t := by
  unfold TreeLang.union
  exact Or.comm

/-- Theorem 32: Intersection is commutative. -/
theorem treeLang_inter_comm (L1 L2 : TreeLang) (t : GTerm) :
    TreeLang.inter L1 L2 t ↔ TreeLang.inter L2 L1 t := by
  unfold TreeLang.inter
  exact And.comm

/-- Theorem 33: De Morgan for tree languages (one direction). -/
theorem treeLang_deMorgan_union (L1 L2 : TreeLang) (t : GTerm) :
    TreeLang.compl (TreeLang.union L1 L2) t →
    TreeLang.inter (TreeLang.compl L1) (TreeLang.compl L2) t := by
  unfold TreeLang.compl TreeLang.union TreeLang.inter
  intro h
  exact ⟨fun h1 => h (Or.inl h1), fun h2 => h (Or.inr h2)⟩

/-- Theorem 34: De Morgan for tree languages (other direction). -/
theorem treeLang_deMorgan_union' (L1 L2 : TreeLang) (t : GTerm) :
    TreeLang.inter (TreeLang.compl L1) (TreeLang.compl L2) t →
    TreeLang.compl (TreeLang.union L1 L2) t := by
  unfold TreeLang.compl TreeLang.union TreeLang.inter
  intro ⟨h1, h2⟩ h
  cases h with
  | inl h => exact h1 h
  | inr h => exact h2 h

/-- Theorem 35: Union with complement is everything. -/
theorem treeLang_union_compl (L : TreeLang) (t : GTerm) :
    TreeLang.union L (TreeLang.compl L) t := by
  unfold TreeLang.union TreeLang.compl
  exact Classical.em (L t)

/-- Theorem 36: Intersection with complement is empty. -/
theorem treeLang_inter_compl (L : TreeLang) (t : GTerm) :
    ¬ TreeLang.inter L (TreeLang.compl L) t := by
  unfold TreeLang.inter TreeLang.compl
  intro ⟨h1, h2⟩
  exact h2 h1

/-! ## Equivalence of Automata -/

/-- Two automata are equivalent if they recognize the same language. -/
noncomputable def autEquiv (a1 a2 : BUTA) : Prop :=
  ∀ t, BUTA.lang a1 t ↔ BUTA.lang a2 t

/-- Theorem 37: Automata equivalence is reflexive. -/
theorem autEquiv_refl (a : BUTA) : autEquiv a a := by
  intro _; exact Iff.rfl

/-- Theorem 38: Automata equivalence is symmetric. -/
theorem autEquiv_symm {a1 a2 : BUTA} (h : autEquiv a1 a2) :
    autEquiv a2 a1 := by
  intro t; exact (h t).symm

/-- Theorem 39: Automata equivalence is transitive. -/
theorem autEquiv_trans {a1 a2 a3 : BUTA}
    (h1 : autEquiv a1 a2) (h2 : autEquiv a2 a3) :
    autEquiv a1 a3 := by
  intro t; exact (h1 t).trans (h2 t)

/-! ## Path-Based Tree Substitution -/

/-- Substitute at the root: replace root symbol. -/
noncomputable def substRoot (t : GTerm) (f : RankedSym) : GTerm :=
  .node f t.children

/-- Path showing substitution coherence. -/
noncomputable def substRootPath (f : RankedSym) {t1 t2 : GTerm}
    (p : Path t1 t2) : Path (substRoot t1 f) (substRoot t2 f) :=
  Path.congrArg (substRoot · f) p

/-- Theorem 40: substRoot path preserves trans. -/
theorem substRoot_trans (f : RankedSym) {t1 t2 t3 : GTerm}
    (p : Path t1 t2) (q : Path t2 t3) :
    substRootPath f (Path.trans p q) =
    Path.trans (substRootPath f p) (substRootPath f q) := by
  unfold substRootPath
  simp [Path.congrArg_trans]

/-- Theorem 41: substRoot path preserves symm. -/
theorem substRoot_symm (f : RankedSym) {t1 t2 : GTerm}
    (p : Path t1 t2) :
    substRootPath f (Path.symm p) =
    Path.symm (substRootPath f p) := by
  unfold substRootPath
  simp [Path.congrArg_symm]

/-! ## Embedding and Simulation -/

/-- A simulation between two BUTAs. -/
structure Simulation (a1 a2 : BUTA) where
  stateMap : TAState → TAState
  preservesFinal : ∀ q, q ∈ a1.finalStates → stateMap q ∈ a2.finalStates

/-- Lift a simulation through a path. -/
noncomputable def Simulation.liftPath {a1 a2 : BUTA} (sim : Simulation a1 a2)
    {q1 q2 : TAState} (p : Path q1 q2) :
    Path (sim.stateMap q1) (sim.stateMap q2) :=
  Path.congrArg sim.stateMap p

/-- Theorem 42: Simulation lift preserves trans. -/
theorem sim_lift_trans {a1 a2 : BUTA} (sim : Simulation a1 a2)
    {q1 q2 q3 : TAState} (p : Path q1 q2) (r : Path q2 q3) :
    sim.liftPath (Path.trans p r) =
    Path.trans (sim.liftPath p) (sim.liftPath r) := by
  unfold Simulation.liftPath
  simp [Path.congrArg_trans]

/-- Theorem 43: Simulation lift preserves symm. -/
theorem sim_lift_symm {a1 a2 : BUTA} (sim : Simulation a1 a2)
    {q1 q2 : TAState} (p : Path q1 q2) :
    sim.liftPath (Path.symm p) =
    Path.symm (sim.liftPath p) := by
  unfold Simulation.liftPath
  simp [Path.congrArg_symm]

/-! ## Projection Paths -/

/-- Project product state to first component. -/
noncomputable def projFst (q : TAState) : TAState := ⟨q.id / 1000⟩

/-- Project product state to second component. -/
noncomputable def projSnd (q : TAState) : TAState := ⟨q.id % 1000⟩

/-- Theorem 44: Projection paths compose with trans. -/
theorem proj_fst_trans {q1 q2 q3 : TAState}
    (p : Path q1 q2) (r : Path q2 q3) :
    Path.congrArg projFst (Path.trans p r) =
    Path.trans (Path.congrArg projFst p) (Path.congrArg projFst r) := by
  simp [Path.congrArg_trans]

/-- Theorem 45: Projection paths compose with symm. -/
theorem proj_snd_symm {q1 q2 : TAState}
    (p : Path q1 q2) :
    Path.congrArg projSnd (Path.symm p) =
    Path.symm (Path.congrArg projSnd p) := by
  simp [Path.congrArg_symm]

/-! ## Recognizable Step Algebra -/

/-- An extended transition captures the full step info. -/
structure ExtTransition where
  source : List TAState
  target : TAState
  symbol : RankedSym
  deriving DecidableEq, Repr

/-- Composition of extended transitions path. -/
noncomputable def extTransPath {e1 e2 : ExtTransition}
    (p : Path e1 e2) : Path e1.target e2.target :=
  Path.congrArg ExtTransition.target p

/-- Theorem 46: Extended transition path preserves trans. -/
theorem extTrans_trans {e1 e2 e3 : ExtTransition}
    (p : Path e1 e2) (q : Path e2 e3) :
    extTransPath (Path.trans p q) =
    Path.trans (extTransPath p) (extTransPath q) := by
  unfold extTransPath
  simp [Path.congrArg_trans]

/-- Theorem 47: Extended transition path preserves symm. -/
theorem extTrans_symm {e1 e2 : ExtTransition}
    (p : Path e1 e2) :
    extTransPath (Path.symm p) =
    Path.symm (extTransPath p) := by
  unfold extTransPath
  simp [Path.congrArg_symm]

/-! ## Determinization Path -/

/-- Powerset state (represented as sorted list of state ids). -/
structure PowerState where
  ids : List Nat
  deriving DecidableEq, Repr

/-- Singleton powerset state. -/
noncomputable def PowerState.singleton (q : TAState) : PowerState := ⟨[q.id]⟩

/-- Union of powerset states. -/
noncomputable def PowerState.union (ps1 ps2 : PowerState) : PowerState :=
  ⟨(ps1.ids ++ ps2.ids).eraseDups⟩

/-- Path showing determinization preserves structure. -/
noncomputable def detPath {ps1 ps2 : PowerState}
    (p : Path ps1 ps2) : Path (PowerState.union ps1 ps1) (PowerState.union ps2 ps2) :=
  Path.congrArg (fun ps => PowerState.union ps ps) p

/-- Theorem 48: Determinization path preserves trans. -/
theorem det_path_trans {ps1 ps2 ps3 : PowerState}
    (p : Path ps1 ps2) (q : Path ps2 ps3) :
    detPath (Path.trans p q) =
    Path.trans (detPath p) (detPath q) := by
  unfold detPath
  simp [Path.congrArg_trans]

/-- Theorem 49: Determinization path preserves symm. -/
theorem det_path_symm {ps1 ps2 : PowerState}
    (p : Path ps1 ps2) :
    detPath (Path.symm p) =
    Path.symm (detPath p) := by
  unfold detPath
  simp [Path.congrArg_symm]

/-! ## Grand Coherence Theorems -/

/-- Theorem 50: Functorial composition of lifts. -/
theorem functorial_comp (f g : TAState → TAState)
    {a b : TAState} (p : Path a b) :
    Path.congrArg g (Path.congrArg f p) =
    Path.congrArg (fun x => g (f x)) p := by
  simp [Path.congrArg_comp]

/-- Theorem 51: Path algebra coherence for four-fold composition. -/
theorem four_fold_assoc {a b c d e : TAState}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s =
    Path.trans p (Path.trans q (Path.trans r s)) := by
  simp [Path.trans_assoc]

/-- Theorem 52: Triple symm. -/
theorem triple_symm {a b : TAState}
    (p : Path a b) : Path.symm (Path.symm (Path.symm p)) = Path.symm p := by
  simp [Path.symm_symm]

/-- Theorem 53: CongrArg of refl is refl. -/
theorem congrArg_refl_state (f : TAState → TAState) (a : TAState) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := by
  rfl

/-- Theorem 54: Context plug preserves path. -/
noncomputable def contextPlugPath (c : Context) {t1 t2 : GTerm}
    (p : Path t1 t2) : Path (c.plug t1) (c.plug t2) :=
  Path.congrArg c.plug p

/-- Theorem 55: Context plug path preserves trans. -/
theorem contextPlug_trans (c : Context) {t1 t2 t3 : GTerm}
    (p : Path t1 t2) (q : Path t2 t3) :
    contextPlugPath c (Path.trans p q) =
    Path.trans (contextPlugPath c p) (contextPlugPath c q) := by
  unfold contextPlugPath
  simp [Path.congrArg_trans]

/-- Theorem 56: Context plug path preserves symm. -/
theorem contextPlug_symm (c : Context) {t1 t2 : GTerm}
    (p : Path t1 t2) :
    contextPlugPath c (Path.symm p) =
    Path.symm (contextPlugPath c p) := by
  unfold contextPlugPath
  simp [Path.congrArg_symm]

/-- Theorem 57: Union of tree languages is associative. -/
theorem treeLang_union_assoc (L1 L2 L3 : TreeLang) (t : GTerm) :
    TreeLang.union (TreeLang.union L1 L2) L3 t ↔
    TreeLang.union L1 (TreeLang.union L2 L3) t := by
  unfold TreeLang.union
  exact ⟨fun h => match h with
    | Or.inl (Or.inl h) => Or.inl h
    | Or.inl (Or.inr h) => Or.inr (Or.inl h)
    | Or.inr h => Or.inr (Or.inr h),
   fun h => match h with
    | Or.inl h => Or.inl (Or.inl h)
    | Or.inr (Or.inl h) => Or.inl (Or.inr h)
    | Or.inr (Or.inr h) => Or.inr h⟩

/-- Theorem 58: Intersection of tree languages is associative. -/
theorem treeLang_inter_assoc (L1 L2 L3 : TreeLang) (t : GTerm) :
    TreeLang.inter (TreeLang.inter L1 L2) L3 t ↔
    TreeLang.inter L1 (TreeLang.inter L2 L3) t := by
  unfold TreeLang.inter
  exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩,
         fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

end TreeAutomataDeep
