/-
  ComputationalPaths.Path.Rewriting.GraphRewritingDeep
  Graph Rewriting and Double Pushout via Computational Paths

  This module develops graph rewriting theory — including single pushout (SPO),
  double pushout (DPO), confluence, critical pairs, and Church-Rosser properties —
  using Path as the canonical rewriting witness throughout.
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths.GraphRewritingDeep

open ComputationalPaths
open ComputationalPaths.Path

/-! ## 1. Graph Structure -/

/-- A directed graph with vertex and edge types, plus source/target maps. -/
structure Graph where
  Vertex : Type
  Edge : Type
  src : Edge → Vertex
  tgt : Edge → Vertex

/-- A graph morphism preserving source and target maps. -/
structure GraphMorphism (G H : Graph) where
  onVertex : G.Vertex → H.Vertex
  onEdge : G.Edge → H.Edge
  preserveSrc : ∀ e : G.Edge, onVertex (G.src e) = H.src (onEdge e)
  preserveTgt : ∀ e : G.Edge, onVertex (G.tgt e) = H.tgt (onEdge e)

/-- Identity graph morphism. -/
def GraphMorphism.id (G : Graph) : GraphMorphism G G where
  onVertex := fun v => v
  onEdge := fun e => e
  preserveSrc := fun _ => rfl
  preserveTgt := fun _ => rfl

/-- Composition of graph morphisms. -/
def GraphMorphism.comp {G H K : Graph} (f : GraphMorphism G H) (g : GraphMorphism H K)
    : GraphMorphism G K where
  onVertex := g.onVertex ∘ f.onVertex
  onEdge := g.onEdge ∘ f.onEdge
  preserveSrc := fun e => by
    simp [Function.comp]
    rw [f.preserveSrc e, g.preserveSrc (f.onEdge e)]
  preserveTgt := fun e => by
    simp [Function.comp]
    rw [f.preserveTgt e, g.preserveTgt (f.onEdge e)]

/-! ## 2. Path witnesses for morphism functoriality -/

-- Theorem 1: Identity morphism acts as identity on vertices
theorem idMorphism_vertex (G : Graph) (v : G.Vertex) :
    (GraphMorphism.id G).onVertex v = v :=
  rfl

-- Theorem 2: Composition of morphisms is associative on vertices
theorem compMorphism_assoc_vertex {G H K L : Graph}
    (f : GraphMorphism G H) (g : GraphMorphism H K) (h : GraphMorphism K L)
    (v : G.Vertex) :
    ((f.comp g).comp h).onVertex v = (f.comp (g.comp h)).onVertex v :=
  rfl

-- Theorem 3: Identity composed on the left
theorem compId_left_vertex {G H : Graph} (f : GraphMorphism G H) (v : G.Vertex) :
    ((GraphMorphism.id G).comp f).onVertex v = f.onVertex v :=
  rfl

-- Theorem 4: Identity composed on the right
theorem compId_right_vertex {G H : Graph} (f : GraphMorphism G H) (v : G.Vertex) :
    (f.comp (GraphMorphism.id H)).onVertex v = f.onVertex v :=
  rfl

-- Theorem 5: Edge-level identity
theorem idMorphism_edge (G : Graph) (e : G.Edge) :
    (GraphMorphism.id G).onEdge e = e :=
  rfl

-- Theorem 6: Edge-level associativity
theorem compMorphism_assoc_edge {G H K L : Graph}
    (f : GraphMorphism G H) (g : GraphMorphism H K) (h : GraphMorphism K L)
    (e : G.Edge) :
    ((f.comp g).comp h).onEdge e = (f.comp (g.comp h)).onEdge e :=
  rfl

-- Theorem 7: congrArg lifts vertex maps along paths
def morphism_vertex_congr {G H : Graph} (f : GraphMorphism G H)
    {v1 v2 : G.Vertex} (p : Path v1 v2) :
    Path (f.onVertex v1) (f.onVertex v2) :=
  Path.congrArg f.onVertex p

-- Theorem 8: congrArg lifts edge maps along paths
def morphism_edge_congr {G H : Graph} (f : GraphMorphism G H)
    {e1 e2 : G.Edge} (p : Path e1 e2) :
    Path (f.onEdge e1) (f.onEdge e2) :=
  Path.congrArg f.onEdge p

-- Theorem 9: Composition of morphism congruences
def morphism_comp_congr {G H K : Graph}
    (f : GraphMorphism G H) (g : GraphMorphism H K)
    {v1 v2 : G.Vertex} (p : Path v1 v2) :
    Path ((f.comp g).onVertex v1) ((f.comp g).onVertex v2) :=
  Path.congrArg (f.comp g).onVertex p

-- Theorem 10: congrArg distributes over trans for morphism application
theorem morphism_congr_trans {G H : Graph} (f : GraphMorphism G H)
    {v1 v2 v3 : G.Vertex} (p : Path v1 v2) (q : Path v2 v3) :
    Path.congrArg f.onVertex (Path.trans p q) =
      Path.trans (Path.congrArg f.onVertex p) (Path.congrArg f.onVertex q) :=
  Path.congrArg_trans f.onVertex p q

-- Theorem 11: congrArg distributes over symm for morphism application
theorem morphism_congr_symm {G H : Graph} (f : GraphMorphism G H)
    {v1 v2 : G.Vertex} (p : Path v1 v2) :
    Path.congrArg f.onVertex (Path.symm p) =
      Path.symm (Path.congrArg f.onVertex p) :=
  Path.congrArg_symm f.onVertex p

/-! ## 3. Rewriting Rules as Spans -/

/-- A graph rewriting rule as a span L ← K → R (DPO style). -/
structure RewriteRule where
  L : Graph
  K : Graph
  R : Graph
  lMorphism : GraphMorphism K L
  rMorphism : GraphMorphism K R

/-- A single pushout rule: just L → R. -/
structure SPORule where
  L : Graph
  R : Graph
  morphism : GraphMorphism L R

/-- A match of a pattern in a host graph. -/
structure Match (L G : Graph) where
  morphism : GraphMorphism L G

/-! ## 4. Rewriting Steps via Path -/

/-- A rewriting step tags a transformation from one graph state to another. -/
structure RewriteStep (Gam : Type) where
  before : Gam
  after : Gam
  witness : Path before after

/-- Identity rewriting step. -/
def RewriteStep.idStep {Gam : Type} (g : Gam) : RewriteStep Gam where
  before := g
  after := g
  witness := Path.refl g

/-- Composition of rewriting steps via Path.trans. -/
def RewriteStep.compose {Gam : Type} (s1 s2 : RewriteStep Gam)
    (h : Path s1.after s2.before) : RewriteStep Gam where
  before := s1.before
  after := s2.after
  witness := Path.trans s1.witness (Path.trans h s2.witness)

/-! ## 5. Rewriting Sequences -/

/-- A rewriting sequence is a list of steps chained via Path.trans. -/
inductive RewriteSeq (Gam : Type) : Gam → Gam → Type where
  | nil : (g : Gam) → RewriteSeq Gam g g
  | cons : {g1 g2 g3 : Gam} → Path g1 g2 → RewriteSeq Gam g2 g3 → RewriteSeq Gam g1 g3

/-- Convert a rewriting sequence to a single Path. -/
def RewriteSeq.toPath {Gam : Type} {g1 g2 : Gam} : RewriteSeq Gam g1 g2 → Path g1 g2
  | .nil _ => Path.refl _
  | .cons p rest => Path.trans p rest.toPath

/-- Concatenate two rewriting sequences. -/
def RewriteSeq.append {Gam : Type} {g1 g2 g3 : Gam}
    (s1 : RewriteSeq Gam g1 g2) (s2 : RewriteSeq Gam g2 g3) : RewriteSeq Gam g1 g3 :=
  match s1 with
  | .nil _ => s2
  | .cons p rest => .cons p (rest.append s2)

/-- Length of a rewriting sequence. -/
def RewriteSeq.length {Gam : Type} {g1 g2 : Gam} : RewriteSeq Gam g1 g2 → Nat
  | .nil _ => 0
  | .cons _ rest => 1 + rest.length

/-- A single-step sequence. -/
def RewriteSeq.single {Gam : Type} {g1 g2 : Gam} (p : Path g1 g2) : RewriteSeq Gam g1 g2 :=
  .cons p (.nil g2)

-- Theorem 12: Single-step sequence has length 1
theorem RewriteSeq.single_length {Gam : Type} {g1 g2 : Gam} (p : Path g1 g2) :
    (RewriteSeq.single p).length = 1 :=
  rfl

-- Theorem 13: Nil sequence has length 0
theorem RewriteSeq.nil_length {Gam : Type} (g : Gam) :
    (RewriteSeq.nil g).length = 0 :=
  rfl

-- Theorem 14: toPath of nil is refl
theorem RewriteSeq.nil_toPath {Gam : Type} (g : Gam) :
    (RewriteSeq.nil g).toPath = Path.refl g :=
  rfl

-- Theorem 15: toPath of single is trans with refl
theorem RewriteSeq.single_toPath {Gam : Type} {g1 g2 : Gam} (p : Path g1 g2) :
    (RewriteSeq.single p).toPath = Path.trans p (Path.refl g2) :=
  rfl

-- Theorem 16: single toPath simplifies via trans_refl_right
theorem RewriteSeq.single_toPath_simplified {Gam : Type} {g1 g2 : Gam} (p : Path g1 g2) :
    (RewriteSeq.single p).toPath = p := by
  simp [RewriteSeq.single, RewriteSeq.toPath]

/-! ## 6. Confluence and Church-Rosser -/

/-- Two elements are joinable if they share a common reduct via Paths. -/
structure Joinable {Gam : Type} (a b : Gam) where
  common : Gam
  pathA : Path a common
  pathB : Path b common

/-- Joinability is reflexive. -/
def Joinable.refl {Gam : Type} (a : Gam) : Joinable a a where
  common := a
  pathA := Path.refl a
  pathB := Path.refl a

/-- Joinability is symmetric. -/
def Joinable.symm {Gam : Type} {a b : Gam} (j : Joinable a b) : Joinable b a where
  common := j.common
  pathA := j.pathB
  pathB := j.pathA

/-- A rewriting system is locally confluent if diverging one-step rewrites are joinable. -/
structure LocallyConfluent (Gam : Type) where
  join : ∀ (a b c : Gam), Path a b → Path a c → Joinable b c

/-- A rewriting system is confluent if all diverging paths are joinable. -/
structure Confluent (Gam : Type) where
  join : ∀ (a b c : Gam), RewriteSeq Gam a b → RewriteSeq Gam a c → Joinable b c

/-- Church-Rosser: convertible elements are joinable. -/
structure ChurchRosser (Gam : Type) where
  crProp : ∀ (a b : Gam), Path a b → Joinable a b

-- Theorem 17: Church-Rosser implies any Path gives joinability
def churchRosser_path_joinable {Gam : Type} (cr : ChurchRosser Gam)
    {a b : Gam} (p : Path a b) : Joinable a b :=
  cr.crProp a b p

-- Theorem 18: Symmetric joinability via Path.symm
def joinable_from_path {Gam : Type} {a b : Gam} (p : Path a b) :
    Joinable a b where
  common := b
  pathA := p
  pathB := Path.refl b

-- Theorem 19: Inverse path also gives joinability (reversed)
def joinable_from_path_symm {Gam : Type} {a b : Gam} (p : Path a b) :
    Joinable b a where
  common := b
  pathA := Path.refl b
  pathB := p

/-! ## 7. Dangling Edge Condition -/

/-- The dangling edge condition: no edge in G \ d(L\K) is incident to a deleted vertex. -/
structure DanglingCondition (rule : RewriteRule) (G : Graph)
    (m : GraphMorphism rule.L G) where
  noDangling : ∀ (e : G.Edge) (v : rule.L.Vertex),
    G.src e = m.onVertex v ∨ G.tgt e = m.onVertex v →
    (∃ e' : rule.L.Edge, m.onEdge e' = e) ∨
    (∃ k : rule.K.Vertex, rule.lMorphism.onVertex k = v)

/-! ## 8. Identification Condition -/

/-- The identification condition: if m identifies two elements, they must be in K. -/
structure IdentificationCondition (rule : RewriteRule) (G : Graph)
    (m : GraphMorphism rule.L G) where
  noIdVertex : ∀ (v1 v2 : rule.L.Vertex),
    m.onVertex v1 = m.onVertex v2 → v1 ≠ v2 →
    (∃ k1 k2 : rule.K.Vertex,
      rule.lMorphism.onVertex k1 = v1 ∧ rule.lMorphism.onVertex k2 = v2)

/-! ## 9. DPO Applicability -/

/-- A DPO rule is applicable when both conditions hold. -/
structure DPOApplicable (rule : RewriteRule) (G : Graph)
    (m : GraphMorphism rule.L G) where
  dangling : DanglingCondition rule G m
  identification : IdentificationCondition rule G m

-- Theorem 20: DPO applicability implies dangling condition
theorem dpo_implies_dangling (rule : RewriteRule) (G : Graph)
    (m : GraphMorphism rule.L G) (app : DPOApplicable rule G m) :
    DanglingCondition rule G m :=
  app.dangling

-- Theorem 21: DPO applicability implies identification condition
theorem dpo_implies_identification (rule : RewriteRule) (G : Graph)
    (m : GraphMorphism rule.L G) (app : DPOApplicable rule G m) :
    IdentificationCondition rule G m :=
  app.identification

/-! ## 10. Graph Transformation Units -/

/-- A graph transformation unit packages a set of rules with control flow. -/
structure TransformationUnit where
  rules : List RewriteRule
  controlDesc : String

/-- Sequential composition of transformation units. -/
def TransformationUnit.seqCompose (u1 u2 : TransformationUnit) : TransformationUnit where
  rules := u1.rules ++ u2.rules
  controlDesc := u1.controlDesc ++ " ; " ++ u2.controlDesc

-- Theorem 22: Sequential composition of units is associative
theorem seqCompose_assoc (u1 u2 u3 : TransformationUnit) :
    (u1.seqCompose u2).seqCompose u3 =
    u1.seqCompose (u2.seqCompose u3) := by
  simp [TransformationUnit.seqCompose, List.append_assoc, String.append_assoc]

-- Theorem 23: Empty unit is left identity for rules
theorem seqCompose_empty_left (u : TransformationUnit) :
    (TransformationUnit.mk [] "").seqCompose u =
    { rules := u.rules, controlDesc := " ; " ++ u.controlDesc } := by
  simp [TransformationUnit.seqCompose]

/-! ## 11. Amalgamation of Rules -/

/-- An amalgamation specification: two rules sharing a common sub-rule. -/
structure Amalgamation where
  rule1 : RewriteRule
  rule2 : RewriteRule
  commonL : Graph
  commonK : Graph
  commonR : Graph
  embedL1 : GraphMorphism commonL rule1.L
  embedL2 : GraphMorphism commonL rule2.L
  embedK1 : GraphMorphism commonK rule1.K
  embedK2 : GraphMorphism commonK rule2.K
  embedR1 : GraphMorphism commonR rule1.R
  embedR2 : GraphMorphism commonR rule2.R

-- Theorem 24: Amalgamation vertex coherence as Path
def amalgamation_vertex_path {G : Graph}
    (amal : Amalgamation)
    (m1 : GraphMorphism amal.rule1.L G)
    (m2 : GraphMorphism amal.rule2.L G)
    (v : amal.commonL.Vertex)
    (h : m1.onVertex (amal.embedL1.onVertex v) = m2.onVertex (amal.embedL2.onVertex v)) :
    Path (m1.onVertex (amal.embedL1.onVertex v)) (m2.onVertex (amal.embedL2.onVertex v)) :=
  Path.ofEq h

/-! ## 12. Critical Pairs -/

/-- A critical pair: two overlapping rule applications from a common redex. -/
structure CriticalPair (Gam : Type) where
  redex : Gam
  result1 : Gam
  result2 : Gam
  step1 : Path redex result1
  step2 : Path redex result2

/-- A critical pair is convergent if the results are joinable. -/
def CriticalPair.isConvergent {Gam : Type} (cp : CriticalPair Gam) : Prop :=
  ∃ (common : Gam) (_ : cp.result1 = common) (_ : cp.result2 = common), True

/-- Construct joinability from a convergent critical pair. -/
def CriticalPair.toJoinable {Gam : Type} (cp : CriticalPair Gam)
    (common : Gam) (p1 : Path cp.result1 common) (p2 : Path cp.result2 common) :
    Joinable cp.result1 cp.result2 where
  common := common
  pathA := p1
  pathB := p2

/-- A trivial critical pair where both results are the same. -/
def CriticalPair.trivial {Gam : Type} (redex result : Gam)
    (p : Path redex result) : CriticalPair Gam where
  redex := redex
  result1 := result
  result2 := result
  step1 := p
  step2 := p

-- Theorem 25: Trivial critical pairs are always convergent
theorem trivial_cp_convergent {Gam : Type} (redex result : Gam)
    (p : Path redex result) :
    (CriticalPair.trivial redex result p).isConvergent :=
  ⟨result, rfl, rfl, trivial⟩

-- Theorem 26: Trivial CP has equal results
theorem trivial_cp_results_eq {Gam : Type} (redex result : Gam)
    (p : Path redex result) :
    (CriticalPair.trivial redex result p).result1 =
    (CriticalPair.trivial redex result p).result2 :=
  rfl

-- Theorem 27: Trivial CP steps are equal
theorem trivial_cp_steps_eq {Gam : Type} (redex result : Gam)
    (p : Path redex result) :
    (CriticalPair.trivial redex result p).step1 =
    (CriticalPair.trivial redex result p).step2 :=
  rfl

/-! ## 13. Path Algebra for Rewriting -/

-- Theorem 28: Trans associativity for rewriting chains
theorem rewrite_chain_assoc {Gam : Type} {a b c d : Gam}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

-- Theorem 29: Refl is left identity for trans
theorem rewrite_refl_left {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

-- Theorem 30: Refl is right identity for trans
theorem rewrite_refl_right {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

-- Theorem 31: Double symmetry is identity
theorem rewrite_symm_symm {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

-- Theorem 32: Symm distributes over trans (reversed)
theorem rewrite_symm_trans {Gam : Type} {a b c : Gam}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

-- Theorem 33: congrArg distributes over trans
theorem rewrite_congrArg_trans {Gam Sym : Type} (f : Gam → Sym)
    {a b c : Gam} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

-- Theorem 34: congrArg distributes over symm
theorem rewrite_congrArg_symm {Gam Sym : Type} (f : Gam → Sym)
    {a b : Gam} (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

-- Theorem 35: Symm followed by trans cancels (toEq level)
theorem rewrite_symm_cancel_toEq {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.toEq (Path.trans (Path.symm p) p) = rfl :=
  Path.toEq_symm_trans p

-- Theorem 36: Trans followed by symm cancels (toEq level)
theorem rewrite_trans_symm_cancel_toEq {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.toEq (Path.trans p (Path.symm p)) = rfl :=
  Path.toEq_trans_symm p

/-! ## 14. SPO Rewriting -/

/-- SPO rewriting step. -/
structure SPOStep (Gam : Type) where
  before : Gam
  after : Gam
  witness : Path before after

/-- SPO steps compose via Path.trans. -/
def SPOStep.compose {Gam : Type} (s1 s2 : SPOStep Gam)
    (h : Path s1.after s2.before) : SPOStep Gam where
  before := s1.before
  after := s2.after
  witness := Path.trans s1.witness (Path.trans h s2.witness)

/-- SPO identity step. -/
def SPOStep.idStep {Gam : Type} (g : Gam) : SPOStep Gam where
  before := g
  after := g
  witness := Path.refl g

-- Theorem 37: SPO id compose with any step
theorem spo_id_compose {Gam : Type} (s : SPOStep Gam) :
    (SPOStep.compose (SPOStep.idStep s.before) s (Path.refl s.before)).witness =
    Path.trans (Path.refl s.before) (Path.trans (Path.refl s.before) s.witness) :=
  rfl

/-! ## 15. DPO Rewriting Step -/

/-- A DPO step records the full pushout complement data. -/
structure DPOStep where
  rule : RewriteRule
  hostBefore : Graph
  hostAfter : Graph
  context : Graph
  matchMorphism : GraphMorphism rule.L hostBefore

/-! ## 16. Derivation Traces -/

/-- A derivation trace records the sequence of rule applications. -/
structure DerivationTrace (Gam : Type) where
  states : List Gam
  nonEmpty : states ≠ []

/-- The start state of a derivation trace. -/
def DerivationTrace.start {Gam : Type} (dt : DerivationTrace Gam) : Gam :=
  match h : dt.states with
  | [] => absurd h dt.nonEmpty
  | s :: _ => s

/-- A singleton trace. -/
def DerivationTrace.singleton {Gam : Type} (g : Gam) : DerivationTrace Gam where
  states := [g]
  nonEmpty := List.cons_ne_nil g []

-- Theorem 38: The start of a singleton trace is the element itself
theorem singleton_start {Gam : Type} (g : Gam) :
    (DerivationTrace.singleton g).start = g :=
  rfl

/-! ## 17. Rule Application Witness -/

/-- Witness that a rule application transforms source to target. -/
structure RuleApplication (Gam : Type) where
  source : Gam
  target : Gam
  ruleId : Nat
  path : Path source target

/-- Composing two rule applications. -/
def RuleApplication.compose {Gam : Type} (r1 r2 : RuleApplication Gam)
    (h : Path r1.target r2.source) : RuleApplication Gam where
  source := r1.source
  target := r2.target
  ruleId := r1.ruleId
  path := Path.trans r1.path (Path.trans h r2.path)

/-- Identity rule application. -/
def RuleApplication.identity {Gam : Type} (g : Gam) : RuleApplication Gam where
  source := g
  target := g
  ruleId := 0
  path := Path.refl g

-- Theorem 39: Identity rule application path is refl
theorem identity_app_path {Gam : Type} (g : Gam) :
    (RuleApplication.identity g).path = Path.refl g :=
  rfl

-- Theorem 40: Identity rule application source = target
theorem identity_app_source_target {Gam : Type} (g : Gam) :
    (RuleApplication.identity g).source = (RuleApplication.identity g).target :=
  rfl

/-! ## 18. Confluence via Critical Pair Lemma -/

/-- If all critical pairs converge, the system is locally confluent (statement). -/
structure CriticalPairLemma (Gam : Type) where
  allCriticalPairsConverge :
    ∀ (cp : CriticalPair Gam), cp.isConvergent
  localConfluence : LocallyConfluent Gam

/-- Newman's Lemma: terminating + locally confluent ⟹ confluent. -/
structure NewmansLemma (Gam : Type) where
  terminating : ∀ (f : Nat → Gam), ∃ n, ∀ m, m > n → f m = f n
  locallyConfluent : LocallyConfluent Gam
  confluent : Confluent Gam

/-! ## 19. Reversible Rewriting -/

/-- A reversible rewriting step. -/
structure ReversibleStep (Gam : Type) where
  forward : RewriteStep Gam
  backward : RewriteStep Gam
  forwardBackward : forward.before = backward.after
  backwardForward : backward.before = forward.after

/-- Construct a reversible step from a Path. -/
def ReversibleStep.fromPath {Gam : Type} {a b : Gam} (p : Path a b) :
    ReversibleStep Gam where
  forward := { before := a, after := b, witness := p }
  backward := { before := b, after := a, witness := Path.symm p }
  forwardBackward := rfl
  backwardForward := rfl

-- Theorem 41: Double reversal restores original path
theorem reversible_double_inverse {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.symm (Path.symm p) = p :=
  Path.symm_symm p

-- Theorem 42: symm distributes over trans in reverse
theorem symm_trans_distribute {Gam : Type} {a b c : Gam}
    (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

-- Theorem 43: Symm of refl is refl
theorem symm_refl_is_refl {Gam : Type} (a : Gam) :
    Path.symm (Path.refl a) = Path.refl a :=
  Path.symm_refl a

/-! ## 20. Congruence Closure for Graph Properties -/

-- Theorem 44: Image connectivity
def image_connected {G H : Graph} (f : GraphMorphism G H)
    {v1 v2 : G.Vertex} (p : Path v1 v2) :
    Path (f.onVertex v1) (f.onVertex v2) :=
  Path.congrArg f.onVertex p

-- Theorem 45: Image connectivity respects trans
theorem image_connected_trans {G H : Graph} (f : GraphMorphism G H)
    {v1 v2 v3 : G.Vertex} (p : Path v1 v2) (q : Path v2 v3) :
    Path.congrArg f.onVertex (Path.trans p q) =
      Path.trans (Path.congrArg f.onVertex p) (Path.congrArg f.onVertex q) :=
  Path.congrArg_trans f.onVertex p q

-- Theorem 46: Image connectivity respects symm
theorem image_connected_symm {G H : Graph} (f : GraphMorphism G H)
    {v1 v2 : G.Vertex} (p : Path v1 v2) :
    Path.congrArg f.onVertex (Path.symm p) =
      Path.symm (Path.congrArg f.onVertex p) :=
  Path.congrArg_symm f.onVertex p

/-! ## 21. Graph Grammar -/

/-- A graph grammar: start graph plus production rules. -/
structure GraphGrammar where
  startGraph : Graph
  productions : List RewriteRule

/-- A grammar derivation records how many steps. -/
structure GrammarDerivation where
  grammar : GraphGrammar
  stepCount : Nat

-- Theorem 47: Zero-step derivation has same step count
theorem zero_step_count (gg : GraphGrammar) :
    (GrammarDerivation.mk gg 0).stepCount = 0 :=
  rfl

/-! ## 22. Pushout Construction -/

/-- A pushout square in the category of graphs. -/
structure PushoutSquare where
  A : Graph
  B : Graph
  C : Graph
  D : Graph
  f : GraphMorphism A B
  g : GraphMorphism A C
  inB : GraphMorphism B D
  inC : GraphMorphism C D

/-- Pushout commutativity at vertex level: inB ∘ f = inC ∘ g. -/
structure PushoutCommutes (sq : PushoutSquare) where
  vertexCommute : ∀ (a : sq.A.Vertex),
    sq.inB.onVertex (sq.f.onVertex a) = sq.inC.onVertex (sq.g.onVertex a)

/-- Path witness for pushout commutativity. -/
def pushoutCommutePath (sq : PushoutSquare) (pc : PushoutCommutes sq)
    (a : sq.A.Vertex) :
    Path (sq.inB.onVertex (sq.f.onVertex a)) (sq.inC.onVertex (sq.g.onVertex a)) :=
  Path.ofEq (pc.vertexCommute a)

/-- Pushout universal property. -/
structure PushoutUniversal (sq : PushoutSquare) where
  universal : ∀ (E : Graph) (hB : GraphMorphism sq.B E) (hC : GraphMorphism sq.C E),
    (∀ a : sq.A.Vertex, hB.onVertex (sq.f.onVertex a) = hC.onVertex (sq.g.onVertex a)) →
    GraphMorphism sq.D E

-- Theorem 48: Pushout commutativity is symmetric as equation
theorem pushout_commute_symm (sq : PushoutSquare) (pc : PushoutCommutes sq)
    (a : sq.A.Vertex) :
    sq.inC.onVertex (sq.g.onVertex a) = sq.inB.onVertex (sq.f.onVertex a) :=
  (pc.vertexCommute a).symm

/-! ## 23. Mapped Rewriting Sequences -/

/-- Apply a function along a rewriting sequence. -/
def mapRewriteSeq {Gam Sym : Type} (f : Gam → Sym)
    {g1 g2 : Gam} (s : RewriteSeq Gam g1 g2) : RewriteSeq Sym (f g1) (f g2) :=
  match s with
  | .nil g => .nil (f g)
  | .cons p rest => .cons (Path.congrArg f p) (mapRewriteSeq f rest)

-- Theorem 49: Mapping preserves length
theorem mapRewriteSeq_length {Gam Sym : Type} (f : Gam → Sym)
    {g1 g2 : Gam} (s : RewriteSeq Gam g1 g2) :
    (mapRewriteSeq f s).length = s.length := by
  induction s with
  | nil _ => rfl
  | cons _ _ ih => simp [mapRewriteSeq, RewriteSeq.length, ih]

-- Theorem 50: Mapping commutes with toPath
theorem mapRewriteSeq_toPath {Gam Sym : Type} (f : Gam → Sym)
    {g1 g2 : Gam} (s : RewriteSeq Gam g1 g2) :
    (mapRewriteSeq f s).toPath = Path.congrArg f s.toPath := by
  induction s with
  | nil g =>
    simp [mapRewriteSeq, RewriteSeq.toPath]
  | cons p rest ih =>
    simp [mapRewriteSeq, RewriteSeq.toPath, ih]

/-! ## 24. Additional Properties -/

-- Theorem 51: Composition of morphisms preserves vertex paths
theorem comp_preserves_paths {G H K : Graph}
    (f : GraphMorphism G H) (g : GraphMorphism H K)
    {v1 v2 : G.Vertex} (p : Path v1 v2) :
    Path.congrArg (f.comp g).onVertex p =
    Path.congrArg (fun v => g.onVertex (f.onVertex v)) p :=
  rfl

-- Theorem 52: Double composition coherence
theorem double_comp_coherence {G H K L : Graph}
    (f : GraphMorphism G H) (g : GraphMorphism H K) (h : GraphMorphism K L)
    (v : G.Vertex) :
    ((f.comp g).comp h).onVertex v = (f.comp (g.comp h)).onVertex v :=
  rfl

-- Theorem 53: Rewriting is a groupoid: trans_assoc
theorem rewriting_groupoid_assoc {Gam : Type} {a b c d : Gam}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

-- Theorem 54: Path composition with symm cancels (toEq)
theorem groupoid_inverse_left {Gam : Type} {a b : Gam} (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq := by
  simp

-- Theorem 55: Path composition with symm cancels other direction (toEq)
theorem groupoid_inverse_right {Gam : Type} {a b : Gam} (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := by
  simp

-- Theorem 56: congrArg composition law
theorem congrArg_composition {Gam Sym Del : Type} (f : Gam → Sym) (g : Sym → Del)
    {a b : Gam} (p : Path a b) :
    Path.congrArg (fun x => g (f x)) p = Path.congrArg g (Path.congrArg f p) :=
  Path.congrArg_comp g f p

-- Theorem 57: congrArg id law
theorem congrArg_identity {Gam : Type} {a b : Gam} (p : Path a b) :
    Path.congrArg (fun x : Gam => x) p = p :=
  Path.congrArg_id p

-- Theorem 58: Append of rewrite sequences preserves toPath structure
theorem append_toPath {Gam : Type} {g1 g2 g3 : Gam}
    (s1 : RewriteSeq Gam g1 g2) (s2 : RewriteSeq Gam g2 g3) :
    (s1.append s2).toPath = Path.trans s1.toPath s2.toPath := by
  induction s1 with
  | nil _ => simp [RewriteSeq.append, RewriteSeq.toPath]
  | cons p rest ih =>
    simp [RewriteSeq.append, RewriteSeq.toPath, ih]

-- Theorem 59: Append length is additive
theorem append_length {Gam : Type} {g1 g2 g3 : Gam}
    (s1 : RewriteSeq Gam g1 g2) (s2 : RewriteSeq Gam g2 g3) :
    (s1.append s2).length = s1.length + s2.length := by
  induction s1 with
  | nil _ => simp [RewriteSeq.append, RewriteSeq.length]
  | cons _ rest ih =>
    simp [RewriteSeq.append, RewriteSeq.length, ih, Nat.add_assoc]

-- Theorem 60: Nil append is identity
theorem nil_append {Gam : Type} {g1 g2 : Gam} (s : RewriteSeq Gam g1 g2) :
    (RewriteSeq.nil g1).append s = s :=
  rfl

end ComputationalPaths.GraphRewritingDeep
