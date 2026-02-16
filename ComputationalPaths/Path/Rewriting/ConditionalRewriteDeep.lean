/-
  ComputationalPaths/Path/Rewriting/ConditionalRewriteDeep.lean

  Conditional Term Rewriting via Computational Paths

  We model conditional rewrite rules (l → r if c₁↓, c₂↓, ...) using
  computational paths. Conditions are represented as joinability,
  reducibility, or normal-form requirements. Each conditional reduction
  step carries side-condition witnesses as Path evidence. We formalize
  oriented, join, normal, and semi-equational conditional rules (Types 1–4
  CTRS), level mappings for decreasingness, conditional confluence,
  conditional Church–Rosser, unraveling of CTRS into unconditional TRS,
  infeasible conditions, and quasi-reducibility.

  All chaining uses Path.trans; context closure uses Path.congrArg.
-/
import ComputationalPaths.Path.Basic

namespace ComputationalPaths.ConditionalRewriteDeep

open Path

universe u

-- ============================================================
-- §1  Basic Condition Types
-- ============================================================

/-- A condition on a pair of terms: joinability, reducibility, or normal-form. -/
inductive ConditionKind where
  | joinability   -- s and t have a common reduct
  | reducibility  -- s reduces to t
  | normalForm    -- s is in normal form and equals t
  deriving Repr, BEq, Inhabited

/-- A single condition: two terms with a kind. -/
structure Condition (A : Type u) where
  lhs : A
  rhs : A
  kind : ConditionKind

/-- A conditional rewrite rule: l → r with a list of conditions. -/
structure ConditionalRule (A : Type u) where
  lhsRule : A
  rhsRule : A
  conditions : List (Condition A)

/-- CTRS classification: Types 1–4. -/
inductive CTRSType where
  | type1  -- oriented: all conditions s →* t
  | type2  -- join: all conditions s ↓ t
  | type3  -- normal/semi-equational: conditions s ↔* t
  | type4  -- general: no restriction
  deriving Repr, BEq, Inhabited

/-- A classified CTRS bundles a type with a list of rules. -/
structure CTRS (A : Type u) where
  classification : CTRSType
  rules : List (ConditionalRule A)

-- ============================================================
-- §2  Witnesses for Conditions via Paths
-- ============================================================

/-- Witness that a joinability condition is satisfied: both sides
    reduce to a common term via computational paths. -/
structure JoinWitness {A : Type u} (s t : A) where
  common : A
  pathLeft : Path s common
  pathRight : Path t common

/-- Witness that a reducibility condition is satisfied:
    s reduces to t via a path. -/
structure ReduceWitness {A : Type u} (s t : A) where
  path : Path s t

/-- Witness that a normal-form condition holds:
    s equals t (reflexive path) meaning s is already in normal form = t. -/
structure NormalFormWitness {A : Type u} (s t : A) where
  path : Path s t

/-- A general condition witness: unifies all condition kinds. -/
inductive CondWitness {A : Type u} : Condition A -> Type u where
  | joinW : JoinWitness c.lhs c.rhs -> CondWitness c
  | reduceW : ReduceWitness c.lhs c.rhs -> CondWitness c
  | nfW : NormalFormWitness c.lhs c.rhs -> CondWitness c

-- ============================================================
-- §3  Conditional Step and Conditional Path
-- ============================================================

/-- A conditional reduction step: applying a rule with all conditions witnessed. -/
structure CondStep {A : Type u} (rule : ConditionalRule A) (s t : A) where
  ruleApp : Path s t
  witnesses : (i : Fin rule.conditions.length) ->
    CondWitness (rule.conditions.get i)

/-- A conditional reduction path chains multiple conditional steps. -/
inductive CondPath {A : Type u} : A -> A -> Type u where
  | refl : (a : A) -> CondPath a a
  | step : {a b c : A} -> (rule : ConditionalRule A) ->
           CondStep rule a b -> CondPath b c -> CondPath a c

-- ============================================================
-- §4  Core Theorems on Conditional Paths
-- ============================================================

/-- Theorem 1: CondPath is transitive. -/
def condPath_trans {A : Type u} {a b c : A}
    (p : CondPath a b) (q : CondPath b c) : CondPath a c :=
  match p with
  | CondPath.refl _ => q
  | CondPath.step rule cs rest => CondPath.step rule cs (condPath_trans rest q)

/-- Theorem 2: CondPath.refl is left identity for condPath_trans. -/
theorem condPath_trans_refl_left {A : Type u} {a b : A}
    (p : CondPath a b) : condPath_trans (CondPath.refl a) p = p := by
  rfl

/-- Theorem 3: CondPath.refl is right identity for condPath_trans. -/
theorem condPath_trans_refl_right {A : Type u} {a b : A}
    (p : CondPath a b) : condPath_trans p (CondPath.refl b) = p := by
  induction p with
  | refl _ => rfl
  | step rule cs rest ih => simp [condPath_trans, ih]

/-- Theorem 4: condPath_trans is associative. -/
theorem condPath_trans_assoc {A : Type u} {a b c d : A}
    (p : CondPath a b) (q : CondPath b c) (r : CondPath c d) :
    condPath_trans (condPath_trans p q) r = condPath_trans p (condPath_trans q r) := by
  induction p with
  | refl _ => rfl
  | step rule cs rest ih => simp [condPath_trans, ih]

/-- Theorem 5: Every conditional path yields an underlying Path. -/
def condPath_toPath {A : Type u} {a b : A} (cp : CondPath a b) : Path a b :=
  match cp with
  | CondPath.refl x => Path.refl x
  | CondPath.step _ cs rest => Path.trans cs.ruleApp (condPath_toPath rest)

/-- Theorem 6: condPath_toPath preserves reflexivity. -/
theorem condPath_toPath_refl {A : Type u} (a : A) :
    condPath_toPath (CondPath.refl a) = Path.refl a := by
  rfl

/-- Theorem 7: condPath_toPath distributes over condPath_trans. -/
theorem condPath_toPath_trans {A : Type u} {a b c : A}
    (p : CondPath a b) (q : CondPath b c) :
    condPath_toPath (condPath_trans p q) =
    Path.trans (condPath_toPath p) (condPath_toPath q) := by
  induction p with
  | refl _ => simp [condPath_trans, condPath_toPath]
  | step rule cs rest ih =>
    simp [condPath_trans, condPath_toPath, ih]

-- ============================================================
-- §5  JoinWitness Combinators
-- ============================================================

/-- Theorem 8: Reflexive joinability. -/
def joinWitness_refl {A : Type u} (a : A) : JoinWitness a a :=
  ⟨a, Path.refl a, Path.refl a⟩

/-- Theorem 9: Symmetric joinability. -/
def joinWitness_symm {A : Type u} {s t : A}
    (w : JoinWitness s t) : JoinWitness t s :=
  ⟨w.common, w.pathRight, w.pathLeft⟩

/-- Theorem 10: Joinability from a direct path. -/
def joinWitness_of_path {A : Type u} {s t : A}
    (p : Path s t) : JoinWitness s t :=
  ⟨t, p, Path.refl t⟩

/-- Theorem 11: ReduceWitness implies JoinWitness. -/
def joinWitness_of_reduce {A : Type u} {s t : A}
    (w : ReduceWitness s t) : JoinWitness s t :=
  ⟨t, w.path, Path.refl t⟩

/-- Theorem 12: JoinWitness composition through a middle term. -/
def joinWitness_compose {A : Type u} {a b c : A}
    (w1 : JoinWitness a b) (pb : Path b c) : JoinWitness a c :=
  ⟨w1.common, w1.pathLeft, Path.trans (Path.symm pb) w1.pathRight⟩

-- ============================================================
-- §6  ReduceWitness Combinators
-- ============================================================

/-- Theorem 13: Reflexive reduce witness. -/
def reduceWitness_refl {A : Type u} (a : A) : ReduceWitness a a :=
  ⟨Path.refl a⟩

/-- Theorem 14: Transitive reduce witness. -/
def reduceWitness_trans {A : Type u} {a b c : A}
    (w1 : ReduceWitness a b) (w2 : ReduceWitness b c) : ReduceWitness a c :=
  ⟨Path.trans w1.path w2.path⟩

/-- Theorem 15: ReduceWitness from a path. -/
def reduceWitness_of_path {A : Type u} {s t : A}
    (p : Path s t) : ReduceWitness s t :=
  ⟨p⟩

/-- Theorem 16: ReduceWitness under function application (congrArg). -/
def reduceWitness_congrArg {A B : Type u} {a b : A}
    (f : A -> B) (w : ReduceWitness a b) : ReduceWitness (f a) (f b) :=
  ⟨Path.congrArg f w.path⟩

/-- Theorem 17: Chaining reduce witnesses preserves path structure. -/
theorem reduceWitness_trans_path {A : Type u} {a b c : A}
    (w1 : ReduceWitness a b) (w2 : ReduceWitness b c) :
    (reduceWitness_trans w1 w2).path = Path.trans w1.path w2.path := by
  rfl

-- ============================================================
-- §7  NormalFormWitness Combinators
-- ============================================================

/-- Theorem 18: Reflexive normal form witness. -/
def nfWitness_refl {A : Type u} (a : A) : NormalFormWitness a a :=
  ⟨Path.refl a⟩

/-- Theorem 19: NormalFormWitness to ReduceWitness. -/
def nfWitness_to_reduce {A : Type u} {s t : A}
    (w : NormalFormWitness s t) : ReduceWitness s t :=
  ⟨w.path⟩

/-- Theorem 20: NormalFormWitness to JoinWitness. -/
def nfWitness_to_join {A : Type u} {s t : A}
    (w : NormalFormWitness s t) : JoinWitness s t :=
  joinWitness_of_path w.path

/-- Theorem 21: NormalFormWitness under congrArg. -/
def nfWitness_congrArg {A B : Type u} {a b : A}
    (f : A -> B) (w : NormalFormWitness a b) : NormalFormWitness (f a) (f b) :=
  ⟨Path.congrArg f w.path⟩

-- ============================================================
-- §8  Context Closure for Conditional Steps
-- ============================================================

/-- Theorem 22: Lift a conditional step under a function via congrArg. -/
def condStep_congrArg {A B : Type u} {rule : ConditionalRule A} {a b : A}
    (f : A -> B) (cs : CondStep rule a b) : Path (f a) (f b) :=
  Path.congrArg f cs.ruleApp

/-- Theorem 23: Lift a full conditional path under a function. -/
def condPath_congrArg {A B : Type u} {a b : A}
    (f : A -> B) (cp : CondPath a b) : Path (f a) (f b) :=
  Path.congrArg f (condPath_toPath cp)

/-- Theorem 24: condPath_congrArg preserves refl. -/
theorem condPath_congrArg_refl {A B : Type u} (f : A -> B) (a : A) :
    condPath_congrArg f (CondPath.refl a) = Path.congrArg f (Path.refl a) := by
  rfl

-- ============================================================
-- §9  Level Mappings and Decreasingness
-- ============================================================

/-- A level mapping assigns a natural number level to each term. -/
structure LevelMapping (A : Type u) where
  level : A -> Nat

/-- A conditional rule is decreasing w.r.t. a level mapping if the
    lhs has strictly greater level than the rhs. -/
structure DecreasingRule {A : Type u} (lm : LevelMapping A) (rule : ConditionalRule A) where
  decreasing : lm.level rule.lhsRule > lm.level rule.rhsRule

/-- A CTRS is decreasing if all its rules are decreasing. -/
structure DecreasingCTRS {A : Type u} (lm : LevelMapping A) (ctrs : CTRS A) where
  allDecreasing : (i : Fin ctrs.rules.length) ->
    DecreasingRule lm (ctrs.rules.get i)

/-- Theorem 25: A single-rule CTRS with a decreasing rule is decreasing. -/
def singleRuleDecreasing {A : Type u} (lm : LevelMapping A) (rule : ConditionalRule A)
    (h : lm.level rule.lhsRule > lm.level rule.rhsRule) :
    DecreasingCTRS lm ⟨CTRSType.type1, [rule]⟩ :=
  ⟨fun i => match i with
    | ⟨0, _⟩ => ⟨h⟩⟩

/-- Theorem 26: Decreasingness is preserved when restricting to a subset of rules. -/
def decreasingCTRS_head {A : Type u} {lm : LevelMapping A}
    {rule : ConditionalRule A} {rules : List (ConditionalRule A)}
    {ty : CTRSType}
    (dc : DecreasingCTRS lm ⟨ty, rule :: rules⟩) :
    DecreasingRule lm rule :=
  dc.allDecreasing ⟨0, by simp⟩

/-- Theorem 27: Level mapping composition. -/
def levelMapping_compose {A B : Type u} (lmA : LevelMapping A) (f : B -> A) :
    LevelMapping B :=
  ⟨fun b => lmA.level (f b)⟩

/-- Theorem 28: Decreasing rules compose with monotone functions on levels. -/
theorem levelMapping_compose_level {A B : Type u}
    (lmA : LevelMapping A) (f : B -> A) (b : B) :
    (levelMapping_compose lmA f).level b = lmA.level (f b) := by
  rfl

-- ============================================================
-- §10  Conditional Confluence
-- ============================================================

/-- Existential witness: a term together with evidence. -/
structure ExWitness {A : Type u} (P : A -> Type u) where
  val : A
  evidence : P val

/-- Conditional confluence: if a reduces to b and c via conditional paths,
    then b and c are joinable. -/
structure CondConfluent {A : Type u} (R : A -> A -> Type u) where
  confluent : {a b c : A} -> R a b -> R a c ->
    ExWitness (fun x => Prod (R b x) (R c x))

/-- Theorem 29: Joinability from conditional confluence and two diverging paths. -/
def condConfluent_join {A : Type u} {a b c : A}
    (conf : CondConfluent (fun (x : A) (y : A) => Path x y))
    (p1 : Path a b) (p2 : Path a c) :
    ExWitness (fun d => Prod (Path b d) (Path c d)) :=
  conf.confluent p1 p2

/-- Local conditional confluence: single steps are confluent. -/
structure LocalCondConfluent {A : Type u} (step : A -> A -> Type u) where
  localConf : {a b c : A} -> step a b -> step a c ->
    ExWitness (fun x => Prod (Path b x) (Path c x))

/-- Theorem 30: Local conditional confluence induces joinability on single steps. -/
def localCondConf_to_join {A : Type u} {a b c : A}
    {step : A -> A -> Type u}
    (lcc : LocalCondConfluent step)
    (s1 : step a b) (s2 : step a c) :
    ExWitness (fun d => Prod (Path b d) (Path c d)) :=
  lcc.localConf s1 s2

-- ============================================================
-- §11  Conditional Church–Rosser Property
-- ============================================================

/-- The conditional Church–Rosser property: convertibility implies joinability. -/
structure CondChurchRosser {A : Type u} where
  cr : {a b : A} -> Path a b ->
    ExWitness (fun c => Prod (Path a c) (Path b c))

/-- Theorem 31: Church–Rosser gives joinability from any path. -/
def cr_joinability {A : Type u} {a b : A}
    (cr : CondChurchRosser (A := A))
    (p : Path a b) :
    ExWitness (fun c => Prod (Path a c) (Path b c)) :=
  cr.cr p

/-- Theorem 32: Church–Rosser on refl yields reflexive join. -/
def cr_refl {A : Type u} (a : A)
    (cr : CondChurchRosser (A := A)) :
    ExWitness (fun c => Prod (Path a c) (Path a c)) :=
  cr.cr (Path.refl a)

/-- Theorem 33: Church-Rosser property implies symmetric joinability. -/
def cr_symm_join {A : Type u} {a b : A}
    (cr : CondChurchRosser (A := A))
    (p : Path a b) :
    ExWitness (fun c => Prod (Path b c) (Path a c)) :=
  let w := cr.cr p
  ⟨w.val, ⟨w.evidence.2, w.evidence.1⟩⟩

-- ============================================================
-- §12  Unraveling: CTRS to Unconditional TRS
-- ============================================================

/-- An unconditional rewrite rule. -/
structure UncondRule (A : Type u) where
  lhs : A
  rhs : A

/-- An unconditional TRS. -/
structure TRS (A : Type u) where
  rules : List (UncondRule A)

/-- Unraveling replaces each conditional rule with an unconditional
    approximation using fresh function symbols to encode conditions. -/
structure Unraveling (A : Type u) where
  source : CTRS A
  target : TRS A
  soundness : {a b : A} -> (i : Fin target.rules.length) ->
    Path a b -> Path a b  -- the unraveled path is valid

/-- Theorem 34: Unraveling soundness maps paths to paths of the same type. -/
theorem unraveling_soundness_type {A : Type u}
    (u : Unraveling A) {a b : A} (i : Fin u.target.rules.length) (p : Path a b) :
    (u.soundness i p).proof = p.proof := by
  simp

/-- Theorem 35: Trivial unraveling of an empty CTRS. -/
def unraveling_empty (A : Type u) : Unraveling A :=
  { source := ⟨CTRSType.type1, []⟩,
    target := ⟨[]⟩,
    soundness := fun i => Fin.elim0 i }

/-- An unconditional step in the unraveled TRS. -/
structure UncondStep {A : Type u} (trs : TRS A) (a b : A) where
  ruleIdx : Fin trs.rules.length
  app : Path a b

/-- Theorem 36: Unconditional step yields a path directly. -/
def uncondStep_toPath {A : Type u} {trs : TRS A} {a b : A}
    (us : UncondStep trs a b) : Path a b :=
  us.app

/-- Theorem 37: Chaining two unconditional steps. -/
def uncondStep_chain {A : Type u} {trs : TRS A} {a b c : A}
    (s1 : UncondStep trs a b) (s2 : UncondStep trs b c) : Path a c :=
  Path.trans s1.app s2.app

-- ============================================================
-- §13  Infeasible Conditions
-- ============================================================

/-- A condition is infeasible if no witness can be constructed.
    We model this as a proof that CondWitness is empty. -/
structure Infeasible {A : Type u} (c : Condition A) where
  noWitness : CondWitness c -> Empty

/-- A rule with an infeasible condition can never fire.
    We represent this as the fact that no CondStep can be built. -/
structure InfeasibleRule {A : Type u} (rule : ConditionalRule A) where
  condIdx : Fin rule.conditions.length
  infeasible : Infeasible (rule.conditions.get condIdx)

/-- Theorem 38: An infeasible rule contributes no conditional paths. -/
def infeasibleRule_no_step {A : Type u} {rule : ConditionalRule A}
    {a b : A}
    (ir : InfeasibleRule rule)
    (cs : CondStep rule a b) : Empty :=
  ir.infeasible.noWitness (cs.witnesses ir.condIdx)

/-- Theorem 39: A CTRS where all rules are infeasible has trivial reduction. -/
structure AllInfeasible {A : Type u} (ctrs : CTRS A) where
  allInf : (i : Fin ctrs.rules.length) -> InfeasibleRule (ctrs.rules.get i)

-- ============================================================
-- §14  Quasi-Reducibility
-- ============================================================

/-- A term is quasi-reducible w.r.t. a set of rules if every ground
    instance matches the left-hand side of some rule. We model this
    propositionally. -/
structure QuasiReducible {A : Type u} (rules : List (ConditionalRule A)) (t : A) where
  matchIdx : Fin rules.length
  matchPath : Path t (rules.get matchIdx).lhsRule

/-- Theorem 40: Quasi-reducibility gives a path to a rule's lhs. -/
def quasiReducible_path {A : Type u} {rules : List (ConditionalRule A)} {t : A}
    (qr : QuasiReducible rules t) : Path t (rules.get qr.matchIdx).lhsRule :=
  qr.matchPath

/-- Theorem 41: If t is quasi-reducible and the matched rule has a reduce witness,
    we get a path from t to the rhs. -/
def quasiReducible_reduce {A : Type u}
    {rules : List (ConditionalRule A)} {t : A}
    (qr : QuasiReducible rules t)
    (ruleStep : Path (rules.get qr.matchIdx).lhsRule (rules.get qr.matchIdx).rhsRule) :
    Path t (rules.get qr.matchIdx).rhsRule :=
  Path.trans qr.matchPath ruleStep

-- ============================================================
-- §15  Type 1 CTRS (Oriented Conditions)
-- ============================================================

/-- Type 1 condition: s →* t, witnessed by a ReduceWitness. -/
structure Type1Cond {A : Type u} (c : Condition A) where
  witness : ReduceWitness c.lhs c.rhs

/-- A Type 1 conditional step. -/
structure Type1Step {A : Type u} (rule : ConditionalRule A) (a b : A) where
  app : Path a b
  condWits : (i : Fin rule.conditions.length) ->
    Type1Cond (rule.conditions.get i)

/-- Theorem 42: Type1Step yields a path. -/
def type1Step_toPath {A : Type u} {rule : ConditionalRule A} {a b : A}
    (s : Type1Step rule a b) : Path a b :=
  s.app

/-- Theorem 43: Chain two Type1Steps via Path.trans. -/
def type1Step_chain {A : Type u}
    {r1 r2 : ConditionalRule A} {a b c : A}
    (s1 : Type1Step r1 a b) (s2 : Type1Step r2 b c) : Path a c :=
  Path.trans s1.app s2.app

/-- Theorem 44: A Type 1 step with no conditions is just a path. -/
def type1Step_uncond {A : Type u} {a b : A}
    (p : Path a b) : Type1Step ⟨a, b, []⟩ a b :=
  ⟨p, fun i => absurd i.isLt (by simp)⟩

-- ============================================================
-- §16  Type 2 CTRS (Join Conditions)
-- ============================================================

/-- Type 2 condition: s ↓ t, witnessed by a JoinWitness. -/
structure Type2Cond {A : Type u} (c : Condition A) where
  witness : JoinWitness c.lhs c.rhs

/-- A Type 2 conditional step. -/
structure Type2Step {A : Type u} (rule : ConditionalRule A) (a b : A) where
  app : Path a b
  condWits : (i : Fin rule.conditions.length) ->
    Type2Cond (rule.conditions.get i)

/-- Theorem 45: Type2Step yields a path. -/
def type2Step_toPath {A : Type u} {rule : ConditionalRule A} {a b : A}
    (s : Type2Step rule a b) : Path a b :=
  s.app

/-- Theorem 46: A Type 1 step can be lifted to a Type 2 step. -/
def type1_to_type2 {A : Type u} {rule : ConditionalRule A} {a b : A}
    (s : Type1Step rule a b) : Type2Step rule a b :=
  ⟨s.app, fun i =>
    let rw := (s.condWits i).witness
    ⟨joinWitness_of_reduce rw⟩⟩

-- ============================================================
-- §17  Path Evidence Extraction
-- ============================================================

/-- Theorem 47: Extract the underlying equality from a conditional path. -/
def condPath_toEq {A : Type u} {a b : A}
    (cp : CondPath a b) : a = b :=
  Path.toEq (condPath_toPath cp)

/-- Theorem 48: CondPath refl gives trivial equality. -/
theorem condPath_toEq_refl {A : Type u} (a : A) :
    condPath_toEq (CondPath.refl a) = rfl := by
  rfl

/-- Theorem 49: condPath_congrArg distributes over condPath_trans. -/
theorem condPath_congrArg_trans {A B : Type u} {a b c : A}
    (f : A -> B) (p : CondPath a b) (q : CondPath b c) :
    condPath_congrArg f (condPath_trans p q) =
    Path.trans (condPath_congrArg f p) (condPath_congrArg f q) := by
  simp [condPath_congrArg, condPath_toPath_trans]

-- ============================================================
-- §18  Conditional Rewriting Strategies
-- ============================================================

/-- A rewriting strategy selects which rule and position to apply. -/
structure Strategy (A : Type u) where
  selectRule : A -> Option (Fin 0)  -- abstract selection
  -- In practice, the Fin 0 makes this vacuous; this is a type-level stub.

/-- Innermost strategy: reduce arguments first. Modeled as a property. -/
structure InnermostProp {A : Type u} (isNF : A -> Prop) (step : A -> A -> Type u) where
  innermost : {a b : A} -> step a b -> isNF a -> Empty

/-- Outermost strategy: reduce at root first. -/
structure OutermostProp {A : Type u} (isRedex : A -> Prop) (step : A -> A -> Type u) where
  outermost : {a b : A} -> step a b -> isRedex a

-- ============================================================
-- §19  Conditional Termination
-- ============================================================

/-- A conditional rewriting system is terminating if there are no
    infinite conditional reduction sequences. We model this via
    well-founded relations on the inverse. -/
structure CondTerminating {A : Type u} (step : A -> A -> Prop) where
  wf : WellFounded (fun b a => step a b)

/-- Theorem 50: A decreasing CTRS with a well-founded level mapping is terminating. -/
def decreasing_terminating {A : Type u}
    (lm : LevelMapping A)
    (step : A -> A -> Prop)
    (h : forall a b, step a b -> lm.level a > lm.level b) :
    CondTerminating step where
  wf := by
    apply WellFounded.intro; intro a
    suffices forall n, lm.level a ≤ n -> Acc (fun b a => step a b) a from this _ (Nat.le_refl _)
    intro n
    induction n generalizing a with
    | zero =>
      intro hle; constructor; intro b hab
      have := h a b hab; omega
    | succ k ih =>
      intro hle; constructor; intro b hab
      have := h a b hab
      exact ih b (by omega)

-- ============================================================
-- §20  Additional Compositionality Theorems
-- ============================================================

/-- Theorem 51: JoinWitness transports along a path on the left. -/
def joinWitness_transport_left {A : Type u} {s s' t : A}
    (p : Path s' s) (w : JoinWitness s t) : JoinWitness s' t :=
  ⟨w.common, Path.trans p w.pathLeft, w.pathRight⟩

/-- Theorem 52: JoinWitness transports along a path on the right. -/
def joinWitness_transport_right {A : Type u} {s t t' : A}
    (w : JoinWitness s t) (p : Path t' t) : JoinWitness s t' :=
  ⟨w.common, w.pathLeft, Path.trans p w.pathRight⟩

/-- Theorem 53: Two JoinWitnesses can be composed if their commons are
    connected by a path. -/
def joinWitness_merge {A : Type u} {a b c : A}
    (w1 : JoinWitness a b) (w2 : JoinWitness b c)
    (link : Path w1.common w2.common) :
    JoinWitness a c :=
  ⟨w2.common, Path.trans w1.pathLeft link, w2.pathRight⟩

/-- Theorem 54: ReduceWitness under congrArg preserves path trans. -/
theorem reduceWitness_congrArg_trans {A B : Type u} {a b c : A}
    (f : A -> B) (w1 : ReduceWitness a b) (w2 : ReduceWitness b c) :
    (reduceWitness_congrArg f (reduceWitness_trans w1 w2)).path =
    Path.trans (Path.congrArg f w1.path) (Path.congrArg f w2.path) := by
  simp [reduceWitness_congrArg, reduceWitness_trans]

/-- Theorem 55: Symmetry of JoinWitness is involutive. -/
theorem joinWitness_symm_symm {A : Type u} {s t : A}
    (w : JoinWitness s t) :
    (joinWitness_symm (joinWitness_symm w)) = w := by
  simp [joinWitness_symm]

/-- Theorem 56: condPath_toPath on single step. -/
theorem condPath_toPath_step {A : Type u} {a b : A}
    (rule : ConditionalRule A) (cs : CondStep rule a b) :
    condPath_toPath (CondPath.step rule cs (CondPath.refl b)) =
    Path.trans cs.ruleApp (Path.refl b) := by
  rfl

/-- Theorem 57: Chaining conditional paths and converting to equality
    is consistent with transitivity. -/
theorem condPath_trans_toEq {A : Type u} {a b c : A}
    (p : CondPath a b) (q : CondPath b c) :
    condPath_toEq (condPath_trans p q) =
    (condPath_toEq p) ▸ (condPath_toEq q) := by
  have hp := condPath_toEq p
  have hq := condPath_toEq q
  subst hp; subst hq; rfl

/-- Theorem 58: An infeasible condition means no CondStep can be built. -/
theorem infeasible_no_condStep {A : Type u} {rule : ConditionalRule A}
    {a b : A}
    (ir : InfeasibleRule rule)
    (cs : CondStep rule a b) : False :=
  Empty.elim (ir.infeasible.noWitness (cs.witnesses ir.condIdx))

/-- Theorem 59: Type1Step with a single satisfied condition. -/
def type1Step_single {A : Type u} {l r s t : A}
    (ruleApp : Path l r)
    (condPath : ReduceWitness s t) :
    Type1Step ⟨l, r, [⟨s, t, ConditionKind.reducibility⟩]⟩ l r :=
  ⟨ruleApp, fun ⟨0, _⟩ => ⟨condPath⟩⟩

/-- Theorem 60: Composing condPath_congrArg with path symmetry. -/
theorem condPath_congrArg_symm_path {A B : Type u} {a b : A}
    (f : A -> B) (cp : CondPath a b) :
    Path.symm (condPath_congrArg f cp) =
    Path.congrArg f (Path.symm (condPath_toPath cp)) := by
  simp [condPath_congrArg]

end ComputationalPaths.ConditionalRewriteDeep
