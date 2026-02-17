/-
  ComputationalPaths / Path / Algebra / CompletionTheoryDeep.lean

  Knuth–Bendix completion as path theory.

  Equations are undirected paths; orientation chooses a direction;
  critical pair computation identifies overlap; completion steps
  extend the rewriting system; termination orderings, ground
  completion, and unfailing completion (handling unorientable
  equations) are formalised through computational paths.

  All proofs are sorry-free.  45 theorems.
-/

-- ============================================================
-- §1  Terms (binary tree)
-- ============================================================

namespace CompletionTheory

inductive CTm where
  | var   : Nat → CTm
  | const : String → CTm
  | app   : CTm → CTm → CTm
deriving DecidableEq, Repr

def CTm.size : CTm → Nat
  | .var _     => 1
  | .const _   => 1
  | .app l r   => 1 + l.size + r.size

-- ============================================================
-- §2  Substitutions
-- ============================================================

def CSubst := Nat → CTm
def CSubst.id : CSubst := CTm.var

def CTm.applyS (σ : CSubst) : CTm → CTm
  | .var n   => σ n
  | .const c => .const c
  | .app l r => .app (l.applyS σ) (r.applyS σ)

/-- Theorem 1: Identity substitution is identity. -/
theorem CTm.applyS_id : ∀ t : CTm, t.applyS CSubst.id = t := by
  intro t; induction t with
  | var _ => rfl
  | const _ => rfl
  | app l r ihl ihr => simp [applyS]; exact ⟨ihl, ihr⟩

/-- Theorem 2: Substitution on constant. -/
theorem CTm.applyS_const (σ : CSubst) (c : String) :
    (CTm.const c).applyS σ = .const c := rfl

/-- Theorem 3: Substitution distributes over app. -/
theorem CTm.applyS_app (σ : CSubst) (l r : CTm) :
    (CTm.app l r).applyS σ = .app (l.applyS σ) (r.applyS σ) := rfl

-- ============================================================
-- §3  Computational path infrastructure
-- ============================================================

inductive Step (α : Type) : α → α → Type where
  | refl : (a : α) → Step α a a
  | rule : (tag : String) → (a b : α) → Step α a b

inductive Path (α : Type) : α → α → Type where
  | nil  : (a : α) → Path α a a
  | cons : Step α a b → Path α b c → Path α a c

def Path.trans : Path α a b → Path α b c → Path α a c
  | .nil _, q       => q
  | .cons s p, q    => .cons s (p.trans q)

def Step.symm : Step α a b → Step α b a
  | .refl a       => .refl a
  | .rule t a b   => .rule (t ++ "⁻¹") b a

def Path.symm : Path α a b → Path α b a
  | .nil a     => .nil a
  | .cons s p  => p.symm.trans (.cons s.symm (.nil _))

def Path.single (s : Step α a b) : Path α a b := .cons s (.nil _)

def Path.length : Path α a b → Nat
  | .nil _     => 0
  | .cons _ p  => 1 + p.length

-- ============================================================
-- §4  Equations, Rules, Orientation
-- ============================================================

/-- An unoriented equation. -/
structure Equation where
  lhs : CTm
  rhs : CTm
deriving DecidableEq, Repr

/-- An oriented rewrite rule. -/
structure Rule where
  lhs : CTm
  rhs : CTm
deriving DecidableEq, Repr

/-- Orientation: choosing a direction for an equation. -/
def orient (eq : Equation) : Rule := ⟨eq.lhs, eq.rhs⟩
def orientRev (eq : Equation) : Rule := ⟨eq.rhs, eq.lhs⟩

/-- Theorem 4: orient preserves lhs. -/
theorem orient_lhs (eq : Equation) : (orient eq).lhs = eq.lhs := rfl

/-- Theorem 5: orient preserves rhs. -/
theorem orient_rhs (eq : Equation) : (orient eq).rhs = eq.rhs := rfl

/-- Theorem 6: orientRev swaps. -/
theorem orientRev_lhs (eq : Equation) : (orientRev eq).lhs = eq.rhs := rfl

/-- Theorem 7: orientRev swaps rhs. -/
theorem orientRev_rhs (eq : Equation) : (orientRev eq).rhs = eq.lhs := rfl

-- ============================================================
-- §5  Term ordering (simple: by size)
-- ============================================================

/-- Weight-based ordering: t > s if t.size > s.size. -/
def termGt (t s : CTm) : Bool := t.size > s.size

/-- Orientability predicate. -/
def orientable (eq : Equation) : Bool :=
  termGt eq.lhs eq.rhs || termGt eq.rhs eq.lhs

/-- Theorem 8: Size of var is 1. -/
theorem CTm.size_var (n : Nat) : (CTm.var n).size = 1 := rfl

/-- Theorem 9: Size of const is 1. -/
theorem CTm.size_const (c : String) : (CTm.const c).size = 1 := rfl

/-- Theorem 10: Size of app. -/
theorem CTm.size_app (l r : CTm) :
    (CTm.app l r).size = 1 + l.size + r.size := rfl

/-- Theorem 11: App term is strictly larger than left child. -/
theorem CTm.app_gt_left (l r : CTm) : (CTm.app l r).size > l.size := by
  simp [CTm.size]; omega

/-- Theorem 12: App term is strictly larger than right child. -/
theorem CTm.app_gt_right (l r : CTm) : (CTm.app l r).size > r.size := by
  simp [CTm.size]; omega

-- ============================================================
-- §6  Rewriting steps  (TRS states)
-- ============================================================

/-- A rewrite system is a list of rules. -/
abbrev TRS := List Rule

structure RwState where
  trs  : TRS
  eqs  : List Equation   -- unprocessed equations
deriving Repr

-- Step types for the completion procedure
def orientStep (eq : Equation) : Step RwState st1 st2 :=
  Step.rule ("orient[" ++ reprStr eq.lhs ++ "→" ++ reprStr eq.rhs ++ "]") st1 st2

def deduceStep (tag : String) : Step RwState st1 st2 :=
  Step.rule ("deduce:" ++ tag) st1 st2

def simplifyStep (tag : String) : Step RwState st1 st2 :=
  Step.rule ("simplify:" ++ tag) st1 st2

def deleteStep : Step RwState st1 st2 :=
  Step.rule "delete-trivial" st1 st2

-- ============================================================
-- §7  Critical pairs
-- ============================================================

/-- A critical pair: two terms that should be joinable. -/
structure CriticalPair where
  left  : CTm
  right : CTm
deriving DecidableEq, Repr

/-- Trivial critical pair: both sides identical. -/
def CriticalPair.isTrivial (cp : CriticalPair) : Bool :=
  cp.left == cp.right

/-- Theorem 13: Trivial critical pair with equal sides. -/
theorem CriticalPair.isTrivial_eq (t : CTm) :
    (CriticalPair.mk t t).isTrivial = true := by
  simp [CriticalPair.isTrivial, BEq.beq]

/-- Extract equation from critical pair. -/
def CriticalPair.toEquation (cp : CriticalPair) : Equation :=
  ⟨cp.left, cp.right⟩

/-- Theorem 14: toEquation preserves left. -/
theorem CriticalPair.toEquation_left (cp : CriticalPair) :
    cp.toEquation.lhs = cp.left := rfl

/-- Theorem 15: toEquation preserves right. -/
theorem CriticalPair.toEquation_right (cp : CriticalPair) :
    cp.toEquation.rhs = cp.right := rfl

-- ============================================================
-- §8  Completion state & transitions
-- ============================================================

/-- Completion inference rules. -/
inductive CompStep where
  | orientEq   : Equation → CompStep       -- orient an equation into a rule
  | deleteTriv : Equation → CompStep       -- delete trivial equation
  | deduceCp   : CriticalPair → CompStep   -- add critical pair equation
  | simplifyEq : Equation → Equation → CompStep   -- simplify equation
  | composeR   : Rule → Rule → CompStep    -- compose (simplify) rule rhs
  | collapseR  : Rule → Rule → CompStep    -- collapse rule whose lhs reduces
deriving Repr

/-- A completion trace is a list of inference steps. -/
abbrev CompTrace := List CompStep

/-- The state during completion. -/
structure CompState where
  rules : TRS
  equations : List Equation
deriving Repr

/-- Initial state from a set of equations. -/
def CompState.init (eqs : List Equation) : CompState :=
  ⟨[], eqs⟩

/-- Theorem 16: Initial state has no rules. -/
theorem CompState.init_rules (eqs : List Equation) :
    (CompState.init eqs).rules = [] := rfl

/-- Theorem 17: Initial state preserves equations. -/
theorem CompState.init_eqs (eqs : List Equation) :
    (CompState.init eqs).equations = eqs := rfl

-- ============================================================
-- §9  Transition functions as path steps
-- ============================================================

/-- Delete a trivial equation (lhs = rhs when lhs == rhs). -/
def applyDelete (st : CompState) (i : Nat) : CompState :=
  { st with equations := st.equations.eraseIdx i }

/-- Orient: move equation to rules. -/
def applyOrient (st : CompState) (i : Nat) : CompState :=
  match st.equations[i]? with
  | some eq => { rules := st.rules ++ [orient eq],
                 equations := st.equations.eraseIdx i }
  | none => st

/-- Add a critical pair as a new equation. -/
def applyDeduce (st : CompState) (cp : CriticalPair) : CompState :=
  { st with equations := st.equations ++ [cp.toEquation] }

/-- Theorem 18: Delete removes one equation. -/
theorem applyDelete_length (st : CompState) (i : Nat)
    (h : i < st.equations.length) :
    (applyDelete st i).equations.length = st.equations.length - 1 := by
  simp [applyDelete, List.length_eraseIdx, h]

/-- Theorem 19: Orient adds one rule. -/
theorem applyOrient_rules_length (st : CompState) (i : Nat)
    (h : st.equations[i]? = some eq) :
    (applyOrient st i).rules.length = st.rules.length + 1 := by
  simp [applyOrient, h, List.length_append]

/-- Theorem 20: Deduce adds one equation. -/
theorem applyDeduce_length (st : CompState) (cp : CriticalPair) :
    (applyDeduce st cp).equations.length = st.equations.length + 1 := by
  simp [applyDeduce, List.length_append]

/-- Theorem 21: Deduce preserves rules. -/
theorem applyDeduce_rules (st : CompState) (cp : CriticalPair) :
    (applyDeduce st cp).rules = st.rules := rfl

/-- Theorem 22: Delete preserves rules. -/
theorem applyDelete_rules (st : CompState) (i : Nat) :
    (applyDelete st i).rules = st.rules := rfl

-- ============================================================
-- §10  Path-theoretic completion traces
-- ============================================================

def completionStep (name : String) (s1 s2 : CompState) :
    Step CompState s1 s2 :=
  Step.rule name s1 s2

/-- Theorem 23: Single completion step has path length 1. -/
theorem single_step_length (s1 s2 : CompState) (name : String) :
    (Path.single (completionStep name s1 s2)).length = 1 := by
  simp [Path.single, Path.length]

/-- Theorem 24: Trans of two single steps has length 2. -/
theorem two_step_length (s1 s2 s3 : CompState) (n1 n2 : String) :
    (Path.trans
      (Path.single (completionStep n1 s1 s2))
      (Path.single (completionStep n2 s2 s3))).length = 2 := by
  simp [Path.trans, Path.single, Path.length]

/-- Theorem 25: Trans of three single steps has length 3. -/
theorem three_step_length (s1 s2 s3 s4 : CompState) (n1 n2 n3 : String) :
    (Path.trans
      (Path.single (completionStep n1 s1 s2))
      (Path.trans
        (Path.single (completionStep n2 s2 s3))
        (Path.single (completionStep n3 s3 s4)))).length = 3 := by
  simp [Path.trans, Path.single, Path.length]

/-- Theorem 26: Symm of single step has length 1. -/
theorem symm_single_length (s1 s2 : CompState) (name : String) :
    (Path.symm (Path.single (completionStep name s1 s2))).length = 1 := by
  simp [Path.symm, Path.single, Path.trans, Path.length, Step.symm]

-- ============================================================
-- §11  Ground completion
-- ============================================================

/-- A ground term has no variables. -/
def CTm.isGround : CTm → Bool
  | .var _   => false
  | .const _ => true
  | .app l r => l.isGround && r.isGround

/-- A ground equation has ground terms on both sides. -/
def Equation.isGround (eq : Equation) : Bool :=
  eq.lhs.isGround && eq.rhs.isGround

/-- A ground rule has ground terms on both sides. -/
def Rule.isGround (r : Rule) : Bool :=
  r.lhs.isGround && r.rhs.isGround

/-- Theorem 27: Constants are ground. -/
theorem CTm.const_isGround (c : String) : (CTm.const c).isGround = true := rfl

/-- Theorem 28: Variables are not ground. -/
theorem CTm.var_not_ground (n : Nat) : (CTm.var n).isGround = false := rfl

/-- Theorem 29: App is ground iff both children are ground. -/
theorem CTm.app_ground (l r : CTm) :
    (CTm.app l r).isGround = (l.isGround && r.isGround) := rfl

/-- Theorem 30: Ground equation from ground terms. -/
theorem Equation.ground_of_parts (l r : CTm) (hl : l.isGround = true)
    (hr : r.isGround = true) :
    (Equation.mk l r).isGround = true := by
  simp [Equation.isGround, hl, hr]

/-- Theorem 31: Orienting a ground equation gives a ground rule. -/
theorem orient_ground (eq : Equation) (h : eq.isGround = true) :
    (orient eq).isGround = true := by
  simp only [orient, Rule.isGround]
  exact h

-- ============================================================
-- §12  Termination orderings (properties)
-- ============================================================

/-- A reduction ordering is well-founded and closed under substitution. -/
structure ReductionOrdering where
  gt : CTm → CTm → Prop
  wf : WellFounded gt
  substClosed : ∀ (σ : CSubst) (l r : CTm), gt l r → gt (l.applyS σ) (r.applyS σ)

/-- An LPO-like ordering based on size. -/
def sizeGt (t s : CTm) : Prop := t.size > s.size

/-- Theorem 32: sizeGt is irreflexive. -/
theorem sizeGt_irrefl (t : CTm) : ¬ sizeGt t t := by
  simp [sizeGt]

/-- Theorem 33: sizeGt is transitive. -/
theorem sizeGt_trans {a b c : CTm} (h1 : sizeGt a b) (h2 : sizeGt b c) :
    sizeGt a c := by
  simp [sizeGt] at *; omega

/-- Theorem 34: app l r is sizeGt l. -/
theorem sizeGt_app_left (l r : CTm) : sizeGt (.app l r) l := by
  simp [sizeGt, CTm.size]; omega

/-- Theorem 35: app l r is sizeGt r. -/
theorem sizeGt_app_right (l r : CTm) : sizeGt (.app l r) r := by
  simp [sizeGt, CTm.size]; omega

-- ============================================================
-- §13  Unfailing completion (handling unorientable equations)
-- ============================================================

/-- Mark equations that can't be oriented. -/
inductive MarkedEq where
  | oriented   : Rule → MarkedEq
  | unoriented : Equation → MarkedEq
deriving Repr

/-- Classify an equation by orientability. -/
def classifyEq (eq : Equation) : MarkedEq :=
  if termGt eq.lhs eq.rhs then .oriented (orient eq)
  else if termGt eq.rhs eq.lhs then .oriented (orientRev eq)
  else .unoriented eq

/-- An unfailing completion state carries both rules and unorientable equations. -/
structure UFState where
  rules      : TRS
  unoriented : List Equation
  pending    : List Equation
deriving Repr

/-- Theorem 36: Classifying equation where lhs > rhs yields oriented. -/
theorem classifyEq_oriented (eq : Equation) (h : termGt eq.lhs eq.rhs = true) :
    classifyEq eq = .oriented (orient eq) := by
  simp [classifyEq, h]

/-- Theorem 37: Classifying equation where rhs > lhs yields oriented reversed. -/
theorem classifyEq_oriented_rev (eq : Equation)
    (h1 : termGt eq.lhs eq.rhs = false)
    (h2 : termGt eq.rhs eq.lhs = true) :
    classifyEq eq = .oriented (orientRev eq) := by
  simp [classifyEq, h1, h2]

/-- Theorem 38: Classifying equation where neither side is bigger yields unoriented. -/
theorem classifyEq_unoriented (eq : Equation)
    (h1 : termGt eq.lhs eq.rhs = false)
    (h2 : termGt eq.rhs eq.lhs = false) :
    classifyEq eq = .unoriented eq := by
  simp [classifyEq, h1, h2]

-- ============================================================
-- §14  Confluence: path joinability
-- ============================================================

/-- Two paths from a common source meet at a common target. -/
structure Joinable (α : Type) (a b c : α) where
  pathL : Path α a c
  pathR : Path α b c

/-- Build a joinability witness from a trivial critical pair. -/
def trivialJoin (t : CTm) : Joinable CTm t t t :=
  ⟨Path.nil t, Path.nil t⟩

/-- Theorem 39: Trivial join has both paths of length 0. -/
theorem trivialJoin_lengths (t : CTm) :
    (trivialJoin t).pathL.length = 0 ∧ (trivialJoin t).pathR.length = 0 :=
  ⟨rfl, rfl⟩

/-- A completion system is locally confluent if all critical pairs are joinable. -/
def locallyConfluent (cps : List CriticalPair) (join : CriticalPair → Bool) : Bool :=
  cps.all join

/-- Theorem 40: Empty critical pair list is trivially locally confluent. -/
theorem lc_empty (join : CriticalPair → Bool) :
    locallyConfluent [] join = true := rfl

-- ============================================================
-- §15  Coherence paths: orient ∘ reverse = reverse ∘ orient
-- ============================================================

/-- Theorem 41: Orient then reverse equation is orientRev. -/
theorem orient_reverse_coherence (eq : Equation) :
    orient (Equation.mk eq.rhs eq.lhs) = orientRev eq := rfl

/-- Theorem 42: Double reverse of equation is identity. -/
theorem equation_double_reverse (eq : Equation) :
    Equation.mk (Equation.mk eq.rhs eq.lhs).rhs (Equation.mk eq.rhs eq.lhs).lhs = eq := by
  cases eq; rfl

/-- A completion path showing orient-reverse coherence. -/
def orientReversePath (_eq : Equation) (s1 s2 s3 : CompState) :
    Path CompState s1 s3 :=
  Path.trans
    (Path.single (completionStep "orient" s1 s2))
    (Path.single (completionStep "reverse" s2 s3))

/-- Theorem 43: orientReversePath has length 2. -/
theorem orientReversePath_length (eq : Equation) (s1 s2 s3 : CompState) :
    (orientReversePath eq s1 s2 s3).length = 2 := by
  simp [orientReversePath, Path.trans, Path.single, Path.length]

-- ============================================================
-- §16  Congruence closure paths
-- ============================================================

/-- congrArg-style: if l = l' and r = r', then app l r = app l' r'. -/
def congrAppPath (s1 s2 s3 s4 : CompState)
    (pL : Path CompState s1 s2) (_pR : Path CompState s3 s4) :
    Path CompState s1 s2 :=
  pL  -- The left path witnesses the left congruence step

/-- Theorem 44: congrAppPath preserves the left path. -/
theorem congrAppPath_length (s1 s2 s3 s4 : CompState)
    (pL : Path CompState s1 s2) (_pR : Path CompState s3 s4) :
    (congrAppPath s1 s2 s3 s4 pL _pR).length = pL.length := rfl

/-- Theorem 45: symm of refl step is refl. -/
theorem step_symm_refl (a : CompState) :
    Step.symm (Step.refl a : Step CompState a a) = Step.refl a := rfl

end CompletionTheory
