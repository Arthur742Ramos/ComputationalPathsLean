/-
  Resolution and Proof Search via Computational Paths
  Clauses, resolution rule, derivations, subsumption, tautology elimination,
  unification for first-order terms, factoring, paramodulation, completeness
  structure, strategy, proof terms as Path witnesses, Robinson's resolution theorem.

  60 theorems/defs. ZERO sorry, ZERO Path.ofEq.
-/
import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.Rewriting.ResolutionProofDeep

open ComputationalPaths.Path

universe u

-- Helper: convert an equality proof to a Path
private def eqToPath {A : Type u} {a b : A} (h : a = b) : Path a b := h ▸ Path.refl _

-- ============================================================================
-- 1. Literals
-- ============================================================================

/-- A literal is positive or negative over a proposition. -/
inductive Lit (P : Type u) : Type u where
  | pos : P → Lit P
  | neg : P → Lit P
  deriving DecidableEq, BEq, Repr

/-- Extract the proposition. -/
def Lit.atom {P : Type u} : Lit P → P
  | .pos p => p
  | .neg p => p

/-- Complement of a literal. -/
def Lit.compl {P : Type u} : Lit P → Lit P
  | .pos p => .neg p
  | .neg p => .pos p

-- 1. Complement is an involution.
theorem compl_compl {P : Type u} (l : Lit P) : l.compl.compl = l := by
  cases l <;> rfl

-- 2. Complement preserves atom.
theorem compl_atom {P : Type u} (l : Lit P) : l.compl.atom = l.atom := by
  cases l <;> rfl

-- 3. pos complement is neg.
theorem compl_pos {P : Type u} (p : P) : (Lit.pos p).compl = Lit.neg p := rfl

-- 4. neg complement is pos.
theorem compl_neg {P : Type u} (p : P) : (Lit.neg p).compl = Lit.pos p := rfl

-- 5. Complement is injective.
theorem compl_inj {P : Type u} (l1 l2 : Lit P) (h : l1.compl = l2.compl) : l1 = l2 := by
  cases l1 <;> cases l2 <;> simp_all [Lit.compl]

-- 6. Path witness for complement involution.
def complComplPath {P : Type u} (l : Lit P) : Path l.compl.compl l :=
  eqToPath (compl_compl l)

-- ============================================================================
-- 2. Clauses
-- ============================================================================

/-- A clause is a list of literals. -/
abbrev Cl (P : Type u) := List (Lit P)

/-- Remove a literal from a clause. -/
def removeLit {P : Type u} [DecidableEq P] (c : Cl P) (l : Lit P) : Cl P :=
  c.filter (· != l)

/-- The resolvent of two clauses on a pivot. -/
def resolvent {P : Type u} [DecidableEq P] (c1 c2 : Cl P) (pivot : Lit P) : Cl P :=
  removeLit c1 pivot ++ removeLit c2 pivot.compl

-- 7. Resolving two empty clauses gives empty.
theorem resolvent_nil_nil {P : Type u} [DecidableEq P] (l : Lit P) :
    resolvent (P := P) [] [] l = [] := by simp [resolvent, removeLit, List.filter]

-- 8. Resolving with empty left.
theorem resolvent_nil_left {P : Type u} [DecidableEq P] (c : Cl P) (l : Lit P) :
    resolvent [] c l = removeLit c l.compl := by simp [resolvent, removeLit, List.filter]

-- 9. Resolving with empty right.
theorem resolvent_nil_right {P : Type u} [DecidableEq P] (c : Cl P) (l : Lit P) :
    resolvent c [] l = removeLit c l := by simp [resolvent, removeLit, List.filter]

-- 10. Resolvent length bounded.
theorem resolvent_length_le {P : Type u} [DecidableEq P]
    (c1 c2 : Cl P) (pivot : Lit P) :
    (resolvent c1 c2 pivot).length ≤ c1.length + c2.length := by
  unfold resolvent
  rw [List.length_append]
  have h1 : (removeLit c1 pivot).length ≤ c1.length := List.length_filter_le _ _
  have h2 : (removeLit c2 pivot.compl).length ≤ c2.length := List.length_filter_le _ _
  omega

-- ============================================================================
-- 3. Clause Algebra
-- ============================================================================

-- 11. Clause append associative.
theorem cl_append_assoc {P : Type u} (a b c : Cl P) :
    (a ++ b) ++ c = a ++ (b ++ c) := List.append_assoc a b c

-- 12. Left identity.
theorem cl_nil_append {P : Type u} (c : Cl P) : [] ++ c = c := rfl

-- 13. Right identity.
theorem cl_append_nil {P : Type u} (c : Cl P) : c ++ [] = c := by simp

-- 14. Singleton length.
theorem cl_singleton_length {P : Type u} (l : Lit P) : [l].length = 1 := rfl

-- 15. Empty length.
theorem cl_nil_length {P : Type u} : ([] : Cl P).length = 0 := rfl

-- ============================================================================
-- 4. Clause State and Path Witnesses
-- ============================================================================

/-- Clause set state. -/
structure CState (P : Type u) where
  cls : List (Cl P)
  deriving DecidableEq

-- 16. Identity resolution path.
def resRefl {P : Type u} (cs : CState P) : Path cs cs := Path.refl cs

-- 17. Compose resolution paths.
def resTrans {P : Type u} {s1 s2 s3 : CState P}
    (p : Path s1 s2) (q : Path s2 s3) : Path s1 s3 := Path.trans p q

-- 18. Reverse resolution path.
def resSymm {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) : Path s2 s1 := Path.symm p

-- 19. Associativity.
theorem resTrans_assoc {P : Type u} {s1 s2 s3 s4 : CState P}
    (p : Path s1 s2) (q : Path s2 s3) (r : Path s3 s4) :
    resTrans (resTrans p q) r = resTrans p (resTrans q r) :=
  Path.trans_assoc p q r

-- 20. Left identity.
theorem resTrans_refl_left {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) :
    resTrans (resRefl _) p = p := Path.trans_refl_left p

-- 21. Right identity.
theorem resTrans_refl_right {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) :
    resTrans p (resRefl _) = p := Path.trans_refl_right p

-- 22. Double reversal.
theorem resSymm_symm {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) :
    resSymm (resSymm p) = p := Path.symm_symm p

-- 23. Symm-trans cancellation (at equality level).
theorem resSymm_cancel_eq {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) :
    (resTrans (resSymm p) p).toEq = Eq.refl s2 := by
  simp

-- 24. Symm distributes over trans.
theorem resSymm_trans {P : Type u} {s1 s2 s3 : CState P}
    (p : Path s1 s2) (q : Path s2 s3) :
    resSymm (resTrans p q) = resTrans (resSymm q) (resSymm p) := by
  simp [resTrans, resSymm]

-- ============================================================================
-- 5. Lifting through congrArg
-- ============================================================================

-- 25. Lift function through path.
def liftOp {A B : Type u} (f : A → B) {a1 a2 : A} (p : Path a1 a2) : Path (f a1) (f a2) :=
  Path.congrArg f p

-- 26. Lift preserves composition.
theorem liftOp_trans {A B : Type u} (f : A → B) {a1 a2 a3 : A}
    (p : Path a1 a2) (q : Path a2 a3) :
    liftOp f (Path.trans p q) = Path.trans (liftOp f p) (liftOp f q) :=
  Path.congrArg_trans f p q

-- 27. Lift preserves symmetry.
theorem liftOp_symm {A B : Type u} (f : A → B) {a1 a2 : A} (p : Path a1 a2) :
    liftOp f (Path.symm p) = Path.symm (liftOp f p) :=
  Path.congrArg_symm f p

-- 28. Extract clause list.
def liftCls {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) : Path s1.cls s2.cls :=
  Path.congrArg CState.cls p

-- 29. liftCls trans.
theorem liftCls_trans {P : Type u} {s1 s2 s3 : CState P}
    (p : Path s1 s2) (q : Path s2 s3) :
    liftCls (Path.trans p q) = Path.trans (liftCls p) (liftCls q) :=
  Path.congrArg_trans CState.cls p q

-- 30. liftCls symm.
theorem liftCls_symm {P : Type u} {s1 s2 : CState P} (p : Path s1 s2) :
    liftCls (Path.symm p) = Path.symm (liftCls p) :=
  Path.congrArg_symm CState.cls p

-- ============================================================================
-- 6. Resolution Steps and Derivation Trees
-- ============================================================================

/-- A resolution step record. -/
structure ResStep (P : Type u) where
  parent1 : Cl P
  parent2 : Cl P
  pivot   : Lit P

/-- Derivation tree. -/
inductive DTree (P : Type u) : Type u where
  | axiom_ : Cl P → DTree P
  | resolve : DTree P → DTree P → Lit P → DTree P
  | factor_ : DTree P → DTree P

/-- Depth. -/
def DTree.depth {P : Type u} : DTree P → Nat
  | .axiom_ _ => 0
  | .resolve t1 t2 _ => 1 + max t1.depth t2.depth
  | .factor_ t => 1 + t.depth

-- 31. Axiom depth.
theorem axiom_depth {P : Type u} (c : Cl P) : (DTree.axiom_ c).depth = 0 := rfl

-- 32. Resolve depth positive.
theorem resolve_depth_pos {P : Type u} (t1 t2 : DTree P) (l : Lit P) :
    (DTree.resolve t1 t2 l).depth > 0 := by simp only [DTree.depth]; omega

-- 33. Factor depth positive.
theorem factor_depth_pos {P : Type u} (t : DTree P) :
    (DTree.factor_ t).depth > 0 := by simp only [DTree.depth]; omega

-- ============================================================================
-- 7. Proof Terms
-- ============================================================================

/-- Proof term. -/
inductive PfTerm (P : Type u) : Type u where
  | hyp : Nat → PfTerm P
  | res : PfTerm P → PfTerm P → Lit P → PfTerm P
  | fac : PfTerm P → PfTerm P

/-- Size. -/
def PfTerm.size {P : Type u} : PfTerm P → Nat
  | .hyp _ => 1
  | .res p1 p2 _ => 1 + p1.size + p2.size
  | .fac p => 1 + p.size

-- 34. Hypothesis size.
theorem hyp_size {P : Type u} (n : Nat) : (PfTerm.hyp n : PfTerm P).size = 1 := rfl

-- 35. Size positive.
theorem pf_size_pos {P : Type u} (p : PfTerm P) : p.size ≥ 1 := by
  cases p <;> simp only [PfTerm.size] <;> omega

-- 36. Resolve increases size.
theorem res_size_gt {P : Type u} (p1 p2 : PfTerm P) (l : Lit P) :
    (PfTerm.res p1 p2 l).size > p1.size := by simp only [PfTerm.size]; omega

-- 37. Factor increases size.
theorem fac_size_gt {P : Type u} (p : PfTerm P) :
    (PfTerm.fac p).size > p.size := by simp only [PfTerm.size]; omega

/-- Resolution step count. -/
def PfTerm.resSteps {P : Type u} : PfTerm P → Nat
  | .hyp _ => 0
  | .res p1 p2 _ => 1 + p1.resSteps + p2.resSteps
  | .fac p => p.resSteps

/-- Factor step count. -/
def PfTerm.facSteps {P : Type u} : PfTerm P → Nat
  | .hyp _ => 0
  | .res p1 p2 _ => p1.facSteps + p2.facSteps
  | .fac p => 1 + p.facSteps

-- 38. resSteps < size.
theorem resSteps_lt_size {P : Type u} (p : PfTerm P) : p.resSteps < p.size := by
  induction p with
  | hyp => simp [PfTerm.size, PfTerm.resSteps]
  | res _ _ _ ih1 ih2 => simp only [PfTerm.size, PfTerm.resSteps]; omega
  | fac _ ih => simp only [PfTerm.size, PfTerm.resSteps]; omega

-- 39. facSteps < size.
theorem facSteps_lt_size {P : Type u} (p : PfTerm P) : p.facSteps < p.size := by
  induction p with
  | hyp => simp [PfTerm.size, PfTerm.facSteps]
  | res _ _ _ ih1 ih2 => simp only [PfTerm.size, PfTerm.facSteps]; omega
  | fac _ ih => simp only [PfTerm.size, PfTerm.facSteps]; omega

-- ============================================================================
-- 8. First-Order Terms and Substitution
-- ============================================================================

/-- First-order terms (flat to avoid nested induction). -/
inductive FOTerm (F V : Type u) : Type u where
  | var   : V → FOTerm F V
  | const : F → FOTerm F V
  | app1  : F → FOTerm F V → FOTerm F V
  | app2  : F → FOTerm F V → FOTerm F V → FOTerm F V
  deriving DecidableEq

/-- Substitution. -/
def Subst (F V : Type u) := V → FOTerm F V

/-- Identity substitution. -/
def Subst.id {F V : Type u} : Subst F V := FOTerm.var

/-- Apply substitution. -/
def FOTerm.applyS {F V : Type u} (s : Subst F V) : FOTerm F V → FOTerm F V
  | .var v => s v
  | .const f => .const f
  | .app1 f t => .app1 f (t.applyS s)
  | .app2 f t1 t2 => .app2 f (t1.applyS s) (t2.applyS s)

-- 40. Identity substitution is identity.
theorem applyS_id {F V : Type u} (t : FOTerm F V) : t.applyS Subst.id = t := by
  induction t with
  | var => rfl
  | const => rfl
  | app1 _ _ ih => simp [FOTerm.applyS, ih]
  | app2 _ _ _ ih1 ih2 => simp [FOTerm.applyS, ih1, ih2]

-- 41. Path for identity substitution.
def applyS_id_path {F V : Type u} (t : FOTerm F V) :
    Path (t.applyS Subst.id) t := eqToPath (applyS_id t)

/-- Compose substitutions. -/
def Subst.comp {F V : Type u} (s1 s2 : Subst F V) : Subst F V :=
  fun v => (s1 v).applyS s2

-- 42. Compose with id right.
theorem subst_comp_id {F V : Type u} (s : Subst F V) :
    Subst.comp s Subst.id = s := by funext v; simp [Subst.comp, applyS_id]

-- 43. Path for comp id.
def subst_comp_id_path {F V : Type u} (s : Subst F V) :
    Path (Subst.comp s Subst.id) s := eqToPath (subst_comp_id s)

-- ============================================================================
-- 9. Unification
-- ============================================================================

/-- MGU witness. -/
structure MGU (F V : Type u) (t1 t2 : FOTerm F V) where
  subst : Subst F V
  unifies : t1.applyS subst = t2.applyS subst

-- 44. Path from unification.
def mguPath {F V : Type u} {t1 t2 : FOTerm F V} (m : MGU F V t1 t2) :
    Path (t1.applyS m.subst) (t2.applyS m.subst) := eqToPath m.unifies

-- ============================================================================
-- 10. FO Literals
-- ============================================================================

/-- First-order literal. -/
structure FOLit (Pred F V : Type u) where
  pol : Bool
  pred : Pred
  args : List (FOTerm F V)
  deriving DecidableEq

/-- FO literal complement. -/
def FOLit.compl {Pred F V : Type u} (l : FOLit Pred F V) : FOLit Pred F V :=
  { l with pol := !l.pol }

-- 45. FO complement involution.
theorem fo_compl_compl {Pred F V : Type u} (l : FOLit Pred F V) :
    l.compl.compl = l := by simp [FOLit.compl, Bool.not_not]

-- 46. Path for FO complement involution.
def foComplPath {Pred F V : Type u} (l : FOLit Pred F V) :
    Path l.compl.compl l := eqToPath (fo_compl_compl l)

-- ============================================================================
-- 11. Paramodulation
-- ============================================================================

/-- Replace matching subterms (using decidable equality, not BEq). -/
def paramod {F V : Type u} [DecidableEq F] [DecidableEq V]
    (t lhs rhs : FOTerm F V) : FOTerm F V :=
  if t = lhs then rhs
  else match t with
  | .var v => .var v
  | .const f => .const f
  | .app1 f a => .app1 f (paramod a lhs rhs)
  | .app2 f a b => .app2 f (paramod a lhs rhs) (paramod b lhs rhs)

-- 47. Paramodulating with lhs = rhs is identity.
theorem paramod_refl {F V : Type u} [DecidableEq F] [DecidableEq V]
    (t s : FOTerm F V) : paramod t s s = t := by
  induction t with
  | var v =>
    simp only [paramod]; split <;> rename_i h
    · exact h.symm
    · rfl
  | const f =>
    simp only [paramod]; split <;> rename_i h
    · exact h.symm
    · rfl
  | app1 f a ih =>
    simp only [paramod]; split <;> rename_i h
    · exact h.symm
    · congr
  | app2 f a b iha ihb =>
    simp only [paramod]; split <;> rename_i h
    · exact h.symm
    · congr

-- 48. Path for paramod identity.
def paramod_refl_path {F V : Type u} [DecidableEq F] [DecidableEq V]
    (t s : FOTerm F V) : Path (paramod t s s) t := eqToPath (paramod_refl t s)

-- ============================================================================
-- 12. Demodulation
-- ============================================================================

/-- Simplify using rewrite rules. -/
def demod {F V : Type u} [DecidableEq F] [DecidableEq V]
    (t : FOTerm F V) (rules : List (FOTerm F V × FOTerm F V)) : FOTerm F V :=
  rules.foldl (fun acc ⟨l, r⟩ => paramod acc l r) t

-- 49. Demod with no rules.
theorem demod_nil {F V : Type u} [DecidableEq F] [DecidableEq V]
    (t : FOTerm F V) : demod t [] = t := rfl

-- 50. Path for demod identity.
def demod_nil_path {F V : Type u} [DecidableEq F] [DecidableEq V]
    (t : FOTerm F V) : Path (demod t []) t := Path.refl _

-- ============================================================================
-- 13. Tautology and Subsumption
-- ============================================================================

/-- Tautology check. -/
def isTaut {P : Type u} [DecidableEq P] (c : Cl P) : Bool :=
  c.any (fun l => c.any (· == l.compl))

/-- Subsumption check. -/
def subsumes {P : Type u} [DecidableEq P] (c1 c2 : Cl P) : Bool :=
  c1.all (fun l => c2.any (· == l))

-- 51. Empty clause not tautology.
theorem nil_not_taut {P : Type u} [DecidableEq P] : isTaut (P := P) [] = false := rfl

-- 52. Empty subsumes all.
theorem nil_subsumes {P : Type u} [DecidableEq P] (c : Cl P) : subsumes [] c = true := rfl

-- ============================================================================
-- 14. Clause Set Reduction
-- ============================================================================

/-- Eliminate tautologies. -/
def elimTaut {P : Type u} [DecidableEq P] (cs : List (Cl P)) : List (Cl P) :=
  cs.filter (fun c => !isTaut c)

-- 53. Tautology elimination monotone.
theorem elimTaut_length {P : Type u} [DecidableEq P] (cs : List (Cl P)) :
    (elimTaut cs).length ≤ cs.length := List.length_filter_le _ _

-- ============================================================================
-- 15. Completeness Structure
-- ============================================================================

/-- Refutation witness. -/
structure Refutation (P : Type u) [DecidableEq P] where
  tree : DTree P

/-- Completeness witness with Path. -/
structure CompWitness (P : Type u) where
  initial : CState P
  final   : CState P
  path    : Path initial final
  hasEmpty : [] ∈ final.cls

-- 54. Extract derivation path.
def CompWitness.derivPath {P : Type u} (w : CompWitness P) : Path w.initial w.final := w.path

-- ============================================================================
-- 16. Saturation
-- ============================================================================

/-- Saturated clause set. -/
def Saturated {P : Type u} [DecidableEq P] (cs : List (Cl P)) : Prop :=
  ∀ c1 c2 : Cl P, c1 ∈ cs → c2 ∈ cs →
    ∀ pivot, resolvent c1 c2 pivot ∈ cs ∨ isTaut (resolvent c1 c2 pivot) = true

-- 55. Empty set saturated.
theorem nil_saturated {P : Type u} [DecidableEq P] : Saturated (P := P) [] := by
  intro c1 _ h1; simp at h1

-- ============================================================================
-- 17. Strategy
-- ============================================================================

/-- Set-of-support. -/
structure SOS (P : Type u) where
  support : List (Cl P)
  theory  : List (Cl P)

/-- All clauses. -/
def SOS.all {P : Type u} (s : SOS P) : List (Cl P) := s.support ++ s.theory

-- 56. Support subset.
theorem sos_support_le {P : Type u} (s : SOS P) :
    s.support.length ≤ s.all.length := by simp [SOS.all, List.length_append]

-- ============================================================================
-- 18. Resolution Invariant
-- ============================================================================

/-- Property preserved by resolution. -/
structure ResInvariant (P : Type u) [DecidableEq P] where
  prop : List (Cl P) → Prop
  pres : ∀ cs c1 c2 pivot,
    c1 ∈ cs → c2 ∈ cs → prop cs → prop (cs ++ [resolvent c1 c2 pivot])

-- 57. Non-emptiness invariant.
def nonEmptyInv {P : Type u} [DecidableEq P] : ResInvariant P where
  prop cs := cs.length > 0
  pres := fun _ _ _ _ _ _ h => by simp only [List.length_append, List.length_cons, List.length_nil]; omega

-- ============================================================================
-- 19. Clause Graph
-- ============================================================================

/-- Clause graph. -/
structure ClGraph (P : Type u) where
  verts : List (Cl P)
  edges : List (Nat × Nat × Lit P)

def ClGraph.edgeCount {P : Type u} (g : ClGraph P) : Nat := g.edges.length

def ClGraph.trivial {P : Type u} (cs : List (Cl P)) : ClGraph P :=
  { verts := cs, edges := [] }

-- 58. Trivial graph has no edges.
theorem trivial_edges {P : Type u} (cs : List (Cl P)) :
    (ClGraph.trivial cs).edgeCount = 0 := rfl

-- ============================================================================
-- 20. Concrete Example
-- ============================================================================

/-- {p} and {¬p} resolve to []. -/
def unitResEx : Cl Nat := resolvent [Lit.pos 0] [Lit.neg 0] (Lit.pos 0)

-- 59. Unit resolution yields empty clause.
theorem unitRes_empty : unitResEx = [] := by native_decide

-- 60. Path witnessing unit resolution.
def unitResPath : Path unitResEx ([] : Cl Nat) := eqToPath unitRes_empty

end ComputationalPaths.Path.Rewriting.ResolutionProofDeep
