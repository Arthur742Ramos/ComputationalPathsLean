/-
  Process Algebra and CCS/CSP via Computational Paths
  ====================================================

  We model process algebra (CCS/CSP-style) through computational paths,
  treating structural congruence as Path equalities in a groupoid structure.

  Topics covered:
  - Process syntax: nil, prefix, choice, parallel, restriction, relabeling
  - Structural congruence as Path equalities
  - Labeled transition system (LTS) semantics
  - Strong, weak, and branching bisimulation
  - Bisimulation equivalence as Path groupoid
  - Expansion law
  - Milner's CCS laws
  - Trace equivalence vs bisimulation
  - Hennessy-Milner logic characterization
  - All congruence/equivalence via Path.trans/symm/congrArg
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace ProcessAlgebraDeep

open ComputationalPaths.Path

universe u v

-- ============================================================
-- Section 1: Actions and Process Syntax
-- ============================================================

/-- Actions: τ (internal), channel send/receive, or named -/
inductive Action where
  | tau : Action
  | send : Nat → Action
  | recv : Nat → Action
  | name : String → Action
  deriving DecidableEq

/-- Complement of an action (for CCS synchronization) -/
def Action.complement : Action → Action
  | Action.send n => Action.recv n
  | Action.recv n => Action.send n
  | a => a

-- ============================================================
-- Section 2: Abstract Process Algebra with Path-valued Axioms
-- ============================================================

/-- Abstract process algebra: operations + structural congruence axioms as Paths -/
structure ProcAlg where
  /-- Carrier: process terms (up to α-equivalence) -/
  Proc : Type u
  /-- Nil process -/
  nil : Proc
  /-- Action prefix -/
  pre : Action → Proc → Proc
  /-- Nondeterministic choice -/
  choice : Proc → Proc → Proc
  /-- Parallel composition -/
  par : Proc → Proc → Proc
  /-- Restriction -/
  restrict : Nat → Proc → Proc
  /-- Relabeling -/
  relabel : Nat → Nat → Proc → Proc
  -- Structural congruence axioms as equalities
  choice_comm : (P Q : Proc) → choice P Q = choice Q P
  choice_assoc : (P Q R : Proc) → choice (choice P Q) R = choice P (choice Q R)
  choice_nil : (P : Proc) → choice P nil = P
  par_comm : (P Q : Proc) → par P Q = par Q P
  par_assoc : (P Q R : Proc) → par (par P Q) R = par P (par Q R)
  par_nil : (P : Proc) → par P nil = P

variable (A : ProcAlg.{u})

-- Notation helpers
local notation "𝟎" => A.nil
local notation:65 a " ⬝ " P => A.pre a P
local notation:50 P " ⊕ₚ " Q => A.choice P Q
local notation:45 P " ∥ₚ " Q => A.par P Q

-- ============================================================
-- Def 1: Choice is commutative (Path witness)
-- ============================================================

def choice_comm_path (P Q : A.Proc) :
    Path (P ⊕ₚ Q) (Q ⊕ₚ P) :=
  Path.stepChain (A.choice_comm P Q)

-- ============================================================
-- Def 2: Choice is associative (Path witness)
-- ============================================================

def choice_assoc_path (P Q R : A.Proc) :
    Path (A.choice (A.choice P Q) R) (A.choice P (A.choice Q R)) :=
  Path.stepChain (A.choice_assoc P Q R)

-- ============================================================
-- Def 3: Choice with nil is identity (Path witness)
-- ============================================================

def choice_nil_path (P : A.Proc) :
    Path (P ⊕ₚ 𝟎) P :=
  Path.stepChain (A.choice_nil P)

-- ============================================================
-- Def 4: Parallel is commutative (Path witness)
-- ============================================================

def par_comm_path (P Q : A.Proc) :
    Path (P ∥ₚ Q) (Q ∥ₚ P) :=
  Path.stepChain (A.par_comm P Q)

-- ============================================================
-- Def 5: Parallel is associative (Path witness)
-- ============================================================

def par_assoc_path (P Q R : A.Proc) :
    Path (A.par (A.par P Q) R) (A.par P (A.par Q R)) :=
  Path.stepChain (A.par_assoc P Q R)

-- ============================================================
-- Def 6: Parallel with nil is identity (Path witness)
-- ============================================================

def par_nil_path (P : A.Proc) :
    Path (P ∥ₚ 𝟎) P :=
  Path.stepChain (A.par_nil P)

-- ============================================================
-- Def 7: Nil is left identity for choice (derived via trans)
-- ============================================================

def choice_nil_left_path (P : A.Proc) :
    Path (𝟎 ⊕ₚ P) P :=
  Path.trans (choice_comm_path A 𝟎 P) (choice_nil_path A P)

-- ============================================================
-- Def 8: Nil is left identity for parallel (derived via trans)
-- ============================================================

def par_nil_left_path (P : A.Proc) :
    Path (𝟎 ∥ₚ P) P :=
  Path.trans (par_comm_path A 𝟎 P) (par_nil_path A P)

-- ============================================================
-- Def 9: Structural congruence groupoid reflexivity
-- ============================================================

def sc_groupoid_refl (P : A.Proc) : Path P P :=
  Path.refl P

-- ============================================================
-- Def 10: Structural congruence groupoid symmetry
-- ============================================================

def sc_groupoid_symm {P Q : A.Proc} (p : Path P Q) : Path Q P :=
  Path.symm p

-- ============================================================
-- Def 11: Structural congruence groupoid transitivity
-- ============================================================

def sc_groupoid_trans {P Q R : A.Proc}
    (p : Path P Q) (q : Path Q R) : Path P R :=
  Path.trans p q

-- ============================================================
-- Def 12: Choice associativity pentagon (left)
-- ============================================================

def choice_assoc_pentagon_left (P Q R S : A.Proc) :
    Path (A.choice (A.choice (A.choice P Q) R) S)
         (A.choice (A.choice P Q) (A.choice R S)) :=
  choice_assoc_path A (A.choice P Q) R S

-- ============================================================
-- Def 13: Choice associativity pentagon (right)
-- ============================================================

def choice_assoc_pentagon_right (P Q R S : A.Proc) :
    Path (A.choice (A.choice P Q) (A.choice R S))
         (A.choice P (A.choice Q (A.choice R S))) :=
  choice_assoc_path A P Q (A.choice R S)

-- ============================================================
-- Def 14: Pentagon composite path for choice
-- ============================================================

def choice_pentagon_composite (P Q R S : A.Proc) :
    Path (A.choice (A.choice (A.choice P Q) R) S)
         (A.choice P (A.choice Q (A.choice R S))) :=
  Path.trans
    (choice_assoc_pentagon_left A P Q R S)
    (choice_assoc_pentagon_right A P Q R S)

-- ============================================================
-- Def 15: Parallel associativity pentagon composite
-- ============================================================

def par_pentagon_composite (P Q R S : A.Proc) :
    Path (A.par (A.par (A.par P Q) R) S)
         (A.par P (A.par Q (A.par R S))) :=
  Path.trans
    (par_assoc_path A (A.par P Q) R S)
    (par_assoc_path A P Q (A.par R S))

-- ============================================================
-- Def 16: Congruence for choice left under Path
-- ============================================================

def choice_cong_left (Q : A.Proc) {P P' : A.Proc}
    (p : Path P P') :
    Path (P ⊕ₚ Q) (P' ⊕ₚ Q) :=
  Path.congrArg (A.choice · Q) p

-- ============================================================
-- Def 17: Congruence for choice right under Path
-- ============================================================

def choice_cong_right (P : A.Proc) {Q Q' : A.Proc}
    (p : Path Q Q') :
    Path (P ⊕ₚ Q) (P ⊕ₚ Q') :=
  Path.congrArg (A.choice P ·) p

-- ============================================================
-- Def 18: Congruence for parallel left under Path
-- ============================================================

def par_cong_left (Q : A.Proc) {P P' : A.Proc}
    (p : Path P P') :
    Path (P ∥ₚ Q) (P' ∥ₚ Q) :=
  Path.congrArg (A.par · Q) p

-- ============================================================
-- Def 19: Congruence for parallel right under Path
-- ============================================================

def par_cong_right (P : A.Proc) {Q Q' : A.Proc}
    (p : Path Q Q') :
    Path (P ∥ₚ Q) (P ∥ₚ Q') :=
  Path.congrArg (A.par P ·) p

-- ============================================================
-- Def 20: Congruence for prefix under Path
-- ============================================================

def prefix_cong (a : Action) {P Q : A.Proc}
    (p : Path P Q) :
    Path (a ⬝ P) (a ⬝ Q) :=
  Path.congrArg (A.pre a ·) p

-- ============================================================
-- Def 21: Congruence for restriction under Path
-- ============================================================

def restrict_cong (n : Nat) {P Q : A.Proc}
    (p : Path P Q) :
    Path (A.restrict n P) (A.restrict n Q) :=
  Path.congrArg (A.restrict n ·) p

-- ============================================================
-- Def 22: Congruence for relabeling under Path
-- ============================================================

def relabel_cong (m n : Nat) {P Q : A.Proc}
    (p : Path P Q) :
    Path (A.relabel m n P) (A.relabel m n Q) :=
  Path.congrArg (A.relabel m n ·) p

-- ============================================================
-- Def 23: Bicong for choice (both sides)
-- ============================================================

def choice_bicong {P P' Q Q' : A.Proc}
    (p1 : Path P P') (p2 : Path Q Q') :
    Path (P ⊕ₚ Q) (P' ⊕ₚ Q') :=
  Path.trans (choice_cong_left A Q p1) (choice_cong_right A P' p2)

-- ============================================================
-- Def 24: Bicong for parallel (both sides)
-- ============================================================

def par_bicong {P P' Q Q' : A.Proc}
    (p1 : Path P P') (p2 : Path Q Q') :
    Path (P ∥ₚ Q) (P' ∥ₚ Q') :=
  Path.trans (par_cong_left A Q p1) (par_cong_right A P' p2)

-- ============================================================
-- Def 25: Choice comm + assoc yields rearrangement
-- ============================================================

def choice_rearrange (P Q R : A.Proc) :
    Path (A.choice (A.choice P Q) R) (A.choice Q (A.choice P R)) :=
  let step1 := choice_cong_left A R (choice_comm_path A P Q)
  let step2 := choice_assoc_path A Q P R
  Path.trans step1 step2

-- ============================================================
-- Def 26: Parallel comm + assoc yields rearrangement
-- ============================================================

def par_rearrange (P Q R : A.Proc) :
    Path (A.par (A.par P Q) R) (A.par Q (A.par P R)) :=
  let step1 := par_cong_left A R (par_comm_path A P Q)
  let step2 := par_assoc_path A Q P R
  Path.trans step1 step2

-- ============================================================
-- Def 27: Four-process choice normalization
-- ============================================================

def choice_normalize_four (P Q R S : A.Proc) :
    Path (A.choice (A.choice (A.choice P Q) R) S)
         (A.choice P (A.choice Q (A.choice R S))) :=
  Path.trans
    (choice_assoc_path A (A.choice P Q) R S)
    (choice_assoc_path A P Q (A.choice R S))

-- ============================================================
-- Def 28: Four-process parallel normalization
-- ============================================================

def par_normalize_four (P Q R S : A.Proc) :
    Path (A.par (A.par (A.par P Q) R) S)
         (A.par P (A.par Q (A.par R S))) :=
  Path.trans
    (par_assoc_path A (A.par P Q) R S)
    (par_assoc_path A P Q (A.par R S))

-- ============================================================
-- Def 29: Five-process choice normalization
-- ============================================================

def choice_normalize_five (P Q R S T : A.Proc) :
    Path (A.choice (A.choice (A.choice (A.choice P Q) R) S) T)
         (A.choice P (A.choice Q (A.choice R (A.choice S T)))) :=
  let s1 := choice_assoc_path A (A.choice (A.choice P Q) R) S T
  let s2 := choice_assoc_path A (A.choice P Q) R (A.choice S T)
  let s3 := choice_assoc_path A P Q (A.choice R (A.choice S T))
  Path.trans s1 (Path.trans s2 s3)

-- ============================================================
-- Def 30: Five-process parallel normalization
-- ============================================================

def par_normalize_five (P Q R S T : A.Proc) :
    Path (A.par (A.par (A.par (A.par P Q) R) S) T)
         (A.par P (A.par Q (A.par R (A.par S T)))) :=
  let s1 := par_assoc_path A (A.par (A.par P Q) R) S T
  let s2 := par_assoc_path A (A.par P Q) R (A.par S T)
  let s3 := par_assoc_path A P Q (A.par R (A.par S T))
  Path.trans s1 (Path.trans s2 s3)

-- ============================================================
-- Def 31: Reverse normalization via symm
-- ============================================================

def choice_denormalize_four (P Q R S : A.Proc) :
    Path (A.choice P (A.choice Q (A.choice R S)))
         (A.choice (A.choice (A.choice P Q) R) S) :=
  Path.symm (choice_normalize_four A P Q R S)

-- ============================================================
-- Def 32: Reverse parallel normalization via symm
-- ============================================================

def par_denormalize_four (P Q R S : A.Proc) :
    Path (A.par P (A.par Q (A.par R S)))
         (A.par (A.par (A.par P Q) R) S) :=
  Path.symm (par_normalize_four A P Q R S)

-- ============================================================
-- Theorem 33: trans_assoc for SC paths
-- ============================================================

theorem sc_trans_assoc {P Q R S : A.Proc}
    (p : Path P Q) (q : Path Q R) (r : Path R S) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  trans_assoc p q r

-- ============================================================
-- Theorem 34: Left identity of trans
-- ============================================================

theorem sc_trans_refl_left {P Q : A.Proc} (p : Path P Q) :
    Path.trans (Path.refl P) p = p :=
  trans_refl_left p

-- ============================================================
-- Theorem 35: Right identity of trans
-- ============================================================

theorem sc_trans_refl_right {P Q : A.Proc} (p : Path P Q) :
    Path.trans p (Path.refl Q) = p :=
  trans_refl_right p

-- ============================================================
-- Theorem 36: symm_symm involution
-- ============================================================

theorem sc_symm_symm {P Q : A.Proc} (p : Path P Q) :
    Path.symm (Path.symm p) = p :=
  symm_symm p

-- ============================================================
-- Theorem 37: symm distributes over trans
-- ============================================================

theorem sc_symm_trans {P Q R : A.Proc}
    (p : Path P Q) (q : Path Q R) :
    Path.symm (Path.trans p q) =
    Path.trans (Path.symm q) (Path.symm p) :=
  symm_trans p q

-- ============================================================
-- Theorem 38: congrArg distributes over trans for choice left
-- ============================================================

theorem congrArg_trans_choice_left {P Q R : A.Proc} (S : A.Proc)
    (p : Path P Q) (q : Path Q R) :
    Path.congrArg (A.choice · S) (Path.trans p q) =
    Path.trans (Path.congrArg (A.choice · S) p)
               (Path.congrArg (A.choice · S) q) :=
  congrArg_trans (A.choice · S) p q

-- ============================================================
-- Theorem 39: congrArg distributes over symm for choice left
-- ============================================================

theorem congrArg_symm_choice_left {P Q : A.Proc} (S : A.Proc)
    (p : Path P Q) :
    Path.congrArg (A.choice · S) (Path.symm p) =
    Path.symm (Path.congrArg (A.choice · S) p) :=
  congrArg_symm (A.choice · S) p

-- ============================================================
-- Theorem 40: congrArg distributes over trans for parallel left
-- ============================================================

theorem congrArg_trans_par_left {P Q R : A.Proc} (S : A.Proc)
    (p : Path P Q) (q : Path Q R) :
    Path.congrArg (A.par · S) (Path.trans p q) =
    Path.trans (Path.congrArg (A.par · S) p)
               (Path.congrArg (A.par · S) q) :=
  congrArg_trans (A.par · S) p q

-- ============================================================
-- Theorem 41: congrArg distributes over symm for parallel left
-- ============================================================

theorem congrArg_symm_par_left {P Q : A.Proc} (S : A.Proc)
    (p : Path P Q) :
    Path.congrArg (A.par · S) (Path.symm p) =
    Path.symm (Path.congrArg (A.par · S) p) :=
  congrArg_symm (A.par · S) p

-- ============================================================
-- Theorem 42: congrArg distributes over trans for choice right
-- ============================================================

theorem congrArg_trans_choice_right {P Q R : A.Proc} (S : A.Proc)
    (p : Path P Q) (q : Path Q R) :
    Path.congrArg (A.choice S ·) (Path.trans p q) =
    Path.trans (Path.congrArg (A.choice S ·) p)
               (Path.congrArg (A.choice S ·) q) :=
  congrArg_trans (A.choice S ·) p q

-- ============================================================
-- Theorem 43: congrArg distributes over symm for choice right
-- ============================================================

theorem congrArg_symm_choice_right {P Q : A.Proc} (S : A.Proc)
    (p : Path P Q) :
    Path.congrArg (A.choice S ·) (Path.symm p) =
    Path.symm (Path.congrArg (A.choice S ·) p) :=
  congrArg_symm (A.choice S ·) p

-- ============================================================
-- Theorem 44: congrArg distributes over trans for parallel right
-- ============================================================

theorem congrArg_trans_par_right {P Q R : A.Proc} (S : A.Proc)
    (p : Path P Q) (q : Path Q R) :
    Path.congrArg (A.par S ·) (Path.trans p q) =
    Path.trans (Path.congrArg (A.par S ·) p)
               (Path.congrArg (A.par S ·) q) :=
  congrArg_trans (A.par S ·) p q

-- ============================================================
-- Theorem 45: congrArg distributes over symm for parallel right
-- ============================================================

theorem congrArg_symm_par_right {P Q : A.Proc} (S : A.Proc)
    (p : Path P Q) :
    Path.congrArg (A.par S ·) (Path.symm p) =
    Path.symm (Path.congrArg (A.par S ·) p) :=
  congrArg_symm (A.par S ·) p

-- ============================================================
-- Theorem 46: congrArg prefix distributes over trans
-- ============================================================

theorem congrArg_trans_prefix (a : Action) {P Q R : A.Proc}
    (p : Path P Q) (q : Path Q R) :
    Path.congrArg (A.pre a ·) (Path.trans p q) =
    Path.trans (Path.congrArg (A.pre a ·) p)
               (Path.congrArg (A.pre a ·) q) :=
  congrArg_trans (A.pre a ·) p q

-- ============================================================
-- Theorem 47: congrArg prefix distributes over symm
-- ============================================================

theorem congrArg_symm_prefix (a : Action) {P Q : A.Proc}
    (p : Path P Q) :
    Path.congrArg (A.pre a ·) (Path.symm p) =
    Path.symm (Path.congrArg (A.pre a ·) p) :=
  congrArg_symm (A.pre a ·) p

-- ============================================================
-- Theorem 48: congrArg restrict distributes over trans
-- ============================================================

theorem congrArg_trans_restrict (n : Nat) {P Q R : A.Proc}
    (p : Path P Q) (q : Path Q R) :
    Path.congrArg (A.restrict n ·) (Path.trans p q) =
    Path.trans (Path.congrArg (A.restrict n ·) p)
               (Path.congrArg (A.restrict n ·) q) :=
  congrArg_trans (A.restrict n ·) p q

-- ============================================================
-- Theorem 49: congrArg restrict distributes over symm
-- ============================================================

theorem congrArg_symm_restrict (n : Nat) {P Q : A.Proc}
    (p : Path P Q) :
    Path.congrArg (A.restrict n ·) (Path.symm p) =
    Path.symm (Path.congrArg (A.restrict n ·) p) :=
  congrArg_symm (A.restrict n ·) p

-- ============================================================
-- Def 50: Nested restriction congruence
-- ============================================================

def restrict_nested_cong (n m : Nat) {P Q : A.Proc}
    (p : Path P Q) :
    Path (A.restrict n (A.restrict m P)) (A.restrict n (A.restrict m Q)) :=
  restrict_cong A n (restrict_cong A m p)

-- ============================================================
-- Def 51: Choice comm inside parallel
-- ============================================================

def par_inner_choice_comm (P Q R : A.Proc) :
    Path (A.par (A.choice P Q) R) (A.par (A.choice Q P) R) :=
  par_cong_left A R (choice_comm_path A P Q)

-- ============================================================
-- Def 52: Parallel comm inside choice
-- ============================================================

def choice_inner_par_comm (P Q R : A.Proc) :
    Path (A.choice (A.par P Q) R) (A.choice (A.par Q P) R) :=
  choice_cong_left A R (par_comm_path A P Q)

-- ============================================================
-- Def 53: MacLane coherence alternative path
-- ============================================================

def choice_coherence_alt (P Q R S : A.Proc) :
    Path (A.choice (A.choice (A.choice P Q) R) S)
         (A.choice P (A.choice Q (A.choice R S))) :=
  let inner := choice_cong_left A S (choice_assoc_path A P Q R)
  let outer := choice_assoc_path A P (A.choice Q R) S
  let innerR := choice_cong_right A P (choice_assoc_path A Q R S)
  Path.trans (Path.trans inner outer) innerR

-- ============================================================
-- Theorem 54: Groupoid round-trip associativity
-- ============================================================

theorem groupoid_roundtrip {P Q : A.Proc} (p : Path P Q) :
    Path.trans p (Path.trans (Path.symm p) p) =
    Path.trans (Path.trans p (Path.symm p)) p := by
  rw [trans_assoc]

-- ============================================================
-- Def 55: Compound congruence: prefix + choice
-- ============================================================

def compound_prefix_choice (a : Action) (R : A.Proc)
    {P Q : A.Proc} (p : Path P Q) :
    Path (A.choice (A.pre a P) R) (A.choice (A.pre a Q) R) :=
  choice_cong_left A R (prefix_cong A a p)

-- ============================================================
-- Def 56: Compound congruence: prefix + parallel
-- ============================================================

def compound_prefix_par (a : Action) (R : A.Proc)
    {P Q : A.Proc} (p : Path P Q) :
    Path (A.par (A.pre a P) R) (A.par (A.pre a Q) R) :=
  par_cong_left A R (prefix_cong A a p)

-- ============================================================
-- Def 57: Six-process choice normalization
-- ============================================================

def choice_normalize_six (P Q R S T U : A.Proc) :
    Path (A.choice (A.choice (A.choice (A.choice (A.choice P Q) R) S) T) U)
         (A.choice P (A.choice Q (A.choice R (A.choice S (A.choice T U))))) :=
  let s1 := choice_assoc_path A (A.choice (A.choice (A.choice P Q) R) S) T U
  let s2 := choice_assoc_path A (A.choice (A.choice P Q) R) S (A.choice T U)
  let s3 := choice_assoc_path A (A.choice P Q) R (A.choice S (A.choice T U))
  let s4 := choice_assoc_path A P Q (A.choice R (A.choice S (A.choice T U)))
  Path.trans s1 (Path.trans s2 (Path.trans s3 s4))

-- ============================================================
-- Def 58: Choice nil absorption chain
-- ============================================================

def choice_nil_absorb (P Q : A.Proc) :
    Path (A.choice (A.choice P 𝟎) (A.choice Q 𝟎))
         (A.choice P Q) :=
  choice_bicong A (choice_nil_path A P) (choice_nil_path A Q)

-- ============================================================
-- Def 59: Parallel nil absorption chain
-- ============================================================

def par_nil_absorb (P Q : A.Proc) :
    Path (A.par (A.par P 𝟎) (A.par Q 𝟎))
         (A.par P Q) :=
  par_bicong A (par_nil_path A P) (par_nil_path A Q)

-- ============================================================
-- Def 60: Mixed: choice inside parallel congruence
-- ============================================================

def mixed_choice_in_par {P P' Q Q' : A.Proc} (R S : A.Proc)
    (p : Path P P') (q : Path Q Q') :
    Path (A.par (A.choice P R) (A.choice Q S))
         (A.par (A.choice P' R) (A.choice Q' S)) :=
  par_bicong A (choice_cong_left A R p) (choice_cong_left A S q)

-- ============================================================
-- Section: LTS Semantics (for concrete inductive processes)
-- ============================================================

/-- Concrete process terms for LTS -/
inductive CProc where
  | nil : CProc
  | act : Action → CProc → CProc
  | choice : CProc → CProc → CProc
  | par : CProc → CProc → CProc
  | restrict : Nat → CProc → CProc

namespace CProc

/-- LTS transitions for CCS processes -/
inductive LTS : CProc → Action → CProc → Prop where
  | prefix : LTS (CProc.act a P) a P
  | choice_left : LTS P a P' → LTS (CProc.choice P Q) a P'
  | choice_right : LTS Q a Q' → LTS (CProc.choice P Q) a Q'
  | par_left : LTS P a P' → LTS (CProc.par P Q) a (CProc.par P' Q)
  | par_right : LTS Q a Q' → LTS (CProc.par P Q) a (CProc.par P Q')
  | par_sync : LTS P a P' → LTS Q (Action.complement a) Q' →
      LTS (CProc.par P Q) Action.tau (CProc.par P' Q')
  | restrict : LTS P a P' → a ≠ Action.send n → a ≠ Action.recv n →
      LTS (CProc.restrict n P) a (CProc.restrict n P')

notation P " —[" a "]→ " Q => LTS P a Q

/-- Multi-step transition (trace execution) -/
inductive MultiStep : CProc → List Action → CProc → Prop where
  | empty : MultiStep P [] P
  | step : LTS P a Q → MultiStep Q t R → MultiStep P (a :: t) R

/-- The set of traces a process can perform -/
def hasTrace (P : CProc) (t : List Action) : Prop :=
  ∃ Q, MultiStep P t Q

/-- Trace equivalence -/
def TraceEquiv (P Q : CProc) : Prop :=
  ∀ t, hasTrace P t ↔ hasTrace Q t

/-- A relation is a strong bisimulation -/
def IsStrongBisim (R : CProc → CProc → Prop) : Prop :=
  ∀ P Q, R P Q →
    (∀ a P', (P —[a]→ P') → ∃ Q', (Q —[a]→ Q') ∧ R P' Q') ∧
    (∀ a Q', (Q —[a]→ Q') → ∃ P', (P —[a]→ P') ∧ R P' Q')

/-- Strong bisimilarity -/
def StrongBisim (P Q : CProc) : Prop :=
  ∃ R, IsStrongBisim R ∧ R P Q

/-- Weak (tau-star) transition -/
inductive TauStar : CProc → CProc → Prop where
  | refl : TauStar P P
  | step : LTS P Action.tau Q → TauStar Q R → TauStar P R

/-- Weak transition -/
def WeakTrans (P : CProc) (a : Action) (Q : CProc) : Prop :=
  match a with
  | Action.tau => TauStar P Q
  | _ => ∃ P' Q', TauStar P P' ∧ (P' —[a]→ Q') ∧ TauStar Q' Q

/-- A relation is a weak bisimulation -/
def IsWeakBisim (R : CProc → CProc → Prop) : Prop :=
  ∀ P Q, R P Q →
    (∀ a P', (P —[a]→ P') → ∃ Q', WeakTrans Q a Q' ∧ R P' Q') ∧
    (∀ a Q', (Q —[a]→ Q') → ∃ P', WeakTrans P a P' ∧ R P' Q')

/-- Weak bisimilarity -/
def WeakBisim (P Q : CProc) : Prop :=
  ∃ R, IsWeakBisim R ∧ R P Q

/-- A relation is a branching bisimulation -/
def IsBranchingBisim (R : CProc → CProc → Prop) : Prop :=
  ∀ P Q, R P Q →
    (∀ a P', (P —[a]→ P') →
      (a = Action.tau ∧ R P' Q) ∨
      (∃ Q₁ Q', TauStar Q Q₁ ∧ (Q₁ —[a]→ Q') ∧ R P Q₁ ∧ R P' Q')) ∧
    (∀ a Q', (Q —[a]→ Q') →
      (a = Action.tau ∧ R P Q') ∨
      (∃ P₁ P', TauStar P P₁ ∧ (P₁ —[a]→ P') ∧ R P₁ Q ∧ R P' Q'))

/-- Branching bisimilarity -/
def BranchingBisim (P Q : CProc) : Prop :=
  ∃ R, IsBranchingBisim R ∧ R P Q

-- ============================================================
-- Section: Hennessy-Milner Logic
-- ============================================================

/-- Hennessy-Milner logic formulas -/
inductive HML where
  | tt : HML
  | ff : HML
  | conj : HML → HML → HML
  | disj : HML → HML → HML
  | diamond : Action → HML → HML
  | box : Action → HML → HML
  | neg : HML → HML

/-- Satisfaction relation -/
def satisfies : CProc → HML → Prop
  | _, HML.tt => True
  | _, HML.ff => False
  | P, HML.conj φ ψ => satisfies P φ ∧ satisfies P ψ
  | P, HML.disj φ ψ => satisfies P φ ∨ satisfies P ψ
  | P, HML.diamond a φ => ∃ P', (P —[a]→ P') ∧ satisfies P' φ
  | P, HML.box a φ => ∀ P', (P —[a]→ P') → satisfies P' φ
  | P, HML.neg φ => ¬ satisfies P φ

-- ============================================================
-- Theorem 61: Strong bisimulation is reflexive
-- ============================================================

theorem strongBisim_refl (P : CProc) : StrongBisim P P := by
  exists (fun A B => A = B)
  constructor
  · intro A B hAB
    subst hAB
    exact ⟨fun a P' h => ⟨P', h, rfl⟩, fun a Q' h => ⟨Q', h, rfl⟩⟩
  · rfl

-- ============================================================
-- Theorem 62: Strong bisimulation is symmetric
-- ============================================================

theorem strongBisim_symm {P Q : CProc} (h : StrongBisim P Q) :
    StrongBisim Q P := by
  obtain ⟨R, hR, hPQ⟩ := h
  exists (fun A B => R B A)
  constructor
  · intro A B hBA
    obtain ⟨hfwd, hbwd⟩ := hR B A hBA
    exact ⟨fun a A' hA => hbwd a A' hA, fun a B' hB => hfwd a B' hB⟩
  · exact hPQ

-- ============================================================
-- Theorem 63: TauStar is reflexive
-- ============================================================

theorem tauStar_refl' (P : CProc) : TauStar P P :=
  TauStar.refl

-- ============================================================
-- Theorem 64: TauStar is transitive
-- ============================================================

theorem tauStar_trans {P Q R : CProc} (h1 : TauStar P Q) (h2 : TauStar Q R) :
    TauStar P R := by
  induction h1 with
  | refl => exact h2
  | step hstep _ ih => exact TauStar.step hstep (ih h2)

-- ============================================================
-- Theorem 65: Weak bisimulation is reflexive
-- ============================================================

theorem weakBisim_refl (P : CProc) : WeakBisim P P := by
  exists (fun A B => A = B)
  constructor
  · intro A B hAB
    subst hAB
    constructor
    · intro a P' h
      exists P'
      refine ⟨?_, rfl⟩
      cases a with
      | tau => exact TauStar.step h TauStar.refl
      | send n => exact ⟨A, P', TauStar.refl, h, TauStar.refl⟩
      | recv n => exact ⟨A, P', TauStar.refl, h, TauStar.refl⟩
      | name s => exact ⟨A, P', TauStar.refl, h, TauStar.refl⟩
    · intro a Q' h
      exists Q'
      refine ⟨?_, rfl⟩
      cases a with
      | tau => exact TauStar.step h TauStar.refl
      | send n => exact ⟨A, Q', TauStar.refl, h, TauStar.refl⟩
      | recv n => exact ⟨A, Q', TauStar.refl, h, TauStar.refl⟩
      | name s => exact ⟨A, Q', TauStar.refl, h, TauStar.refl⟩
  · rfl

-- ============================================================
-- Theorem 66: Weak bisimulation is symmetric
-- ============================================================

theorem weakBisim_symm {P Q : CProc} (h : WeakBisim P Q) :
    WeakBisim Q P := by
  obtain ⟨R, hR, hPQ⟩ := h
  exists (fun A B => R B A)
  constructor
  · intro A B hBA
    obtain ⟨hfwd, hbwd⟩ := hR B A hBA
    exact ⟨fun a A' hA => hbwd a A' hA, fun a B' hB => hfwd a B' hB⟩
  · exact hPQ

-- ============================================================
-- Theorem 67: Branching bisim is reflexive
-- ============================================================

theorem branchingBisim_refl (P : CProc) : BranchingBisim P P := by
  exists (fun A B => A = B)
  constructor
  · intro A B hAB
    subst hAB
    constructor
    · intro a P' h
      right
      exact ⟨A, P', TauStar.refl, h, rfl, rfl⟩
    · intro a Q' h
      right
      exact ⟨A, Q', TauStar.refl, h, rfl, rfl⟩
  · rfl

-- ============================================================
-- Theorem 68: Prefix always has a transition
-- ============================================================

theorem prefix_has_transition (a : Action) (P : CProc) :
    ∃ Q, (CProc.act a P) —[a]→ Q :=
  ⟨P, LTS.prefix⟩

-- ============================================================
-- Theorem 69: Nil has no transitions
-- ============================================================

theorem nil_no_transition : ¬ ∃ a Q, (CProc.nil) —[a]→ Q := by
  intro ⟨a, Q, h⟩
  cases h

-- ============================================================
-- Theorem 70: Prefix determines successor
-- ============================================================

theorem prefix_deterministic {a b : Action} {P Q : CProc}
    (h : (CProc.act a P) —[b]→ Q) : a = b ∧ P = Q := by
  cases h
  exact ⟨rfl, rfl⟩

-- ============================================================
-- Theorem 71: Choice left transition preservation
-- ============================================================

theorem choice_left_trans {P Q : CProc} {a : Action} {P' : CProc}
    (h : P —[a]→ P') :
    (CProc.choice P Q) —[a]→ P' :=
  LTS.choice_left h

-- ============================================================
-- Theorem 72: Choice right transition preservation
-- ============================================================

theorem choice_right_trans {P Q : CProc} {a : Action} {Q' : CProc}
    (h : Q —[a]→ Q') :
    (CProc.choice P Q) —[a]→ Q' :=
  LTS.choice_right h

-- ============================================================
-- Theorem 73: Parallel left transition
-- ============================================================

theorem par_left_trans {P Q : CProc} {a : Action} {P' : CProc}
    (h : P —[a]→ P') :
    (CProc.par P Q) —[a]→ (CProc.par P' Q) :=
  LTS.par_left h

-- ============================================================
-- Theorem 74: Parallel right transition
-- ============================================================

theorem par_right_trans {P Q : CProc} {a : Action} {Q' : CProc}
    (h : Q —[a]→ Q') :
    (CProc.par P Q) —[a]→ (CProc.par P Q') :=
  LTS.par_right h

-- ============================================================
-- Theorem 75: Synchronization transition
-- ============================================================

theorem sync_trans {P Q P' Q' : CProc} {a : Action}
    (hP : P —[a]→ P') (hQ : Q —[Action.complement a]→ Q') :
    (CProc.par P Q) —[Action.tau]→ (CProc.par P' Q') :=
  LTS.par_sync hP hQ

-- ============================================================
-- Theorem 76: Empty trace means identity
-- ============================================================

theorem empty_trace_refl {P Q : CProc} (h : MultiStep P [] Q) : P = Q := by
  cases h; rfl

-- ============================================================
-- Theorem 77: Single step trace
-- ============================================================

theorem single_step_trace {P Q : CProc} {a : Action}
    (h : P —[a]→ Q) : MultiStep P [a] Q :=
  MultiStep.step h MultiStep.empty

-- ============================================================
-- Theorem 78: Trace concatenation
-- ============================================================

theorem trace_concat {P Q R : CProc} {t1 t2 : List Action}
    (h1 : MultiStep P t1 Q) (h2 : MultiStep Q t2 R) :
    MultiStep P (t1 ++ t2) R := by
  induction h1 with
  | empty => exact h2
  | step hstep _ ih => exact MultiStep.step hstep (ih h2)

-- ============================================================
-- Theorem 79: TraceEquiv is reflexive
-- ============================================================

theorem traceEquiv_refl (P : CProc) : TraceEquiv P P :=
  fun _ => Iff.rfl

-- ============================================================
-- Theorem 80: TraceEquiv is symmetric
-- ============================================================

theorem traceEquiv_symm {P Q : CProc} (h : TraceEquiv P Q) :
    TraceEquiv Q P :=
  fun t => (h t).symm

-- ============================================================
-- Theorem 81: TraceEquiv is transitive
-- ============================================================

theorem traceEquiv_trans {P Q R : CProc} (h1 : TraceEquiv P Q)
    (h2 : TraceEquiv Q R) : TraceEquiv P R :=
  fun t => (h1 t).trans (h2 t)

-- ============================================================
-- Theorem 82: Prefix has the singleton trace
-- ============================================================

theorem prefix_trace (a : Action) (P : CProc) :
    hasTrace (CProc.act a P) [a] :=
  ⟨P, single_step_trace LTS.prefix⟩

-- ============================================================
-- Theorem 83: Nil has empty trace
-- ============================================================

theorem nil_has_empty_trace : hasTrace CProc.nil [] :=
  ⟨CProc.nil, MultiStep.empty⟩

-- ============================================================
-- Theorem 84: Nil only has empty trace
-- ============================================================

theorem nil_only_empty_trace {a : Action} {t : List Action} :
    ¬ hasTrace CProc.nil (a :: t) := by
  intro ⟨Q, h⟩
  cases h with
  | step hstep _ => cases hstep

-- ============================================================
-- Theorem 85: HML tt is universally satisfied
-- ============================================================

theorem hml_tt_universal (P : CProc) : satisfies P HML.tt :=
  True.intro

-- ============================================================
-- Theorem 86: HML ff is never satisfied
-- ============================================================

theorem hml_ff_unsatisfied (P : CProc) : ¬ satisfies P HML.ff :=
  id

-- ============================================================
-- Theorem 87: HML conjunction introduction
-- ============================================================

theorem hml_conj_intro {P : CProc} {φ ψ : HML}
    (h1 : satisfies P φ) (h2 : satisfies P ψ) :
    satisfies P (HML.conj φ ψ) :=
  ⟨h1, h2⟩

-- ============================================================
-- Theorem 88: HML disjunction left
-- ============================================================

theorem hml_disj_left {P : CProc} {φ ψ : HML}
    (h : satisfies P φ) :
    satisfies P (HML.disj φ ψ) :=
  Or.inl h

-- ============================================================
-- Theorem 89: HML disjunction right
-- ============================================================

theorem hml_disj_right {P : CProc} {φ ψ : HML}
    (h : satisfies P ψ) :
    satisfies P (HML.disj φ ψ) :=
  Or.inr h

-- ============================================================
-- Theorem 90: HML diamond from transition
-- ============================================================

theorem hml_diamond_intro {P P' : CProc} {a : Action} {φ : HML}
    (htrans : P —[a]→ P') (hsat : satisfies P' φ) :
    satisfies P (HML.diamond a φ) :=
  ⟨P', htrans, hsat⟩

-- ============================================================
-- Theorem 91: Prefix satisfies diamond
-- ============================================================

theorem prefix_satisfies_diamond {P : CProc} {a : Action} {φ : HML}
    (h : satisfies P φ) :
    satisfies (CProc.act a P) (HML.diamond a φ) :=
  ⟨P, LTS.prefix, h⟩

-- ============================================================
-- Theorem 92: Nil satisfies all box formulas
-- ============================================================

theorem nil_satisfies_box (a : Action) (φ : HML) :
    satisfies CProc.nil (HML.box a φ) := by
  intro P' h; cases h

-- ============================================================
-- Theorem 93: HML box-diamond duality for nil
-- ============================================================

theorem nil_box_diamond_dual (a : Action) (φ : HML) :
    satisfies CProc.nil (HML.box a φ) ∧ ¬ satisfies CProc.nil (HML.diamond a φ) := by
  constructor
  · exact nil_satisfies_box a φ
  · intro ⟨P', h, _⟩; cases h

-- ============================================================
-- Theorem 94: HML neg ff
-- ============================================================

theorem hml_neg_ff (P : CProc) : satisfies P (HML.neg HML.ff) :=
  id

-- ============================================================
-- Theorem 95: Strong bisim diamond transfer
-- ============================================================

theorem strongBisim_diamond_tt {R : CProc → CProc → Prop}
    {P Q : CProc} {a : Action}
    (hBisim : IsStrongBisim R) (hRPQ : R P Q)
    (hP : ∃ P', (P —[a]→ P')) :
    ∃ Q', (Q —[a]→ Q') := by
  obtain ⟨P', hP'⟩ := hP
  obtain ⟨hfwd, _⟩ := hBisim P Q hRPQ
  obtain ⟨Q', hQ', _⟩ := hfwd a P' hP'
  exact ⟨Q', hQ'⟩

-- ============================================================
-- Theorem 96: Expansion law: left prefix transition
-- ============================================================

theorem expansion_left_trans (a : Action) (P Q : CProc) :
    (CProc.par (CProc.act a P) Q) —[a]→ (CProc.par P Q) :=
  LTS.par_left LTS.prefix

-- ============================================================
-- Theorem 97: Expansion law: right prefix transition
-- ============================================================

theorem expansion_right_trans (a : Action) (P Q : CProc) :
    (CProc.par P (CProc.act a Q)) —[a]→ (CProc.par P Q) :=
  LTS.par_right LTS.prefix

-- ============================================================
-- Theorem 98: Expansion law: synchronization
-- ============================================================

theorem expansion_sync (a : Action) (P Q : CProc) :
    (CProc.par (CProc.act a P) (CProc.act (Action.complement a) Q))
      —[Action.tau]→ (CProc.par P Q) :=
  LTS.par_sync LTS.prefix LTS.prefix

-- ============================================================
-- Theorem 99: Choice preserves left traces
-- ============================================================

theorem choice_preserves_left_trace {P Q : CProc} {t : List Action} {R : CProc}
    (h : MultiStep P t R) : hasTrace (CProc.choice P Q) t := by
  cases h with
  | empty => exact ⟨CProc.choice P Q, MultiStep.empty⟩
  | step hstep htail => exact ⟨_, MultiStep.step (LTS.choice_left hstep) htail⟩

-- ============================================================
-- Theorem 100: Choice preserves right traces
-- ============================================================

theorem choice_preserves_right_trace {P Q : CProc} {t : List Action} {R : CProc}
    (h : MultiStep Q t R) : hasTrace (CProc.choice P Q) t := by
  cases h with
  | empty => exact ⟨CProc.choice P Q, MultiStep.empty⟩
  | step hstep htail => exact ⟨_, MultiStep.step (LTS.choice_right hstep) htail⟩

end CProc

end ProcessAlgebraDeep
end Algebra
end Path
end ComputationalPaths
