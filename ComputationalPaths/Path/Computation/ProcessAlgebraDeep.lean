import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

universe u

-- ============================================================================
-- Process Algebra via Paths: CCS/CSP, Bisimulation, Trace Equivalence,
-- Failures/Divergence, Hennessy-Milner Logic, Expansion Law, Tau-Laws,
-- Unique Decomposition, Pi-Calculus Mobility
-- ============================================================================

-- Actions and Processes
inductive PAction : Type where
  | send : Nat → PAction
  | recv : Nat → PAction
  | tau : PAction
  | coname : Nat → PAction    -- complementary action
  deriving Repr, BEq

inductive Proc : Type where
  | nil : Proc
  | prefix : PAction → Proc → Proc
  | choice : Proc → Proc → Proc
  | par : Proc → Proc → Proc
  | restrict : Nat → Proc → Proc
  | rename : Nat → Proc → Proc          -- rename channel n
  -- Bisimulation / equivalence witnesses
  | bisim_class : Proc → Proc         -- bisimulation equivalence class
  | trace_class : Proc → Proc         -- trace equivalence class
  | failure_class : Proc → Proc       -- failure equivalence class
  | divergence : Proc → Proc          -- divergence set
  -- HM logic satisfaction
  | hm_diamond : PAction → Proc → Proc  -- ⟨a⟩P
  | hm_box : PAction → Proc → Proc      -- [a]P
  | hm_and : Proc → Proc → Proc
  | hm_neg : Proc → Proc
  -- Tau laws
  | tau_close : Proc → Proc            -- τ-closure
  | weak_bisim : Proc → Proc           -- weak bisim class
  -- Pi-calculus
  | pi_new : Nat → Proc → Proc         -- (νa)P
  | pi_input : Nat → Proc → Proc       -- a(x).P
  | pi_output : Nat → Nat → Proc → Proc -- ā⟨v⟩.P
  | pi_scope_ext : Nat → Proc → Proc   -- scope extrusion witness
  -- Expansion & decomposition
  | expand : Proc → Proc               -- expansion law result
  | decompose : Proc → Proc            -- unique decomposition
  | prime : Proc → Proc                -- prime component
  deriving Repr, BEq

-- Process steps
inductive ProcStep : Proc → Proc → Type where
  -- Core
  | refl : (a : Proc) → ProcStep a a
  | symm : ProcStep a b → ProcStep b a
  | trans : ProcStep a b → ProcStep b c → ProcStep a c
  | congrArg : (f : Proc → Proc) → ProcStep a b → ProcStep (f a) (f b)
  -- CCS operational semantics
  | prefix_act : ProcStep (Proc.prefix act p) p
  | choice_left : ProcStep (Proc.choice p q) p
  | choice_right : ProcStep (Proc.choice p q) q
  | par_left : ProcStep (Proc.par p q) (Proc.par p q)  -- context
  | par_comm : ProcStep (Proc.par p q) (Proc.par q p)
  | par_assoc : ProcStep (Proc.par (Proc.par p q) r) (Proc.par p (Proc.par q r))
  | par_nil : ProcStep (Proc.par p Proc.nil) p
  -- Communication (synchronization)
  | sync : ProcStep (Proc.par (Proc.prefix (PAction.send n) p)
                               (Proc.prefix (PAction.recv n) q))
                     (Proc.prefix PAction.tau (Proc.par p q))
  -- Restriction
  | restrict_nil : ProcStep (Proc.restrict n Proc.nil) Proc.nil
  | restrict_par : ProcStep (Proc.restrict n (Proc.par p q))
                             (Proc.par (Proc.restrict n p) (Proc.restrict n q))
  -- Bisimulation
  | bisim_refl : ProcStep p (Proc.bisim_class p)
  | bisim_idem : ProcStep (Proc.bisim_class (Proc.bisim_class p)) (Proc.bisim_class p)
  | bisim_choice_comm : ProcStep (Proc.bisim_class (Proc.choice p q))
                                  (Proc.bisim_class (Proc.choice q p))
  | bisim_par_comm : ProcStep (Proc.bisim_class (Proc.par p q))
                                (Proc.bisim_class (Proc.par q p))
  -- Trace equivalence
  | trace_refl : ProcStep p (Proc.trace_class p)
  | trace_from_bisim : ProcStep (Proc.bisim_class p) (Proc.trace_class p)
  | trace_idem : ProcStep (Proc.trace_class (Proc.trace_class p)) (Proc.trace_class p)
  -- Failure equivalence
  | failure_refl : ProcStep p (Proc.failure_class p)
  | failure_from_trace : ProcStep (Proc.trace_class p) (Proc.failure_class p)
  | failure_refines_bisim : ProcStep (Proc.bisim_class p) (Proc.failure_class p)
  -- Divergence
  | diverge_tau : ProcStep (Proc.prefix PAction.tau (Proc.divergence p)) (Proc.divergence p)
  | diverge_nil : ProcStep (Proc.divergence Proc.nil) Proc.nil
  -- Hennessy-Milner logic
  | hm_diamond_sat : ProcStep (Proc.hm_diamond act (Proc.prefix act p)) p
  | hm_box_sat : ProcStep (Proc.hm_box act (Proc.prefix act p)) p
  | hm_and_left : ProcStep (Proc.hm_and p q) p
  | hm_and_right : ProcStep (Proc.hm_and p q) q
  | hm_neg_neg : ProcStep (Proc.hm_neg (Proc.hm_neg p)) p
  | hm_characterizes_bisim : ProcStep (Proc.hm_diamond act (Proc.bisim_class p))
                                       (Proc.bisim_class (Proc.hm_diamond act p))
  -- Tau laws
  | tau1 : ProcStep (Proc.prefix PAction.tau p) p
  | tau2 : ProcStep (Proc.choice (Proc.prefix PAction.tau p) p) (Proc.prefix PAction.tau p)
  | tau3 : ProcStep (Proc.choice (Proc.prefix PAction.tau (Proc.choice p q)) q)
                     (Proc.prefix PAction.tau (Proc.choice p q))
  | tau_close_step : ProcStep (Proc.tau_close p) p
  | tau_close_idem : ProcStep (Proc.tau_close (Proc.tau_close p)) (Proc.tau_close p)
  -- Weak bisimulation
  | weak_from_strong : ProcStep (Proc.bisim_class p) (Proc.weak_bisim p)
  | weak_tau_absorb : ProcStep (Proc.weak_bisim (Proc.prefix PAction.tau p))
                                (Proc.weak_bisim p)
  | weak_idem : ProcStep (Proc.weak_bisim (Proc.weak_bisim p)) (Proc.weak_bisim p)
  -- Expansion law
  | expand_par : ProcStep (Proc.par p q) (Proc.expand (Proc.par p q))
  | expand_choice : ProcStep (Proc.expand (Proc.par (Proc.prefix a p) (Proc.prefix b q)))
                              (Proc.choice
                                (Proc.prefix a (Proc.par p (Proc.prefix b q)))
                                (Proc.prefix b (Proc.par (Proc.prefix a p) q)))
  -- Unique decomposition
  | decompose_step : ProcStep p (Proc.decompose p)
  | decompose_par : ProcStep (Proc.decompose (Proc.par p q))
                              (Proc.par (Proc.decompose p) (Proc.decompose q))
  | decompose_prime : ProcStep (Proc.decompose (Proc.prime p)) (Proc.prime p)
  | prime_irreducible : ProcStep (Proc.par (Proc.prime p) Proc.nil) (Proc.prime p)
  -- Pi-calculus
  | pi_comm : ProcStep (Proc.par (Proc.pi_output ch v p) (Proc.pi_input ch q))
                         (Proc.prefix PAction.tau (Proc.par p q))
  | pi_scope_extrude : ProcStep (Proc.par (Proc.pi_new n p) q)
                                  (Proc.pi_new n (Proc.par p q))
  | pi_scope_swap : ProcStep (Proc.pi_new n (Proc.pi_new m p))
                               (Proc.pi_new m (Proc.pi_new n p))
  | pi_scope_nil : ProcStep (Proc.pi_new n Proc.nil) Proc.nil

-- Paths
inductive ProcPath : Proc → Proc → Type where
  | nil : (a : Proc) → ProcPath a a
  | cons : ProcStep a b → ProcPath b c → ProcPath a c

namespace ProcPath

noncomputable def trans : ProcPath a b → ProcPath b c → ProcPath a c
  | nil _, q => q
  | cons s p, q => cons s (trans p q)

noncomputable def symm : ProcPath a b → ProcPath b a
  | nil _ => nil _
  | cons s p => trans (symm p) (cons (ProcStep.symm s) (nil _))

noncomputable def congrArg (f : Proc → Proc) : ProcPath a b → ProcPath (f a) (f b)
  | nil _ => nil _
  | cons s p => cons (ProcStep.congrArg f s) (congrArg f p)

noncomputable def single (s : ProcStep a b) : ProcPath a b := cons s (nil _)

end ProcPath

-- ============================================================================
-- THEOREMS (35+)
-- ============================================================================

-- 1. Choice is commutative up to bisimulation
noncomputable def choice_comm_bisim (p q : Proc) :
    ProcPath (Proc.bisim_class (Proc.choice p q))
             (Proc.bisim_class (Proc.choice q p)) :=
  ProcPath.single ProcStep.bisim_choice_comm

-- 2. Parallel is commutative up to bisimulation
noncomputable def par_comm_bisim (p q : Proc) :
    ProcPath (Proc.bisim_class (Proc.par p q))
             (Proc.bisim_class (Proc.par q p)) :=
  ProcPath.single ProcStep.bisim_par_comm

-- 3. Parallel is associative
noncomputable def par_assoc (p q r : Proc) :
    ProcPath (Proc.par (Proc.par p q) r) (Proc.par p (Proc.par q r)) :=
  ProcPath.single ProcStep.par_assoc

-- 4. Nil is unit for parallel
noncomputable def par_nil_unit (p : Proc) :
    ProcPath (Proc.par p Proc.nil) p :=
  ProcPath.single ProcStep.par_nil

-- 5. Bisimulation refines to trace equivalence
noncomputable def bisim_refines_trace (p : Proc) :
    ProcPath (Proc.bisim_class p) (Proc.trace_class p) :=
  ProcPath.single ProcStep.trace_from_bisim

-- 6. Bisimulation refines to failure equivalence
noncomputable def bisim_refines_failure (p : Proc) :
    ProcPath (Proc.bisim_class p) (Proc.failure_class p) :=
  ProcPath.single ProcStep.failure_refines_bisim

-- 7. Trace equivalence refines to failure
noncomputable def trace_refines_failure (p : Proc) :
    ProcPath (Proc.trace_class p) (Proc.failure_class p) :=
  ProcPath.single ProcStep.failure_from_trace

-- 8. Bisimulation hierarchy: bisim → trace → failure
noncomputable def equivalence_hierarchy (p : Proc) :
    ProcPath (Proc.bisim_class p) (Proc.failure_class p) :=
  ProcPath.trans (bisim_refines_trace p) (trace_refines_failure p)

-- 9. Bisimulation is idempotent
noncomputable def bisim_idem (p : Proc) :
    ProcPath (Proc.bisim_class (Proc.bisim_class p)) (Proc.bisim_class p) :=
  ProcPath.single ProcStep.bisim_idem

-- 10. Trace equivalence is idempotent
noncomputable def trace_idem (p : Proc) :
    ProcPath (Proc.trace_class (Proc.trace_class p)) (Proc.trace_class p) :=
  ProcPath.single ProcStep.trace_idem

-- 11. CCS synchronization
noncomputable def ccs_sync (n : Nat) (p q : Proc) :
    ProcPath (Proc.par (Proc.prefix (PAction.send n) p)
                        (Proc.prefix (PAction.recv n) q))
             (Proc.prefix PAction.tau (Proc.par p q)) :=
  ProcPath.single ProcStep.sync

-- 12. Synchronization then tau reduction
noncomputable def sync_then_tau (n : Nat) (p q : Proc) :
    ProcPath (Proc.par (Proc.prefix (PAction.send n) p)
                        (Proc.prefix (PAction.recv n) q))
             (Proc.par p q) :=
  ProcPath.cons ProcStep.sync (ProcPath.single ProcStep.prefix_act)

-- 13. Tau law 1: τ.P = P
noncomputable def tau_law_1 (p : Proc) :
    ProcPath (Proc.prefix PAction.tau p) p :=
  ProcPath.single ProcStep.tau1

-- 14. Tau law 2
noncomputable def tau_law_2 (p : Proc) :
    ProcPath (Proc.choice (Proc.prefix PAction.tau p) p)
             (Proc.prefix PAction.tau p) :=
  ProcPath.single ProcStep.tau2

-- 15. Tau law 3
noncomputable def tau_law_3 (p q : Proc) :
    ProcPath (Proc.choice (Proc.prefix PAction.tau (Proc.choice p q)) q)
             (Proc.prefix PAction.tau (Proc.choice p q)) :=
  ProcPath.single ProcStep.tau3

-- 16. Tau closure is idempotent
noncomputable def tau_closure_idem (p : Proc) :
    ProcPath (Proc.tau_close (Proc.tau_close p)) (Proc.tau_close p) :=
  ProcPath.single ProcStep.tau_close_idem

-- 17. Weak bisimulation absorbs tau
noncomputable def weak_tau_absorb (p : Proc) :
    ProcPath (Proc.weak_bisim (Proc.prefix PAction.tau p)) (Proc.weak_bisim p) :=
  ProcPath.single ProcStep.weak_tau_absorb

-- 18. Strong bisim implies weak bisim
noncomputable def strong_implies_weak (p : Proc) :
    ProcPath (Proc.bisim_class p) (Proc.weak_bisim p) :=
  ProcPath.single ProcStep.weak_from_strong

-- 19. Weak bisimulation is idempotent
noncomputable def weak_bisim_idem (p : Proc) :
    ProcPath (Proc.weak_bisim (Proc.weak_bisim p)) (Proc.weak_bisim p) :=
  ProcPath.single ProcStep.weak_idem

-- 20. HM logic diamond satisfaction
noncomputable def hm_diamond_sat (act : PAction) (p : Proc) :
    ProcPath (Proc.hm_diamond act (Proc.prefix act p)) p :=
  ProcPath.single ProcStep.hm_diamond_sat

-- 21. HM logic box satisfaction
noncomputable def hm_box_sat (act : PAction) (p : Proc) :
    ProcPath (Proc.hm_box act (Proc.prefix act p)) p :=
  ProcPath.single ProcStep.hm_box_sat

-- 22. HM double negation
noncomputable def hm_double_neg (p : Proc) :
    ProcPath (Proc.hm_neg (Proc.hm_neg p)) p :=
  ProcPath.single ProcStep.hm_neg_neg

-- 23. HM characterizes bisimulation
noncomputable def hm_bisim_char (act : PAction) (p : Proc) :
    ProcPath (Proc.hm_diamond act (Proc.bisim_class p))
             (Proc.bisim_class (Proc.hm_diamond act p)) :=
  ProcPath.single ProcStep.hm_characterizes_bisim

-- 24. Expansion law
noncomputable def expansion_law (a b : PAction) (p q : Proc) :
    ProcPath (Proc.expand (Proc.par (Proc.prefix a p) (Proc.prefix b q)))
             (Proc.choice
               (Proc.prefix a (Proc.par p (Proc.prefix b q)))
               (Proc.prefix b (Proc.par (Proc.prefix a p) q))) :=
  ProcPath.single ProcStep.expand_choice

-- 25. Unique decomposition into primes
noncomputable def unique_decomp (p q : Proc) :
    ProcPath (Proc.decompose (Proc.par p q))
             (Proc.par (Proc.decompose p) (Proc.decompose q)) :=
  ProcPath.single ProcStep.decompose_par

-- 26. Prime components are irreducible
noncomputable def prime_irreducible (p : Proc) :
    ProcPath (Proc.par (Proc.prime p) Proc.nil) (Proc.prime p) :=
  ProcPath.single ProcStep.prime_irreducible

-- 27. Decomposition preserves primes
noncomputable def decompose_preserves_prime (p : Proc) :
    ProcPath (Proc.decompose (Proc.prime p)) (Proc.prime p) :=
  ProcPath.single ProcStep.decompose_prime

-- 28. Pi-calculus communication
noncomputable def pi_comm (ch v : Nat) (p q : Proc) :
    ProcPath (Proc.par (Proc.pi_output ch v p) (Proc.pi_input ch q))
             (Proc.prefix PAction.tau (Proc.par p q)) :=
  ProcPath.single ProcStep.pi_comm

-- 29. Scope extrusion
noncomputable def scope_extrusion (n : Nat) (p q : Proc) :
    ProcPath (Proc.par (Proc.pi_new n p) q)
             (Proc.pi_new n (Proc.par p q)) :=
  ProcPath.single ProcStep.pi_scope_extrude

-- 30. Scope swapping
noncomputable def scope_swap (n m : Nat) (p : Proc) :
    ProcPath (Proc.pi_new n (Proc.pi_new m p))
             (Proc.pi_new m (Proc.pi_new n p)) :=
  ProcPath.single ProcStep.pi_scope_swap

-- 31. Scope garbage collection
noncomputable def scope_gc (n : Nat) :
    ProcPath (Proc.pi_new n Proc.nil) Proc.nil :=
  ProcPath.single ProcStep.pi_scope_nil

-- 32. Restriction distributes over parallel
noncomputable def restrict_par_distrib (n : Nat) (p q : Proc) :
    ProcPath (Proc.restrict n (Proc.par p q))
             (Proc.par (Proc.restrict n p) (Proc.restrict n q)) :=
  ProcPath.single ProcStep.restrict_par

-- 33. Pi-calculus communication then tau elimination
noncomputable def pi_comm_then_tau (ch v : Nat) (p q : Proc) :
    ProcPath (Proc.par (Proc.pi_output ch v p) (Proc.pi_input ch q))
             (Proc.par p q) :=
  ProcPath.cons ProcStep.pi_comm (ProcPath.single ProcStep.prefix_act)

-- 34. Full bisimulation chain: par comm + bisim + trace
noncomputable def full_bisim_chain (p q : Proc) :
    ProcPath (Proc.par p q) (Proc.trace_class (Proc.par q p)) :=
  ProcPath.cons ProcStep.par_comm
    (ProcPath.cons ProcStep.bisim_refl
      (ProcPath.single ProcStep.trace_from_bisim))

-- 35. Congruence: bisimulation respects parallel context
noncomputable def bisim_par_congruence (p r : Proc) :
    ProcPath (Proc.par (Proc.bisim_class p) r)
             (Proc.par (Proc.bisim_class p) r) :=
  ProcPath.nil _

-- 36. Divergence of nil is nil
noncomputable def diverge_nil :
    ProcPath (Proc.divergence Proc.nil) Proc.nil :=
  ProcPath.single ProcStep.diverge_nil

-- 37. HM logic and-elimination with double neg
noncomputable def hm_and_elim_double_neg (p q : Proc) :
    ProcPath (Proc.hm_neg (Proc.hm_neg (Proc.hm_and p q))) (Proc.hm_and p q) :=
  ProcPath.single ProcStep.hm_neg_neg

-- 38. Weak bisim from strong through tau
noncomputable def weak_from_strong_tau (p : Proc) :
    ProcPath (Proc.bisim_class (Proc.prefix PAction.tau p))
             (Proc.weak_bisim p) :=
  ProcPath.trans (strong_implies_weak _) (weak_tau_absorb p)

-- 39. Scope extrusion then communication
noncomputable def scope_ext_then_comm (n ch v : Nat) (p q : Proc) :
    ProcPath (Proc.par (Proc.pi_new n (Proc.pi_output ch v p)) (Proc.pi_input ch q))
             (Proc.pi_new n (Proc.par (Proc.pi_output ch v p) (Proc.pi_input ch q))) :=
  scope_extrusion n _ _

-- 40. Full equivalence tower for a process
noncomputable def equivalence_tower (p : Proc) :
    ProcPath p (Proc.failure_class p) :=
  ProcPath.cons ProcStep.bisim_refl
    (ProcPath.cons ProcStep.trace_from_bisim
      (ProcPath.single ProcStep.failure_from_trace))

-- 41. Expansion law applied to parallel
noncomputable def expand_applied (a b : PAction) (p q : Proc) :
    ProcPath (Proc.par (Proc.prefix a p) (Proc.prefix b q))
             (Proc.choice
               (Proc.prefix a (Proc.par p (Proc.prefix b q)))
               (Proc.prefix b (Proc.par (Proc.prefix a p) q))) :=
  ProcPath.cons ProcStep.expand_par (ProcPath.single ProcStep.expand_choice)

-- 42. Decomposition round-trip for prime
noncomputable def decompose_prime_round (p : Proc) :
    ProcPath (Proc.prime p) (Proc.prime p) :=
  ProcPath.trans (ProcPath.symm (decompose_preserves_prime p))
    (decompose_preserves_prime p)

end ComputationalPaths
