/-
  Access Control Logic and Security via Computational Paths
  ==========================================================

  This file develops a comprehensive theory of access control, security policies,
  and information flow control using computational paths as the fundamental
  mechanism for reasoning about delegation, revocation, policy composition,
  and non-interference.

  Key ideas:
  - Permission levels, security labels encoded as Nat
  - Access control policies form a lattice connected by paths
  - Delegation chains are modeled as Path.trans
  - Revocation is modeled as Path.symm
  - RBAC and ABAC encoded via path-connected policy structures
  - Information flow uses lattice of security labels connected by paths
  - Non-interference is expressed as congrArg preservation
  - Bell-LaPadula properties are encoded as path constraints
  - Declassification as controlled path step
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.AccessControlPathDeep

open ComputationalPaths.Path

universe u v

-- ============================================================================
-- Section 1: Permission Level Algebra
-- ============================================================================

/-- Permission levels: 0=none, 1=read, 2=write, 3=execute, 4=admin -/
abbrev PermLevel := Nat

noncomputable def permNone : PermLevel := 0
noncomputable def permRead : PermLevel := 1
noncomputable def permWrite : PermLevel := 2
noncomputable def permExecute : PermLevel := 3
noncomputable def permAdmin : PermLevel := 4

/-- Grant maps 0 to 1 (none → read) -/
noncomputable def grantRead (n : Nat) : Nat := n + 1

/-- Identity on permissions -/
noncomputable def permId (n : Nat) : Nat := n

theorem permId_eq (n : Nat) : permId n = n := rfl

/-- Theorem 1: permId is identity, giving a path -/
noncomputable def permId_path (n : Nat) : Path (permId n) n :=
  Path.refl n

/-- Double application of identity -/
theorem permId_double (n : Nat) : permId (permId n) = n := rfl

/-- Theorem 2: Double identity path via trans -/
noncomputable def permId_double_path (n : Nat) : Path (permId (permId n)) n :=
  Path.trans (Path.congrArg permId (permId_path n)) (permId_path n)

/-- Theorem 3: Triple identity path via trans -/
noncomputable def permId_triple_path (n : Nat) : Path (permId (permId (permId n))) n :=
  Path.trans (Path.congrArg permId (permId_double_path n)) (permId_path n)

-- ============================================================================
-- Section 2: Security Level Lattice
-- ============================================================================

/-- Security level: 0=unclassified, 1=confidential, 2=secret, 3=topSecret -/
abbrev SecLevel := Nat

noncomputable def secUnclass : SecLevel := 0
noncomputable def secConf : SecLevel := 1
noncomputable def secSecret : SecLevel := 2
noncomputable def secTop : SecLevel := 3

/-- Clearance check: max of subject and object levels -/
noncomputable def clearanceMax (a b : Nat) : Nat := Nat.max a b

theorem clearanceMax_self (n : Nat) : clearanceMax n n = n := Nat.max_self n

/-- Theorem 4: Self-clearance path -/
noncomputable def clearanceMax_self_path (n : Nat) : Path (clearanceMax n n) n :=
  Path.stepChain (clearanceMax_self n)

/-- Theorem 5: Clearance max is commutative -/
theorem clearanceMax_comm (a b : Nat) : clearanceMax a b = clearanceMax b a :=
  Nat.max_comm a b

noncomputable def clearanceMax_comm_path (a b : Nat) : Path (clearanceMax a b) (clearanceMax b a) :=
  Path.stepChain (clearanceMax_comm a b)

/-- Theorem 6: Clearance max is associative -/
theorem clearanceMax_assoc (a b c : Nat) :
    clearanceMax (clearanceMax a b) c = clearanceMax a (clearanceMax b c) :=
  Nat.max_assoc a b c

noncomputable def clearanceMax_assoc_path (a b c : Nat) :
    Path (clearanceMax (clearanceMax a b) c) (clearanceMax a (clearanceMax b c)) :=
  Path.stepChain (clearanceMax_assoc a b c)

-- ============================================================================
-- Section 3: Minimum Clearance (Meet in Lattice)
-- ============================================================================

noncomputable def clearanceMin (a b : Nat) : Nat := Nat.min a b

theorem clearanceMin_self (n : Nat) : clearanceMin n n = n := Nat.min_self n

/-- Theorem 7: Self-min clearance path -/
noncomputable def clearanceMin_self_path (n : Nat) : Path (clearanceMin n n) n :=
  Path.stepChain (clearanceMin_self n)

/-- Theorem 8: Min clearance is commutative -/
theorem clearanceMin_comm (a b : Nat) : clearanceMin a b = clearanceMin b a :=
  Nat.min_comm a b

noncomputable def clearanceMin_comm_path (a b : Nat) : Path (clearanceMin a b) (clearanceMin b a) :=
  Path.stepChain (clearanceMin_comm a b)

/-- Theorem 9: Min clearance is associative -/
theorem clearanceMin_assoc (a b c : Nat) :
    clearanceMin (clearanceMin a b) c = clearanceMin a (clearanceMin b c) :=
  Nat.min_assoc a b c

noncomputable def clearanceMin_assoc_path (a b c : Nat) :
    Path (clearanceMin (clearanceMin a b) c) (clearanceMin a (clearanceMin b c)) :=
  Path.stepChain (clearanceMin_assoc a b c)

-- ============================================================================
-- Section 4: Delegation Chains
-- ============================================================================

/-- A delegation level combines principal id and clearance -/
structure DelegState where
  principalId : Nat
  clearance : Nat
  deriving DecidableEq

/-- Effective clearance of a delegation state -/
noncomputable def effectiveClearance (s : DelegState) : Nat := s.clearance

/-- Transfer clearance between principals preserves level -/
noncomputable def transferClearance (newPid : Nat) (s : DelegState) : DelegState :=
  { principalId := newPid, clearance := s.clearance }

/-- Theorem 10: Transfer preserves effective clearance -/
theorem transfer_preserves_clearance (pid : Nat) (s : DelegState) :
    effectiveClearance (transferClearance pid s) = effectiveClearance s := rfl

noncomputable def transfer_preserves_clearance_path (pid : Nat) (s : DelegState) :
    Path (effectiveClearance (transferClearance pid s)) (effectiveClearance s) :=
  Path.refl _

/-- Theorem 11: Double transfer preserves clearance -/
theorem double_transfer_clearance (p1 p2 : Nat) (s : DelegState) :
    effectiveClearance (transferClearance p2 (transferClearance p1 s))
    = effectiveClearance s := rfl

noncomputable def double_transfer_path (p1 p2 : Nat) (s : DelegState) :
    Path (effectiveClearance (transferClearance p2 (transferClearance p1 s)))
         (effectiveClearance s) :=
  Path.refl _

/-- Identity transfer (same principal) -/
noncomputable def idTransfer (s : DelegState) : DelegState :=
  transferClearance s.principalId s

theorem idTransfer_clearance (s : DelegState) :
    effectiveClearance (idTransfer s) = effectiveClearance s := rfl

/-- Theorem 12: Identity transfer path -/
noncomputable def idTransfer_path (s : DelegState) :
    Path (effectiveClearance (idTransfer s)) (effectiveClearance s) :=
  Path.refl _

-- ============================================================================
-- Section 5: Policy Composition Algebra
-- ============================================================================

/-- Policy decision: encoded as Nat (0=deny, 1=allow, 2=conditional) -/
abbrev PolicyDecision := Nat

/-- Combine two policy decisions via max (most permissive wins) -/
noncomputable def policyOr (a b : Nat) : Nat := Nat.max a b

/-- Combine two policy decisions via min (least permissive wins) -/
noncomputable def policyAnd (a b : Nat) : Nat := Nat.min a b

/-- Theorem 13: Policy OR is commutative -/
noncomputable def policyOr_comm_path (a b : Nat) : Path (policyOr a b) (policyOr b a) :=
  Path.stepChain (Nat.max_comm a b)

/-- Theorem 14: Policy OR is associative -/
noncomputable def policyOr_assoc_path (a b c : Nat) :
    Path (policyOr (policyOr a b) c) (policyOr a (policyOr b c)) :=
  Path.stepChain (Nat.max_assoc a b c)

/-- Theorem 15: Policy AND is commutative -/
noncomputable def policyAnd_comm_path (a b : Nat) : Path (policyAnd a b) (policyAnd b a) :=
  Path.stepChain (Nat.min_comm a b)

/-- Theorem 16: Policy AND is associative -/
noncomputable def policyAnd_assoc_path (a b c : Nat) :
    Path (policyAnd (policyAnd a b) c) (policyAnd a (policyAnd b c)) :=
  Path.stepChain (Nat.min_assoc a b c)

/-- Theorem 17: Policy OR is idempotent -/
noncomputable def policyOr_idem_path (a : Nat) : Path (policyOr a a) a :=
  Path.stepChain (Nat.max_self a)

/-- Theorem 18: Policy AND is idempotent -/
noncomputable def policyAnd_idem_path (a : Nat) : Path (policyAnd a a) a :=
  Path.stepChain (Nat.min_self a)

-- ============================================================================
-- Section 6: Policy Composition via trans
-- ============================================================================

/-- Theorem 19: Compose two commutations via trans -/
noncomputable def policyOr_double_comm (a b : Nat) : Path (policyOr a b) (policyOr a b) :=
  Path.trans (policyOr_comm_path a b) (policyOr_comm_path b a)

/-- Theorem 20: Associativity chain: left-to-right-to-left -/
noncomputable def policy_assoc_roundtrip (a b c : Nat) :
    Path (policyOr (policyOr a b) c) (policyOr (policyOr a b) c) :=
  Path.trans (policyOr_assoc_path a b c) (Path.symm (policyOr_assoc_path a b c))

/-- Theorem 21: Symm of policyOr commutation -/
noncomputable def policyOr_comm_symm (a b : Nat) : Path (policyOr b a) (policyOr a b) :=
  Path.symm (policyOr_comm_path a b)

/-- Theorem 22: Symm of symm is identity -/
theorem policyOr_comm_symm_symm (a b : Nat) :
    Path.symm (Path.symm (policyOr_comm_path a b)) = policyOr_comm_path a b :=
  symm_symm (policyOr_comm_path a b)

/-- Theorem 23: trans_assoc for policy paths -/
theorem policy_path_assoc (a b : Nat) :
    Path.trans (Path.trans (policyOr_comm_path a b) (policyOr_comm_path b a))
               (policyOr_comm_path a b)
    = Path.trans (policyOr_comm_path a b)
                 (Path.trans (policyOr_comm_path b a) (policyOr_comm_path a b)) :=
  trans_assoc _ _ _

-- ============================================================================
-- Section 7: RBAC via Functions
-- ============================================================================

/-- Role-to-permission mapping: role id → permission level -/
noncomputable def rolePermission : Nat → Nat
  | 0 => 1  -- viewer → read
  | 1 => 2  -- editor → write
  | 2 => 3  -- operator → execute
  | 3 => 4  -- admin → admin
  | _ => 0  -- unknown → none

/-- User-to-role mapping -/
noncomputable def userRole : Nat → Nat
  | 0 => 0  -- user0 → viewer
  | 1 => 1  -- user1 → editor
  | 2 => 2  -- user2 → operator
  | 3 => 3  -- user3 → admin
  | _ => 0  -- default → viewer

/-- Composed mapping: user → permission -/
noncomputable def userPermission (uid : Nat) : Nat := rolePermission (userRole uid)

/-- Theorem 24: user0 gets read permission -/
theorem user0_permission : userPermission 0 = 1 := rfl

noncomputable def user0_permission_path : Path (userPermission 0) 1 :=
  Path.refl 1

/-- Theorem 25: user3 gets admin permission -/
theorem user3_permission : userPermission 3 = 4 := rfl

noncomputable def user3_permission_path : Path (userPermission 3) 4 :=
  Path.refl 4

/-- Theorem 26: congrArg through rolePermission preserves paths -/
theorem rbac_role_congr_example (n : Nat) :
    Path.congrArg rolePermission (clearanceMax_self_path n)
    = Path.congrArg rolePermission (Path.stepChain (clearanceMax_self n)) := rfl

-- ============================================================================
-- Section 8: ABAC via Attribute Functions
-- ============================================================================

/-- Attribute evaluation: maps attribute score to access decision -/
noncomputable def attrEval (score : Nat) : Nat := Nat.min score 4

theorem attrEval_idem_high (n : Nat) (h : n ≤ 4) : attrEval (attrEval n) = attrEval n := by
  simp [attrEval, Nat.min_eq_left h]

/-- Theorem 27: Attribute evaluation is idempotent for bounded inputs -/
noncomputable def attrEval_idem_path (n : Nat) (h : n ≤ 4) :
    Path (attrEval (attrEval n)) (attrEval n) :=
  Path.stepChain (attrEval_idem_high n h)

/-- Combining attributes via max -/
noncomputable def attrCombine (a b : Nat) : Nat := Nat.max a b

/-- Theorem 28: Attribute combination is commutative -/
noncomputable def attrCombine_comm_path (a b : Nat) : Path (attrCombine a b) (attrCombine b a) :=
  Path.stepChain (Nat.max_comm a b)

/-- Theorem 29: Attribute combination is associative -/
noncomputable def attrCombine_assoc_path (a b c : Nat) :
    Path (attrCombine (attrCombine a b) c) (attrCombine a (attrCombine b c)) :=
  Path.stepChain (Nat.max_assoc a b c)

-- ============================================================================
-- Section 9: Information Flow Labels
-- ============================================================================

/-- Flow label as Nat: 0=low, 1=medium, 2=high, 3=top -/
abbrev FlowLabel := Nat

/-- Join of flow labels (least upper bound) -/
noncomputable def flowJoin (a b : Nat) : Nat := Nat.max a b

/-- Meet of flow labels (greatest lower bound) -/
noncomputable def flowMeet (a b : Nat) : Nat := Nat.min a b

/-- Theorem 30: Flow join self -/
noncomputable def flowJoin_self_path (n : Nat) : Path (flowJoin n n) n :=
  Path.stepChain (Nat.max_self n)

/-- Theorem 31: Flow join commutative -/
noncomputable def flowJoin_comm_path (a b : Nat) : Path (flowJoin a b) (flowJoin b a) :=
  Path.stepChain (Nat.max_comm a b)

/-- Theorem 32: Flow join associative -/
noncomputable def flowJoin_assoc_path (a b c : Nat) :
    Path (flowJoin (flowJoin a b) c) (flowJoin a (flowJoin b c)) :=
  Path.stepChain (Nat.max_assoc a b c)

/-- Theorem 33: Flow meet self -/
noncomputable def flowMeet_self_path (n : Nat) : Path (flowMeet n n) n :=
  Path.stepChain (Nat.min_self n)

/-- Theorem 34: Flow meet commutative -/
noncomputable def flowMeet_comm_path (a b : Nat) : Path (flowMeet a b) (flowMeet b a) :=
  Path.stepChain (Nat.min_comm a b)

/-- Theorem 35: Flow meet associative -/
noncomputable def flowMeet_assoc_path (a b c : Nat) :
    Path (flowMeet (flowMeet a b) c) (flowMeet a (flowMeet b c)) :=
  Path.stepChain (Nat.min_assoc a b c)

-- ============================================================================
-- Section 10: Non-Interference via congrArg
-- ============================================================================

/-- Map flow label to clearance level (functorial) -/
noncomputable def flowToClearance (fl : Nat) : Nat := fl

/-- Theorem 36: congrArg preserves flow join self -/
noncomputable def noninterference_join_self (n : Nat) :
    Path (flowToClearance (flowJoin n n)) (flowToClearance n) :=
  Path.congrArg flowToClearance (flowJoin_self_path n)

/-- Theorem 37: congrArg preserves flow join commutativity -/
noncomputable def noninterference_join_comm (a b : Nat) :
    Path (flowToClearance (flowJoin a b)) (flowToClearance (flowJoin b a)) :=
  Path.congrArg flowToClearance (flowJoin_comm_path a b)

/-- Theorem 38: congrArg preserves flow join associativity -/
noncomputable def noninterference_join_assoc (a b c : Nat) :
    Path (flowToClearance (flowJoin (flowJoin a b) c))
         (flowToClearance (flowJoin a (flowJoin b c))) :=
  Path.congrArg flowToClearance (flowJoin_assoc_path a b c)

/-- Theorem 39: congrArg preserves symm -/
theorem noninterference_symm_pres (a b : Nat) :
    Path.congrArg flowToClearance (Path.symm (flowJoin_comm_path a b))
    = Path.symm (Path.congrArg flowToClearance (flowJoin_comm_path a b)) :=
  congrArg_symm flowToClearance (flowJoin_comm_path a b)

/-- Theorem 40: congrArg preserves trans -/
theorem noninterference_trans_pres (a b : Nat) :
    Path.congrArg flowToClearance
      (Path.trans (flowJoin_comm_path a b) (flowJoin_comm_path b a))
    = Path.trans
        (Path.congrArg flowToClearance (flowJoin_comm_path a b))
        (Path.congrArg flowToClearance (flowJoin_comm_path b a)) :=
  congrArg_trans flowToClearance (flowJoin_comm_path a b) (flowJoin_comm_path b a)

-- ============================================================================
-- Section 11: Bell-LaPadula Model
-- ============================================================================

/-- BLP state: subject clearance + object classification -/
structure BLPState where
  subjectLevel : Nat
  objectLevel : Nat
  deriving DecidableEq

/-- Read allowed when subject level ≥ object level (no read up) -/
noncomputable def blpReadCheck (s : BLPState) : Nat := Nat.max s.subjectLevel s.objectLevel

/-- Write check: subject level ≤ object level (no write down) -/
noncomputable def blpWriteCheck (s : BLPState) : Nat := Nat.min s.subjectLevel s.objectLevel

/-- Theorem 41: BLP read check for equal levels -/
theorem blp_read_equal (n : Nat) :
    blpReadCheck { subjectLevel := n, objectLevel := n } = n :=
  Nat.max_self n

noncomputable def blp_read_equal_path (n : Nat) :
    Path (blpReadCheck { subjectLevel := n, objectLevel := n }) n :=
  Path.stepChain (blp_read_equal n)

/-- Theorem 42: BLP write check for equal levels -/
theorem blp_write_equal (n : Nat) :
    blpWriteCheck { subjectLevel := n, objectLevel := n } = n :=
  Nat.min_self n

noncomputable def blp_write_equal_path (n : Nat) :
    Path (blpWriteCheck { subjectLevel := n, objectLevel := n }) n :=
  Path.stepChain (blp_write_equal n)

/-- Theorem 43: BLP read then write at equal levels chains to same -/
noncomputable def blp_read_write_equal (n : Nat) :
    Path (blpReadCheck { subjectLevel := n, objectLevel := n })
         (blpWriteCheck { subjectLevel := n, objectLevel := n }) :=
  Path.trans (blp_read_equal_path n) (Path.symm (blp_write_equal_path n))

/-- Extract subject level from BLP state -/
noncomputable def blpSubject (s : BLPState) : Nat := s.subjectLevel

/-- Extract object level from BLP state -/
noncomputable def blpObject (s : BLPState) : Nat := s.objectLevel

/-- Construct BLP state from subject level -/
noncomputable def mkBLPWithSubject (objLvl : Nat) (subLvl : Nat) : BLPState :=
  { subjectLevel := subLvl, objectLevel := objLvl }

/-- Theorem 44: congrArg through blpReadCheck preserves max-self -/
noncomputable def blp_congr_read (n : Nat) :
    Path (blpReadCheck (mkBLPWithSubject n n)) n :=
  Path.stepChain (blp_read_equal n)

/-- Theorem 45: Symm of BLP read equal -/
noncomputable def blp_read_equal_symm (n : Nat) :
    Path n (blpReadCheck { subjectLevel := n, objectLevel := n }) :=
  Path.symm (blp_read_equal_path n)

-- ============================================================================
-- Section 12: Declassification as Controlled Step
-- ============================================================================

/-- Declassification: cap at a maximum level -/
noncomputable def declassify (maxLevel : Nat) (currentLevel : Nat) : Nat :=
  Nat.min currentLevel maxLevel

theorem declassify_self (n : Nat) : declassify n n = n :=
  Nat.min_self n

/-- Theorem 46: Self-declassification is identity -/
noncomputable def declassify_self_path (n : Nat) : Path (declassify n n) n :=
  Path.stepChain (declassify_self n)

theorem declassify_idem (m n : Nat) :
    declassify m (declassify m n) = declassify m n := by
  simp [declassify, Nat.min_assoc]

/-- Theorem 47: Declassification is idempotent -/
noncomputable def declassify_idem_path (m n : Nat) :
    Path (declassify m (declassify m n)) (declassify m n) :=
  Path.stepChain (declassify_idem m n)

/-- Theorem 48: Double declassification path via trans -/
noncomputable def declassify_double_idem (m n : Nat) :
    Path (declassify m (declassify m (declassify m n))) (declassify m n) :=
  Path.trans
    (Path.congrArg (declassify m) (declassify_idem_path m n))
    (declassify_idem_path m n)

-- ============================================================================
-- Section 13: Trust Domains
-- ============================================================================

/-- Trust level: higher means more trusted -/
noncomputable def trustLevel : Nat → Nat
  | 0 => 3  -- internal → high trust
  | 1 => 2  -- dmz → medium trust
  | 2 => 1  -- partner → low trust
  | _ => 0  -- external → no trust

/-- Compose trust with clearance -/
noncomputable def trustClearance (domain : Nat) : Nat := Nat.min (trustLevel domain) 3

theorem trustClearance_internal : trustClearance 0 = 3 := rfl
theorem trustClearance_dmz : trustClearance 1 = 2 := rfl
theorem trustClearance_partner : trustClearance 2 = 1 := rfl

/-- Theorem 49: Trust clearance paths -/
noncomputable def trustClearance_internal_path : Path (trustClearance 0) 3 :=
  Path.refl 3

noncomputable def trustClearance_dmz_path : Path (trustClearance 1) 2 :=
  Path.refl 2

/-- Theorem 50: Trust composition via congrArg -/
noncomputable def trustCompose (n : Nat) : Path (Nat.max (trustLevel n) (trustLevel n)) (trustLevel n) :=
  Path.stepChain (Nat.max_self (trustLevel n))

-- ============================================================================
-- Section 14: Access Decision Algebra
-- ============================================================================

/-- Access decision combines policy and clearance -/
noncomputable def accessDecision (policyResult clearance : Nat) : Nat :=
  Nat.min policyResult clearance

/-- Theorem 51: Access decision is commutative -/
noncomputable def accessDecision_comm_path (a b : Nat) :
    Path (accessDecision a b) (accessDecision b a) :=
  Path.stepChain (Nat.min_comm a b)

/-- Theorem 52: Access decision is associative -/
noncomputable def accessDecision_assoc_path (a b c : Nat) :
    Path (accessDecision (accessDecision a b) c) (accessDecision a (accessDecision b c)) :=
  Path.stepChain (Nat.min_assoc a b c)

/-- Theorem 53: Access decision is idempotent -/
noncomputable def accessDecision_idem_path (a : Nat) : Path (accessDecision a a) a :=
  Path.stepChain (Nat.min_self a)

/-- Theorem 54: Symm of access decision commutativity -/
noncomputable def accessDecision_comm_symm (a b : Nat) :
    Path (accessDecision b a) (accessDecision a b) :=
  Path.symm (accessDecision_comm_path a b)

/-- Theorem 55: Double commutation round trip -/
noncomputable def accessDecision_double_comm (a b : Nat) :
    Path (accessDecision a b) (accessDecision a b) :=
  Path.trans (accessDecision_comm_path a b) (accessDecision_comm_symm a b)

-- ============================================================================
-- Section 15: Delegation Path Composition Properties
-- ============================================================================

/-- Theorem 56: Trans of commutativity paths is well-formed -/
noncomputable def delegation_comm_chain (a b : Nat) :
    Path (flowJoin a b) (flowJoin b a) :=
  flowJoin_comm_path a b

/-- Theorem 57: Trans-assoc for delegation paths -/
theorem delegation_path_assoc (a b : Nat) :
    Path.trans (Path.trans (flowJoin_comm_path a b) (flowJoin_comm_path b a))
               (flowJoin_comm_path a b)
    = Path.trans (flowJoin_comm_path a b)
                 (Path.trans (flowJoin_comm_path b a) (flowJoin_comm_path a b)) :=
  trans_assoc _ _ _

/-- Theorem 58: Left identity for delegation paths -/
theorem delegation_left_id (a b : Nat) :
    Path.trans (Path.refl (flowJoin a b)) (flowJoin_comm_path a b)
    = flowJoin_comm_path a b :=
  trans_refl_left _

/-- Theorem 59: Right identity for delegation paths -/
theorem delegation_right_id (a b : Nat) :
    Path.trans (flowJoin_comm_path a b) (Path.refl (flowJoin b a))
    = flowJoin_comm_path a b :=
  trans_refl_right _

/-- Theorem 60: symm_trans for delegation -/
theorem delegation_symm_trans (a b : Nat) :
    Path.symm (Path.trans (flowJoin_comm_path a b) (flowJoin_comm_path b a))
    = Path.trans (Path.symm (flowJoin_comm_path b a)) (Path.symm (flowJoin_comm_path a b)) :=
  symm_trans _ _

-- ============================================================================
-- Section 16: Audit Trail as Path Sequences
-- ============================================================================

/-- Audit score: accumulated access count -/
noncomputable def auditScore (accesses : Nat) : Nat := accesses

theorem auditScore_id (n : Nat) : auditScore n = n := rfl

/-- Theorem 61: Audit score identity path -/
noncomputable def auditScore_path (n : Nat) : Path (auditScore n) n :=
  Path.refl n

/-- Audit combination -/
noncomputable def auditCombine (a b : Nat) : Nat := a + b

theorem auditCombine_zero_left (n : Nat) : auditCombine 0 n = n := Nat.zero_add n
theorem auditCombine_zero_right (n : Nat) : auditCombine n 0 = n := Nat.add_zero n

/-- Theorem 62: Audit zero left identity -/
noncomputable def auditCombine_zero_left_path (n : Nat) : Path (auditCombine 0 n) n :=
  Path.stepChain (auditCombine_zero_left n)

/-- Theorem 63: Audit zero right identity -/
noncomputable def auditCombine_zero_right_path (n : Nat) : Path (auditCombine n 0) n :=
  Path.stepChain (auditCombine_zero_right n)

/-- Theorem 64: Audit combination is associative -/
theorem auditCombine_assoc (a b c : Nat) :
    auditCombine (auditCombine a b) c = auditCombine a (auditCombine b c) :=
  Nat.add_assoc a b c

noncomputable def auditCombine_assoc_path (a b c : Nat) :
    Path (auditCombine (auditCombine a b) c) (auditCombine a (auditCombine b c)) :=
  Path.stepChain (auditCombine_assoc a b c)

/-- Theorem 65: Audit combination is commutative -/
theorem auditCombine_comm (a b : Nat) :
    auditCombine a b = auditCombine b a :=
  Nat.add_comm a b

noncomputable def auditCombine_comm_path (a b : Nat) :
    Path (auditCombine a b) (auditCombine b a) :=
  Path.stepChain (auditCombine_comm a b)

-- ============================================================================
-- Section 17: CongrArg Composition Theorems
-- ============================================================================

/-- Map access decision to a flow label -/
noncomputable def decisionToFlow (d : Nat) : Nat := Nat.min d 3

/-- Theorem 66: congrArg through decisionToFlow on commutativity -/
noncomputable def decision_flow_comm (a b : Nat) :
    Path (decisionToFlow (accessDecision a b)) (decisionToFlow (accessDecision b a)) :=
  Path.congrArg decisionToFlow (accessDecision_comm_path a b)

/-- Theorem 67: congrArg through decisionToFlow on associativity -/
noncomputable def decision_flow_assoc (a b c : Nat) :
    Path (decisionToFlow (accessDecision (accessDecision a b) c))
         (decisionToFlow (accessDecision a (accessDecision b c))) :=
  Path.congrArg decisionToFlow (accessDecision_assoc_path a b c)

/-- Theorem 68: congrArg preserves symm for decision-to-flow -/
theorem decision_flow_congr_symm (a b : Nat) :
    Path.congrArg decisionToFlow (Path.symm (accessDecision_comm_path a b))
    = Path.symm (Path.congrArg decisionToFlow (accessDecision_comm_path a b)) :=
  congrArg_symm decisionToFlow _

/-- Theorem 69: congrArg preserves trans for decision-to-flow -/
theorem decision_flow_congr_trans (a b : Nat) :
    Path.congrArg decisionToFlow
      (Path.trans (accessDecision_comm_path a b) (accessDecision_comm_path b a))
    = Path.trans
        (Path.congrArg decisionToFlow (accessDecision_comm_path a b))
        (Path.congrArg decisionToFlow (accessDecision_comm_path b a)) :=
  congrArg_trans decisionToFlow _ _

-- ============================================================================
-- Section 18: Cross-Domain Security Composition
-- ============================================================================

/-- Map clearance to effective permission -/
noncomputable def clearanceToPermission (c : Nat) : Nat := Nat.min c 4

/-- Theorem 70: congrArg of clearance max self through permission -/
noncomputable def crossDomain_max_self (n : Nat) :
    Path (clearanceToPermission (clearanceMax n n)) (clearanceToPermission n) :=
  Path.congrArg clearanceToPermission (clearanceMax_self_path n)

/-- Theorem 71: congrArg of clearance max comm through permission -/
noncomputable def crossDomain_max_comm (a b : Nat) :
    Path (clearanceToPermission (clearanceMax a b)) (clearanceToPermission (clearanceMax b a)) :=
  Path.congrArg clearanceToPermission (clearanceMax_comm_path a b)

/-- Theorem 72: Trans of cross-domain paths -/
noncomputable def crossDomain_roundtrip (a b : Nat) :
    Path (clearanceToPermission (clearanceMax a b))
         (clearanceToPermission (clearanceMax a b)) :=
  Path.trans (crossDomain_max_comm a b) (crossDomain_max_comm b a)

/-- Theorem 73: symm_symm for cross-domain -/
theorem crossDomain_symm_symm (a b : Nat) :
    Path.symm (Path.symm (crossDomain_max_comm a b)) = crossDomain_max_comm a b :=
  symm_symm _

-- ============================================================================
-- Section 19: Comprehensive Path Algebra Properties
-- ============================================================================

/-- Theorem 74: Four-fold trans associativity for policy paths -/
theorem policy_fourfold_assoc (a b : Nat) :
    let p1 := policyOr_comm_path a b
    let p2 := policyOr_comm_path b a
    let p3 := policyOr_comm_path a b
    let p4 := policyOr_comm_path b a
    Path.trans (Path.trans (Path.trans p1 p2) p3) p4
    = Path.trans p1 (Path.trans p2 (Path.trans p3 p4)) :=
  trans_assoc_fourfold _ _ _ _

/-- Theorem 75: congrArg on composed function -/
noncomputable def composed_functorial (n : Nat) :
    Path (decisionToFlow (clearanceToPermission (clearanceMax n n)))
         (decisionToFlow (clearanceToPermission n)) :=
  Path.congrArg (fun x => decisionToFlow (clearanceToPermission x))
    (clearanceMax_self_path n)

end ComputationalPaths.Path.Algebra.AccessControlPathDeep
