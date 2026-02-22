/-
  Cryptographic Protocols via Computational Paths
  ==============================================

  This module provides a symbolic development of cryptographic protocols using
  computational paths:
  - message algebras and key operations
  - Dolev-Yao style constructors and destructors
  - protocol traces and attack traces
  - authentication and secrecy predicates
  - Needham-Schroeder style message flow
  - protocol equivalence in a symbolic model
  - strand spaces and path-level coherence witnesses
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.CryptographicProtocolsDeep

open ComputationalPaths.Path

universe u

/-! ## Agents, keys, and messages -/

inductive Agent where
  | alice
  | bob
  | server
  | intruder
  | peer (n : Nat)
  deriving DecidableEq, Repr

inductive Key where
  | pub : Agent → Key
  | priv : Agent → Key
  | sym : Nat → Key
  deriving DecidableEq, Repr

noncomputable def invKey : Key → Key
  | .pub a => .priv a
  | .priv a => .pub a
  | .sym n => .sym n

@[simp] theorem invKey_pub (a : Agent) : invKey (Key.pub a) = Key.priv a := rfl
@[simp] theorem invKey_priv (a : Agent) : invKey (Key.priv a) = Key.pub a := rfl
@[simp] theorem invKey_sym (n : Nat) : invKey (Key.sym n) = Key.sym n := rfl

theorem invKey_involutive (k : Key) : invKey (invKey k) = k := by
  cases k <;> rfl

theorem invKey_not_change_sym (n : Nat) : invKey (Key.sym n) = Key.sym n := rfl

noncomputable def invKey_path (k : Key) : Path (invKey (invKey k)) k :=
  Path.stepChain (invKey_involutive k)

inductive Message where
  | atom : Nat → Message
  | nonce : Nat → Agent → Message
  | pair : Message → Message → Message
  | enc : Key → Message → Message
  | hash : Message → Message
  | tag : Agent → Message
  deriving DecidableEq, Repr

abbrev Sym := Message

noncomputable def msgId (m : Message) : Message := m

noncomputable def msgSize : Message → Nat
  | .atom _ => 1
  | .nonce _ _ => 1
  | .pair m n => msgSize m + msgSize n + 1
  | .enc _ m => msgSize m + 1
  | .hash m => msgSize m + 1
  | .tag _ => 1

noncomputable def msgDepth : Message → Nat
  | .atom _ => 0
  | .nonce _ _ => 0
  | .pair m n => Nat.succ (Nat.max (msgDepth m) (msgDepth n))
  | .enc _ m => Nat.succ (msgDepth m)
  | .hash m => Nat.succ (msgDepth m)
  | .tag _ => 0

@[simp] theorem msgId_apply (m : Message) : msgId m = m := rfl
@[simp] theorem msgId_idempotent (m : Message) : msgId (msgId m) = m := rfl

@[simp] theorem msgSize_atom (n : Nat) : msgSize (Message.atom n) = 1 := rfl
@[simp] theorem msgSize_nonce (n : Nat) (a : Agent) : msgSize (Message.nonce n a) = 1 := rfl
@[simp] theorem msgSize_pair (m n : Message) :
    msgSize (Message.pair m n) = msgSize m + msgSize n + 1 := rfl
@[simp] theorem msgSize_enc (k : Key) (m : Message) :
    msgSize (Message.enc k m) = msgSize m + 1 := rfl
@[simp] theorem msgSize_hash (m : Message) :
    msgSize (Message.hash m) = msgSize m + 1 := rfl
@[simp] theorem msgSize_tag (a : Agent) : msgSize (Message.tag a) = 1 := rfl

@[simp] theorem msgDepth_atom (n : Nat) : msgDepth (Message.atom n) = 0 := rfl
@[simp] theorem msgDepth_nonce (n : Nat) (a : Agent) : msgDepth (Message.nonce n a) = 0 := rfl
@[simp] theorem msgDepth_pair (m n : Message) :
    msgDepth (Message.pair m n) = Nat.succ (Nat.max (msgDepth m) (msgDepth n)) := rfl
@[simp] theorem msgDepth_enc (k : Key) (m : Message) :
    msgDepth (Message.enc k m) = Nat.succ (msgDepth m) := rfl
@[simp] theorem msgDepth_hash (m : Message) :
    msgDepth (Message.hash m) = Nat.succ (msgDepth m) := rfl
@[simp] theorem msgDepth_tag (a : Agent) : msgDepth (Message.tag a) = 0 := rfl

theorem msgSize_pair_comm (m n : Message) :
    msgSize (Message.pair m n) = msgSize (Message.pair n m) := by
  simp [msgSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem msgDepth_pair_comm (m n : Message) :
    msgDepth (Message.pair m n) = msgDepth (Message.pair n m) := by
  simp [msgDepth, Nat.max_comm]

theorem msgSize_enc_invKey (k : Key) (m : Message) :
    msgSize (Message.enc (invKey k) m) = msgSize (Message.enc k m) := by
  simp [msgSize]

noncomputable def hashWrap (m : Message) : Message := Message.hash m

noncomputable def hashUnwrap : Message → Message
  | Message.hash m => m
  | m => m

noncomputable def encWrap (k : Key) (m : Message) : Message := Message.enc k m

noncomputable def encUnwrap : Message → Message
  | Message.enc _ m => m
  | m => m

noncomputable def pairLeft : Message → Message
  | Message.pair m _ => m
  | m => m

noncomputable def pairRight : Message → Message
  | Message.pair _ n => n
  | m => m

noncomputable def pairSwap : Message → Message
  | Message.pair m n => Message.pair n m
  | m => m

@[simp] theorem hashUnwrap_hashWrap (m : Message) : hashUnwrap (hashWrap m) = m := rfl
@[simp] theorem encUnwrap_encWrap (k : Key) (m : Message) : encUnwrap (encWrap k m) = m := rfl
@[simp] theorem pairLeft_pair (m n : Message) : pairLeft (Message.pair m n) = m := rfl
@[simp] theorem pairRight_pair (m n : Message) : pairRight (Message.pair m n) = n := rfl

theorem pairRebuild (m n : Message) :
    Message.pair (pairLeft (Message.pair m n)) (pairRight (Message.pair m n)) = Message.pair m n := rfl

theorem pairSwap_twice (m : Message) : pairSwap (pairSwap m) = m := by
  cases m <;> rfl

theorem msgSize_pairSwap (m : Message) : msgSize (pairSwap m) = msgSize m := by
  cases m with
  | atom n => rfl
  | nonce n a => rfl
  | pair x y =>
      simp [pairSwap, msgSize, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
  | enc k x => rfl
  | hash x => rfl
  | tag a => rfl

theorem msgDepth_hashWrap (m : Message) :
    msgDepth (hashWrap m) = Nat.succ (msgDepth m) := rfl

theorem msgSize_hashWrap (m : Message) :
    msgSize (hashWrap m) = msgSize m + 1 := rfl

noncomputable def msgId_path (m : Message) : Path (msgId m) m :=
  Path.refl m

noncomputable def msgId_size_path (m : Message) : Path (msgSize (msgId m)) (msgSize m) :=
  Path.congrArg msgSize (msgId_path m)

noncomputable def pairSwap_roundtrip_path (m : Message) : Path (pairSwap (pairSwap m)) m :=
  Path.stepChain (pairSwap_twice m)

/-! ## Dolev-Yao symbolic operations -/

noncomputable def dyPair (m n : Message) : Message := Message.pair m n

noncomputable def dyEncrypt (k : Key) (m : Message) : Message := Message.enc k m

noncomputable def dyDecrypt (k : Key) : Message → Message
  | Message.enc k' payload =>
      if invKey k = k' then payload else Message.enc k' payload
  | m => m

@[simp] theorem dyPair_eq (m n : Message) : dyPair m n = Message.pair m n := rfl
@[simp] theorem dyEncrypt_eq (k : Key) (m : Message) : dyEncrypt k m = Message.enc k m := rfl

@[simp] theorem dyDecrypt_plain_atom (k : Key) (n : Nat) :
    dyDecrypt k (Message.atom n) = Message.atom n := rfl

@[simp] theorem dyDecrypt_plain_nonce (k : Key) (n : Nat) (a : Agent) :
    dyDecrypt k (Message.nonce n a) = Message.nonce n a := rfl

theorem dyDecrypt_correct (k : Key) (m : Message) :
    dyDecrypt (invKey k) (Message.enc k m) = m := by
  simp [dyDecrypt, invKey_involutive]

theorem dyDecrypt_wrong_key (k1 k2 : Key) (m : Message) (h : invKey k1 ≠ k2) :
    dyDecrypt k1 (Message.enc k2 m) = Message.enc k2 m := by
  simp [dyDecrypt, h]

theorem dyDecrypt_sym_key (n : Nat) (m : Message) :
    dyDecrypt (Key.sym n) (Message.enc (Key.sym n) m) = m := by
  simp [dyDecrypt, invKey]

noncomputable def intruderKnowledge (Gam : List Message) : List Message := Gam

noncomputable def combineKnowledge (Gam1 Gam2 : List Message) : List Message := Gam1 ++ Gam2

noncomputable def intruderSynth (Gam : List Message) : List Message := combineKnowledge Gam Gam

theorem intruderKnowledge_empty : intruderKnowledge [] = [] := rfl

theorem intruderKnowledge_singleton (m : Message) : intruderKnowledge [m] = [m] := rfl

theorem intruderKnowledge_append (Gam1 Gam2 : List Message) :
    intruderKnowledge (Gam1 ++ Gam2) = combineKnowledge Gam1 Gam2 := rfl

theorem combineKnowledge_assoc (Gam1 Gam2 Gam3 : List Message) :
    combineKnowledge (combineKnowledge Gam1 Gam2) Gam3 =
      combineKnowledge Gam1 (combineKnowledge Gam2 Gam3) := by
  simp [combineKnowledge, List.append_assoc]

theorem combineKnowledge_nil_left (Gam : List Message) :
    combineKnowledge [] Gam = Gam := rfl

theorem combineKnowledge_nil_right (Gam : List Message) :
    combineKnowledge Gam [] = Gam := by
  simp [combineKnowledge]

theorem intruderSynth_eq_append (Gam : List Message) :
    intruderSynth Gam = Gam ++ Gam := rfl

theorem intruderSynth_nil : intruderSynth [] = [] := rfl

theorem intruderSynth_length (Gam : List Message) :
    (intruderSynth Gam).length = Gam.length + Gam.length := by
  simp [intruderSynth, combineKnowledge]

noncomputable def intruderSynth_path_assoc (Gam1 Gam2 Gam3 : List Message) :
    Path (combineKnowledge (combineKnowledge Gam1 Gam2) Gam3)
         (combineKnowledge Gam1 (combineKnowledge Gam2 Gam3)) :=
  Path.stepChain (combineKnowledge_assoc Gam1 Gam2 Gam3)

/-! ## Protocol traces -/

inductive Event where
  | send (src dst : Agent) (payload : Message)
  | recv (src dst : Agent) (payload : Message)
  | claimAuth (who peer : Agent) (token : Nat)
  | claimSecret (who : Agent) (secret : Message)
  deriving DecidableEq, Repr

abbrev Trace := List Event

noncomputable def appendTrace (tr1 tr2 : Trace) : Trace := tr1 ++ tr2

noncomputable def traceLen (tr : Trace) : Nat := tr.length

noncomputable def appendEvent (tr : Trace) (ev : Event) : Trace := tr ++ [ev]

noncomputable def reverseTrace (tr : Trace) : Trace := tr.reverse

noncomputable def hasEvent (ev : Event) (tr : Trace) : Prop := ev ∈ tr

theorem appendTrace_assoc (tr1 tr2 tr3 : Trace) :
    appendTrace (appendTrace tr1 tr2) tr3 = appendTrace tr1 (appendTrace tr2 tr3) := by
  simp [appendTrace, List.append_assoc]

theorem appendTrace_nil_left (tr : Trace) : appendTrace [] tr = tr := rfl

theorem appendTrace_nil_right (tr : Trace) : appendTrace tr [] = tr := by
  simp [appendTrace]

theorem traceLen_append (tr1 tr2 : Trace) :
    traceLen (appendTrace tr1 tr2) = traceLen tr1 + traceLen tr2 := by
  simp [traceLen, appendTrace]

theorem appendEvent_eq (tr : Trace) (ev : Event) :
    appendEvent tr ev = tr ++ [ev] := rfl

theorem traceLen_appendEvent (tr : Trace) (ev : Event) :
    traceLen (appendEvent tr ev) = traceLen tr + 1 := by
  simp [traceLen, appendEvent]

theorem reverseTrace_reverse (tr : Trace) : reverseTrace (reverseTrace tr) = tr := by
  simp [reverseTrace]

theorem reverseTrace_append (tr1 tr2 : Trace) :
    reverseTrace (appendTrace tr1 tr2) = appendTrace (reverseTrace tr2) (reverseTrace tr1) := by
  simp [reverseTrace, appendTrace, List.reverse_append]

noncomputable def traceAssoc_path (tr1 tr2 tr3 : Trace) :
    Path (appendTrace (appendTrace tr1 tr2) tr3) (appendTrace tr1 (appendTrace tr2 tr3)) :=
  Path.stepChain (appendTrace_assoc tr1 tr2 tr3)

noncomputable def traceLeftUnit_path (tr : Trace) : Path (appendTrace [] tr) tr :=
  Path.refl tr

noncomputable def traceRightUnit_path (tr : Trace) : Path (appendTrace tr []) tr :=
  Path.stepChain (appendTrace_nil_right tr)

noncomputable def traceRoundtrip_path (tr : Trace) : Path tr tr :=
  Path.trans (Path.refl tr) (Path.refl tr)

theorem hasEvent_append_left (ev : Event) (tr1 tr2 : Trace) :
    hasEvent ev tr1 → hasEvent ev (appendTrace tr1 tr2) := by
  intro h
  simpa [hasEvent, appendTrace] using List.mem_append_left tr2 h

theorem hasEvent_append_right (ev : Event) (tr1 tr2 : Trace) :
    hasEvent ev tr2 → hasEvent ev (appendTrace tr1 tr2) := by
  intro h
  simpa [hasEvent, appendTrace] using List.mem_append_right tr1 h

theorem hasEvent_append_cases (ev : Event) (tr1 tr2 : Trace) :
    hasEvent ev (appendTrace tr1 tr2) ↔ hasEvent ev tr1 ∨ hasEvent ev tr2 := by
  simp [hasEvent, appendTrace]

theorem hasEvent_appendEvent (ev ev' : Event) (tr : Trace) :
    hasEvent ev (appendEvent tr ev') ↔ hasEvent ev tr ∨ ev = ev' := by
  simp [hasEvent, appendEvent]

theorem hasEvent_self_appendEvent (tr : Trace) (ev : Event) :
    hasEvent ev (appendEvent tr ev) := by
  simp [hasEvent, appendEvent]

theorem traceLen_reverse (tr : Trace) : traceLen (reverseTrace tr) = traceLen tr := by
  simp [traceLen, reverseTrace]

/-! ## Authentication and secrecy predicates -/

noncomputable def authentication (tr : Trace) : Prop :=
  ∀ a b m, Event.recv a b m ∈ tr → Event.send b a m ∈ tr

noncomputable def secrecy (secret : Message) (tr : Trace) : Prop :=
  Event.claimSecret Agent.server secret ∈ tr →
    Event.send Agent.intruder Agent.intruder secret ∉ tr

theorem authentication_intro (tr : Trace)
    (h : ∀ a b m, Event.recv a b m ∈ tr → Event.send b a m ∈ tr) :
    authentication tr := h

theorem authentication_empty : authentication [] := by
  intro a b m h
  cases h

theorem authentication_single_send (a b : Agent) (m : Message) :
    authentication [Event.send a b m] := by
  intro x y z hrecv
  simp at hrecv

theorem secrecy_intro (secret : Message) (tr : Trace)
    (h : Event.claimSecret Agent.server secret ∈ tr →
      Event.send Agent.intruder Agent.intruder secret ∉ tr) :
    secrecy secret tr := h

theorem secrecy_vacuous_empty (secret : Message) : secrecy secret [] := by
  intro h
  cases h

theorem secrecy_of_no_server_claim (secret : Message) (tr : Trace)
    (h : Event.claimSecret Agent.server secret ∉ tr) :
    secrecy secret tr := by
  intro hclaim
  exact False.elim (h hclaim)

/-! ## Needham-Schroeder symbolic traces -/

noncomputable def nsNonceA : Message := Message.nonce 0 Agent.alice
noncomputable def nsNonceB : Message := Message.nonce 1 Agent.bob

noncomputable def nsMsg1 : Message :=
  Message.enc (Key.pub Agent.bob) (Message.pair (Message.tag Agent.alice) nsNonceA)

noncomputable def nsMsg2 : Message :=
  Message.enc (Key.pub Agent.alice) (Message.pair nsNonceA nsNonceB)

noncomputable def nsMsg3 : Message :=
  Message.enc (Key.pub Agent.bob) nsNonceB

noncomputable def nsHonestTrace : Trace :=
  [ Event.send Agent.alice Agent.bob nsMsg1
  , Event.recv Agent.bob Agent.alice nsMsg1
  , Event.send Agent.bob Agent.alice nsMsg2
  , Event.recv Agent.alice Agent.bob nsMsg2
  , Event.send Agent.alice Agent.bob nsMsg3
  ]

noncomputable def nsAttackTrace : Trace :=
  [ Event.send Agent.alice Agent.intruder nsMsg1
  , Event.send Agent.intruder Agent.bob nsMsg1
  , Event.send Agent.bob Agent.intruder nsMsg2
  , Event.send Agent.intruder Agent.alice nsMsg2
  , Event.send Agent.alice Agent.intruder nsMsg3
  , Event.send Agent.intruder Agent.bob nsMsg3
  ]

theorem nsMsg1_size : msgSize nsMsg1 = 1 + msgSize nsNonceA + 1 + 1 := by
  simp [nsMsg1, msgSize]

theorem nsMsg2_size : msgSize nsMsg2 = msgSize nsNonceA + msgSize nsNonceB + 1 + 1 := by
  simp [nsMsg2, msgSize]

theorem nsMsg3_size : msgSize nsMsg3 = msgSize nsNonceB + 1 := by
  simp [nsMsg3]

theorem nsHonest_length : traceLen nsHonestTrace = 5 := rfl

theorem nsAttack_length : traceLen nsAttackTrace = 6 := rfl

theorem nsAttack_longer : traceLen nsAttackTrace = traceLen nsHonestTrace + 1 := rfl

theorem nsHonest_head :
    nsHonestTrace.head? = some (Event.send Agent.alice Agent.bob nsMsg1) := rfl

theorem nsAttack_head :
    nsAttackTrace.head? = some (Event.send Agent.alice Agent.intruder nsMsg1) := rfl

theorem nsHonest_contains_msg1 :
    Event.send Agent.alice Agent.bob nsMsg1 ∈ nsHonestTrace := by
  simp [nsHonestTrace]

theorem nsHonest_contains_msg2 :
    Event.send Agent.bob Agent.alice nsMsg2 ∈ nsHonestTrace := by
  simp [nsHonestTrace]

theorem nsAttack_contains_relay :
    Event.send Agent.intruder Agent.bob nsMsg1 ∈ nsAttackTrace := by
  simp [nsAttackTrace]

theorem nsAttack_contains_final_relay :
    Event.send Agent.intruder Agent.bob nsMsg3 ∈ nsAttackTrace := by
  simp [nsAttackTrace]

noncomputable def nsAttack_as_path : Path nsAttackTrace nsAttackTrace :=
  Path.trans (Path.refl nsAttackTrace) (Path.refl nsAttackTrace)

theorem nsAttack_refl_symm :
    Path.symm (Path.refl nsAttackTrace) = Path.refl nsAttackTrace := by
  simpa using Path.symm_refl nsAttackTrace

theorem nsAttack_assoc_path :
    Path.trans nsAttack_as_path (Path.refl nsAttackTrace) =
      Path.trans (Path.refl nsAttackTrace) nsAttack_as_path := by
  simpa [nsAttack_as_path] using
    (Path.trans_assoc (Path.refl nsAttackTrace) (Path.refl nsAttackTrace) (Path.refl nsAttackTrace))

/-! ## Protocol equivalence and symbolic models -/

noncomputable def protocolEquivalent (tr1 tr2 : Trace) : Prop := traceLen tr1 = traceLen tr2

theorem protocolEquivalent_refl (tr : Trace) : protocolEquivalent tr tr := rfl

theorem protocolEquivalent_symm {tr1 tr2 : Trace} :
    protocolEquivalent tr1 tr2 → protocolEquivalent tr2 tr1 := by
  intro h
  exact h.symm

theorem protocolEquivalent_trans {tr1 tr2 tr3 : Trace} :
    protocolEquivalent tr1 tr2 → protocolEquivalent tr2 tr3 → protocolEquivalent tr1 tr3 := by
  intro h1 h2
  exact Eq.trans h1 h2

theorem protocolEquivalent_honest_self : protocolEquivalent nsHonestTrace nsHonestTrace := rfl

theorem protocolEquivalent_attack_self : protocolEquivalent nsAttackTrace nsAttackTrace := rfl

theorem ns_protocol_not_equiv : ¬ protocolEquivalent nsHonestTrace nsAttackTrace := by
  intro h
  simp [protocolEquivalent, nsHonest_length, nsAttack_length] at h

noncomputable def protocolEquivalent_path_of_equiv {tr1 tr2 : Trace}
    (h : protocolEquivalent tr1 tr2) :
    Path (traceLen tr1) (traceLen tr2) :=
  Path.stepChain h

structure SymbolicModel where
  Sym : Type u
  Gam : List Sym

noncomputable def modelCard (M : SymbolicModel) : Nat := M.Gam.length

noncomputable def modelEmpty (Sym : Type u) : SymbolicModel :=
  { Sym := Sym, Gam := [] }

noncomputable def modelInsert (M : SymbolicModel) (x : M.Sym) : SymbolicModel :=
  { Sym := M.Sym, Gam := x :: M.Gam }

noncomputable def messageModel (Gam : List Message) : SymbolicModel :=
  { Sym := Message, Gam := Gam }

theorem modelCard_empty (Sym : Type u) : modelCard (modelEmpty Sym) = 0 := rfl

theorem modelCard_insert (M : SymbolicModel) (x : M.Sym) :
    modelCard (modelInsert M x) = modelCard M + 1 := by
  simp [modelCard, modelInsert]

theorem modelCard_insert_twice (M : SymbolicModel) (x y : M.Sym) :
    modelCard (modelInsert (modelInsert M x) y) = modelCard M + 2 := by
  simp [modelCard, modelInsert, Nat.add_assoc]

theorem messageModel_card (Gam : List Message) :
    modelCard (messageModel Gam) = Gam.length := rfl

theorem messageModel_insert_card (Gam : List Message) (m : Message) :
    modelCard (messageModel (m :: Gam)) = modelCard (messageModel Gam) + 1 := by
  simp [messageModel, modelCard]

/-! ## Strand spaces -/

abbrev Strand := List Event

structure StrandSpace where
  strands : List Strand
  deriving Repr

noncomputable def emptyStrandSpace : StrandSpace := { strands := [] }

noncomputable def addStrand (S : StrandSpace) (s : Strand) : StrandSpace :=
  { strands := s :: S.strands }

noncomputable def strandCount (S : StrandSpace) : Nat := S.strands.length

noncomputable def strandSpaceMessages (S : StrandSpace) : List Event := S.strands.foldr List.append []

noncomputable def strandEquivalent (S1 S2 : StrandSpace) : Prop := strandCount S1 = strandCount S2

theorem strandCount_empty : strandCount emptyStrandSpace = 0 := rfl

theorem strandCount_add (S : StrandSpace) (s : Strand) :
    strandCount (addStrand S s) = strandCount S + 1 := by
  simp [strandCount, addStrand]

theorem strandCount_add_twice (S : StrandSpace) (s1 s2 : Strand) :
    strandCount (addStrand (addStrand S s1) s2) = strandCount S + 2 := by
  simp [strandCount, addStrand, Nat.add_assoc]

theorem strandSpaceMessages_empty : strandSpaceMessages emptyStrandSpace = [] := by
  simp [strandSpaceMessages, emptyStrandSpace]

theorem strandSpaceMessages_add (S : StrandSpace) (s : Strand) :
    strandSpaceMessages (addStrand S s) = s ++ strandSpaceMessages S := by
  simp [strandSpaceMessages, addStrand]

theorem strandEquivalent_refl (S : StrandSpace) : strandEquivalent S S := rfl

theorem strandEquivalent_symm {S1 S2 : StrandSpace} :
    strandEquivalent S1 S2 → strandEquivalent S2 S1 := by
  intro h
  exact h.symm

theorem strandEquivalent_trans {S1 S2 S3 : StrandSpace} :
    strandEquivalent S1 S2 → strandEquivalent S2 S3 → strandEquivalent S1 S3 := by
  intro h1 h2
  exact Eq.trans h1 h2

noncomputable def nsStrandSpace : StrandSpace :=
  { strands := [nsHonestTrace, nsAttackTrace] }

theorem nsStrand_count : strandCount nsStrandSpace = 2 := rfl

theorem nsStrand_has_attack : nsAttackTrace ∈ nsStrandSpace.strands := by
  simp [nsStrandSpace]

theorem nsStrand_has_honest : nsHonestTrace ∈ nsStrandSpace.strands := by
  simp [nsStrandSpace]

noncomputable def strandCount_path (S : StrandSpace) : Path (strandCount S) (strandCount S) :=
  Path.refl (strandCount S)

noncomputable def strandCount_roundtrip_path (S : StrandSpace) :
    Path (strandCount S) (strandCount S) :=
  Path.trans (Path.refl (strandCount S)) (Path.refl (strandCount S))

end ComputationalPaths.Path.Algebra.CryptographicProtocolsDeep
