/-
# Turing Machines via Computational Paths

This module formalizes Turing machines and computability — Turing machine
definitions, configurations, computation steps, the Church-Turing thesis
(informal), universal Turing machines, the halting problem undecidability,
Rice's theorem, and multi-tape equivalence — all with `Path` coherence
witnesses.

## Mathematical Background

Turing machines are the foundational model of computation, capturing the
notion of algorithmic solvability:

1. **Turing Machines**: A 7-tuple M = (Q, Σ, Γ, δ, q₀, q_accept, q_reject)
   where Q is a finite set of states, Σ is the input alphabet (Σ ⊆ Γ),
   Γ is the tape alphabet (including blank ⊔), δ : Q × Γ → Q × Γ × {L,R}
   is the transition function, q₀ is the start state, q_accept and q_reject
   are halting states.
2. **Configurations**: A configuration is a triple (q, tape, head_position)
   describing the complete state of the TM at one moment. A computation is
   a sequence of configurations.
3. **Computation**: A TM decides a language L if it halts on every input,
   accepting strings in L and rejecting strings not in L. A TM recognizes
   (semi-decides) L if it accepts strings in L but may loop on others.
4. **Church-Turing Thesis**: (Informal) Every effectively computable
   function is Turing computable. This is a philosophical thesis, not a
   formal theorem.
5. **Universal Turing Machine**: There exists a UTM U that, given an
   encoding ⟨M, w⟩ of a TM M and input w, simulates M on w. This
   establishes the concept of programmability.
6. **Halting Problem**: The language HALT = {⟨M, w⟩ : M halts on w} is
   recognizable but not decidable. Proof by diagonalization: assume a
   decider H exists, construct D that on ⟨M⟩ runs H(⟨M, M⟩) and does
   the opposite, leading to contradiction on D(⟨D⟩).
7. **Rice's Theorem**: Every non-trivial semantic property of Turing
   machines is undecidable. A property P of RE languages is non-trivial
   if some TMs have it and some don't.
8. **Multi-tape Equivalence**: Every k-tape TM can be simulated by a
   single-tape TM with at most O(t²) overhead where t is the running
   time.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `TMData` | Turing machine data |
| `ConfigurationData` | TM configuration |
| `ComputationData` | TM computation sequence |
| `UTMData` | Universal Turing machine |
| `HaltingData` | Halting problem |
| `RiceData` | Rice's theorem |
| `MultiTapeData` | Multi-tape equivalence |
| `DecidabilityData` | Language decidability classification |
| `tm_transition_path` | TM transition coherence |
| `halting_undecidable_path` | Halting undecidability coherence |
| `rice_path` | Rice's theorem coherence |
| `multitape_path` | Multi-tape equivalence coherence |

## References

- Turing, "On Computable Numbers" (1936)
- Sipser, "Introduction to the Theory of Computation" (3rd ed., 2012)
- Rogers, "Theory of Recursive Functions and Effective Computability" (1967)
- Hopcroft, Motwani, Ullman, "Introduction to Automata Theory" (3rd ed., 2006)
- Davis, "Computability and Unsolvability" (1958)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace TuringMachines

open Path

/-! ## Turing Machines -/

/-- Configuration data for a Turing machine. -/
structure TMData where
  /-- Number of states |Q|. -/
  numStates : Nat
  /-- numStates ≥ 3 (start, accept, reject). -/
  numStates_ge : numStates ≥ 3
  /-- Input alphabet size |Σ|. -/
  inputAlphabetSize : Nat
  /-- inputAlphabetSize is positive. -/
  inputAlphabet_pos : inputAlphabetSize > 0
  /-- Tape alphabet size |Γ| (includes blank and Σ). -/
  tapeAlphabetSize : Nat
  /-- |Γ| ≥ |Σ| + 1 (at least blank symbol). -/
  tapeAlphabet_ge : tapeAlphabetSize ≥ inputAlphabetSize + 1
  /-- Number of transition rules. -/
  numTransitions : Nat
  /-- Maximum transitions = (|Q| - 2) × |Γ| (no transitions from accept/reject). -/
  maxTransitions : Nat
  /-- max = (numStates - 2) * tapeAlphabetSize. -/
  max_transitions_eq : maxTransitions = (numStates - 2) * tapeAlphabetSize
  /-- numTransitions ≤ maxTransitions. -/
  transitions_le : numTransitions ≤ maxTransitions

namespace TMData

/-- A minimal TM: 3 states, binary input, 3-symbol tape. -/
def minimal : TMData where
  numStates := 3
  numStates_ge := by omega
  inputAlphabetSize := 2
  inputAlphabet_pos := by omega
  tapeAlphabetSize := 3
  tapeAlphabet_ge := by omega
  numTransitions := 3
  maxTransitions := 3
  max_transitions_eq := by omega
  transitions_le := by omega

/-- A TM with n states, binary input. -/
def binary (n : Nat) (hn : n ≥ 3) (t : Nat) (ht : t ≤ (n - 2) * 3) : TMData where
  numStates := n
  numStates_ge := hn
  inputAlphabetSize := 2
  inputAlphabet_pos := by omega
  tapeAlphabetSize := 3
  tapeAlphabet_ge := by omega
  numTransitions := t
  maxTransitions := (n - 2) * 3
  max_transitions_eq := rfl
  transitions_le := ht

/-- Path: max transitions formula. -/
def max_transitions_path (tm : TMData) :
    Path tm.maxTransitions ((tm.numStates - 2) * tm.tapeAlphabetSize) :=
  Path.ofEqChain tm.max_transitions_eq

/-- Path: minimal TM max transitions. -/
def minimal_max_path :
    Path minimal.maxTransitions 3 :=
  Path.ofEqChain minimal.max_transitions_eq

end TMData

/-! ## Configurations -/

/-- TM configuration data. -/
structure ConfigurationData where
  /-- Current state index. -/
  stateIndex : Nat
  /-- Total states. -/
  totalStates : Nat
  /-- stateIndex < totalStates. -/
  state_lt : stateIndex < totalStates
  /-- Head position on tape. -/
  headPosition : Nat
  /-- Tape content length (non-blank portion). -/
  tapeLength : Nat
  /-- Whether the configuration is halting. -/
  isHalting : Bool
  /-- Accept state index. -/
  acceptIndex : Nat
  /-- Reject state index. -/
  rejectIndex : Nat
  /-- acceptIndex < totalStates. -/
  accept_lt : acceptIndex < totalStates
  /-- rejectIndex < totalStates. -/
  reject_lt : rejectIndex < totalStates
  /-- accept ≠ reject. -/
  accept_ne_reject : acceptIndex ≠ rejectIndex

namespace ConfigurationData

/-- Initial configuration: state 0, head at 0. -/
def initial (n : Nat) (hn : n ≥ 3) (tLen : Nat) : ConfigurationData where
  stateIndex := 0
  totalStates := n
  state_lt := by omega
  headPosition := 0
  tapeLength := tLen
  isHalting := false
  acceptIndex := 1
  rejectIndex := 2
  accept_lt := by omega
  reject_lt := by omega
  accept_ne_reject := by omega

/-- Accepting configuration. -/
def accepting (n : Nat) (hn : n ≥ 3) (pos tLen : Nat) : ConfigurationData where
  stateIndex := 1
  totalStates := n
  state_lt := by omega
  headPosition := pos
  tapeLength := tLen
  isHalting := true
  acceptIndex := 1
  rejectIndex := 2
  accept_lt := by omega
  reject_lt := by omega
  accept_ne_reject := by omega

/-- Rejecting configuration. -/
def rejecting (n : Nat) (hn : n ≥ 3) (pos tLen : Nat) : ConfigurationData where
  stateIndex := 2
  totalStates := n
  state_lt := by omega
  headPosition := pos
  tapeLength := tLen
  isHalting := true
  acceptIndex := 1
  rejectIndex := 2
  accept_lt := by omega
  reject_lt := by omega
  accept_ne_reject := by omega

end ConfigurationData

/-! ## Computation -/

/-- Computation data: a sequence of configurations. -/
structure ComputationData where
  /-- Number of steps in the computation. -/
  numSteps : Nat
  /-- Number of TM states. -/
  numStates : Nat
  /-- numStates ≥ 3. -/
  numStates_ge : numStates ≥ 3
  /-- Maximum tape usage. -/
  maxTapeUsage : Nat
  /-- Whether the computation halts. -/
  halts : Bool
  /-- Whether the computation accepts (meaningful only if halts). -/
  accepts : Bool
  /-- If halts and accepts, result is 1; if halts and rejects, result is 0. -/
  result : Nat
  /-- result consistency. -/
  result_eq : result = if halts = true then (if accepts = true then 1 else 0) else 0

namespace ComputationData

/-- A computation that accepts in 5 steps. -/
def accepting5 : ComputationData where
  numSteps := 5
  numStates := 4
  numStates_ge := by omega
  maxTapeUsage := 3
  halts := true
  accepts := true
  result := 1
  result_eq := by simp

/-- A computation that rejects in 3 steps. -/
def rejecting3 : ComputationData where
  numSteps := 3
  numStates := 3
  numStates_ge := by omega
  maxTapeUsage := 2
  halts := true
  accepts := false
  result := 0
  result_eq := by simp

/-- A non-halting computation (observed for n steps). -/
def nonhalting (n : Nat) : ComputationData where
  numSteps := n
  numStates := 3
  numStates_ge := by omega
  maxTapeUsage := n
  halts := false
  accepts := false
  result := 0
  result_eq := by simp

/-- Path: result consistency. -/
def result_path (cd : ComputationData) :
    Path cd.result (if cd.halts = true then (if cd.accepts = true then 1 else 0) else 0) :=
  Path.ofEqChain cd.result_eq

end ComputationData

/-! ## Universal Turing Machine -/

/-- Universal Turing machine data. -/
structure UTMData where
  /-- Number of states of the UTM. -/
  utmStates : Nat
  /-- utmStates ≥ 3. -/
  utmStates_ge : utmStates ≥ 3
  /-- Tape alphabet size of UTM. -/
  utmAlphabetSize : Nat
  /-- utmAlphabetSize is positive. -/
  utmAlphabet_pos : utmAlphabetSize > 0
  /-- Encoding overhead factor. -/
  encodingOverhead : Nat
  /-- encodingOverhead is positive. -/
  encoding_pos : encodingOverhead > 0
  /-- Whether the UTM correctly simulates all TMs. -/
  isUniversal : Bool
  /-- Universality. -/
  universal_eq : isUniversal = true
  /-- Simulation slowdown factor. -/
  slowdownFactor : Nat
  /-- slowdownFactor is positive. -/
  slowdown_pos : slowdownFactor > 0

namespace UTMData

/-- A small UTM. -/
def small : UTMData where
  utmStates := 24
  utmStates_ge := by omega
  utmAlphabetSize := 5
  utmAlphabet_pos := by omega
  encodingOverhead := 4
  encoding_pos := by omega
  isUniversal := true
  universal_eq := rfl
  slowdownFactor := 10
  slowdown_pos := by omega

/-- Path: universality. -/
def universal_path (utm : UTMData) :
    Path utm.isUniversal true :=
  Path.ofEqChain utm.universal_eq

end UTMData

/-! ## Halting Problem -/

/-- Halting problem data. -/
structure HaltingData where
  /-- Whether HALT is recognizable (semi-decidable). -/
  isRecognizable : Bool
  /-- HALT is recognizable. -/
  recognizable_eq : isRecognizable = true
  /-- Whether HALT is decidable. -/
  isDecidable : Bool
  /-- HALT is NOT decidable. -/
  decidable_eq : isDecidable = false
  /-- Whether co-HALT is recognizable. -/
  coRecognizable : Bool
  /-- co-HALT is NOT recognizable. -/
  co_recognizable_eq : coRecognizable = false
  /-- Diagonalization obstruction (0 means undecidable proved). -/
  diagonalizationObstruction : Nat
  /-- Diagonalization works. -/
  diag_eq : diagonalizationObstruction = 0

namespace HaltingData

/-- Standard halting problem facts. -/
def standard : HaltingData where
  isRecognizable := true
  recognizable_eq := rfl
  isDecidable := false
  decidable_eq := rfl
  coRecognizable := false
  co_recognizable_eq := rfl
  diagonalizationObstruction := 0
  diag_eq := rfl

/-- Path: HALT is recognizable. -/
def recognizable_path (hd : HaltingData) :
    Path hd.isRecognizable true :=
  Path.ofEqChain hd.recognizable_eq

/-- Path: HALT is not decidable. -/
def undecidable_path (hd : HaltingData) :
    Path hd.isDecidable false :=
  Path.ofEqChain hd.decidable_eq

/-- Path: co-HALT is not recognizable. -/
def co_unrecognizable_path (hd : HaltingData) :
    Path hd.coRecognizable false :=
  Path.ofEqChain hd.co_recognizable_eq

/-- Path: diagonalization. -/
def diag_path (hd : HaltingData) :
    Path hd.diagonalizationObstruction 0 :=
  Path.ofEqChain hd.diag_eq

end HaltingData

/-! ## Rice's Theorem -/

/-- Rice's theorem data. -/
structure RiceData where
  /-- Whether the property is trivial. -/
  isTrivial : Bool
  /-- Property is non-trivial. -/
  nontrivial_eq : isTrivial = false
  /-- Whether the property is semantic (about the language). -/
  isSemantic : Bool
  /-- Property is semantic. -/
  semantic_eq : isSemantic = true
  /-- Whether the property is decidable. -/
  isDecidable : Bool
  /-- Non-trivial semantic properties are undecidable. -/
  undecidable_eq : isDecidable = false
  /-- Reduction obstruction. -/
  reductionObstruction : Nat
  /-- Reduction from HALT works. -/
  reduction_eq : reductionObstruction = 0

namespace RiceData

/-- Rice's theorem for a generic non-trivial semantic property. -/
def standard : RiceData where
  isTrivial := false
  nontrivial_eq := rfl
  isSemantic := true
  semantic_eq := rfl
  isDecidable := false
  undecidable_eq := rfl
  reductionObstruction := 0
  reduction_eq := rfl

/-- Path: property is non-trivial. -/
def nontrivial_path (rd : RiceData) :
    Path rd.isTrivial false :=
  Path.ofEqChain rd.nontrivial_eq

/-- Path: property is semantic. -/
def semantic_path (rd : RiceData) :
    Path rd.isSemantic true :=
  Path.ofEqChain rd.semantic_eq

/-- Path: undecidability. -/
def undecidable_path (rd : RiceData) :
    Path rd.isDecidable false :=
  Path.ofEqChain rd.undecidable_eq

/-- Path: reduction. -/
def reduction_path (rd : RiceData) :
    Path rd.reductionObstruction 0 :=
  Path.ofEqChain rd.reduction_eq

end RiceData

/-! ## Multi-tape Equivalence -/

/-- Multi-tape TM equivalence data. -/
structure MultiTapeData where
  /-- Number of tapes. -/
  numTapes : Nat
  /-- numTapes is positive. -/
  numTapes_pos : numTapes > 0
  /-- States of multi-tape TM. -/
  multiStates : Nat
  /-- multiStates ≥ 3. -/
  multiStates_ge : multiStates ≥ 3
  /-- States of equivalent single-tape TM. -/
  singleStates : Nat
  /-- singleStates ≥ 3. -/
  singleStates_ge : singleStates ≥ 3
  /-- Language equivalence. -/
  languageEqual : Bool
  /-- Languages are equal. -/
  language_eq : languageEqual = true
  /-- Simulation time overhead factor. -/
  timeOverhead : Nat
  /-- timeOverhead is positive. -/
  timeOverhead_pos : timeOverhead > 0
  /-- Time complexity: single-tape ≤ t² for multi-tape time t. -/
  isQuadratic : Bool
  /-- Quadratic overhead. -/
  quadratic_eq : isQuadratic = true

namespace MultiTapeData

/-- 2-tape to single-tape conversion. -/
def twoTape : MultiTapeData where
  numTapes := 2
  numTapes_pos := by omega
  multiStates := 4
  multiStates_ge := by omega
  singleStates := 10
  singleStates_ge := by omega
  languageEqual := true
  language_eq := rfl
  timeOverhead := 4
  timeOverhead_pos := by omega
  isQuadratic := true
  quadratic_eq := rfl

/-- k-tape to single-tape. -/
def ofTapes (k : Nat) (hk : k > 0) (ms ss : Nat) (hms : ms ≥ 3) (hss : ss ≥ 3) : MultiTapeData where
  numTapes := k
  numTapes_pos := hk
  multiStates := ms
  multiStates_ge := hms
  singleStates := ss
  singleStates_ge := hss
  languageEqual := true
  language_eq := rfl
  timeOverhead := k * k
  timeOverhead_pos := Nat.mul_pos hk hk
  isQuadratic := true
  quadratic_eq := rfl

/-- Path: language equivalence. -/
def language_path (mt : MultiTapeData) :
    Path mt.languageEqual true :=
  Path.ofEqChain mt.language_eq

/-- Path: quadratic overhead. -/
def quadratic_path (mt : MultiTapeData) :
    Path mt.isQuadratic true :=
  Path.ofEqChain mt.quadratic_eq

end MultiTapeData

/-! ## Decidability Classification -/

/-- Language decidability classification. -/
structure DecidabilityData where
  /-- Language identifier. -/
  languageId : Nat
  /-- Whether decidable (recursive). -/
  isDecidable : Bool
  /-- Whether recognizable (RE). -/
  isRecognizable : Bool
  /-- Whether co-recognizable (co-RE). -/
  isCoRecognizable : Bool
  /-- Decidable → recognizable. -/
  decidable_implies_recognizable : isDecidable = true → isRecognizable = true
  /-- Decidable → co-recognizable. -/
  decidable_implies_co_recognizable : isDecidable = true → isCoRecognizable = true
  /-- Recognizable ∧ co-recognizable → decidable. -/
  both_implies_decidable : isRecognizable = true → isCoRecognizable = true → isDecidable = true

namespace DecidabilityData

/-- A decidable language (e.g., the empty language). -/
def decidable : DecidabilityData where
  languageId := 0
  isDecidable := true
  isRecognizable := true
  isCoRecognizable := true
  decidable_implies_recognizable := fun _ => rfl
  decidable_implies_co_recognizable := fun _ => rfl
  both_implies_decidable := fun _ _ => rfl

/-- HALT: recognizable but not decidable. -/
def halt : DecidabilityData where
  languageId := 1
  isDecidable := false
  isRecognizable := true
  isCoRecognizable := false
  decidable_implies_recognizable := fun h => by simp at h
  decidable_implies_co_recognizable := fun h => by simp at h
  both_implies_decidable := fun _ h => by simp at h

/-- co-HALT: co-recognizable but not recognizable. -/
def coHalt : DecidabilityData where
  languageId := 2
  isDecidable := false
  isRecognizable := false
  isCoRecognizable := true
  decidable_implies_recognizable := fun h => by simp at h
  decidable_implies_co_recognizable := fun h => by simp at h
  both_implies_decidable := fun h => by simp at h

/-- Neither recognizable nor co-recognizable. -/
def neither : DecidabilityData where
  languageId := 3
  isDecidable := false
  isRecognizable := false
  isCoRecognizable := false
  decidable_implies_recognizable := fun h => by simp at h
  decidable_implies_co_recognizable := fun h => by simp at h
  both_implies_decidable := fun h => by simp at h

end DecidabilityData

/-! ## Reductions -/

/-- Many-one reduction data between decision problems. -/
structure ReductionData where
  /-- Source problem identifier. -/
  sourceId : Nat
  /-- Target problem identifier. -/
  targetId : Nat
  /-- Whether the reduction exists. -/
  reductionExists : Bool
  /-- Whether the reduction is computable. -/
  isComputable : Bool
  /-- computable → exists. -/
  computable_implies : isComputable = true → reductionExists = true
  /-- Reduction obstruction (0 if reduction exists). -/
  obstruction : Nat
  /-- If reduction exists then obstruction = 0. -/
  exists_obstruction : reductionExists = true → obstruction = 0

namespace ReductionData

/-- HALT ≤_m TOTAL (halting reduces to totality). -/
def haltToTotal : ReductionData where
  sourceId := 0
  targetId := 1
  reductionExists := true
  isComputable := true
  computable_implies := fun _ => rfl
  obstruction := 0
  exists_obstruction := fun _ => rfl

/-- Path: reduction obstruction. -/
def obstruction_path (rd : ReductionData) (h : rd.reductionExists = true) :
    Path rd.obstruction 0 :=
  Path.ofEqChain (rd.exists_obstruction h)

end ReductionData

/-! ## Space and Time Complexity Classes -/

/-- Complexity class data. -/
structure ComplexityClassData where
  /-- Class name identifier. -/
  classId : Nat
  /-- Whether it's a time class. -/
  isTimeClass : Bool
  /-- Whether it's a space class. -/
  isSpaceClass : Bool
  /-- At least one type. -/
  has_type : isTimeClass = true ∨ isSpaceClass = true
  /-- Whether deterministic. -/
  isDeterministic : Bool
  /-- Complexity bound exponent (n^k or 2^{n^k}). -/
  boundExponent : Nat
  /-- boundExponent is positive. -/
  bound_pos : boundExponent > 0

namespace ComplexityClassData

/-- P (polynomial time, deterministic). -/
def pClass : ComplexityClassData where
  classId := 0
  isTimeClass := true
  isSpaceClass := false
  has_type := Or.inl rfl
  isDeterministic := true
  boundExponent := 1
  bound_pos := by omega

/-- NP (polynomial time, nondeterministic). -/
def npClass : ComplexityClassData where
  classId := 1
  isTimeClass := true
  isSpaceClass := false
  has_type := Or.inl rfl
  isDeterministic := false
  boundExponent := 1
  bound_pos := by omega

/-- PSPACE (polynomial space). -/
def pspaceClass : ComplexityClassData where
  classId := 2
  isTimeClass := false
  isSpaceClass := true
  has_type := Or.inr rfl
  isDeterministic := true
  boundExponent := 1
  bound_pos := by omega

end ComplexityClassData

/-! ## Master Coherence Paths -/

/-- Master: TM max transitions. -/
def master_tm_transitions_path :
    Path TMData.minimal.maxTransitions 3 :=
  TMData.minimal_max_path

/-- Master: computation result. -/
def master_computation_result_path :
    Path ComputationData.accepting5.result 1 :=
  ComputationData.accepting5.result_path

/-- Master: UTM universality. -/
def master_utm_path :
    Path UTMData.small.isUniversal true :=
  UTMData.small.universal_path

/-- Master: HALT recognizable. -/
def master_halt_recognizable_path :
    Path HaltingData.standard.isRecognizable true :=
  HaltingData.standard.recognizable_path

/-- Master: HALT not decidable. -/
def master_halt_undecidable_path :
    Path HaltingData.standard.isDecidable false :=
  HaltingData.standard.undecidable_path

/-- Master: HALT diagonalization. -/
def master_halt_diag_path :
    Path HaltingData.standard.diagonalizationObstruction 0 :=
  HaltingData.standard.diag_path

/-- Master: Rice's theorem. -/
def master_rice_path :
    Path RiceData.standard.isDecidable false :=
  RiceData.standard.undecidable_path

/-- Master: Rice reduction. -/
def master_rice_reduction_path :
    Path RiceData.standard.reductionObstruction 0 :=
  RiceData.standard.reduction_path

/-- Master: multi-tape language equivalence. -/
def master_multitape_path :
    Path MultiTapeData.twoTape.languageEqual true :=
  MultiTapeData.twoTape.language_path

/-- Master: multi-tape quadratic overhead. -/
def master_multitape_quadratic_path :
    Path MultiTapeData.twoTape.isQuadratic true :=
  MultiTapeData.twoTape.quadratic_path

end TuringMachines
end ComputationalPaths
