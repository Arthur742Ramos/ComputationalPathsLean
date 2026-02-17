/-
# Markov Chains as Path Systems

This module models Markov chains using computational paths:
transition matrices, Chapman-Kolmogorov as path composition,
stationary distributions, ergodicity aspects, absorbing states,
and detailed balance.

## References

- Norris, "Markov Chains"
- Levin, Peres & Wilmer, "Markov Chains and Mixing Times"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace MarkovPaths

universe u v

open ComputationalPaths.Path

/-! ## States and Transitions -/

/-- A finite state space with transition data. -/
structure StateSpace (S : Type u) where
  states : List S

/-- Transition data: transition probability from state i to state j. -/
structure TransData (S : Type u) where
  from_state : S
  to_state : S
  weight : Nat

/-- A transition matrix as a function on state pairs. -/
structure TransMatrix (S : Type u) where
  trans : S → S → Nat
  stateSpace : StateSpace S

/-- Two transition matrices are equal when they agree on all pairs. -/
def transMatEquiv {S : Type u} (m1 m2 : TransMatrix S) : Prop :=
  ∀ i j : S, m1.trans i j = m2.trans i j

/-- Transition matrix equivalence is reflexive. -/
theorem transMatEquiv_refl {S : Type u} (m : TransMatrix S) :
    transMatEquiv m m :=
  fun _ _ => rfl

/-- Transition matrix equivalence is symmetric. -/
theorem transMatEquiv_symm {S : Type u}
    {m1 m2 : TransMatrix S} (h : transMatEquiv m1 m2) :
    transMatEquiv m2 m1 :=
  fun i j => (h i j).symm

/-- Transition matrix equivalence is transitive. -/
theorem transMatEquiv_trans {S : Type u}
    {m1 m2 m3 : TransMatrix S}
    (h1 : transMatEquiv m1 m2) (h2 : transMatEquiv m2 m3) :
    transMatEquiv m1 m3 :=
  fun i j => (h1 i j).trans (h2 i j)

/-! ## Chapman-Kolmogorov as Path Composition -/

/-- Chapman-Kolmogorov data: P^(n+m)(i,j) = Σ_k P^n(i,k)·P^m(k,j). -/
structure ChapmanKolmogorov (S : Type u) where
  state_i : S
  state_j : S
  probNM : Nat       -- P^(n+m)(i,j)
  sumOverK : Nat     -- Σ_k P^n(i,k)·P^m(k,j)
  ckPath : Path probNM sumOverK

/-- Chapman-Kolmogorov path trans refl. -/
theorem ck_trans_refl {S : Type u} (d : ChapmanKolmogorov S) :
    Path.trans d.ckPath (Path.refl d.sumOverK) = d.ckPath := by
  simp

/-- Chapman-Kolmogorov path refl trans. -/
theorem ck_refl_trans {S : Type u} (d : ChapmanKolmogorov S) :
    Path.trans (Path.refl d.probNM) d.ckPath = d.ckPath := by
  simp

/-- Chapman-Kolmogorov path associativity. -/
theorem ck_assoc {S : Type u} (d : ChapmanKolmogorov S)
    {c : Nat} (q : Path d.sumOverK c) :
    Path.trans (Path.trans d.ckPath q) (Path.refl c) =
    Path.trans d.ckPath q := by
  simp

/-- RwEq: CK path trans refl. -/
theorem ck_rweq_trans_refl {S : Type u} (d : ChapmanKolmogorov S) :
    RwEq
      (Path.trans d.ckPath (Path.refl d.sumOverK))
      d.ckPath :=
  rweq_of_step (Step.trans_refl_right d.ckPath)

/-- RwEq: CK path refl trans. -/
theorem ck_rweq_refl_trans {S : Type u} (d : ChapmanKolmogorov S) :
    RwEq
      (Path.trans (Path.refl d.probNM) d.ckPath)
      d.ckPath :=
  rweq_of_step (Step.trans_refl_left d.ckPath)

/-- RwEq: CK path inv cancel right. -/
theorem ck_rweq_inv_right {S : Type u} (d : ChapmanKolmogorov S) :
    RwEq
      (Path.trans d.ckPath (Path.symm d.ckPath))
      (Path.refl d.probNM) :=
  rweq_cmpA_inv_right d.ckPath

/-- RwEq: CK path inv cancel left. -/
theorem ck_rweq_inv_left {S : Type u} (d : ChapmanKolmogorov S) :
    RwEq
      (Path.trans (Path.symm d.ckPath) d.ckPath)
      (Path.refl d.sumOverK) :=
  rweq_cmpA_inv_left d.ckPath

/-- RwEq: CK path symm_symm. -/
theorem ck_rweq_symm_symm {S : Type u} (d : ChapmanKolmogorov S) :
    RwEq
      (Path.symm (Path.symm d.ckPath))
      d.ckPath :=
  rweq_of_step (Step.symm_symm d.ckPath)

/-! ## Stationary Distributions -/

/-- Stationary distribution data: πP = π. -/
structure StationaryData (S : Type u) where
  distribution : S → Nat
  matrix : TransMatrix S
  stateVal : S
  piTimesP : Nat    -- (πP)(s)
  piVal : Nat       -- π(s)
  stationaryPath : Path piTimesP piVal

/-- Stationary path trans refl. -/
theorem stationary_trans_refl {S : Type u} (d : StationaryData S) :
    Path.trans d.stationaryPath (Path.refl d.piVal) = d.stationaryPath := by
  simp

/-- RwEq: stationary path trans refl. -/
theorem stationary_rweq_trans_refl {S : Type u} (d : StationaryData S) :
    RwEq
      (Path.trans d.stationaryPath (Path.refl d.piVal))
      d.stationaryPath :=
  rweq_of_step (Step.trans_refl_right d.stationaryPath)

/-- RwEq: stationary inv cancel right. -/
theorem stationary_rweq_inv_right {S : Type u} (d : StationaryData S) :
    RwEq
      (Path.trans d.stationaryPath (Path.symm d.stationaryPath))
      (Path.refl d.piTimesP) :=
  rweq_cmpA_inv_right d.stationaryPath

/-- RwEq: stationary symm_symm. -/
theorem stationary_rweq_symm_symm {S : Type u} (d : StationaryData S) :
    RwEq
      (Path.symm (Path.symm d.stationaryPath))
      d.stationaryPath :=
  rweq_of_step (Step.symm_symm d.stationaryPath)

/-! ## Absorbing States -/

/-- Absorbing state data: P(s,s) = 1 (full weight). -/
structure AbsorbingData (S : Type u) where
  absState : S
  selfWeight : Nat
  totalWeight : Nat
  absorbPath : Path selfWeight totalWeight

/-- Absorbing path trans refl. -/
theorem absorb_trans_refl {S : Type u} (d : AbsorbingData S) :
    Path.trans d.absorbPath (Path.refl d.totalWeight) = d.absorbPath := by
  simp

/-- RwEq: absorbing inv cancel. -/
theorem absorb_rweq_inv_right {S : Type u} (d : AbsorbingData S) :
    RwEq
      (Path.trans d.absorbPath (Path.symm d.absorbPath))
      (Path.refl d.selfWeight) :=
  rweq_cmpA_inv_right d.absorbPath

/-- RwEq: absorbing trans refl. -/
theorem absorb_rweq_trans_refl {S : Type u} (d : AbsorbingData S) :
    RwEq
      (Path.trans d.absorbPath (Path.refl d.totalWeight))
      d.absorbPath :=
  rweq_of_step (Step.trans_refl_right d.absorbPath)

/-! ## Detailed Balance -/

/-- Detailed balance: π(i)P(i,j) = π(j)P(j,i). -/
structure DetailedBalance (S : Type u) where
  state_i : S
  state_j : S
  piI_Pij : Nat
  piJ_Pji : Nat
  balancePath : Path piI_Pij piJ_Pji

/-- Detailed balance trans refl. -/
theorem balance_trans_refl {S : Type u} (d : DetailedBalance S) :
    Path.trans d.balancePath (Path.refl d.piJ_Pji) = d.balancePath := by
  simp

/-- Detailed balance symmetry. -/
def balance_reverse {S : Type u} (d : DetailedBalance S) :
    Path d.piJ_Pji d.piI_Pij :=
  Path.symm d.balancePath

/-- RwEq: balance inv cancel right. -/
theorem balance_rweq_inv_right {S : Type u} (d : DetailedBalance S) :
    RwEq
      (Path.trans d.balancePath (Path.symm d.balancePath))
      (Path.refl d.piI_Pij) :=
  rweq_cmpA_inv_right d.balancePath

/-- RwEq: balance inv cancel left. -/
theorem balance_rweq_inv_left {S : Type u} (d : DetailedBalance S) :
    RwEq
      (Path.trans (Path.symm d.balancePath) d.balancePath)
      (Path.refl d.piJ_Pji) :=
  rweq_cmpA_inv_left d.balancePath

/-- RwEq: balance symm_symm. -/
theorem balance_rweq_symm_symm {S : Type u} (d : DetailedBalance S) :
    RwEq
      (Path.symm (Path.symm d.balancePath))
      d.balancePath :=
  rweq_of_step (Step.symm_symm d.balancePath)

/-! ## Ergodicity Aspects -/

/-- Ergodic convergence: P^n(i,j) → π(j). -/
structure ErgodicData (S : Type u) where
  state_i : S
  state_j : S
  probN : Nat       -- P^n(i,j) for large n
  piJ : Nat         -- π(j)
  convergePath : Path probN piJ

/-- RwEq: ergodic convergence trans refl. -/
theorem ergodic_rweq_trans_refl {S : Type u} (d : ErgodicData S) :
    RwEq
      (Path.trans d.convergePath (Path.refl d.piJ))
      d.convergePath :=
  rweq_of_step (Step.trans_refl_right d.convergePath)

/-- RwEq: ergodic inv cancel. -/
theorem ergodic_rweq_inv_right {S : Type u} (d : ErgodicData S) :
    RwEq
      (Path.trans d.convergePath (Path.symm d.convergePath))
      (Path.refl d.probN) :=
  rweq_cmpA_inv_right d.convergePath

/-! ## CongrArg and Transport -/

/-- CongrArg for transition matrix. -/
theorem trans_congrArg {S : Type u} (m : TransMatrix S) (i : S)
    {j1 j2 : S} (h : j1 = j2) : m.trans i j1 = m.trans i j2 :=
  _root_.congrArg (m.trans i) h

/-- Path from congrArg on transitions. -/
def trans_congrArg_path {S : Type u} (m : TransMatrix S) (i : S)
    {j1 j2 : S} (h : j1 = j2) : Path (m.trans i j1) (m.trans i j2) :=
  Path.mk [Step.mk _ _ (_root_.congrArg (m.trans i) h)] (_root_.congrArg (m.trans i) h)

/-- Transport for state-indexed data. -/
def state_transport {S : Type u} {P : S → Type v}
    {s1 s2 : S} (h : s1 = s2) (x : P s1) : P s2 :=
  Path.transport (Path.mk [Step.mk _ _ h] h) x

/-- Transport along refl is identity. -/
theorem state_transport_refl {S : Type u} {P : S → Type v}
    (s : S) (x : P s) :
    state_transport (rfl : s = s) x = x := rfl

/-! ## Path Composition for Multi-step Transitions -/

/-- Compose two transition paths. -/
def multi_step_path {a b c : Nat}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Multi-step composition is associative. -/
theorem multi_step_assoc {a b c d : Nat}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by
  simp

/-! ## Trivial Instances -/

/-- Trivial state space on Bool. -/
def trivialStateSpace : StateSpace Bool where
  states := [true, false]

/-- Trivial transition matrix. -/
def trivialTransMatrix : TransMatrix Bool where
  trans := fun _ _ => 1
  stateSpace := trivialStateSpace

/-- Trivial Chapman-Kolmogorov data. -/
def trivialCK : ChapmanKolmogorov Bool where
  state_i := true
  state_j := false
  probNM := 2
  sumOverK := 2
  ckPath := Path.refl 2

/-- Trivial stationary data. -/
def trivialStationary : StationaryData Bool where
  distribution := fun _ => 1
  matrix := trivialTransMatrix
  stateVal := true
  piTimesP := 1
  piVal := 1
  stationaryPath := Path.refl 1

/-- Trivial detailed balance. -/
def trivialBalance : DetailedBalance Bool where
  state_i := true
  state_j := false
  piI_Pij := 1
  piJ_Pji := 1
  balancePath := Path.refl 1

end MarkovPaths
end Computation
end Path
end ComputationalPaths
