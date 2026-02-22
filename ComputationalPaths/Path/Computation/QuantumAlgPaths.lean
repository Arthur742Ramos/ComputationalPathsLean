/-
# Quantum Algorithms via Computational Paths

Deutsch-Jozsa, Grover search, quantum Fourier transform, phase estimation
modeled via computational paths.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Computation.QuantumAlgPaths

open ComputationalPaths.Path

/-! ## Oracle model -/

/-- An oracle on n bits is a Boolean function. -/
noncomputable def Oracle (n : Nat) := (Fin n → Bool) → Bool

/-- Constant oracle: always returns the given value. -/
@[simp] noncomputable def constOracle (n : Nat) (v : Bool) : Oracle n := fun _ => v

/-- An oracle is constant if it gives the same value for all inputs. -/
noncomputable def IsConstant {n : Nat} (f : Oracle n) : Prop :=
  ∀ x y : Fin n → Bool, f x = f y

/-! ## Deutsch-Jozsa algorithm (1-bit case) -/

/-- Deutsch-Jozsa output: determines if oracle is constant or balanced. -/
@[simp] noncomputable def deutschJozsa1 (f : Oracle 1) : Bool :=
  xor (f (fun _ => false)) (f (fun _ => true))

/-- If DJ output is false, oracle gives same output on both inputs. -/
theorem dj1_false_means_constant (f : Oracle 1) :
    deutschJozsa1 f = false → f (fun _ => false) = f (fun _ => true) := by
  intro h
  simp [deutschJozsa1] at h
  cases hf : f (fun _ => false) <;> cases hg : f (fun _ => true) <;> simp_all

/-- Constant oracle always gives DJ = false. -/
theorem dj1_constant_false (v : Bool) :
    deutschJozsa1 (constOracle 1 v) = false := by
  cases v <;> rfl

noncomputable def dj1_constant_path (v : Bool) :
    Path (deutschJozsa1 (constOracle 1 v)) false :=
  Path.mk [Step.mk _ _ (dj1_constant_false v)] (dj1_constant_false v)

/-! ## Grover search -/

/-- A search problem: oracle on finite domain. -/
structure SearchProblem where
  size : Nat
  oracle : Fin size → Bool

/-- Check if a search problem has a solution. -/
noncomputable def hasSolution (sp : SearchProblem) : Prop :=
  ∃ i, sp.oracle i = true

/-- Grover iteration state. -/
structure GroverState where
  iteration : Nat
  found : Bool
deriving DecidableEq, Repr

@[simp] noncomputable def groverInit : GroverState := ⟨0, false⟩

@[simp] noncomputable def groverStep (gs : GroverState) (success : Bool) : GroverState :=
  ⟨gs.iteration + 1, gs.found || success⟩

/-- Optimal number of Grover iterations (simplified). -/
@[simp] noncomputable def optimalIterations (n : Nat) : Nat :=
  if n ≤ 1 then 1
  else if n ≤ 4 then 1
  else if n ≤ 16 then 2
  else n / 4

/-! ## Quantum Fourier Transform -/

/-- QFT on n qubits: modeled as identity permutation. -/
@[simp] noncomputable def qftPerm (n : Nat) (k : Fin (2^n)) : Fin (2^n) := k

/-- Inverse QFT. -/
@[simp] noncomputable def iqftPerm (n : Nat) (k : Fin (2^n)) : Fin (2^n) := k

/-- Phase estimation output. -/
structure PhaseEstimate where
  numerator : Nat
  precision : Nat
deriving DecidableEq, Repr

@[simp] noncomputable def phaseZero : PhaseEstimate := ⟨0, 1⟩
@[simp] noncomputable def phaseHalf : PhaseEstimate := ⟨1, 1⟩

/-! ## Core theorems -/

-- 1. Constant oracle is indeed constant
theorem constOracle_isConstant (n : Nat) (v : Bool) :
    IsConstant (constOracle n v) :=
  fun _ _ => rfl

noncomputable def constOracle_path (n : Nat) (v : Bool) (x y : Fin n → Bool) :
    Path (constOracle n v x) (constOracle n v y) :=
  Path.mk [Step.mk _ _ (constOracle_isConstant n v x y)]
    (constOracle_isConstant n v x y)

-- 2. DJ on constant oracle gives false
theorem dj_constant (v : Bool) : deutschJozsa1 (constOracle 1 v) = false := by
  cases v <;> rfl

-- 3. Grover starts at iteration 0
theorem grover_init_iter : groverInit.iteration = 0 := rfl

-- 4. Grover step increments iteration
theorem grover_step_iter (gs : GroverState) (s : Bool) :
    (groverStep gs s).iteration = gs.iteration + 1 := rfl

-- 5. Grover found is monotone
theorem grover_found_monotone (gs : GroverState) (s : Bool) :
    gs.found = true → (groverStep gs s).found = true := by
  intro h; simp [h]

noncomputable def grover_found_path (gs : GroverState) (s : Bool) (h : gs.found = true) :
    Path (groverStep gs s).found true :=
  Path.mk [Step.mk _ _ (grover_found_monotone gs s h)] (grover_found_monotone gs s h)

-- 6. Grover with success finds
theorem grover_success (gs : GroverState) :
    (groverStep gs true).found = true := by simp

-- 7. QFT followed by inverse is identity
theorem qft_iqft (n : Nat) (k : Fin (2^n)) :
    iqftPerm n (qftPerm n k) = k := rfl

noncomputable def qft_iqft_path (n : Nat) (k : Fin (2^n)) :
    Path (iqftPerm n (qftPerm n k)) k :=
  Path.mk [Step.mk _ _ (qft_iqft n k)] (qft_iqft n k)

-- 8. QFT∘IQFT = id
theorem qft_iqft_comp (n : Nat) :
    iqftPerm n ∘ qftPerm n = id := by funext k; rfl

noncomputable def qft_iqft_comp_path (n : Nat) :
    Path (iqftPerm n ∘ qftPerm n) id :=
  Path.mk [Step.mk _ _ (qft_iqft_comp n)] (qft_iqft_comp n)

-- 9. CongrArg through DJ
noncomputable def dj_congrArg {f g : Oracle 1} (p : Path f g) :
    Path (deutschJozsa1 f) (deutschJozsa1 g) :=
  Path.congrArg deutschJozsa1 p

-- 10. CongrArg through grover step
noncomputable def groverStep_congrArg {gs1 gs2 : GroverState} (s : Bool) (p : Path gs1 gs2) :
    Path (groverStep gs1 s) (groverStep gs2 s) :=
  Path.congrArg (fun gs => groverStep gs s) p

-- 11. Grover n-step composition
noncomputable def groverNSteps : (n : Nat) → (Fin n → Bool) → GroverState
  | 0, _ => groverInit
  | n + 1, successes =>
    groverStep (groverNSteps n (fun i => successes ⟨i.val, by omega⟩))
               (successes ⟨n, by omega⟩)

-- 12. Grover n-step iteration count
theorem groverNSteps_iter : (n : Nat) → (successes : Fin n → Bool) →
    (groverNSteps n successes).iteration = n
  | 0, _ => rfl
  | n + 1, successes => by
    simp [groverNSteps, groverStep]
    exact groverNSteps_iter n _

noncomputable def groverNSteps_path (n : Nat) (successes : Fin n → Bool) :
    Path (groverNSteps n successes).iteration n :=
  Path.mk [Step.mk _ _ (groverNSteps_iter n successes)]
    (groverNSteps_iter n successes)

-- 13. If any success in Grover, final state is found
theorem groverNSteps_any_success : (n : Nat) → (successes : Fin n → Bool) →
    (i : Fin n) → successes i = true →
    (groverNSteps n successes).found = true
  | 0, _, i, _ => absurd i.isLt (by omega)
  | n + 1, successes, i, hi => by
    simp [groverNSteps, groverStep]
    by_cases h : i.val < n
    · left
      exact groverNSteps_any_success n _ ⟨i.val, h⟩ (by simp; exact hi)
    · right
      have heq : i.val = n := by omega
      have : successes ⟨n, by omega⟩ = true := by
        have : i = ⟨n, by omega⟩ := by ext; exact heq
        rw [← this]; exact hi
      exact this

-- 14. Optimal iterations for size 1
theorem optimal_iter_1 : optimalIterations 1 = 1 := by rfl

-- 15. Optimal iterations for size 4
theorem optimal_iter_4 : optimalIterations 4 = 1 := by rfl

-- 16. Transport along grover path
theorem transport_grover :
    Path.transport (D := fun _ => Bool)
      (groverNSteps_path 3 (fun _ => false)) true = true := by
  simp [Path.transport]

-- 17. DJ symmetry for two constant oracles
theorem dj_constant_both :
    deutschJozsa1 (constOracle 1 true) = deutschJozsa1 (constOracle 1 false) := rfl

noncomputable def dj_constant_both_path :
    Path (deutschJozsa1 (constOracle 1 true)) (deutschJozsa1 (constOracle 1 false)) :=
  Path.mk [Step.mk _ _ dj_constant_both] dj_constant_both

-- 18. Path from DJ result to false for constant oracle
noncomputable def dj_to_false_path (v : Bool) :
    Path (deutschJozsa1 (constOracle 1 v)) false :=
  Path.mk [Step.mk _ _ (dj_constant v)] (dj_constant v)

-- 19. Step construction for DJ
noncomputable def dj_step (v : Bool) : Step Bool :=
  ⟨deutschJozsa1 (constOracle 1 v), false, dj_constant v⟩

-- 20. Grover init is not found
theorem grover_init_not_found : groverInit.found = false := rfl

-- 21. Composition of DJ paths
noncomputable def dj_trans_path :
    Path (deutschJozsa1 (constOracle 1 true)) false :=
  Path.trans dj_constant_both_path (dj_to_false_path false)

-- 22. Path coherence for quantum algorithms
theorem qalg_path_coherence {a b : Bool} (p q : Path a b) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

-- 23. Symm of QFT path
theorem qft_path_symm (n : Nat) (k : Fin (2^n)) :
    Path.symm (qft_iqft_path n k) =
      Path.mk [Step.mk _ _ (qft_iqft n k).symm] (qft_iqft n k).symm := rfl

-- 24. Phase estimate zero
theorem phase_zero_num : phaseZero.numerator = 0 := rfl

-- 25. Search problem with marked element has solution
theorem single_marked_has_solution (n : Nat) (pos : Fin n) :
    hasSolution ⟨n, fun i => decide (i = pos)⟩ := by
  exact ⟨pos, by simp⟩

-- 26. Grover composition preserves path structure
noncomputable def grover_compose_path {gs1 gs2 : GroverState} (s : Bool)
    (p : Path gs1 gs2) :
    Path (groverStep gs1 s) (groverStep gs2 s) :=
  Path.congrArg (fun gs => groverStep gs s) p

end ComputationalPaths.Path.Computation.QuantumAlgPaths
