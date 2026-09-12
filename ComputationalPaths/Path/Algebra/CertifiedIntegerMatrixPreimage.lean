import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Data.Int.DivMod

/-!
# Certificate-driven preimages of integer matrices

The executable layer accepts a finite integer certificate, not an oracle for
Smith normal form. Invalid certificates are rejected. There is no claimed
running-time bound for a certificate producer.
-/

namespace ComputationalPaths.Path.Algebra.CertifiedIntegerMatrixPreimage

open Matrix
open scoped BigOperators

abbrev Vec (n : ℕ) := Fin n → ℤ
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℤ

/-- A diagonal image presentation. `T` is the integral quotient of `L*A`
by the row moduli. `R` lifts divisible target coordinates. No divisibility
ordering or positivity of the moduli is needed. Zero moduli encode equations. -/
structure Certificate (m n : ℕ) where
  L : Mat m m
  Linv : Mat m m
  R : Mat n m
  T : Mat m n
  d : Vec m

def Certificate.Valid {m n : ℕ} (c : Certificate m n) (A : Mat m n) : Prop :=
  c.Linv * c.L = 1 ∧
  c.L * A = diagonal c.d * c.T ∧
  c.L * A * c.R = diagonal c.d ∧
  ∀ i, c.d i = 0 → ∀ j, c.T i j = 0

instance {m n : ℕ} (c : Certificate m n) (A : Mat m n) :
    Decidable (c.Valid A) := by
  unfold Certificate.Valid
  letI : Decidable (c.Linv * c.L = 1) := inferInstance
  letI : Decidable (c.L * A = diagonal c.d * c.T) := inferInstance
  letI : Decidable (c.L * A * c.R = diagonal c.d) := inferInstance
  letI : Decidable (∀ i, c.d i = 0 → ∀ j, c.T i j = 0) := by
    letI : DecidablePred (fun i : Fin m => c.d i = 0 → ∀ j, c.T i j = 0) :=
      fun i => by
        letI : DecidablePred (fun j : Fin n => c.T i j = 0) := fun _ => inferInstance
        infer_instance
    exact Nat.decidableForallFin _
  infer_instance

def Certificate.transformed {m n : ℕ} (c : Certificate m n) (z : Vec m) : Vec m :=
  c.L.mulVec z

def Certificate.Feasible {m n : ℕ} (c : Certificate m n) (z : Vec m) : Prop :=
  ∀ i, c.d i ∣ c.transformed z i

instance {m n : ℕ} (c : Certificate m n) (z : Vec m) :
    Decidable (c.Feasible z) :=
  inferInstanceAs (Decidable (∀ i : Fin m, c.d i ∣ c.transformed z i))

def Certificate.candidate {m n : ℕ} (c : Certificate m n) (z : Vec m) : Vec n :=
  c.R.mulVec (fun i => c.transformed z i / c.d i)

/-- A finite generating matrix for the entire integer kernel, not necessarily
an independent basis. -/
def Certificate.kernelGenerator {m n : ℕ} (c : Certificate m n) : Mat n n :=
  1 - c.R * c.T

theorem Certificate.left_injective {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) : Function.Injective c.L.mulVec := by
  intro x y hxy
  have := congrArg c.Linv.mulVec hxy
  simpa only [mulVec_mulVec, h.1, one_mulVec] using this

theorem Certificate.necessary {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (x : Vec n) : c.Feasible (A.mulVec x) := by
  intro i
  change c.d i ∣ (c.L.mulVec (A.mulVec x)) i
  rw [mulVec_mulVec, h.2.1, ← mulVec_mulVec, mulVec_diagonal]
  exact dvd_mul_right _ _

theorem Certificate.candidate_correct {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (z : Vec m) (hz : c.Feasible z) :
    A.mulVec (c.candidate z) = z := by
  apply c.left_injective A h
  change c.L.mulVec (A.mulVec (c.R.mulVec _)) = c.L.mulVec z
  rw [mulVec_mulVec, mulVec_mulVec, h.2.2.1]
  funext i
  rw [mulVec_diagonal]
  exact Int.mul_ediv_cancel' (hz i)

theorem Certificate.feasible_iff {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (z : Vec m) :
    c.Feasible z ↔ ∃ x, A.mulVec x = z := by
  constructor
  · intro hz
    exact ⟨c.candidate z, c.candidate_correct A h z hz⟩
  · rintro ⟨x, rfl⟩
    exact c.necessary A h x

theorem Certificate.obstruction {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (z : Vec m) (i : Fin m)
    (hi : ¬ c.d i ∣ c.transformed z i) : ¬ ∃ x, A.mulVec x = z := by
  intro hx
  exact hi ((c.feasible_iff A h z).mpr hx i)

theorem Certificate.kernel_T {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (x : Vec n) (hx : A.mulVec x = 0) :
    c.T.mulVec x = 0 := by
  have heq : (diagonal c.d).mulVec (c.T.mulVec x) = 0 := by
    rw [mulVec_mulVec, ← h.2.1, ← mulVec_mulVec, hx, mulVec_zero]
  funext i
  by_cases hi : c.d i = 0
  · simp [mulVec, dotProduct, h.2.2.2 i hi]
  · have hei := congrFun heq i
    rw [mulVec_diagonal] at hei
    exact (mul_eq_zero.mp hei).resolve_left hi

theorem Certificate.kernelGenerator_correct {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (v : Vec n) :
    A.mulVec (c.kernelGenerator.mulVec v) = 0 := by
  apply c.left_injective A h
  simp only [kernelGenerator, sub_mulVec, one_mulVec, mulVec_sub, mulVec_zero]
  rw [mulVec_mulVec, mulVec_mulVec, mulVec_mulVec,
    ← Matrix.mul_assoc (c.L * A) c.R c.T, h.2.2.1, ← h.2.1, sub_self]

theorem Certificate.kernelGenerator_complete {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (x : Vec n) (hx : A.mulVec x = 0) :
    c.kernelGenerator.mulVec x = x := by
  simp only [kernelGenerator, sub_mulVec, one_mulVec, ← mulVec_mulVec,
    c.kernel_T A h x hx, mulVec_zero, sub_zero]

/-- The computed kernel generator is an integral projection, not merely a list
of vectors that happen to lie in the kernel. -/
theorem Certificate.kernelGenerator_idempotent {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) :
    c.kernelGenerator * c.kernelGenerator = c.kernelGenerator := by
  apply Matrix.ext_of_mulVec_single
  intro j
  rw [← mulVec_mulVec]
  exact c.kernelGenerator_complete A h _ (c.kernelGenerator_correct A h _)

theorem Certificate.kernel_iff {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (x : Vec n) :
    A.mulVec x = 0 ↔ ∃ v, c.kernelGenerator.mulVec v = x := by
  constructor
  · intro hx
    exact ⟨x, c.kernelGenerator_complete A h x hx⟩
  · rintro ⟨v, rfl⟩
    exact c.kernelGenerator_correct A h v

/-- All solutions are an explicitly generated affine integer lattice. -/
theorem Certificate.all_solutions {m n : ℕ} (c : Certificate m n)
    (A : Mat m n) (h : c.Valid A) (z : Vec m) (hz : c.Feasible z) (x : Vec n) :
    A.mulVec x = z ↔ ∃ v, x = c.candidate z + c.kernelGenerator.mulVec v := by
  have hx0 := c.candidate_correct A h z hz
  constructor
  · intro hx
    refine ⟨x - c.candidate z, ?_⟩
    have hk : A.mulVec (x - c.candidate z) = 0 := by
      rw [mulVec_sub, hx, hx0, sub_self]
    rw [c.kernelGenerator_complete A h _ hk, add_sub_cancel]
  · rintro ⟨v, rfl⟩
    rw [mulVec_add, hx0, c.kernelGenerator_correct A h v, add_zero]

/-- The first failed row is an explicit divisibility or zero-row obstruction. -/
def Certificate.firstFailure {m n : ℕ} (c : Certificate m n) (z : Vec m) :
    Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (¬ c.d i ∣ c.transformed z i))

theorem Certificate.firstFailure_none {m n : ℕ} (c : Certificate m n) (z : Vec m) :
    c.firstFailure z = none ↔ c.Feasible z := by
  simp [firstFailure, List.find?_eq_none, Feasible]

theorem Certificate.firstFailure_some {m n : ℕ} (c : Certificate m n) (z : Vec m)
    (i : Fin m) (hi : c.firstFailure z = some i) :
    ¬ c.d i ∣ c.transformed z i := by
  have hf := List.find?_some (p := fun j => decide (¬ c.d j ∣ c.transformed z j)) hi
  exact of_decide_eq_true hf

inductive Outcome (m n : ℕ) where
  | invalid
  | solved (x : Vec n)
  | obstructed (row : Fin m)
  deriving DecidableEq

/-- A total executable checker/solver. `invalid` is never a mathematical
nonexistence answer. A valid certificate always gives a witness or obstruction. -/
def solve {m n : ℕ} (A : Mat m n) (c : Certificate m n) (z : Vec m) : Outcome m n :=
  if c.Valid A then
    match c.firstFailure z with
    | none => .solved (c.candidate z)
    | some i => .obstructed i
  else .invalid

def Outcome.Correct {m n : ℕ} (A : Mat m n) (c : Certificate m n) (z : Vec m) :
    Outcome m n → Prop
  | .invalid => ¬ c.Valid A
  | .solved x => c.Valid A ∧ A.mulVec x = z ∧
      ∀ y, A.mulVec y = z ↔ ∃ v, y = x + c.kernelGenerator.mulVec v
  | .obstructed i => c.Valid A ∧ ¬ c.d i ∣ c.transformed z i ∧
      ¬ ∃ x, A.mulVec x = z

theorem solve_correct {m n : ℕ} (A : Mat m n) (c : Certificate m n) (z : Vec m) :
    (solve A c z).Correct A c z := by
  unfold solve
  split
  · rename_i h
    split
    · rename_i hf
      have hz := (c.firstFailure_none z).mp hf
      exact ⟨h, c.candidate_correct A h z hz, c.all_solutions A h z hz⟩
    · rename_i i hf
      have hi := c.firstFailure_some z i hf
      exact ⟨h, hi, c.obstruction A h z i hi⟩
  · assumption

end ComputationalPaths.Path.Algebra.CertifiedIntegerMatrixPreimage
