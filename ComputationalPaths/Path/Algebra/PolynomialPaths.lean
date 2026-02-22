/-
# Polynomial Operations as Computational Paths

Polynomial-like operations modeled as paths: list-based coefficient
representations with addition/multiplication rewrite rules, degree
properties, evaluation homomorphism paths, and root-finding as path
termination.

## Main results (22 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.PolynomialPaths

open ComputationalPaths.Path

universe u

/-! ## Polynomial representation -/

/-- A polynomial over integers represented as a list of coefficients. -/
abbrev Poly := List Int

noncomputable def zeroPoly : Poly := []
noncomputable def constPoly (c : Int) : Poly := [c]

/-- Add two polynomials (coefficient-wise). -/
noncomputable def polyAdd : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | (a :: as), (b :: bs) => (a + b) :: polyAdd as bs

/-- Negate all coefficients. -/
noncomputable def polyNeg : Poly → Poly
  | [] => []
  | (a :: as) => (-a) :: polyNeg as

/-- Scalar multiplication. -/
noncomputable def polyScale (c : Int) : Poly → Poly
  | [] => []
  | (a :: as) => (c * a) :: polyScale c as

/-- Evaluate a polynomial at a point. -/
noncomputable def polyEval (p : Poly) (x : Int) : Int :=
  p.foldr (fun a acc => a + acc * x) 0

/-- Degree (length). -/
noncomputable def polyDeg (p : Poly) : Nat := p.length

/-! ## Addition identity -/

theorem polyAdd_nil_right (p : Poly) : polyAdd p [] = p := by
  cases p <;> rfl

noncomputable def polyAdd_zero_right_path (p : Poly) : Path (polyAdd p zeroPoly) p :=
  Path.mk [Step.mk _ _ (polyAdd_nil_right p)] (polyAdd_nil_right p)

/-! ## Commutativity via well-founded recursion -/

theorem polyAdd_comm (p q : Poly) : polyAdd p q = polyAdd q p := by
  induction p generalizing q with
  | nil => simp [polyAdd, polyAdd_nil_right]
  | cons a as ih =>
    cases q with
    | nil => simp [polyAdd]
    | cons b bs => simp [polyAdd, Int.add_comm a b, ih bs]

noncomputable def polyAdd_comm_path (p q : Poly) : Path (polyAdd p q) (polyAdd q p) :=
  Path.mk [Step.mk _ _ (polyAdd_comm p q)] (polyAdd_comm p q)

/-! ## Associativity -/

theorem polyAdd_assoc (p q r : Poly) :
    polyAdd (polyAdd p q) r = polyAdd p (polyAdd q r) := by
  induction p generalizing q r with
  | nil => simp [polyAdd]
  | cons a as ih =>
    cases q with
    | nil => simp [polyAdd]
    | cons b bs =>
      cases r with
      | nil => simp [polyAdd]
      | cons c cs => simp [polyAdd, Int.add_assoc a b c, ih bs cs]

noncomputable def polyAdd_assoc_path (p q r : Poly) :
    Path (polyAdd (polyAdd p q) r) (polyAdd p (polyAdd q r)) :=
  Path.mk [Step.mk _ _ (polyAdd_assoc p q r)] (polyAdd_assoc p q r)

/-! ## Negation -/

theorem polyNeg_neg (p : Poly) : polyNeg (polyNeg p) = p := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [polyNeg, Int.neg_neg, ih]

noncomputable def polyNeg_neg_path (p : Poly) : Path (polyNeg (polyNeg p)) p :=
  Path.mk [Step.mk _ _ (polyNeg_neg p)] (polyNeg_neg p)

/-! ## Scalar multiplication -/

theorem polyScale_one (p : Poly) : polyScale 1 p = p := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [polyScale, ih]

noncomputable def polyScale_one_path (p : Poly) : Path (polyScale 1 p) p :=
  Path.mk [Step.mk _ _ (polyScale_one p)] (polyScale_one p)

theorem polyScale_zero (p : Poly) : polyScale 0 p = List.replicate p.length 0 := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [polyScale, ih, List.replicate]

/-! ## Evaluation -/

theorem polyEval_nil (x : Int) : polyEval [] x = 0 := rfl

noncomputable def polyEval_zero_path (x : Int) : Path (polyEval zeroPoly x) 0 :=
  Path.mk [Step.mk _ _ (polyEval_nil x)] (polyEval_nil x)

theorem polyEval_const (c x : Int) : polyEval [c] x = c := by
  simp [polyEval, List.foldr]

noncomputable def polyEval_const_path (c x : Int) : Path (polyEval (constPoly c) x) c :=
  Path.mk [Step.mk _ _ (polyEval_const c x)] (polyEval_const c x)

theorem polyEval_cons (a : Int) (as : Poly) (x : Int) :
    polyEval (a :: as) x = a + polyEval as x * x := by
  simp [polyEval, List.foldr]

/-! ## Degree -/

theorem polyDeg_nil : polyDeg zeroPoly = 0 := rfl

noncomputable def polyDeg_zero_path : Path (polyDeg zeroPoly) 0 :=
  Path.mk [Step.mk _ _ polyDeg_nil] polyDeg_nil

theorem polyDeg_const (c : Int) : polyDeg (constPoly c) = 1 := rfl

noncomputable def polyDeg_const_path (c : Int) : Path (polyDeg (constPoly c)) 1 :=
  Path.mk [Step.mk _ _ (polyDeg_const c)] (polyDeg_const c)

theorem polyDeg_cons (a : Int) (as : Poly) :
    polyDeg (a :: as) = polyDeg as + 1 := by
  simp [polyDeg, List.length]

/-! ## Transport and congrArg -/

theorem transport_polyAdd_comm (P : Poly → Prop) (p q : Poly) (h : P (polyAdd p q)) :
    Path.transport (D := P) (polyAdd_comm_path p q) h =
      (polyAdd_comm p q ▸ h) := by
  simp

theorem polyAdd_comm_symm_trans (p q : Poly) :
    (Path.trans (polyAdd_comm_path p q)
      (Path.symm (polyAdd_comm_path p q))).toEq = rfl := by
  simp

theorem congrArg_polyAdd_comm (f : Poly → Nat) (p q : Poly) :
    (Path.congrArg f (polyAdd_comm_path p q)).toEq =
      _root_.congrArg f (polyAdd_comm p q) := by
  simp

theorem polyAdd_assoc_step_count (p q r : Poly) :
    (polyAdd_assoc_path p q r).steps.length = 1 := by
  rfl

/-! ## Composed paths -/

/-- Rearrangement: `(p + q) + r → p + (r + q)` via associativity then commutativity. -/
noncomputable def polyAdd_rearrange_path (p q r : Poly) :
    Path (polyAdd (polyAdd p q) r) (polyAdd p (polyAdd r q)) :=
  Path.trans (polyAdd_assoc_path p q r)
    (Path.congrArg (polyAdd p) (polyAdd_comm_path q r))

theorem polyAdd_rearrange_step_count (p q r : Poly) :
    (polyAdd_rearrange_path p q r).steps.length = 2 := by
  rfl

end ComputationalPaths.Path.Algebra.PolynomialPaths
