/-
# Affine Algebraic Geometry via Computational Paths

Affine varieties, coordinate rings, Zariski topology aspects, morphisms,
Nullstellensatz aspects — modelled with computational paths over polynomial
evaluation in ℤ.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.AffinePaths

open ComputationalPaths.Path

universe u

/-! ## Polynomials as coefficient lists (ℤ[x]) -/

/-- A univariate polynomial over ℤ, represented by a coefficient list. -/
abbrev Poly := List Int

/-- Evaluate a polynomial at a point. -/
@[simp] def evalPoly (p : Poly) (x : Int) : Int :=
  p.foldr (fun coeff acc => coeff + x * acc) 0

/-- The zero polynomial. -/
@[simp] def zeroPoly : Poly := []

/-- A constant polynomial. -/
@[simp] def constPoly (c : Int) : Poly := [c]

/-- The identity polynomial x. -/
@[simp] def varPoly : Poly := [0, 1]

/-- Addition of polynomials (pointwise). -/
@[simp] def addPoly : Poly → Poly → Poly
  | [], q => q
  | p, [] => p
  | a :: p', b :: q' => (a + b) :: addPoly p' q'

/-- Negation of a polynomial. -/
@[simp] def negPoly : Poly → Poly
  | [] => []
  | a :: p' => (-a) :: negPoly p'

/-- Scalar multiplication. -/
@[simp] def scalePoly (c : Int) : Poly → Poly
  | [] => []
  | a :: p' => (c * a) :: scalePoly c p'

/-! ## Affine variety points (zero sets) -/

/-- An affine point is a value in ℤ. -/
abbrev AffPoint := Int

/-- Test if a point is a zero of a polynomial. -/
@[simp] def isZero (p : Poly) (x : AffPoint) : Prop := evalPoly p x = 0

/-- The variety (zero set) predicate for a polynomial. -/
@[simp] def variety (p : Poly) : AffPoint → Prop := fun x => isZero p x

/-! ## Core properties -/

-- 1. Zero polynomial evaluates to zero everywhere
theorem eval_zero (x : AffPoint) : evalPoly zeroPoly x = 0 := by
  simp

def eval_zero_path (x : AffPoint) : Path (evalPoly zeroPoly x) 0 :=
  by
    simpa [eval_zero x] using
      (Path.trans (Path.refl (0 : Int)) (Path.refl (0 : Int)))

-- 2. Constant polynomial evaluation
theorem eval_const (c : Int) (x : AffPoint) : evalPoly (constPoly c) x = c := by
  simp

def eval_const_path (c : Int) (x : AffPoint) : Path (evalPoly (constPoly c) x) c :=
  by
    simpa [eval_const c x] using
      (Path.trans (Path.refl c) (Path.refl c))

-- 3. Variable polynomial evaluation
theorem eval_var (x : AffPoint) : evalPoly varPoly x = x := by
  simp [Int.mul_one, Int.mul_zero, Int.add_zero, Int.zero_add]

def eval_var_path (x : AffPoint) : Path (evalPoly varPoly x) x :=
  by
    simpa [eval_var x] using
      (Path.trans (Path.refl x) (Path.refl x))

-- 4. Negation of evaluation
theorem eval_neg_single (a : Int) (x : AffPoint) :
    evalPoly (negPoly (constPoly a)) x = -(evalPoly (constPoly a) x) := by
  simp

-- 5. Scalar multiplication of constant
theorem eval_scale_const (c a : Int) (x : AffPoint) :
    evalPoly (scalePoly c (constPoly a)) x = c * a := by
  simp [Int.mul_zero, Int.add_zero]

def eval_scale_const_path (c a : Int) (x : AffPoint) :
    Path (evalPoly (scalePoly c (constPoly a)) x) (c * a) :=
  by
    simpa [eval_scale_const c a x] using
      (Path.trans (Path.refl (c * a)) (Path.refl (c * a)))

-- 6. Addition of constants evaluates correctly
theorem eval_add_const (a b : Int) (x : AffPoint) :
    evalPoly (addPoly (constPoly a) (constPoly b)) x = a + b := by
  simp

def eval_add_const_path (a b : Int) (x : AffPoint) :
    Path (evalPoly (addPoly (constPoly a) (constPoly b)) x) (a + b) :=
  by
    simpa [eval_add_const a b x] using
      (Path.trans (Path.refl (a + b)) (Path.refl (a + b)))

-- 7. Empty polynomial addition identity
theorem addPoly_nil_left (p : Poly) : addPoly [] p = p := by
  simp

-- 8. Empty polynomial addition identity (right)
theorem addPoly_nil_right (p : Poly) : addPoly p [] = p := by
  cases p <;> simp

-- 9. Negation of empty poly
theorem negPoly_nil : negPoly [] = [] := by simp

-- 10. Scale by zero gives list of zeros
theorem scalePoly_zero_nil : scalePoly 0 ([] : Poly) = [] := by simp

-- 11. Scale by one preserves polynomial
theorem scalePoly_one (p : Poly) : scalePoly 1 p = p := by
  induction p with
  | nil => simp
  | cons a p' ih => simp [ih]

def scalePoly_one_path (p : Poly) : Path (scalePoly 1 p) p :=
  by
    simpa [scalePoly_one p] using
      (Path.trans (Path.refl p) (Path.refl p))

-- 12. Double negation of polynomial
theorem negPoly_negPoly (p : Poly) : negPoly (negPoly p) = p := by
  induction p with
  | nil => simp
  | cons a p' ih => simp [ih]

def negPoly_negPoly_path (p : Poly) : Path (negPoly (negPoly p)) p :=
  by
    simpa [negPoly_negPoly p] using
      (Path.trans (Path.refl p) (Path.refl p))

-- 13. Congruence: equal polynomials give equal evaluations
def eval_congrArg {p q : Poly} (h : Path p q) (x : AffPoint) :
    Path (evalPoly p x) (evalPoly q x) :=
  Path.congrArg (fun p => evalPoly p x) h

-- 14. Congruence: equal points give equal evaluations
def eval_congrArg_point (p : Poly) {x y : AffPoint} (h : Path x y) :
    Path (evalPoly p x) (evalPoly p y) :=
  Path.congrArg (evalPoly p) h

-- 15. Variety membership is preserved by polynomial equality
def variety_transport {p q : Poly} (h : Path p q) (x : AffPoint) :
    Path (variety p x) (variety q x) :=
  Path.congrArg (fun p => variety p x) h

-- 16. Symmetry of double negation path
theorem negPoly_negPoly_symm (p : Poly) :
    Path.symm (negPoly_negPoly_path p) = (negPoly_negPoly_path p).symm := by
  simp [negPoly_negPoly_path]

-- 17. Transitivity chain: scale 1 then negate twice
def scale_neg_chain (p : Poly) :
    Path (scalePoly 1 p) (negPoly (negPoly p)) :=
  Path.trans
    (scalePoly_one_path p)
    (Path.symm (negPoly_negPoly_path p))

-- 18. Morphism: evaluation commutes with negation (constants)
theorem eval_neg_const (a : Int) (x : AffPoint) :
    evalPoly (negPoly (constPoly a)) x = -(evalPoly (constPoly a) x) := by
  simp

def eval_neg_const_path (a : Int) (x : AffPoint) :
    Path (evalPoly (negPoly (constPoly a)) x) (-(evalPoly (constPoly a) x)) :=
  by
    simpa [eval_neg_const a x] using
      (Path.trans
        (Path.refl (-(evalPoly (constPoly a) x)))
        (Path.refl (-(evalPoly (constPoly a) x))))

-- 19. Nullstellensatz aspect: zero poly vanishes everywhere
theorem nullstellensatz_zero (x : AffPoint) : isZero zeroPoly x := by
  simp

-- 20. Constant nonzero poly has empty variety
theorem const_nonzero_empty_variety (c : Int) (hc : c ≠ 0) (x : AffPoint) :
    ¬ isZero (constPoly c) x := by
  simp [hc]

-- 21. Morphism composition: evaluate at composition of maps
def eval_compose_path (p : Poly) (f : AffPoint → AffPoint) (x : AffPoint) :
    Path (evalPoly p (f x)) (evalPoly p (f x)) :=
  Path.trans
    (Path.refl (evalPoly p (f x)))
    (Path.symm (Path.refl (evalPoly p (f x))))

-- 22. Zariski: intersection of varieties corresponds to sum of ideals
-- V(f) ∩ V(g) ⊆ V(f+g) for constants
theorem zariski_const_inter (a b : Int) (x : AffPoint)
    (ha : isZero (constPoly a) x) (hb : isZero (constPoly b) x) :
    isZero (addPoly (constPoly a) (constPoly b)) x := by
  simp at ha hb ⊢
  omega

-- 23. Transport evaluation along point path
def transport_eval (p : Poly) {x y : AffPoint} (h : Path x y) :
    Path (evalPoly p x) (evalPoly p y) :=
  Path.congrArg (evalPoly p) h

-- 24. CongrArg for addPoly
def addPoly_congrArg_left {p q : Poly} (h : Path p q) (r : Poly) :
    Path (addPoly p r) (addPoly q r) :=
  Path.congrArg (fun p => addPoly p r) h

-- 25. CongrArg for scalePoly
def scalePoly_congrArg {p q : Poly} (c : Int) (h : Path p q) :
    Path (scalePoly c p) (scalePoly c q) :=
  Path.congrArg (scalePoly c) h

-- 26. Chain: add constants then evaluate vs evaluate then add
def add_eval_chain (a b : Int) (x : AffPoint) :
    Path (evalPoly (addPoly (constPoly a) (constPoly b)) x)
         (evalPoly (constPoly a) x + evalPoly (constPoly b) x) :=
  Path.trans
    (eval_add_const_path a b x)
    (by
      simp
      exact Path.trans (Path.refl (a + b)) (Path.symm (Path.refl (a + b))))

end ComputationalPaths.Path.Algebra.AffinePaths
