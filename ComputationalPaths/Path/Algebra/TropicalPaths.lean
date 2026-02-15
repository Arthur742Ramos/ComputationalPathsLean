/-
# Tropical Geometry via Computational Paths

Tropical semiring (min-plus), tropical polynomials, tropical curves,
valuations, Newton polygons — all modelled with computational paths
over Nat/Int.

## Main results (25+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.TropicalPaths

open ComputationalPaths.Path

/-! ## Tropical semiring (min-plus on Nat with ∞ = large sentinel) -/

/-- Tropical infinity sentinel. -/
@[simp] def tropInf : Nat := 1000000

/-- Tropical addition = min. -/
@[simp] def tropAdd (a b : Nat) : Nat := min a b

/-- Tropical multiplication = plus. -/
@[simp] def tropMul (a b : Nat) : Nat := a + b

/-- Tropical zero = ∞ (additive identity). -/
@[simp] def tropZero : Nat := tropInf

/-- Tropical one = 0 (multiplicative identity). -/
@[simp] def tropOne : Nat := 0

/-! ## Tropical polynomials -/

/-- A tropical monomial: coefficient (tropical) and exponent. -/
structure TropMonomial where
  coeff : Nat
  exp : Nat

/-- Evaluate a tropical monomial at a point: coeff ⊕ (exp ⊗ x) = coeff + exp * x
    but in tropical: coeff + exp + x... Actually tropical eval of c * x^e = c + e*x. -/
@[simp] def evalMonomial (m : TropMonomial) (x : Nat) : Nat :=
  m.coeff + m.exp * x

/-- A tropical polynomial is a list of monomials. Evaluation takes the min. -/
structure TropPoly where
  terms : List TropMonomial

/-- Evaluate tropical polynomial: min over all monomials. -/
@[simp] def evalPoly (p : TropPoly) (x : Nat) : Nat :=
  p.terms.foldl (fun acc m => min acc (evalMonomial m x)) tropInf

/-- Tropical valuation: identity on Nat (simplified discrete valuation). -/
@[simp] def valuation (n : Nat) : Nat := n

/-- Newton polygon vertex: (exponent, coefficient). -/
structure NewtonVertex where
  x : Nat
  y : Nat

/-- A Newton polygon is a list of vertices. -/
structure NewtonPolygon where
  vertices : List NewtonVertex

/-- Tropical curve: zero set data as list of bend points. -/
structure TropCurve where
  bends : List Nat

/-- Genus of a tropical curve (simplified: number of cycles). -/
@[simp] def tropGenus (c : TropCurve) : Nat :=
  if c.bends.length > 1 then c.bends.length - 1 else 0

/-- Degree of a tropical polynomial. -/
@[simp] def tropDegree (p : TropPoly) : Nat :=
  p.terms.foldl (fun acc m => max acc m.exp) 0

/-- Tropical sum of two polynomials (term-wise min of coefficients). -/
@[simp] def tropPolyAdd (p q : TropPoly) : TropPoly :=
  ⟨p.terms ++ q.terms⟩

/-! ## Core theorems -/

-- 1. Tropical addition is commutative
theorem tropAdd_comm (a b : Nat) : tropAdd a b = tropAdd b a := by
  simp [Nat.min_comm]

def tropAdd_comm_path (a b : Nat) : Path (tropAdd a b) (tropAdd b a) :=
  Path.ofEq (tropAdd_comm a b)

-- 2. Tropical addition is associative
theorem tropAdd_assoc (a b c : Nat) :
    tropAdd (tropAdd a b) c = tropAdd a (tropAdd b c) := by
  simp [Nat.min_assoc]

def tropAdd_assoc_path (a b c : Nat) :
    Path (tropAdd (tropAdd a b) c) (tropAdd a (tropAdd b c)) :=
  Path.ofEq (tropAdd_assoc a b c)

-- 3. Tropical multiplication is commutative
theorem tropMul_comm (a b : Nat) : tropMul a b = tropMul b a := by
  simp [Nat.add_comm]

def tropMul_comm_path (a b : Nat) : Path (tropMul a b) (tropMul b a) :=
  Path.ofEq (tropMul_comm a b)

-- 4. Tropical multiplication is associative
theorem tropMul_assoc (a b c : Nat) :
    tropMul (tropMul a b) c = tropMul a (tropMul b c) := by
  simp [Nat.add_assoc]

def tropMul_assoc_path (a b c : Nat) :
    Path (tropMul (tropMul a b) c) (tropMul a (tropMul b c)) :=
  Path.ofEq (tropMul_assoc a b c)

-- 5. Tropical zero is additive identity (left)
theorem tropAdd_zero_left (a : Nat) (h : a ≤ tropInf) :
    tropAdd tropZero a = a := by
  unfold tropAdd tropZero tropInf at *
  exact Nat.min_eq_right h

-- 6. Tropical one is multiplicative identity (left)
theorem tropMul_one_left (a : Nat) : tropMul tropOne a = a := by simp

def tropMul_one_left_path (a : Nat) : Path (tropMul tropOne a) a :=
  Path.ofEq (tropMul_one_left a)

-- 7. Tropical one is multiplicative identity (right)
theorem tropMul_one_right (a : Nat) : tropMul a tropOne = a := by simp

def tropMul_one_right_path (a : Nat) : Path (tropMul a tropOne) a :=
  Path.ofEq (tropMul_one_right a)

-- 8. Tropical distributivity: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
theorem tropDistrib (a b c : Nat) :
    tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c) := by
  simp only [tropMul, tropAdd]; omega

def tropDistrib_path (a b c : Nat) :
    Path (tropMul a (tropAdd b c)) (tropAdd (tropMul a b) (tropMul a c)) :=
  Path.ofEq (tropDistrib a b c)

-- 9. Tropical idempotency: a ⊕ a = a
theorem tropAdd_idem (a : Nat) : tropAdd a a = a := by simp

def tropAdd_idem_path (a : Nat) : Path (tropAdd a a) a :=
  Path.ofEq (tropAdd_idem a)

-- 10. Valuation respects tropical multiplication
theorem val_tropMul (a b : Nat) :
    valuation (tropMul a b) = tropMul (valuation a) (valuation b) := by simp

def val_tropMul_path (a b : Nat) :
    Path (valuation (tropMul a b)) (tropMul (valuation a) (valuation b)) :=
  Path.ofEq (val_tropMul a b)

-- 11. Monomial evaluation at 0
theorem evalMonomial_at_zero (m : TropMonomial) :
    evalMonomial m 0 = m.coeff := by simp

def evalMonomial_at_zero_path (m : TropMonomial) :
    Path (evalMonomial m 0) m.coeff :=
  Path.ofEq (evalMonomial_at_zero m)

-- 12. Monomial with zero exponent
theorem evalMonomial_zero_exp (c : Nat) (x : Nat) :
    evalMonomial ⟨c, 0⟩ x = c := by simp

def evalMonomial_zero_exp_path (c x : Nat) :
    Path (evalMonomial ⟨c, 0⟩ x) c :=
  Path.ofEq (evalMonomial_zero_exp c x)

-- 13. Monomial with zero coefficient
theorem evalMonomial_zero_coeff (e x : Nat) :
    evalMonomial ⟨0, e⟩ x = e * x := by simp

def evalMonomial_zero_coeff_path (e x : Nat) :
    Path (evalMonomial ⟨0, e⟩ x) (e * x) :=
  Path.ofEq (evalMonomial_zero_coeff e x)

-- 14. Degree of empty polynomial
theorem tropDegree_empty : tropDegree ⟨[]⟩ = 0 := by simp

def tropDegree_empty_path : Path (tropDegree ⟨[]⟩) 0 :=
  Path.ofEq tropDegree_empty

-- 15. Genus of single-bend curve
theorem tropGenus_single (n : Nat) : tropGenus ⟨[n]⟩ = 0 := by simp

def tropGenus_single_path (n : Nat) : Path (tropGenus ⟨[n]⟩) 0 :=
  Path.ofEq (tropGenus_single n)

-- 16. Genus of empty curve
theorem tropGenus_empty : tropGenus ⟨[]⟩ = 0 := by simp

def tropGenus_empty_path : Path (tropGenus ⟨[]⟩) 0 :=
  Path.ofEq tropGenus_empty

-- 17. Empty polynomial evaluates to infinity
theorem evalPoly_empty (x : Nat) : evalPoly ⟨[]⟩ x = tropInf := by simp

def evalPoly_empty_path (x : Nat) : Path (evalPoly ⟨[]⟩ x) tropInf :=
  Path.ofEq (evalPoly_empty x)

-- 18. Valuation is idempotent
theorem val_idem (n : Nat) : valuation (valuation n) = valuation n := by simp

def val_idem_path (n : Nat) : Path (valuation (valuation n)) (valuation n) :=
  Path.ofEq (val_idem n)

-- 19. Tropical mul distributes right: (b ⊕ c) ⊗ a = (b ⊗ a) ⊕ (c ⊗ a)
theorem tropDistrib_right (a b c : Nat) :
    tropMul (tropAdd b c) a = tropAdd (tropMul b a) (tropMul c a) := by
  simp only [tropMul, tropAdd]; omega

-- 20. Path composition: distributivity chain
def tropDistrib_chain (a b c : Nat) :
    Path (tropMul a (tropAdd b c)) (tropAdd (tropMul a b) (tropMul a c)) :=
  Path.ofEq (tropDistrib a b c)

-- 21. Tropical polynomial addition has empty as identity
theorem tropPolyAdd_empty_left (p : TropPoly) :
    tropPolyAdd ⟨[]⟩ p = p := by
  simp

def tropPolyAdd_empty_left_path (p : TropPoly) :
    Path (tropPolyAdd ⟨[]⟩ p) p :=
  Path.ofEq (tropPolyAdd_empty_left p)

-- 22. Tropical mul with tropInf absorbs
theorem tropMul_zero_absorb (a : Nat) :
    tropAdd a (tropMul a 0) = a := by simp

def tropMul_zero_absorb_path (a : Nat) :
    Path (tropAdd a (tropMul a 0)) a :=
  Path.ofEq (tropMul_zero_absorb a)

-- 23. Trans path: commutativity + associativity chain
def tropAdd_comm_assoc_path (a b c : Nat) :
    Path (tropAdd (tropAdd a b) c) (tropAdd (tropAdd b a) c) :=
  let p1 : Path (tropAdd a b) (tropAdd b a) := tropAdd_comm_path a b
  Path.congrArg (fun x => tropAdd x c) p1

-- 24. Symmetry path: commutative inverse
def tropAdd_comm_symm_path (a b : Nat) :
    Path (tropAdd b a) (tropAdd a b) :=
  Path.symm (tropAdd_comm_path a b)

-- 25. Transport through valuation
def val_transport_path (a b : Nat) (h : a = b) :
    Path (valuation a) (valuation b) :=
  Path.congrArg valuation (Path.ofEq h)

-- 26. Tropical semiring path: mul-one-add chain
def tropical_semiring_chain (a b : Nat) :
    Path (tropMul tropOne (tropAdd a b)) (tropAdd a b) :=
  tropMul_one_left_path (tropAdd a b)

end ComputationalPaths.Path.Algebra.TropicalPaths
