/-
# Tropical Geometry via Computational Paths

Tropical semiring (min-plus), tropical polynomials, tropical curves,
valuations, Newton polygons — all modelled with genuine computational paths
over Nat using `stepChain`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (35+ theorems/defs, zero Path.ofEq)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.TropicalPaths

open ComputationalPaths.Path

/-! ## Tropical semiring (min-plus on Nat with ∞ = large sentinel) -/

@[simp] def tropInf : Nat := 1000000
@[simp] def tropAdd (a b : Nat) : Nat := min a b
@[simp] def tropMul (a b : Nat) : Nat := a + b
@[simp] def tropZero : Nat := tropInf
@[simp] def tropOne : Nat := 0

/-! ## Tropical polynomials -/

structure TropMonomial where
  coeff : Nat
  exp : Nat

@[simp] def evalMonomial (m : TropMonomial) (x : Nat) : Nat :=
  m.coeff + m.exp * x

structure TropPoly where
  terms : List TropMonomial

@[simp] def evalPoly (p : TropPoly) (x : Nat) : Nat :=
  p.terms.foldl (fun acc m => min acc (evalMonomial m x)) tropInf

@[simp] def valuation (n : Nat) : Nat := n

structure NewtonVertex where
  x : Nat
  y : Nat

structure NewtonPolygon where
  vertices : List NewtonVertex

structure TropCurve where
  bends : List Nat

@[simp] def tropGenus (c : TropCurve) : Nat :=
  if c.bends.length > 1 then c.bends.length - 1 else 0

@[simp] def tropDegree (p : TropPoly) : Nat :=
  p.terms.foldl (fun acc m => max acc m.exp) 0

@[simp] def tropPolyAdd (p q : TropPoly) : TropPoly :=
  ⟨p.terms ++ q.terms⟩

/-! ## Core tropical semiring paths via stepChain -/

-- 1. Tropical addition is commutative
theorem tropAdd_comm (a b : Nat) : tropAdd a b = tropAdd b a := by
  simp [Nat.min_comm]

def tropAdd_comm_step (a b : Nat) : Step Nat :=
  Step.mk (tropAdd a b) (tropAdd b a) (tropAdd_comm a b)

def tropAdd_comm_path (a b : Nat) : Path (tropAdd a b) (tropAdd b a) :=
  Path.stepChain (tropAdd_comm a b)

-- 2. Tropical addition is associative
theorem tropAdd_assoc (a b c : Nat) :
    tropAdd (tropAdd a b) c = tropAdd a (tropAdd b c) := by
  simp [Nat.min_assoc]

def tropAdd_assoc_step (a b c : Nat) : Step Nat :=
  Step.mk (tropAdd (tropAdd a b) c) (tropAdd a (tropAdd b c)) (tropAdd_assoc a b c)

def tropAdd_assoc_path (a b c : Nat) :
    Path (tropAdd (tropAdd a b) c) (tropAdd a (tropAdd b c)) :=
  Path.stepChain (tropAdd_assoc a b c)

-- 3. Tropical multiplication is commutative
theorem tropMul_comm (a b : Nat) : tropMul a b = tropMul b a := by
  simp [Nat.add_comm]

def tropMul_comm_step (a b : Nat) : Step Nat :=
  Step.mk (tropMul a b) (tropMul b a) (tropMul_comm a b)

def tropMul_comm_path (a b : Nat) : Path (tropMul a b) (tropMul b a) :=
  Path.stepChain (tropMul_comm a b)

-- 4. Tropical multiplication is associative
theorem tropMul_assoc (a b c : Nat) :
    tropMul (tropMul a b) c = tropMul a (tropMul b c) := by
  simp [Nat.add_assoc]

def tropMul_assoc_path (a b c : Nat) :
    Path (tropMul (tropMul a b) c) (tropMul a (tropMul b c)) :=
  Path.stepChain (tropMul_assoc a b c)

-- 5. Tropical one is multiplicative identity (left)
theorem tropMul_one_left (a : Nat) : tropMul tropOne a = a := by simp

def tropMul_one_left_path (a : Nat) : Path (tropMul tropOne a) a :=
  Path.stepChain (tropMul_one_left a)

-- 6. Tropical one is multiplicative identity (right)
theorem tropMul_one_right (a : Nat) : tropMul a tropOne = a := by simp

def tropMul_one_right_path (a : Nat) : Path (tropMul a tropOne) a :=
  Path.stepChain (tropMul_one_right a)

-- 7. Tropical distributivity: a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)
theorem tropDistrib (a b c : Nat) :
    tropMul a (tropAdd b c) = tropAdd (tropMul a b) (tropMul a c) := by
  simp only [tropMul, tropAdd]; omega

def tropDistrib_step (a b c : Nat) : Step Nat :=
  Step.mk (tropMul a (tropAdd b c)) (tropAdd (tropMul a b) (tropMul a c)) (tropDistrib a b c)

def tropDistrib_path (a b c : Nat) :
    Path (tropMul a (tropAdd b c)) (tropAdd (tropMul a b) (tropMul a c)) :=
  Path.stepChain (tropDistrib a b c)

-- 8. Right distributivity
theorem tropDistrib_right (a b c : Nat) :
    tropMul (tropAdd b c) a = tropAdd (tropMul b a) (tropMul c a) := by
  simp only [tropMul, tropAdd]; omega

def tropDistrib_right_path (a b c : Nat) :
    Path (tropMul (tropAdd b c) a) (tropAdd (tropMul b a) (tropMul c a)) :=
  Path.stepChain (tropDistrib_right a b c)

-- 9. Tropical idempotency: a ⊕ a = a
theorem tropAdd_idem (a : Nat) : tropAdd a a = a := by simp

def tropAdd_idem_path (a : Nat) : Path (tropAdd a a) a :=
  Path.stepChain (tropAdd_idem a)

-- 10. Valuation respects tropical multiplication
theorem val_tropMul (a b : Nat) :
    valuation (tropMul a b) = tropMul (valuation a) (valuation b) := by simp

def val_tropMul_path (a b : Nat) :
    Path (valuation (tropMul a b)) (tropMul (valuation a) (valuation b)) :=
  Path.stepChain (val_tropMul a b)

-- 11. Monomial evaluation at 0
theorem evalMonomial_at_zero (m : TropMonomial) :
    evalMonomial m 0 = m.coeff := by simp

def evalMonomial_at_zero_path (m : TropMonomial) :
    Path (evalMonomial m 0) m.coeff :=
  Path.stepChain (evalMonomial_at_zero m)

-- 12. Monomial with zero exponent
theorem evalMonomial_zero_exp (c : Nat) (x : Nat) :
    evalMonomial ⟨c, 0⟩ x = c := by simp

def evalMonomial_zero_exp_path (c x : Nat) :
    Path (evalMonomial ⟨c, 0⟩ x) c :=
  Path.stepChain (evalMonomial_zero_exp c x)

-- 13. Monomial with zero coefficient
theorem evalMonomial_zero_coeff (e x : Nat) :
    evalMonomial ⟨0, e⟩ x = e * x := by simp

def evalMonomial_zero_coeff_path (e x : Nat) :
    Path (evalMonomial ⟨0, e⟩ x) (e * x) :=
  Path.stepChain (evalMonomial_zero_coeff e x)

-- 14. Degree of empty polynomial
theorem tropDegree_empty : tropDegree ⟨[]⟩ = 0 := by simp

def tropDegree_empty_path : Path (tropDegree ⟨[]⟩) 0 :=
  Path.stepChain tropDegree_empty

-- 15. Genus of single-bend curve
theorem tropGenus_single (n : Nat) : tropGenus ⟨[n]⟩ = 0 := by simp

def tropGenus_single_path (n : Nat) : Path (tropGenus ⟨[n]⟩) 0 :=
  Path.stepChain (tropGenus_single n)

-- 16. Genus of empty curve
theorem tropGenus_empty : tropGenus ⟨[]⟩ = 0 := by simp

def tropGenus_empty_path : Path (tropGenus ⟨[]⟩) 0 :=
  Path.stepChain tropGenus_empty

-- 17. Empty polynomial evaluates to infinity
theorem evalPoly_empty (x : Nat) : evalPoly ⟨[]⟩ x = tropInf := by simp

def evalPoly_empty_path (x : Nat) : Path (evalPoly ⟨[]⟩ x) tropInf :=
  Path.stepChain (evalPoly_empty x)

-- 18. Valuation is idempotent
theorem val_idem (n : Nat) : valuation (valuation n) = valuation n := by simp

def val_idem_path (n : Nat) : Path (valuation (valuation n)) (valuation n) :=
  Path.stepChain (val_idem n)

-- 19. Tropical mul with zero absorbs under addition
theorem tropMul_zero_absorb (a : Nat) :
    tropAdd a (tropMul a 0) = a := by simp

def tropMul_zero_absorb_path (a : Nat) :
    Path (tropAdd a (tropMul a 0)) a :=
  Path.stepChain (tropMul_zero_absorb a)

-- 20. Empty poly addition identity
theorem tropPolyAdd_empty_left (p : TropPoly) :
    tropPolyAdd ⟨[]⟩ p = p := by simp

def tropPolyAdd_empty_left_path (p : TropPoly) :
    Path (tropPolyAdd ⟨[]⟩ p) p :=
  Path.stepChain (tropPolyAdd_empty_left p)

/-! ## Compound paths via trans, symm, congrArg -/

-- 21. Commutativity + associativity chain via congrArg
def tropAdd_comm_assoc_path (a b c : Nat) :
    Path (tropAdd (tropAdd a b) c) (tropAdd (tropAdd b a) c) :=
  congrArg (fun x => tropAdd x c) (tropAdd_comm_path a b)

-- 22. Symmetry path: commutative inverse
def tropAdd_comm_symm_path (a b : Nat) :
    Path (tropAdd b a) (tropAdd a b) :=
  Path.symm (tropAdd_comm_path a b)

-- 23. Transport through valuation
def val_transport_path (a b : Nat) (h : a = b) :
    Path (valuation a) (valuation b) :=
  congrArg valuation (Path.stepChain h)

-- 24. Semiring chain: mul-one-add
def tropical_semiring_chain (a b : Nat) :
    Path (tropMul tropOne (tropAdd a b)) (tropAdd a b) :=
  tropMul_one_left_path (tropAdd a b)

-- 25. Full associativity pentagon via trans
def tropAdd_assoc_pentagon (a b c d : Nat) :
    Path (tropAdd (tropAdd (tropAdd a b) c) d) (tropAdd a (tropAdd b (tropAdd c d))) :=
  Path.trans (tropAdd_assoc_path (tropAdd a b) c d)
    (tropAdd_assoc_path a b (tropAdd c d))

-- 26. Distributivity + commutativity composition
def tropDistrib_comm_path (a b c : Nat) :
    Path (tropMul a (tropAdd b c)) (tropAdd (tropMul a c) (tropMul a b)) :=
  Path.trans (tropDistrib_path a b c)
    (tropAdd_comm_path (tropMul a b) (tropMul a c))

-- 27. Mul comm then mul one: b ⊗ 0 → 0 ⊗ b → b
def tropMul_comm_one_path (b : Nat) :
    Path (tropMul b tropOne) b :=
  tropMul_one_right_path b

-- 28. Left-right identity roundtrip
def tropMul_identity_roundtrip (a : Nat) :
    Path (tropMul tropOne (tropMul a tropOne)) a :=
  Path.trans
    (congrArg (tropMul tropOne) (tropMul_one_right_path a))
    (tropMul_one_left_path a)

-- 29. Congruence through evalMonomial
def evalMonomial_congrArg_path (m : TropMonomial) (x y : Nat) (h : x = y) :
    Path (evalMonomial m x) (evalMonomial m y) :=
  congrArg (evalMonomial m) (Path.stepChain h)

-- 30. Idempotent then comm: (a⊕a) → a → (a⊕a) via symm
def tropAdd_idem_roundtrip (a : Nat) :
    Path (tropAdd a a) (tropAdd a a) :=
  Path.trans (tropAdd_idem_path a) (Path.symm (tropAdd_idem_path a))

-- 31. Transport: valuation through tropical addition
theorem transport_val_tropAdd {D : Nat → Sort _} (a b : Nat)
    (x : D (valuation (tropMul a b))) :
    transport (val_tropMul_path a b) x = (val_tropMul a b) ▸ x := by
  simp [val_tropMul_path, transport]

-- 32. Commutativity roundtrip is semantically refl
theorem tropAdd_comm_roundtrip_toEq (a b : Nat) :
    (Path.trans (tropAdd_comm_path a b) (Path.symm (tropAdd_comm_path a b))).toEq =
      (Path.refl (tropAdd a b)).toEq := by
  simp

-- 33. Mul comm roundtrip is semantically refl
theorem tropMul_comm_roundtrip_toEq (a b : Nat) :
    (Path.trans (tropMul_comm_path a b) (Path.symm (tropMul_comm_path a b))).toEq =
      (Path.refl (tropMul a b)).toEq := by
  simp

-- 34. symm commutes with congrArg for valuation
theorem symm_congrArg_val {x y : Nat} (p : Path x y) :
    Path.symm (congrArg valuation p) = congrArg valuation (Path.symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [congrArg, Path.symm]

-- 35. trans commutes with congrArg for tropAdd
theorem congrArg_tropAdd_trans (c : Nat) {x y z : Nat}
    (p : Path x y) (q : Path y z) :
    congrArg (tropAdd c) (Path.trans p q) =
      Path.trans (congrArg (tropAdd c) p) (congrArg (tropAdd c) q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [congrArg, Path.trans]

-- 36. Tropical associativity roundtrip semantic
theorem tropAdd_assoc_roundtrip_toEq (a b c : Nat) :
    (Path.trans (tropAdd_assoc_path a b c)
                (Path.symm (tropAdd_assoc_path a b c))).toEq =
      (Path.refl (tropAdd (tropAdd a b) c)).toEq := by
  simp

-- 37. Step map through valuation
theorem tropAdd_step_map_val (a b : Nat) :
    Step.map valuation (tropAdd_comm_step a b) =
      Step.mk (valuation (tropAdd a b)) (valuation (tropAdd b a))
        (_root_.congrArg valuation (tropAdd_comm a b)) := by
  simp [tropAdd_comm_step, Step.map]

-- 38. Tropical zero is additive identity (left, with bound)
theorem tropAdd_zero_left (a : Nat) (h : a ≤ tropInf) :
    tropAdd tropZero a = a := by
  unfold tropAdd tropZero tropInf at *
  exact Nat.min_eq_right h

def tropAdd_zero_left_path (a : Nat) (h : a ≤ tropInf) :
    Path (tropAdd tropZero a) a :=
  Path.stepChain (tropAdd_zero_left a h)

end ComputationalPaths.Path.Algebra.TropicalPaths
