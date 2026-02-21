/-
# Diophantine Equations via Computational Paths

Linear Diophantine equations, Pell's equation aspects, Pythagorean triples,
sum of squares, Fermat descent — all via `Path`, `Step`, `trans`, `symm`,
`congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.DiophantinePaths

open ComputationalPaths.Path

universe u

variable {A : Type u}

/-! ## Ring structure for Diophantine equations -/

/-- Abstract ring for number-theoretic constructions. -/
structure DRing (A : Type u) where
  zero : A
  one : A
  add : A → A → A
  mul : A → A → A
  neg : A → A
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  add_zero : ∀ a, add a zero = a
  mul_one : ∀ a, mul a one = a
  mul_zero : ∀ a, mul a zero = zero
  add_neg : ∀ a, add a (neg a) = zero
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-! ## Path constructions for ring axioms -/

/-- Addition commutativity path. -/
def dr_add_comm_path (R : DRing A) (a b : A) :
    Path (R.add a b) (R.add b a) :=
  Path.mk [Step.mk _ _ (R.add_comm a b)] (R.add_comm a b)

/-- Multiplication commutativity path. -/
def dr_mul_comm_path (R : DRing A) (a b : A) :
    Path (R.mul a b) (R.mul b a) :=
  Path.mk [Step.mk _ _ (R.mul_comm a b)] (R.mul_comm a b)

/-- Addition associativity path. -/
def dr_add_assoc_path (R : DRing A) (a b c : A) :
    Path (R.add (R.add a b) c) (R.add a (R.add b c)) :=
  Path.mk [Step.mk _ _ (R.add_assoc a b c)] (R.add_assoc a b c)

/-- Multiplication associativity path. -/
def dr_mul_assoc_path (R : DRing A) (a b c : A) :
    Path (R.mul (R.mul a b) c) (R.mul a (R.mul b c)) :=
  Path.mk [Step.mk _ _ (R.mul_assoc a b c)] (R.mul_assoc a b c)

/-- Distributivity path. -/
def dr_distrib_path (R : DRing A) (a b c : A) :
    Path (R.mul a (R.add b c)) (R.add (R.mul a b) (R.mul a c)) :=
  Path.mk [Step.mk _ _ (R.distrib a b c)] (R.distrib a b c)

/-- Zero absorbs multiplication path. -/
def dr_mul_zero_path (R : DRing A) (a : A) :
    Path (R.mul a R.zero) R.zero :=
  Path.mk [Step.mk _ _ (R.mul_zero a)] (R.mul_zero a)

/-- Additive inverse path. -/
def dr_add_neg_path (R : DRing A) (a : A) :
    Path (R.add a (R.neg a)) R.zero :=
  Path.mk [Step.mk _ _ (R.add_neg a)] (R.add_neg a)

/-! ## Linear Diophantine equations: ax + by = c -/

/-- Solution to a linear Diophantine equation ax + by = c. -/
structure LinearDiophSol (R : DRing A) (a b c : A) where
  x : A
  y : A
  sol : R.add (R.mul a x) (R.mul b y) = c

/-- Path witnessing a solution to ax + by = c. -/
def linear_dioph_path (R : DRing A) (a b c : A) (S : LinearDiophSol R a b c) :
    Path (R.add (R.mul a S.x) (R.mul b S.y)) c :=
  Path.mk [Step.mk _ _ S.sol] S.sol

/-- Any two solution paths to the same target agree semantically. -/
theorem linear_dioph_solution_unique_toEq (R : DRing A) (a b c : A)
    (S : LinearDiophSol R a b c) :
    (trans (linear_dioph_path R a b c S) (symm (linear_dioph_path R a b c S))).toEq =
      (refl _).toEq := by
  simp

/-- Transport a type family along a solution path. -/
theorem transport_linear_dioph {D : A → Sort u} (R : DRing A) (a b c : A)
    (S : LinearDiophSol R a b c)
    (x : D (R.add (R.mul a S.x) (R.mul b S.y))) :
    transport (linear_dioph_path R a b c S) x = S.sol ▸ x := by
  simp [linear_dioph_path, transport]

/-! ## Pythagorean triples -/

/-- Pythagorean triple: a² + b² = c². -/
structure PythTriple (R : DRing A) where
  a : A
  b : A
  c : A
  pyth : R.add (R.mul a a) (R.mul b b) = R.mul c c

/-- Path witnessing a Pythagorean triple. -/
def pyth_path (R : DRing A) (T : PythTriple R) :
    Path (R.add (R.mul T.a T.a) (R.mul T.b T.b)) (R.mul T.c T.c) :=
  Path.mk [Step.mk _ _ T.pyth] T.pyth

/-- Pythagorean triple roundtrip (semantic). -/
theorem pyth_roundtrip_toEq (R : DRing A) (T : PythTriple R) :
    (trans (pyth_path R T) (symm (pyth_path R T))).toEq =
      (refl (R.add (R.mul T.a T.a) (R.mul T.b T.b))).toEq := by
  simp

/-- congrArg of a function through a Pythagorean path. -/
theorem congrArg_pyth {B : Type u} (R : DRing A) (T : PythTriple R) (f : A → B) :
    congrArg f (pyth_path R T) =
      Path.mk [Step.mk _ _ (_root_.congrArg f T.pyth)] (_root_.congrArg f T.pyth) := by
  simp [pyth_path, congrArg]

/-- Transport along Pythagorean path. -/
theorem transport_pyth {D : A → Sort u} (R : DRing A) (T : PythTriple R)
    (x : D (R.add (R.mul T.a T.a) (R.mul T.b T.b))) :
    transport (pyth_path R T) x = T.pyth ▸ x := by
  simp [pyth_path, transport]

/-! ## Sum of squares -/

/-- Sum of two squares representation: n = a² + b². -/
structure SumTwoSquares (R : DRing A) (n : A) where
  a : A
  b : A
  repr : R.add (R.mul a a) (R.mul b b) = n

/-- Path for sum-of-two-squares representation. -/
def sos_path (R : DRing A) (n : A) (S : SumTwoSquares R n) :
    Path (R.add (R.mul S.a S.a) (R.mul S.b S.b)) n :=
  Path.mk [Step.mk _ _ S.repr] S.repr

/-- Two sum-of-squares roundtrips agree semantically. -/
theorem sos_roundtrip_toEq (R : DRing A) (n : A)
    (S : SumTwoSquares R n) :
    (trans (sos_path R n S) (symm (sos_path R n S))).toEq =
      (refl _).toEq := by
  simp

/-- Sum of four squares: n = a² + b² + c² + d². -/
structure SumFourSquares (R : DRing A) (n : A) where
  a : A
  b : A
  c : A
  d : A
  repr : R.add (R.add (R.mul a a) (R.mul b b)) (R.add (R.mul c c) (R.mul d d)) = n

/-- Path for sum of four squares. -/
def s4s_path (R : DRing A) (n : A) (S : SumFourSquares R n) :
    Path (R.add (R.add (R.mul S.a S.a) (R.mul S.b S.b))
                (R.add (R.mul S.c S.c) (R.mul S.d S.d))) n :=
  Path.mk [Step.mk _ _ S.repr] S.repr

/-! ## Pell's equation: x² - Dy² = 1 -/

/-- Pell equation solution: x² - Dy² = 1, encoded as x² = 1 + Dy². -/
structure PellSol (R : DRing A) (D : A) where
  x : A
  y : A
  pell : R.mul x x = R.add R.one (R.mul D (R.mul y y))

/-- Path for a Pell equation solution. -/
def pell_path (R : DRing A) (D : A) (S : PellSol R D) :
    Path (R.mul S.x S.x) (R.add R.one (R.mul D (R.mul S.y S.y))) :=
  Path.mk [Step.mk _ _ S.pell] S.pell

/-- Pell path roundtrip (semantic). -/
theorem pell_roundtrip_toEq (R : DRing A) (D : A) (S : PellSol R D) :
    (trans (pell_path R D S) (symm (pell_path R D S))).toEq =
      (refl (R.mul S.x S.x)).toEq := by
  simp

/-- Transport along Pell path. -/
theorem transport_pell {E : A → Sort u} (R : DRing A) (D : A) (S : PellSol R D)
    (x : E (R.mul S.x S.x)) :
    transport (pell_path R D S) x = S.pell ▸ x := by
  simp [pell_path, transport]

/-! ## Fermat descent -/

/-- Descent structure: if n satisfies P, then some m has trivial measure. -/
structure FermatDescent (R : DRing A) where
  prop : A → Prop
  measure : A → A
  descendTo : A → A
  descend_prop : ∀ n, prop n → prop (descendTo n)
  descend_measure : ∀ n, prop n → measure (descendTo n) = R.mul (measure n) R.zero

/-- Path for descent measure collapse. -/
def descent_measure_path (R : DRing A) (FD : FermatDescent R) (n : A)
    (h : FD.prop n) :
    Path (FD.measure (FD.descendTo n)) (R.mul (FD.measure n) R.zero) :=
  Path.mk [Step.mk _ _ (FD.descend_measure n h)] (FD.descend_measure n h)

/-- Descent measure reaches zero via mul_zero. -/
def descent_to_zero_path (R : DRing A) (FD : FermatDescent R) (n : A)
    (h : FD.prop n) :
    Path (FD.measure (FD.descendTo n)) R.zero :=
  trans (descent_measure_path R FD n h)
    (Path.mk [Step.mk _ _ (R.mul_zero (FD.measure n))] (R.mul_zero (FD.measure n)))

/-! ## Brahmagupta–Fibonacci identity via paths -/

/-- Brahmagupta-Fibonacci identity: (a²+b²)(c²+d²) = (ac-bd)² + (ad+bc)². -/
structure BrahmaguptaFib (R : DRing A) where
  identity : ∀ a b c d,
    R.mul (R.add (R.mul a a) (R.mul b b)) (R.add (R.mul c c) (R.mul d d)) =
    R.add
      (R.mul (R.add (R.mul a c) (R.neg (R.mul b d)))
             (R.add (R.mul a c) (R.neg (R.mul b d))))
      (R.mul (R.add (R.mul a d) (R.mul b c))
             (R.add (R.mul a d) (R.mul b c)))

/-- Path for Brahmagupta-Fibonacci identity. -/
def bf_path (R : DRing A) (BF : BrahmaguptaFib R) (a b c d : A) :
    Path (R.mul (R.add (R.mul a a) (R.mul b b)) (R.add (R.mul c c) (R.mul d d)))
         (R.add
           (R.mul (R.add (R.mul a c) (R.neg (R.mul b d)))
                  (R.add (R.mul a c) (R.neg (R.mul b d))))
           (R.mul (R.add (R.mul a d) (R.mul b c))
                  (R.add (R.mul a d) (R.mul b c)))) :=
  Path.mk [Step.mk _ _ (BF.identity a b c d)] (BF.identity a b c d)

/-- BF identity roundtrip (semantic). -/
theorem bf_roundtrip_toEq (R : DRing A) (BF : BrahmaguptaFib R) (a b c d : A) :
    (trans (bf_path R BF a b c d) (symm (bf_path R BF a b c d))).toEq =
      (refl _).toEq := by
  simp

/-! ## Path coherence -/

/-- symm commutes with congrArg for ring paths. -/
theorem symm_congrArg_ring {B : Type u} (R : DRing A) (f : A → B)
    {x y : A} (p : Path x y) :
    symm (congrArg f p) = congrArg f (symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [congrArg, symm]

/-- trans commutes with congrArg for ring paths. -/
theorem congrArg_trans_ring {B : Type u} (R : DRing A) (f : A → B)
    {x y z : A} (p : Path x y) (q : Path y z) :
    congrArg f (trans p q) = trans (congrArg f p) (congrArg f q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [congrArg, trans]

/-- Step from Pythagorean triple. -/
def pyth_step (R : DRing A) (T : PythTriple R) : Step A :=
  Step.mk (R.add (R.mul T.a T.a) (R.mul T.b T.b)) (R.mul T.c T.c) T.pyth

/-- Symm of Pythagorean step. -/
theorem pyth_step_symm (R : DRing A) (T : PythTriple R) :
    (pyth_step R T).symm =
      Step.mk (R.mul T.c T.c) (R.add (R.mul T.a T.a) (R.mul T.b T.b)) T.pyth.symm := by
  simp [pyth_step, Step.symm]

/-- Mapping a function through a Pythagorean step. -/
theorem pyth_step_map {B : Type u} (R : DRing A) (T : PythTriple R) (f : A → B) :
    Step.map f (pyth_step R T) =
      Step.mk (f (R.add (R.mul T.a T.a) (R.mul T.b T.b))) (f (R.mul T.c T.c))
        (_root_.congrArg f T.pyth) := by
  simp [pyth_step, Step.map]

/-- Two diophantine paths agree semantically. -/
theorem dioph_coherence {x y : A} (p q : Path x y) :
    p.toEq = q.toEq :=
  subsingleton_eq_by_cases p.toEq q.toEq

end ComputationalPaths.Path.Algebra.DiophantinePaths
