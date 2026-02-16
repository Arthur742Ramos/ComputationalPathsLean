/-
# Algebraic Number Theory via Computational Paths

Number fields, rings of integers, norms, traces, discriminants, ideal factorization
— all encoded through genuine `Path` ops: `stepChain`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (35+ theorems/defs, zero Path.ofEq)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.NumberFieldPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Number field structure -/

structure NumberField (K : Type u) where
  zero : K
  one : K
  add : K → K → K
  mul : K → K → K
  neg : K → K
  inv : K → K
  add_comm : ∀ a b, add a b = add b a
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  add_zero : ∀ a, add a zero = a
  mul_one : ∀ a, mul a one = a
  add_neg : ∀ a, add a (neg a) = zero
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-! ## Core field paths via stepChain -/

-- 1.
def add_comm_step (NF : NumberField A) (a b : A) : Step A :=
  Step.mk (NF.add a b) (NF.add b a) (NF.add_comm a b)

def add_comm_path (NF : NumberField A) (a b : A) :
    Path (NF.add a b) (NF.add b a) :=
  Path.stepChain (NF.add_comm a b)

-- 2.
def mul_comm_path (NF : NumberField A) (a b : A) :
    Path (NF.mul a b) (NF.mul b a) :=
  Path.stepChain (NF.mul_comm a b)

-- 3.
def add_assoc_path (NF : NumberField A) (a b c : A) :
    Path (NF.add (NF.add a b) c) (NF.add a (NF.add b c)) :=
  Path.stepChain (NF.add_assoc a b c)

-- 4.
def mul_assoc_path (NF : NumberField A) (a b c : A) :
    Path (NF.mul (NF.mul a b) c) (NF.mul a (NF.mul b c)) :=
  Path.stepChain (NF.mul_assoc a b c)

-- 5.
def add_zero_path (NF : NumberField A) (a : A) :
    Path (NF.add a NF.zero) a :=
  Path.stepChain (NF.add_zero a)

-- 6.
def mul_one_path (NF : NumberField A) (a : A) :
    Path (NF.mul a NF.one) a :=
  Path.stepChain (NF.mul_one a)

-- 7.
def add_neg_path (NF : NumberField A) (a : A) :
    Path (NF.add a (NF.neg a)) NF.zero :=
  Path.stepChain (NF.add_neg a)

-- 8.
def distrib_path (NF : NumberField A) (a b c : A) :
    Path (NF.mul a (NF.add b c)) (NF.add (NF.mul a b) (NF.mul a c)) :=
  Path.stepChain (NF.distrib a b c)

/-! ## Norm, Trace, Discriminant -/

structure NormTrace (K : Type u) (NF : NumberField K) where
  norm : K → K
  trace : K → K
  norm_mul : ∀ a b, norm (NF.mul a b) = NF.mul (norm a) (norm b)
  trace_add : ∀ a b, trace (NF.add a b) = NF.add (trace a) (trace b)
  norm_one : norm NF.one = NF.one
  trace_zero : trace NF.zero = NF.zero

-- 9.
def norm_mul_path (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.norm (NF.mul a b)) (NF.mul (NT.norm a) (NT.norm b)) :=
  Path.stepChain (NT.norm_mul a b)

-- 10.
def trace_add_path (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.trace (NF.add a b)) (NF.add (NT.trace a) (NT.trace b)) :=
  Path.stepChain (NT.trace_add a b)

-- 11.
def norm_one_path (NF : NumberField A) (NT : NormTrace A NF) :
    Path (NT.norm NF.one) NF.one :=
  Path.stepChain NT.norm_one

-- 12.
def trace_zero_path (NF : NumberField A) (NT : NormTrace A NF) :
    Path (NT.trace NF.zero) NF.zero :=
  Path.stepChain NT.trace_zero

-- 13. Transport through norm multiplicativity
theorem transport_norm_mul {D : A → Sort u} (NF : NumberField A) (NT : NormTrace A NF)
    (a b : A) (x : D (NT.norm (NF.mul a b))) :
    transport (norm_mul_path NF NT a b) x = (NT.norm_mul a b) ▸ x := by
  simp [norm_mul_path, transport]

-- 14. congrArg of norm through add commutativity
theorem congrArg_norm_add_comm (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    congrArg NT.norm (add_comm_path NF a b) =
      Path.stepChain (_root_.congrArg NT.norm (NF.add_comm a b)) := by
  simp [add_comm_path, congrArg, Path.stepChain]

-- 15. congrArg of trace through mul commutativity
theorem congrArg_trace_mul_comm (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    congrArg NT.trace (mul_comm_path NF a b) =
      Path.stepChain (_root_.congrArg NT.trace (NF.mul_comm a b)) := by
  simp [mul_comm_path, congrArg, Path.stepChain]

/-! ## Ideal structure -/

structure Ideal (K : Type u) (NF : NumberField K) where
  mem : K → Prop
  zero_mem : mem NF.zero
  add_mem : ∀ a b, mem a → mem b → mem (NF.add a b)
  mul_mem : ∀ a b, mem a → mem (NF.mul a b)

structure IdealOps (K : Type u) (NF : NumberField K) where
  prod : Ideal K NF → Ideal K NF → Ideal K NF
  unit : Ideal K NF
  prod_assoc : ∀ I J L, prod (prod I J) L = prod I (prod J L)
  prod_comm : ∀ I J, prod I J = prod J I
  prod_unit : ∀ I, prod I unit = I

-- 16.
def ideal_prod_assoc_path (NF : NumberField A) (IO : IdealOps A NF)
    (I J L : Ideal A NF) :
    Path (IO.prod (IO.prod I J) L) (IO.prod I (IO.prod J L)) :=
  Path.stepChain (IO.prod_assoc I J L)

-- 17.
def ideal_prod_comm_path (NF : NumberField A) (IO : IdealOps A NF)
    (I J : Ideal A NF) :
    Path (IO.prod I J) (IO.prod J I) :=
  Path.stepChain (IO.prod_comm I J)

-- 18.
def ideal_prod_unit_path (NF : NumberField A) (IO : IdealOps A NF)
    (I : Ideal A NF) :
    Path (IO.prod I IO.unit) I :=
  Path.stepChain (IO.prod_unit I)

-- 19. Ideal associator roundtrip
theorem ideal_assoc_roundtrip_toEq (NF : NumberField A) (IO : IdealOps A NF)
    (I J L : Ideal A NF) :
    (trans (ideal_prod_assoc_path NF IO I J L)
           (symm (ideal_prod_assoc_path NF IO I J L))).toEq =
      (refl (IO.prod (IO.prod I J) L)).toEq := by
  simp

/-! ## Prime ideal factorization -/

structure PrimeIdeal (K : Type u) (NF : NumberField K) extends Ideal K NF where
  is_prime : ∀ a b, mem (NF.mul a b) → mem a ∨ mem b
  ne_unit : ∃ a, ¬ mem a

structure DedekindDomain (K : Type u) (NF : NumberField K) (IO : IdealOps K NF) where
  factor : Ideal K NF → List (PrimeIdeal K NF)
  to_ideal : PrimeIdeal K NF → Ideal K NF
  prod_list : List (PrimeIdeal K NF) → Ideal K NF
  factorize : ∀ I, prod_list (factor I) = I

-- 20.
def dedekind_factor_path (NF : NumberField A) (IO : IdealOps A NF)
    (DD : DedekindDomain A NF IO) (I : Ideal A NF) :
    Path (DD.prod_list (DD.factor I)) I :=
  Path.stepChain (DD.factorize I)

-- 21. Factorization roundtrip
theorem dedekind_roundtrip_toEq (NF : NumberField A) (IO : IdealOps A NF)
    (DD : DedekindDomain A NF IO) (I : Ideal A NF) :
    (trans (dedekind_factor_path NF IO DD I)
           (symm (dedekind_factor_path NF IO DD I))).toEq =
      (refl (DD.prod_list (DD.factor I))).toEq := by
  simp

/-! ## Discriminant -/

structure Discriminant (K : Type u) (NF : NumberField K) (NT : NormTrace K NF) where
  disc : K
  disc_formula : disc = NT.norm NF.one

-- 22.
def disc_path (NF : NumberField A) (NT : NormTrace A NF) (D : Discriminant A NF NT) :
    Path D.disc (NT.norm NF.one) :=
  Path.stepChain D.disc_formula

-- 23. Transport through discriminant
theorem transport_disc {C : A → Sort u} (NF : NumberField A) (NT : NormTrace A NF)
    (D : Discriminant A NF NT) (x : C D.disc) :
    transport (disc_path NF NT D) x = D.disc_formula ▸ x := by
  simp [disc_path, transport]

/-! ## Path coherence for field operations -/

-- 24. Mul comm roundtrip
theorem mul_comm_roundtrip_toEq (NF : NumberField A) (a b : A) :
    (trans (mul_comm_path NF a b) (symm (mul_comm_path NF a b))).toEq =
      (refl (NF.mul a b)).toEq := by
  simp [mul_comm_path]

-- 25. Add comm roundtrip
theorem add_comm_roundtrip_toEq (NF : NumberField A) (a b : A) :
    (trans (add_comm_path NF a b) (symm (add_comm_path NF a b))).toEq =
      (refl (NF.add a b)).toEq := by
  simp [add_comm_path]

-- 26. symm commutes with congrArg for norm
theorem symm_congrArg_norm (NF : NumberField A) (NT : NormTrace A NF)
    {x y : A} (p : Path x y) :
    symm (congrArg NT.norm p) = congrArg NT.norm (symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [congrArg, symm]

-- 27. trans commutes with congrArg for trace
theorem congrArg_trace_trans (NF : NumberField A) (NT : NormTrace A NF)
    {x y z : A} (p : Path x y) (q : Path y z) :
    congrArg NT.trace (trans p q) = trans (congrArg NT.trace p) (congrArg NT.trace q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [congrArg, trans]

-- 28. Step from norm multiplicativity
def norm_mul_step (NF : NumberField A) (NT : NormTrace A NF) (a b : A) : Step A :=
  Step.mk (NT.norm (NF.mul a b)) (NF.mul (NT.norm a) (NT.norm b)) (NT.norm_mul a b)

-- 29. Step map through norm
theorem norm_mul_step_map (NF : NumberField A) (NT : NormTrace A NF) (f : A → B) (a b : A) :
    Step.map f (norm_mul_step NF NT a b) =
      Step.mk (f (NT.norm (NF.mul a b))) (f (NF.mul (NT.norm a) (NT.norm b)))
        (_root_.congrArg f (NT.norm_mul a b)) := by
  simp [norm_mul_step, Step.map]

/-! ## Compound paths via trans, symm, congrArg -/

-- 30. Distributivity then commutativity of addends
def distrib_add_comm_path (NF : NumberField A) (a b c : A) :
    Path (NF.mul a (NF.add b c)) (NF.add (NF.mul a c) (NF.mul a b)) :=
  Path.trans (distrib_path NF a b c)
    (add_comm_path NF (NF.mul a b) (NF.mul a c))

-- 31. Norm through multiplication commutativity
def norm_mul_comm_path (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.norm (NF.mul a b)) (NT.norm (NF.mul b a)) :=
  congrArg NT.norm (mul_comm_path NF a b)

-- 32. Trace through addition commutativity
def trace_add_comm_path (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.trace (NF.add a b)) (NT.trace (NF.add b a)) :=
  congrArg NT.trace (add_comm_path NF a b)

-- 33. Norm mul + unpack: norm(a*b) → norm(a)*norm(b) → norm(b)*norm(a)
def norm_mul_comm_chain (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.norm (NF.mul a b)) (NF.mul (NT.norm b) (NT.norm a)) :=
  Path.trans (norm_mul_path NF NT a b)
    (mul_comm_path NF (NT.norm a) (NT.norm b))

-- 34. Addition associativity pentagon
def add_assoc_pentagon (NF : NumberField A) (a b c d : A) :
    Path (NF.add (NF.add (NF.add a b) c) d) (NF.add a (NF.add b (NF.add c d))) :=
  Path.trans (add_assoc_path NF (NF.add a b) c d)
    (add_assoc_path NF a b (NF.add c d))

-- 35. Mul identity roundtrip: (a*1) → a → (a*1)
def mul_one_roundtrip (NF : NumberField A) (a : A) :
    Path (NF.mul a NF.one) (NF.mul a NF.one) :=
  Path.trans (mul_one_path NF a) (Path.symm (mul_one_path NF a))

-- 36. Ideal product commutativity + associativity chain
def ideal_comm_assoc_chain (NF : NumberField A) (IO : IdealOps A NF)
    (I J L : Ideal A NF) :
    Path (IO.prod (IO.prod I J) L) (IO.prod (IO.prod J I) L) :=
  congrArg (fun x => IO.prod x L) (ideal_prod_comm_path NF IO I J)

-- 37. Factorization then re-factor (roundtrip)
def dedekind_factor_roundtrip (NF : NumberField A) (IO : IdealOps A NF)
    (DD : DedekindDomain A NF IO) (I : Ideal A NF) :
    Path (DD.prod_list (DD.factor I)) (DD.prod_list (DD.factor I)) :=
  Path.trans (dedekind_factor_path NF IO DD I)
    (Path.symm (dedekind_factor_path NF IO DD I))

-- 38. Norm one then mul one: norm(1) → 1 → mul(1, 1)
def norm_one_mul_one_path (NF : NumberField A) (NT : NormTrace A NF) :
    Path (NT.norm NF.one) (NF.mul NF.one NF.one) :=
  Path.trans (norm_one_path NF NT) (Path.symm (mul_one_path NF NF.one))

end ComputationalPaths.Path.Algebra.NumberFieldPaths
