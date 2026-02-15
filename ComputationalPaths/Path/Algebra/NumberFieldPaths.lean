/-
# Algebraic Number Theory via Computational Paths

Number fields, rings of integers, norms, traces, discriminants, ideal factorization
— all encoded through `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.NumberFieldPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type v}

/-! ## Number field structure -/

/-- Abstract number field with path-level algebraic operations. -/
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

/-- Path witnessing commutativity of addition. -/
def add_comm_path (NF : NumberField A) (a b : A) :
    Path (NF.add a b) (NF.add b a) :=
  Path.ofEq (NF.add_comm a b)

/-- Path witnessing commutativity of multiplication. -/
def mul_comm_path (NF : NumberField A) (a b : A) :
    Path (NF.mul a b) (NF.mul b a) :=
  Path.ofEq (NF.mul_comm a b)

/-- Path witnessing associativity of addition. -/
def add_assoc_path (NF : NumberField A) (a b c : A) :
    Path (NF.add (NF.add a b) c) (NF.add a (NF.add b c)) :=
  Path.ofEq (NF.add_assoc a b c)

/-- Path witnessing associativity of multiplication. -/
def mul_assoc_path (NF : NumberField A) (a b c : A) :
    Path (NF.mul (NF.mul a b) c) (NF.mul a (NF.mul b c)) :=
  Path.ofEq (NF.mul_assoc a b c)

/-- Path witnessing a + 0 = a. -/
def add_zero_path (NF : NumberField A) (a : A) :
    Path (NF.add a NF.zero) a :=
  Path.ofEq (NF.add_zero a)

/-- Path witnessing a * 1 = a. -/
def mul_one_path (NF : NumberField A) (a : A) :
    Path (NF.mul a NF.one) a :=
  Path.ofEq (NF.mul_one a)

/-- Path witnessing a + (-a) = 0. -/
def add_neg_path (NF : NumberField A) (a : A) :
    Path (NF.add a (NF.neg a)) NF.zero :=
  Path.ofEq (NF.add_neg a)

/-- Distributivity path. -/
def distrib_path (NF : NumberField A) (a b c : A) :
    Path (NF.mul a (NF.add b c)) (NF.add (NF.mul a b) (NF.mul a c)) :=
  Path.ofEq (NF.distrib a b c)

/-! ## Norm, Trace, Discriminant -/

/-- Norm/Trace structure on a number field. -/
structure NormTrace (K : Type u) (NF : NumberField K) where
  norm : K → K
  trace : K → K
  norm_mul : ∀ a b, norm (NF.mul a b) = NF.mul (norm a) (norm b)
  trace_add : ∀ a b, trace (NF.add a b) = NF.add (trace a) (trace b)
  norm_one : norm NF.one = NF.one
  trace_zero : trace NF.zero = NF.zero

/-- Path witnessing multiplicativity of norm. -/
def norm_mul_path (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.norm (NF.mul a b)) (NF.mul (NT.norm a) (NT.norm b)) :=
  Path.ofEq (NT.norm_mul a b)

/-- Path witnessing additivity of trace. -/
def trace_add_path (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    Path (NT.trace (NF.add a b)) (NF.add (NT.trace a) (NT.trace b)) :=
  Path.ofEq (NT.trace_add a b)

/-- Path witnessing norm(1) = 1. -/
def norm_one_path (NF : NumberField A) (NT : NormTrace A NF) :
    Path (NT.norm NF.one) NF.one :=
  Path.ofEq NT.norm_one

/-- Path witnessing trace(0) = 0. -/
def trace_zero_path (NF : NumberField A) (NT : NormTrace A NF) :
    Path (NT.trace NF.zero) NF.zero :=
  Path.ofEq NT.trace_zero

/-- Transport through norm multiplicativity. -/
theorem transport_norm_mul {D : A → Sort u} (NF : NumberField A) (NT : NormTrace A NF)
    (a b : A) (x : D (NT.norm (NF.mul a b))) :
    transport (norm_mul_path NF NT a b) x = (NT.norm_mul a b) ▸ x := by
  simp [norm_mul_path, transport]

/-- congrArg of norm through add commutativity path. -/
theorem congrArg_norm_add_comm (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    congrArg NT.norm (add_comm_path NF a b) =
      Path.ofEq (_root_.congrArg NT.norm (NF.add_comm a b)) := by
  simp [add_comm_path, congrArg, Path.ofEq]

/-- congrArg of trace through mul commutativity path. -/
theorem congrArg_trace_mul_comm (NF : NumberField A) (NT : NormTrace A NF) (a b : A) :
    congrArg NT.trace (mul_comm_path NF a b) =
      Path.ofEq (_root_.congrArg NT.trace (NF.mul_comm a b)) := by
  simp [mul_comm_path, congrArg, Path.ofEq]

/-! ## Ideal structure -/

/-- Abstract ideal in a number ring. -/
structure Ideal (K : Type u) (NF : NumberField K) where
  mem : K → Prop
  zero_mem : mem NF.zero
  add_mem : ∀ a b, mem a → mem b → mem (NF.add a b)
  mul_mem : ∀ a b, mem a → mem (NF.mul a b)

/-- Ideal product operation. -/
structure IdealOps (K : Type u) (NF : NumberField K) where
  prod : Ideal K NF → Ideal K NF → Ideal K NF
  unit : Ideal K NF
  prod_assoc : ∀ I J L, prod (prod I J) L = prod I (prod J L)
  prod_comm : ∀ I J, prod I J = prod J I
  prod_unit : ∀ I, prod I unit = I

/-- Path for ideal product associativity. -/
def ideal_prod_assoc_path (NF : NumberField A) (IO : IdealOps A NF)
    (I J L : Ideal A NF) :
    Path (IO.prod (IO.prod I J) L) (IO.prod I (IO.prod J L)) :=
  Path.ofEq (IO.prod_assoc I J L)

/-- Path for ideal product commutativity. -/
def ideal_prod_comm_path (NF : NumberField A) (IO : IdealOps A NF)
    (I J : Ideal A NF) :
    Path (IO.prod I J) (IO.prod J I) :=
  Path.ofEq (IO.prod_comm I J)

/-- Path for ideal product unit. -/
def ideal_prod_unit_path (NF : NumberField A) (IO : IdealOps A NF)
    (I : Ideal A NF) :
    Path (IO.prod I IO.unit) I :=
  Path.ofEq (IO.prod_unit I)

/-- Ideal product associator roundtrip (semantic). -/
theorem ideal_assoc_roundtrip_toEq (NF : NumberField A) (IO : IdealOps A NF)
    (I J L : Ideal A NF) :
    (trans (ideal_prod_assoc_path NF IO I J L)
           (symm (ideal_prod_assoc_path NF IO I J L))).toEq =
      (refl (IO.prod (IO.prod I J) L)).toEq := by
  simp

/-! ## Prime ideal factorization -/

/-- A prime ideal structure. -/
structure PrimeIdeal (K : Type u) (NF : NumberField K) extends Ideal K NF where
  is_prime : ∀ a b, mem (NF.mul a b) → mem a ∨ mem b
  ne_unit : ∃ a, ¬ mem a

/-- Dedekind domain: unique factorization of ideals into primes. -/
structure DedekindDomain (K : Type u) (NF : NumberField K) (IO : IdealOps K NF) where
  factor : Ideal K NF → List (PrimeIdeal K NF)
  to_ideal : PrimeIdeal K NF → Ideal K NF
  prod_list : List (PrimeIdeal K NF) → Ideal K NF
  factorize : ∀ I, prod_list (factor I) = I

/-- Path from factored form to original ideal. -/
def dedekind_factor_path (NF : NumberField A) (IO : IdealOps A NF)
    (DD : DedekindDomain A NF IO) (I : Ideal A NF) :
    Path (DD.prod_list (DD.factor I)) I :=
  Path.ofEq (DD.factorize I)

/-- Factorization roundtrip (semantic). -/
theorem dedekind_roundtrip_toEq (NF : NumberField A) (IO : IdealOps A NF)
    (DD : DedekindDomain A NF IO) (I : Ideal A NF) :
    (trans (dedekind_factor_path NF IO DD I)
           (symm (dedekind_factor_path NF IO DD I))).toEq =
      (refl (DD.prod_list (DD.factor I))).toEq := by
  simp

/-! ## Discriminant -/

/-- Discriminant structure. -/
structure Discriminant (K : Type u) (NF : NumberField K) (NT : NormTrace K NF) where
  disc : K
  disc_formula : disc = NT.norm NF.one  -- simplified

/-- Path for discriminant formula. -/
def disc_path (NF : NumberField A) (NT : NormTrace A NF) (D : Discriminant A NF NT) :
    Path D.disc (NT.norm NF.one) :=
  Path.ofEq D.disc_formula

/-- Transport through discriminant formula. -/
theorem transport_disc {C : A → Sort u} (NF : NumberField A) (NT : NormTrace A NF)
    (D : Discriminant A NF NT) (x : C D.disc) :
    transport (disc_path NF NT D) x = D.disc_formula ▸ x := by
  simp [disc_path, transport]

/-! ## Path coherence for field operations -/

/-- Multiplication commutativity roundtrip (semantic). -/
theorem mul_comm_roundtrip_toEq (NF : NumberField A) (a b : A) :
    (trans (mul_comm_path NF a b) (symm (mul_comm_path NF a b))).toEq =
      (refl (NF.mul a b)).toEq := by
  simp [mul_comm_path]

/-- Addition commutativity roundtrip (semantic). -/
theorem add_comm_roundtrip_toEq (NF : NumberField A) (a b : A) :
    (trans (add_comm_path NF a b) (symm (add_comm_path NF a b))).toEq =
      (refl (NF.add a b)).toEq := by
  simp [add_comm_path]

/-- symm commutes with congrArg for norm on field paths. -/
theorem symm_congrArg_norm (NF : NumberField A) (NT : NormTrace A NF)
    {x y : A} (p : Path x y) :
    symm (congrArg NT.norm p) = congrArg NT.norm (symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [congrArg, symm]

/-- trans commutes with congrArg for trace. -/
theorem congrArg_trace_trans (NF : NumberField A) (NT : NormTrace A NF)
    {x y z : A} (p : Path x y) (q : Path y z) :
    congrArg NT.trace (trans p q) = trans (congrArg NT.trace p) (congrArg NT.trace q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [congrArg, trans]

/-- Step from norm multiplicativity. -/
def norm_mul_step (NF : NumberField A) (NT : NormTrace A NF) (a b : A) : Step A :=
  Step.mk (NT.norm (NF.mul a b)) (NF.mul (NT.norm a) (NT.norm b)) (NT.norm_mul a b)

/-- Mapping norm through a norm_mul step. -/
theorem norm_mul_step_map (NF : NumberField A) (NT : NormTrace A NF) (f : A → B) (a b : A) :
    Step.map f (norm_mul_step NF NT a b) =
      Step.mk (f (NT.norm (NF.mul a b))) (f (NF.mul (NT.norm a) (NT.norm b)))
        (_root_.congrArg f (NT.norm_mul a b)) := by
  simp [norm_mul_step, Step.map]

end ComputationalPaths.Path.Algebra.NumberFieldPaths
