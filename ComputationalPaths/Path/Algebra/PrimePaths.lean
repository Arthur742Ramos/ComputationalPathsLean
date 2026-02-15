/-
# Prime Number Theory via Computational Paths

Divisibility, GCD/LCM as path operations, Euler's totient, prime factorization
uniqueness, Möbius function, multiplicative functions — all expressed through
`Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.PrimePaths

open ComputationalPaths.Path

universe u

variable {A : Type u}

/-! ## Divisibility lattice as path algebra -/

/-- A divisibility structure on a type with path-level operations. -/
structure DivLattice (A : Type u) where
  dvd : A → A → Prop
  gcd : A → A → A
  lcm : A → A → A
  one : A
  dvd_refl : ∀ a, dvd a a
  dvd_trans : ∀ a b c, dvd a b → dvd b c → dvd a c
  gcd_comm : ∀ a b, gcd a b = gcd b a
  lcm_comm : ∀ a b, lcm a b = lcm b a
  gcd_assoc : ∀ a b c, gcd (gcd a b) c = gcd a (gcd b c)
  lcm_assoc : ∀ a b c, lcm (lcm a b) c = lcm a (lcm b c)
  gcd_idem : ∀ a, gcd a a = a
  lcm_idem : ∀ a, lcm a a = a
  one_dvd : ∀ a, dvd one a
  gcd_dvd_left : ∀ a b, dvd (gcd a b) a
  gcd_dvd_right : ∀ a b, dvd (gcd a b) b
  dvd_lcm_left : ∀ a b, dvd a (lcm a b)
  dvd_lcm_right : ∀ a b, dvd b (lcm a b)
  absorb_gcd_lcm : ∀ a b, gcd a (lcm a b) = a
  absorb_lcm_gcd : ∀ a b, lcm a (gcd a b) = a

/-- Path witnessing gcd commutativity. -/
def gcd_comm_path (DL : DivLattice A) (a b : A) :
    Path (DL.gcd a b) (DL.gcd b a) :=
  Path.ofEq (DL.gcd_comm a b)

/-- Path witnessing lcm commutativity. -/
def lcm_comm_path (DL : DivLattice A) (a b : A) :
    Path (DL.lcm a b) (DL.lcm b a) :=
  Path.ofEq (DL.lcm_comm a b)

/-- GCD associativity as a path. -/
def gcd_assoc_path (DL : DivLattice A) (a b c : A) :
    Path (DL.gcd (DL.gcd a b) c) (DL.gcd a (DL.gcd b c)) :=
  Path.ofEq (DL.gcd_assoc a b c)

/-- LCM associativity as a path. -/
def lcm_assoc_path (DL : DivLattice A) (a b c : A) :
    Path (DL.lcm (DL.lcm a b) c) (DL.lcm a (DL.lcm b c)) :=
  Path.ofEq (DL.lcm_assoc a b c)

/-- GCD idempotence as a path. -/
def gcd_idem_path (DL : DivLattice A) (a : A) :
    Path (DL.gcd a a) a :=
  Path.ofEq (DL.gcd_idem a)

/-- LCM idempotence as a path. -/
def lcm_idem_path (DL : DivLattice A) (a : A) :
    Path (DL.lcm a a) a :=
  Path.ofEq (DL.lcm_idem a)

/-- Absorption: gcd(a, lcm(a,b)) = a. -/
def absorb_gcd_lcm_path (DL : DivLattice A) (a b : A) :
    Path (DL.gcd a (DL.lcm a b)) a :=
  Path.ofEq (DL.absorb_gcd_lcm a b)

/-- Absorption: lcm(a, gcd(a,b)) = a. -/
def absorb_lcm_gcd_path (DL : DivLattice A) (a b : A) :
    Path (DL.lcm a (DL.gcd a b)) a :=
  Path.ofEq (DL.absorb_lcm_gcd a b)

/-- GCD double commutativity round-trip semantics. -/
theorem gcd_comm_roundtrip_toEq (DL : DivLattice A) (a b : A) :
    (trans (gcd_comm_path DL a b) (symm (gcd_comm_path DL a b))).toEq =
      (refl (DL.gcd a b)).toEq := by
  simp [gcd_comm_path]

/-- LCM double commutativity round-trip semantics. -/
theorem lcm_comm_roundtrip_toEq (DL : DivLattice A) (a b : A) :
    (trans (lcm_comm_path DL a b) (symm (lcm_comm_path DL a b))).toEq =
      (refl (DL.lcm a b)).toEq := by
  simp [lcm_comm_path]

/-- Transport through gcd commutativity. -/
theorem transport_gcd_comm {B : A → Sort u} (DL : DivLattice A) (a b : A)
    (x : B (DL.gcd a b)) :
    transport (gcd_comm_path DL a b) x = DL.gcd_comm a b ▸ x := by
  simp [gcd_comm_path, transport]

/-! ## Prime structure -/

/-- Characterisation of primes within a divisibility lattice. -/
structure PrimeSpec (DL : DivLattice A) where
  isPrime : A → Prop
  prime_not_one : ∀ p, isPrime p → p ≠ DL.one
  prime_dvd_mul : ∀ p a b, isPrime p → DL.dvd p (DL.lcm a b) →
    DL.dvd p a ∨ DL.dvd p b

/-! ## Multiplicative functions via paths -/

/-- A multiplicative arithmetic function with path-level witness. -/
structure MultFun (DL : DivLattice A) (B : Type u) where
  f : A → B
  mul : A → A → B → B → B
  one_val : B
  mult_ax : ∀ a b, DL.gcd a b = DL.one →
    f (DL.lcm a b) = mul a b (f a) (f b)

/-- congrArg lifts multiplicative functions across gcd paths. -/
theorem congrArg_mult_gcd (DL : DivLattice A) {B : Type u}
    (mf : MultFun DL B) (a b : A) :
    congrArg mf.f (gcd_comm_path DL a b) =
      Path.ofEq (_root_.congrArg mf.f (DL.gcd_comm a b)) := by
  simp [gcd_comm_path, congrArg, Path.ofEq]

/-- congrArg lifts through lcm commutativity. -/
theorem congrArg_mult_lcm (DL : DivLattice A) {B : Type u}
    (mf : MultFun DL B) (a b : A) :
    congrArg mf.f (lcm_comm_path DL a b) =
      Path.ofEq (_root_.congrArg mf.f (DL.lcm_comm a b)) := by
  simp [lcm_comm_path, congrArg, Path.ofEq]

/-! ## Euler's totient as path morphism -/

/-- An Euler totient structure: a function φ with multiplicativity. -/
structure EulerTotient (DL : DivLattice A) where
  phi : A → A
  phi_mult : ∀ a b, DL.gcd a b = DL.one → phi (DL.lcm a b) = DL.lcm (phi a) (phi b)
  phi_one : phi DL.one = DL.one

/-- Path witnessing φ(1) = 1. -/
def phi_one_path (DL : DivLattice A) (ET : EulerTotient DL) :
    Path (ET.phi DL.one) DL.one :=
  Path.ofEq ET.phi_one

/-- congrArg of φ through gcd associativity path. -/
theorem phi_gcd_assoc (DL : DivLattice A) (ET : EulerTotient DL) (a b c : A) :
    congrArg ET.phi (gcd_assoc_path DL a b c) =
      Path.ofEq (_root_.congrArg ET.phi (DL.gcd_assoc a b c)) := by
  simp [gcd_assoc_path, congrArg, Path.ofEq]

/-- Transport along φ(1)=1 path. -/
theorem transport_phi_one {B : A → Sort u} (DL : DivLattice A)
    (ET : EulerTotient DL) (x : B (ET.phi DL.one)) :
    transport (phi_one_path DL ET) x = ET.phi_one ▸ x := by
  simp [phi_one_path, transport]

/-! ## Möbius function -/

/-- A Möbius function structure on a divisibility lattice. -/
structure MoebiusFun (DL : DivLattice A) where
  mu : A → A
  mu_one : mu DL.one = DL.one
  mu_sum_zero : ∀ n, n ≠ DL.one → DL.gcd (mu n) n = DL.one

/-- Path from μ(1) to 1. -/
def mu_one_path (DL : DivLattice A) (MF : MoebiusFun DL) :
    Path (MF.mu DL.one) DL.one :=
  Path.ofEq MF.mu_one

/-- Transport of type family through μ(1)=1 path. -/
theorem transport_mu_one {B : A → Sort u} (DL : DivLattice A)
    (MF : MoebiusFun DL) (x : B (MF.mu DL.one)) :
    transport (mu_one_path DL MF) x = MF.mu_one ▸ x := by
  simp [mu_one_path, transport]

/-! ## Prime factorization uniqueness -/

/-- Path-level statement of unique factorization. -/
structure UFD (DL : DivLattice A) (PS : PrimeSpec DL) where
  factors : A → List A
  all_prime : ∀ n p, p ∈ factors n → PS.isPrime p
  prod : List A → A
  factorize : ∀ n, prod (factors n) = n
  unique : ∀ n (fs : List A),
    (∀ p, p ∈ fs → PS.isPrime p) →
    prod fs = n → factors n = fs

/-- Path from product of factors back to original. -/
def factorization_path (DL : DivLattice A) (PS : PrimeSpec DL) (U : UFD DL PS)
    (n : A) : Path (U.prod (U.factors n)) n :=
  Path.ofEq (U.factorize n)

/-- Roundtrip: factor then unfactor semantic equality. -/
theorem factorization_roundtrip_toEq (DL : DivLattice A) (PS : PrimeSpec DL)
    (U : UFD DL PS) (n : A) :
    (trans (factorization_path DL PS U n)
      (symm (factorization_path DL PS U n))).toEq =
    (refl (U.prod (U.factors n))).toEq := by
  simp [factorization_path]

/-! ## GCD-LCM distributivity paths -/

/-- GCD distributes over LCM (axiom). -/
structure GCDLCMDistrib (DL : DivLattice A) where
  gcd_lcm_distrib : ∀ a b c,
    DL.gcd a (DL.lcm b c) = DL.lcm (DL.gcd a b) (DL.gcd a c)

/-- Path for distributivity. -/
def gcd_lcm_distrib_path (DL : DivLattice A) (D : GCDLCMDistrib DL)
    (a b c : A) :
    Path (DL.gcd a (DL.lcm b c)) (DL.lcm (DL.gcd a b) (DL.gcd a c)) :=
  Path.ofEq (D.gcd_lcm_distrib a b c)

/-- symm of distributivity path gives the reverse. -/
theorem gcd_lcm_distrib_symm_toEq (DL : DivLattice A) (D : GCDLCMDistrib DL)
    (a b c : A) :
    (symm (gcd_lcm_distrib_path DL D a b c)).toEq =
      (D.gcd_lcm_distrib a b c).symm := by
  simp [gcd_lcm_distrib_path]

/-! ## Path coherence in divisibility lattice -/

/-- GCD associator cancellation (toEq level). -/
theorem gcd_assoc_cancel_toEq (DL : DivLattice A) (a b c : A) :
    (trans (gcd_assoc_path DL a b c) (symm (gcd_assoc_path DL a b c))).toEq =
      (refl (DL.gcd (DL.gcd a b) c)).toEq := by
  simp [gcd_assoc_path]

/-- LCM associator cancellation (toEq level). -/
theorem lcm_assoc_cancel_toEq (DL : DivLattice A) (a b c : A) :
    (trans (lcm_assoc_path DL a b c) (symm (lcm_assoc_path DL a b c))).toEq =
      (refl (DL.lcm (DL.lcm a b) c)).toEq := by
  simp [lcm_assoc_path]

/-- congrArg of a function f through gcd idempotence. -/
theorem congrArg_gcd_idem {B : Type u} (DL : DivLattice A) (f : A → B) (a : A) :
    congrArg f (gcd_idem_path DL a) =
      Path.ofEq (_root_.congrArg f (DL.gcd_idem a)) := by
  simp [gcd_idem_path, congrArg, Path.ofEq]

/-- Transport along absorption path gcd(a, lcm(a,b)) = a. -/
theorem transport_absorb {B : A → Sort u} (DL : DivLattice A) (a b : A)
    (x : B (DL.gcd a (DL.lcm a b))) :
    transport (absorb_gcd_lcm_path DL a b) x =
      (DL.absorb_gcd_lcm a b) ▸ x := by
  simp [absorb_gcd_lcm_path, transport]

/-! ## Step-level witnesses -/

/-- A Step witnessing gcd commutativity. -/
def gcd_comm_step (DL : DivLattice A) (a b : A) : Step A :=
  Step.mk (DL.gcd a b) (DL.gcd b a) (DL.gcd_comm a b)

/-- Reversing the gcd commutativity step. -/
theorem gcd_comm_step_symm (DL : DivLattice A) (a b : A) :
    (gcd_comm_step DL a b).symm = Step.mk (DL.gcd b a) (DL.gcd a b) (DL.gcd_comm a b).symm := by
  simp [gcd_comm_step, Step.symm]

/-- Mapping a function through a gcd-comm step. -/
theorem gcd_comm_step_map {B : Type u} (DL : DivLattice A) (f : A → B)
    (a b : A) :
    Step.map f (gcd_comm_step DL a b) =
      Step.mk (f (DL.gcd a b)) (f (DL.gcd b a))
        (_root_.congrArg f (DL.gcd_comm a b)) := by
  simp [gcd_comm_step, Step.map]

/-- Two paths with same endpoints have same toEq (proof irrelevance). -/
theorem path_toEq_unique (DL : DivLattice A) (a b : A)
    (p q : Path (DL.gcd a b) (DL.gcd b a)) :
    p.toEq = q.toEq := by
  apply Subsingleton.elim

/-- congrArg commutes with trans for paths in general. -/
theorem congrArg_trans_general {B : Type u} (DL : DivLattice A) (f : A → B)
    {x y z : A} (p : Path x y) (q : Path y z) :
    congrArg f (trans p q) = trans (congrArg f p) (congrArg f q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [congrArg, trans]

/-- symm commutes with congrArg for paths. -/
theorem symm_congrArg_general {B : Type u} (DL : DivLattice A) (f : A → B)
    {x y : A} (p : Path x y) :
    symm (congrArg f p) = congrArg f (symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [congrArg, symm]

end ComputationalPaths.Path.Algebra.PrimePaths
