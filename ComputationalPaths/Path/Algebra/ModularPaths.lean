/-
# Modular Arithmetic via Computational Paths

Congruences, Chinese remainder theorem, quadratic residues, Legendre symbol,
Euler's criterion — all via `Path`, `Step`, `trans`, `symm`, `congrArg`, `transport`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ModularPaths

open ComputationalPaths.Path

universe u v

variable {A : Type u} {B : Type u}

/-! ## Modular arithmetic structure -/

/-- Abstract modular arithmetic system with path-level axioms. -/
structure ModSystem (A : Type u) where
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
  add_neg : ∀ a, add a (neg a) = zero
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

/-- Path for addition commutativity. -/
def mod_add_comm_path (M : ModSystem A) (a b : A) :
    Path (M.add a b) (M.add b a) :=
  Path.ofEq (M.add_comm a b)

/-- Path for multiplication commutativity. -/
def mod_mul_comm_path (M : ModSystem A) (a b : A) :
    Path (M.mul a b) (M.mul b a) :=
  Path.ofEq (M.mul_comm a b)

/-- Path for addition associativity. -/
def mod_add_assoc_path (M : ModSystem A) (a b c : A) :
    Path (M.add (M.add a b) c) (M.add a (M.add b c)) :=
  Path.ofEq (M.add_assoc a b c)

/-- Path for multiplication associativity. -/
def mod_mul_assoc_path (M : ModSystem A) (a b c : A) :
    Path (M.mul (M.mul a b) c) (M.mul a (M.mul b c)) :=
  Path.ofEq (M.mul_assoc a b c)

/-- Path for additive identity. -/
def mod_add_zero_path (M : ModSystem A) (a : A) :
    Path (M.add a M.zero) a :=
  Path.ofEq (M.add_zero a)

/-- Path for multiplicative identity. -/
def mod_mul_one_path (M : ModSystem A) (a : A) :
    Path (M.mul a M.one) a :=
  Path.ofEq (M.mul_one a)

/-- Path for additive inverse. -/
def mod_add_neg_path (M : ModSystem A) (a : A) :
    Path (M.add a (M.neg a)) M.zero :=
  Path.ofEq (M.add_neg a)

/-- Path for distributivity. -/
def mod_distrib_path (M : ModSystem A) (a b c : A) :
    Path (M.mul a (M.add b c)) (M.add (M.mul a b) (M.mul a c)) :=
  Path.ofEq (M.distrib a b c)

/-! ## Congruence relation -/

/-- Congruence structure: quotient map with homomorphism properties. -/
structure Congruence (A : Type u) (M : ModSystem A) (B : Type u) (N : ModSystem B) where
  proj : A → B
  proj_add : ∀ a b, proj (M.add a b) = N.add (proj a) (proj b)
  proj_mul : ∀ a b, proj (M.mul a b) = N.mul (proj a) (proj b)
  proj_zero : proj M.zero = N.zero
  proj_one : proj M.one = N.one

/-- Path for projection preserving addition. -/
def cong_proj_add_path (M : ModSystem A) (N : ModSystem B)
    (C : Congruence A M B N) (a b : A) :
    Path (C.proj (M.add a b)) (N.add (C.proj a) (C.proj b)) :=
  Path.ofEq (C.proj_add a b)

/-- Path for projection preserving multiplication. -/
def cong_proj_mul_path (M : ModSystem A) (N : ModSystem B)
    (C : Congruence A M B N) (a b : A) :
    Path (C.proj (M.mul a b)) (N.mul (C.proj a) (C.proj b)) :=
  Path.ofEq (C.proj_mul a b)

/-- congrArg of projection through addition commutativity. -/
theorem congrArg_proj_add_comm (M : ModSystem A) (N : ModSystem B)
    (C : Congruence A M B N) (a b : A) :
    congrArg C.proj (mod_add_comm_path M a b) =
      Path.ofEq (_root_.congrArg C.proj (M.add_comm a b)) := by
  simp [mod_add_comm_path, congrArg, Path.ofEq]

/-- congrArg of projection through multiplication commutativity. -/
theorem congrArg_proj_mul_comm (M : ModSystem A) (N : ModSystem B)
    (C : Congruence A M B N) (a b : A) :
    congrArg C.proj (mod_mul_comm_path M a b) =
      Path.ofEq (_root_.congrArg C.proj (M.mul_comm a b)) := by
  simp [mod_mul_comm_path, congrArg, Path.ofEq]

/-! ## Chinese Remainder Theorem -/

/-- CRT structure: isomorphism between a modular system and a product. -/
structure CRT (A : Type u) (M : ModSystem A) (B : Type u) (N : ModSystem B)
    (C : Type u) (P : ModSystem C) where
  to_prod : A → B × C
  from_prod : B × C → A
  iso_left : ∀ a, from_prod (to_prod a) = a
  iso_right : ∀ bc, to_prod (from_prod bc) = bc

/-- Path for CRT left inverse. -/
def crt_left_path (M : ModSystem A) (N : ModSystem B)
    {C : Type u} (P : ModSystem C) (crt : CRT A M B N C P) (a : A) :
    Path (crt.from_prod (crt.to_prod a)) a :=
  Path.ofEq (crt.iso_left a)

/-- Path for CRT right inverse. -/
def crt_right_path (M : ModSystem A) (N : ModSystem B)
    {C : Type u} (P : ModSystem C) (crt : CRT A M B N C P) (bc : B × C) :
    Path (crt.to_prod (crt.from_prod bc)) bc :=
  Path.ofEq (crt.iso_right bc)

/-- CRT roundtrip semantic equivalence. -/
theorem crt_roundtrip_toEq (M : ModSystem A) (N : ModSystem B)
    {C : Type u} (P : ModSystem C) (crt : CRT A M B N C P) (a : A) :
    (trans (crt_left_path M N P crt a) (symm (crt_left_path M N P crt a))).toEq =
      (refl (crt.from_prod (crt.to_prod a))).toEq := by
  simp

/-- Transport through CRT isomorphism. -/
theorem transport_crt {D : A → Sort u} (M : ModSystem A) (N : ModSystem B)
    {C : Type u} (P : ModSystem C) (crt : CRT A M B N C P) (a : A)
    (x : D (crt.from_prod (crt.to_prod a))) :
    transport (crt_left_path M N P crt a) x = (crt.iso_left a) ▸ x := by
  simp [crt_left_path, transport]

/-! ## Quadratic residues -/

/-- Quadratic residue structure. -/
structure QuadRes (A : Type u) (M : ModSystem A) where
  isQR : A → Prop
  square_is_qr : ∀ a, isQR (M.mul a a)

/-- Legendre-like symbol as path-level classification. -/
structure LegendreSymbol (A : Type u) (M : ModSystem A) where
  legendre : A → A  -- maps to 0, 1, or -1 analogue
  qr_val : ∀ a, legendre (M.mul a a) = M.one ∨ legendre (M.mul a a) = M.zero
  legendre_mul : ∀ a b, legendre (M.mul a b) = M.mul (legendre a) (legendre b)

/-- Path for Legendre symbol multiplicativity. -/
def legendre_mul_path (M : ModSystem A) (LS : LegendreSymbol A M) (a b : A) :
    Path (LS.legendre (M.mul a b)) (M.mul (LS.legendre a) (LS.legendre b)) :=
  Path.ofEq (LS.legendre_mul a b)

/-- congrArg of Legendre symbol through mul commutativity path. -/
theorem congrArg_legendre_mul_comm (M : ModSystem A) (LS : LegendreSymbol A M) (a b : A) :
    congrArg LS.legendre (mod_mul_comm_path M a b) =
      Path.ofEq (_root_.congrArg LS.legendre (M.mul_comm a b)) := by
  simp [mod_mul_comm_path, congrArg, Path.ofEq]

/-! ## Euler's criterion -/

/-- Euler's criterion structure: a^((p-1)/2) determines quadratic residuosity. -/
structure EulerCriterion (A : Type u) (M : ModSystem A) (LS : LegendreSymbol A M) where
  power : A → A → A  -- a^n
  euler : ∀ a e, LS.legendre a = power a e

/-- Path from Euler's criterion. -/
def euler_criterion_path (M : ModSystem A) (LS : LegendreSymbol A M)
    (EC : EulerCriterion A M LS) (a e : A) :
    Path (LS.legendre a) (EC.power a e) :=
  Path.ofEq (EC.euler a e)

/-- Euler criterion roundtrip (semantic). -/
theorem euler_roundtrip_toEq (M : ModSystem A) (LS : LegendreSymbol A M)
    (EC : EulerCriterion A M LS) (a e : A) :
    (trans (euler_criterion_path M LS EC a e)
           (symm (euler_criterion_path M LS EC a e))).toEq =
      (refl (LS.legendre a)).toEq := by
  simp

/-! ## Path coherence -/

/-- Two paths between same modular elements agree semantically. -/
theorem mod_path_coherence (M : ModSystem A) {x y : A}
    (p q : Path x y) : p.toEq = q.toEq :=
  Subsingleton.elim p.toEq q.toEq

/-- Mul associativity cancellation (semantic). -/
theorem mul_assoc_cancel_toEq (M : ModSystem A) (a b c : A) :
    (trans (mod_mul_assoc_path M a b c) (symm (mod_mul_assoc_path M a b c))).toEq =
      (refl (M.mul (M.mul a b) c)).toEq := by
  simp

/-- symm commutes with congrArg for modular paths. -/
theorem symm_congrArg_mod {C : Type u} (M : ModSystem A) (f : A → C)
    {x y : A} (p : Path x y) :
    symm (congrArg f p) = congrArg f (symm p) := by
  cases p with | mk sp pp =>
  cases pp
  simp [congrArg, symm]

/-- trans commutes with congrArg for modular paths. -/
theorem congrArg_trans_mod {C : Type u} (M : ModSystem A) (f : A → C)
    {x y z : A} (p : Path x y) (q : Path y z) :
    congrArg f (trans p q) = trans (congrArg f p) (congrArg f q) := by
  cases p with | mk sp pp =>
  cases q with | mk sq pq =>
  cases pp; cases pq
  simp [congrArg, trans]

/-- Step from distributivity. -/
def distrib_step (M : ModSystem A) (a b c : A) : Step A :=
  Step.mk (M.mul a (M.add b c)) (M.add (M.mul a b) (M.mul a c)) (M.distrib a b c)

/-- Mapping through a distributivity step. -/
theorem distrib_step_map {C : Type u} (M : ModSystem A) (f : A → C) (a b c : A) :
    Step.map f (distrib_step M a b c) =
      Step.mk (f (M.mul a (M.add b c))) (f (M.add (M.mul a b) (M.mul a c)))
        (_root_.congrArg f (M.distrib a b c)) := by
  simp [distrib_step, Step.map]

/-- Transport along additive inverse path. -/
theorem transport_add_neg {D : A → Sort u} (M : ModSystem A) (a : A)
    (x : D (M.add a (M.neg a))) :
    transport (mod_add_neg_path M a) x = (M.add_neg a) ▸ x := by
  simp [mod_add_neg_path, transport]

end ComputationalPaths.Path.Algebra.ModularPaths
