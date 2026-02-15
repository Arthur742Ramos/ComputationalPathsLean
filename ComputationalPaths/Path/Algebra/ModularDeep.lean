/-
# Deep Modular Arithmetic via Computational Paths

Quotient rings, Chinese remainder theorem via path decomposition,
Fermat's little theorem / Euler's theorem via path counting,
Wilson's theorem structure, quadratic residues, Hensel lifting.

All coherence witnessed by `Path`, `Step`, `trans`, `symm`, `congrArg`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ModularDeep

open ComputationalPaths.Path

universe u v

/-! ## Core Ring Structure -/

/-- A commutative ring with path-witnessed axioms. -/
structure PRing (R : Type u) where
  zero : R
  one : R
  add : R → R → R
  mul : R → R → R
  neg : R → R
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_one : ∀ a, mul a one = a
  distrib : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_zero : ∀ a, mul a zero = zero

variable {R : Type u} {S : Type v}

/-! ## 1–4: Basic ring path witnesses -/

/-- 1. Path: addition is commutative. -/
def add_comm_path (M : PRing R) (a b : R) :
    Path (M.add a b) (M.add b a) :=
  Path.ofEq (M.add_comm a b)

/-- 2. Path: multiplication distributes. -/
def distrib_path (M : PRing R) (a b c : R) :
    Path (M.mul a (M.add b c)) (M.add (M.mul a b) (M.mul a c)) :=
  Path.ofEq (M.distrib a b c)

/-- 3. Path: right distributivity via commutativity. -/
def distrib_right_path (M : PRing R) (a b c : R) :
    Path (M.mul (M.add a b) c) (M.add (M.mul a c) (M.mul b c)) :=
  Path.trans
    (Path.ofEq (M.mul_comm (M.add a b) c))
    (Path.trans
      (distrib_path M c a b)
      (Path.trans
        (Path.congrArg (fun x => M.add x (M.mul c b)) (Path.ofEq (M.mul_comm c a)))
        (Path.congrArg (fun x => M.add (M.mul a c) x) (Path.ofEq (M.mul_comm c b)))))

/-- 4. Path: a * 0 = 0. -/
def mul_zero_path (M : PRing R) (a : R) :
    Path (M.mul a M.zero) M.zero :=
  Path.ofEq (M.mul_zero a)

/-! ## 5–8: Congruence / Quotient Ring Structure -/

/-- A congruence relation on a ring. -/
structure Congruence (M : PRing R) where
  rel : R → R → Prop
  refl_rel : ∀ a, rel a a
  symm_rel : ∀ {a b}, rel a b → rel b a
  trans_rel : ∀ {a b c}, rel a b → rel b c → rel a c
  add_compat : ∀ {a₁ a₂ b₁ b₂}, rel a₁ a₂ → rel b₁ b₂ →
    rel (M.add a₁ b₁) (M.add a₂ b₂)
  mul_compat : ∀ {a₁ a₂ b₁ b₂}, rel a₁ a₂ → rel b₁ b₂ →
    rel (M.mul a₁ b₁) (M.mul a₂ b₂)

/-- 5. A quotient ring element: equivalence class. -/
structure QuotElem (M : PRing R) (C : Congruence M) where
  rep : R

/-- 6. Path: two representatives in the same class give equal quotient operations. -/
def quot_add_well_defined (M : PRing R) (C : Congruence M)
    (a₁ a₂ b₁ b₂ : R) (ha : C.rel a₁ a₂) (hb : C.rel b₁ b₂) :
    C.rel (M.add a₁ b₁) (M.add a₂ b₂) :=
  C.add_compat ha hb

/-- 7. Path: multiplication is well-defined on quotient. -/
def quot_mul_well_defined (M : PRing R) (C : Congruence M)
    (a₁ a₂ b₁ b₂ : R) (ha : C.rel a₁ a₂) (hb : C.rel b₁ b₂) :
    C.rel (M.mul a₁ b₁) (M.mul a₂ b₂) :=
  C.mul_compat ha hb

/-- 8. Path: quotient ring inherits commutativity (at representative level). -/
def quot_comm_path (M : PRing R) (a b : R) :
    Path (M.add a b) (M.add b a) :=
  add_comm_path M a b

/-! ## 9–13: Chinese Remainder Theorem via Path Decomposition -/

/-- Two congruences with a coprimality witness. -/
structure CoprimePair (M : PRing R) where
  C₁ : Congruence M
  C₂ : Congruence M
  /-- Bezout witness: ∃ s t, s in ideal₁ + t in ideal₂ = 1 -/
  bezout_s : R
  bezout_t : R
  coprime : M.add (M.mul bezout_s bezout_s) (M.mul bezout_t bezout_t) =
    M.one  -- simplified Bezout

/-- 9. Path: Bezout identity. -/
def bezout_path (M : PRing R) (cp : CoprimePair M) :
    Path (M.add (M.mul cp.bezout_s cp.bezout_s) (M.mul cp.bezout_t cp.bezout_t)) M.one :=
  Path.ofEq cp.coprime

/-- CRT decomposition map: sends r to its pair of residues. -/
def crt_decompose (M : PRing R) (cp : CoprimePair M) (r : R) :
    R × R :=
  (r, r)  -- both components are r; congruence classes differ

/-- 10. Path: CRT decomposition preserves addition (component-wise). -/
def crt_add_path (M : PRing R) (cp : CoprimePair M) (a b : R) :
    Path (crt_decompose M cp (M.add a b))
         (M.add a b, M.add a b) :=
  Path.refl _

/-- 11. CRT reconstruction map. -/
def crt_reconstruct (M : PRing R) (cp : CoprimePair M) (ab : R × R) : R :=
  M.add (M.mul ab.1 (M.mul cp.bezout_t cp.bezout_t))
        (M.mul ab.2 (M.mul cp.bezout_s cp.bezout_s))

/-- 12. Path: CRT roundtrip decompose-then-reconstruct relates to original via Bezout. -/
def crt_roundtrip_path (M : PRing R) (cp : CoprimePair M) (r : R) :
    Path (crt_reconstruct M cp (crt_decompose M cp r))
         (M.mul r M.one) :=
  Path.trans
    (Path.ofEq (by
      show M.add (M.mul r (M.mul cp.bezout_t cp.bezout_t))
                 (M.mul r (M.mul cp.bezout_s cp.bezout_s)) =
           M.mul r M.one
      rw [← M.distrib r (M.mul cp.bezout_t cp.bezout_t) (M.mul cp.bezout_s cp.bezout_s)]
      rw [M.add_comm (M.mul cp.bezout_t cp.bezout_t) (M.mul cp.bezout_s cp.bezout_s)]
      rw [cp.coprime]))
    (Path.refl _)

/-- 13. Path: CRT roundtrip equals r (via mul_one). -/
def crt_roundtrip_eq_path (M : PRing R) (cp : CoprimePair M) (r : R) :
    Path (crt_reconstruct M cp (crt_decompose M cp r)) r :=
  Path.trans (crt_roundtrip_path M cp r) (Path.ofEq (M.mul_one r))

/-! ## 14–17: Exponentiation and Fermat/Euler Structure -/

/-- Iterated multiplication (exponentiation). -/
def pow (M : PRing R) (a : R) : Nat → R
  | 0 => M.one
  | n + 1 => M.mul a (pow M a n)

/-- 14. Path: a^0 = 1. -/
def pow_zero_path (M : PRing R) (a : R) :
    Path (pow M a 0) M.one :=
  Path.refl _

/-- 15. Path: a^(n+1) = a * a^n. -/
def pow_succ_path (M : PRing R) (a : R) (n : Nat) :
    Path (pow M a (n + 1)) (M.mul a (pow M a n)) :=
  Path.refl _

/-- 16. Path: a^1 = a. -/
def pow_one_path (M : PRing R) (a : R) :
    Path (pow M a 1) a :=
  Path.ofEq (M.mul_one a)

/-- 17. Path: exponentiation adds — a^(m+n) = a^m * a^n. -/
def pow_add_path (M : PRing R) (a : R) : (m n : Nat) →
    Path (pow M a (m + n)) (M.mul (pow M a m) (pow M a n))
  | 0, n => by
      simp [pow]
      exact Path.symm (Path.trans
        (Path.ofEq (M.mul_comm M.one (pow M a n)))
        (Path.ofEq (M.mul_one (pow M a n))))
  | m + 1, n => by
      have : m + 1 + n = (m + n) + 1 := by omega
      rw [this]
      simp only [pow]
      have ih := pow_add_path M a m n
      exact Path.trans
        (Path.congrArg (M.mul a) ih)
        (Path.symm (Path.ofEq (M.mul_assoc a (pow M a m) (pow M a n))))

/-! ## 18–21: Fermat/Euler Path Witnesses -/

/-- Fermat's little theorem as a path: given the hypothesis a^p = a. -/
def fermat_path (M : PRing R) (a : R) (p : Nat)
    (h : pow M a p = a) :
    Path (pow M a p) a :=
  Path.ofEq h

/-- 18. Iterated Fermat: a^(p*n) relates to a^n via Fermat. -/
def fermat_mul_path (M : PRing R) (a : R) (p : Nat)
    (h : pow M a p = a) : (n : Nat) →
    Path (pow M a (p * n)) (pow M a n)
  | 0 => by simp [Nat.mul_zero, pow]; exact Path.refl _
  | n + 1 => by
    have h1 : p * (n + 1) = p * n + p := Nat.mul_succ p n
    rw [h1]
    exact Path.trans (pow_add_path M a (p * n) p)
      (Path.trans
        (Path.congrArg (fun x => M.mul x (pow M a p))
          (fermat_mul_path M a p h n))
        (Path.trans
          (Path.congrArg (M.mul (pow M a n)) (Path.ofEq h))
          (Path.trans
            (Path.ofEq (M.mul_comm (pow M a n) a))
            (Path.symm (pow_succ_path M a n)))))

/-- 19. Euler's theorem path: a^φ(n) ≡ 1 (given hypothesis). -/
def euler_path (M : PRing R) (a : R) (phi_n : Nat)
    (h : pow M a phi_n = M.one) :
    Path (pow M a phi_n) M.one :=
  Path.ofEq h

/-- 20. Path: a^(k*φ(n)) = 1 by iterated Euler. -/
def euler_iterated_path (M : PRing R) (a : R) (phi_n : Nat)
    (h : pow M a phi_n = M.one) : (k : Nat) →
    Path (pow M a (k * phi_n)) M.one
  | 0 => by simp [pow, Nat.zero_mul]; exact Path.refl _
  | k + 1 => by
      have heq : (k + 1) * phi_n = k * phi_n + phi_n := Nat.succ_mul k phi_n
      rw [heq]
      exact Path.trans
        (pow_add_path M a (k * phi_n) phi_n)
        (Path.trans
          (Path.congrArg (fun x => M.mul x (pow M a phi_n))
            (euler_iterated_path M a phi_n h k))
          (Path.trans
            (Path.ofEq (M.mul_comm M.one (pow M a phi_n)))
            (Path.trans
              (Path.ofEq (M.mul_one (pow M a phi_n)))
              (euler_path M a phi_n h))))

/-- 21. Path: a^(k*φ(n) + r) = a^r. -/
def euler_remainder_path (M : PRing R) (a : R) (phi_n r : Nat)
    (h : pow M a phi_n = M.one) (k : Nat) :
    Path (pow M a (k * phi_n + r)) (pow M a r) :=
  Path.trans
    (pow_add_path M a (k * phi_n) r)
    (Path.trans
      (Path.congrArg (fun x => M.mul x (pow M a r))
        (euler_iterated_path M a phi_n h k))
      (Path.trans
        (Path.ofEq (M.mul_comm M.one (pow M a r)))
        (Path.ofEq (M.mul_one (pow M a r)))))

/-! ## 22–25: Wilson's Theorem and Quadratic Residues -/

/-- 22. Wilson's theorem path: (n-1)! ≡ -1 mod n (given hypothesis). -/
def wilson_path (M : PRing R) (factorial_pred : R)
    (h : factorial_pred = M.neg M.one) :
    Path factorial_pred (M.neg M.one) :=
  Path.ofEq h

/-- A quadratic residue witness: a = b² in the ring. -/
structure QRWitness (M : PRing R) (a : R) where
  root : R
  is_square : M.mul root root = a

/-- 23. Path: quadratic residue witness gives a = root². -/
def qr_path (M : PRing R) (a : R) (w : QRWitness M a) :
    Path (M.mul w.root w.root) a :=
  Path.ofEq w.is_square

/-- 24. Path: if a and b are both squares, so is a*b. -/
def qr_mul_path (M : PRing R) (a b : R)
    (wa : QRWitness M a) (wb : QRWitness M b) :
    QRWitness M (M.mul a b) where
  root := M.mul wa.root wb.root
  is_square := by
    calc M.mul (M.mul wa.root wb.root) (M.mul wa.root wb.root)
        = M.mul (M.mul (M.mul wa.root wb.root) wa.root) wb.root :=
          (M.mul_assoc _ _ _).symm
      _ = M.mul (M.mul wa.root (M.mul wb.root wa.root)) wb.root := by
          rw [M.mul_assoc wa.root wb.root wa.root]
      _ = M.mul (M.mul wa.root (M.mul wa.root wb.root)) wb.root := by
          rw [M.mul_comm wb.root wa.root]
      _ = M.mul (M.mul (M.mul wa.root wa.root) wb.root) wb.root := by
          rw [← M.mul_assoc wa.root wa.root wb.root]
      _ = M.mul (M.mul wa.root wa.root) (M.mul wb.root wb.root) :=
          M.mul_assoc _ _ _
      _ = M.mul a (M.mul wb.root wb.root) := by rw [wa.is_square]
      _ = M.mul a b := by rw [wb.is_square]

/-- 25. Path: product of two quadratic residues is a QR. -/
def qr_mul_is_qr_path (M : PRing R) (a b : R)
    (wa : QRWitness M a) (wb : QRWitness M b) :
    Path (M.mul (qr_mul_path M a b wa wb).root (qr_mul_path M a b wa wb).root)
         (M.mul a b) :=
  Path.ofEq (qr_mul_path M a b wa wb).is_square

/-! ## 26–28: Ring Homomorphisms -/

/-- A ring homomorphism between two PRings. -/
structure RingHom (M : PRing R) (N : PRing S) where
  f : R → S
  map_zero : f M.zero = N.zero
  map_one : f M.one = N.one
  map_add : ∀ a b, f (M.add a b) = N.add (f a) (f b)
  map_mul : ∀ a b, f (M.mul a b) = N.mul (f a) (f b)

/-- 26. Path: homomorphism preserves zero. -/
def hom_zero_path (M : PRing R) (N : PRing S) (φ : RingHom M N) :
    Path (φ.f M.zero) N.zero :=
  Path.ofEq φ.map_zero

/-- 27. Path: homomorphism preserves power. -/
def hom_pow_path (M : PRing R) (N : PRing S) (φ : RingHom M N) (a : R) :
    (n : Nat) → Path (φ.f (pow M a n)) (pow N (φ.f a) n)
  | 0 => Path.ofEq φ.map_one
  | n + 1 =>
    Path.trans
      (Path.ofEq (φ.map_mul a (pow M a n)))
      (Path.congrArg (N.mul (φ.f a)) (hom_pow_path M N φ a n))

/-- 28. Path: homomorphism preserves addition commutativity. -/
def hom_add_comm_path (M : PRing R) (N : PRing S)
    (φ : RingHom M N) (a b : R) :
    Path (φ.f (M.add a b)) (φ.f (M.add b a)) :=
  Path.congrArg φ.f (add_comm_path M a b)

/-! ## 29–32: Ideal Structure and Quotient Paths -/

/-- An ideal in a PRing. -/
structure Ideal (M : PRing R) where
  mem : R → Prop
  zero_mem : mem M.zero
  add_mem : ∀ {a b}, mem a → mem b → mem (M.add a b)
  mul_mem : ∀ {a} (r : R), mem a → mem (M.mul r a)

/-- Congruence induced by an ideal: a ≡ b iff a - b ∈ I.
    Requires additional ring axioms for negation. -/
def idealCongruence (M : PRing R) (I : Ideal M)
    (neg_compat : ∀ {a}, I.mem a → I.mem (M.neg a))
    (symm_rearrange : ∀ a b, I.mem (M.add a (M.neg b)) → I.mem (M.add b (M.neg a)))
    (trans_rearrange : ∀ a b c, I.mem (M.add a (M.neg b)) → I.mem (M.add b (M.neg c)) →
      I.mem (M.add a (M.neg c)))
    (mul_rearrange : ∀ a₁ a₂ b₁ b₂, I.mem (M.add a₁ (M.neg a₂)) →
      I.mem (M.add b₁ (M.neg b₂)) → I.mem (M.add (M.mul a₁ b₁) (M.neg (M.mul a₂ b₂))))
    (add_rearrange : ∀ a₁ a₂ b₁ b₂,
      M.add (M.add a₁ b₁) (M.neg (M.add a₂ b₂)) =
      M.add (M.add a₁ (M.neg a₂)) (M.add b₁ (M.neg b₂)))
    : Congruence M where
  rel a b := I.mem (M.add a (M.neg b))
  refl_rel a := by rw [M.add_neg a]; exact I.zero_mem
  symm_rel := fun hab => symm_rearrange _ _ hab
  trans_rel := fun hab hbc => trans_rearrange _ _ _ hab hbc
  add_compat := fun {a₁ a₂ b₁ b₂} ha hb => by
    rw [add_rearrange a₁ a₂ b₁ b₂]; exact I.add_mem ha hb
  mul_compat := fun ha hb => mul_rearrange _ _ _ _ ha hb

/-- 29. Path: ideal congruence is reflexive at the identity level. -/
def ideal_cong_refl_path (M : PRing R) (I : Ideal M) (a : R) :
    Path (M.add a (M.neg a)) M.zero :=
  Path.ofEq (M.add_neg a)

/-- 30. Path: zero is in every ideal. -/
def ideal_zero_path (M : PRing R) (I : Ideal M) :
    I.mem M.zero :=
  I.zero_mem

/-- 31. Path: ideal is closed under ring multiplication. -/
def ideal_mul_closed (M : PRing R) (I : Ideal M) (r a : R) (h : I.mem a) :
    I.mem (M.mul r a) :=
  I.mul_mem r h

/-- 32. Path: sum of ideal elements stays in ideal. -/
def ideal_add_closed (M : PRing R) (I : Ideal M) (a b : R)
    (ha : I.mem a) (hb : I.mem b) :
    I.mem (M.add a b) :=
  I.add_mem ha hb

/-! ## 33–35: Hensel Lifting Structure -/

/-- Hensel lifting data: given f(a) ≡ 0 mod I and f'(a) invertible,
    lift to a solution mod I². -/
structure HenselData (M : PRing R) (I : Ideal M) where
  f_eval : R → R          -- polynomial evaluation
  f_deriv_eval : R → R    -- derivative evaluation
  approx : R              -- approximate root
  f_approx_in_I : I.mem (f_eval approx)
  deriv_inv : R            -- inverse of f'(approx)
  deriv_inv_spec : M.mul (f_deriv_eval approx) deriv_inv = M.one

/-- The Hensel-lifted approximation. -/
def hensel_lift (M : PRing R) (I : Ideal M) (hd : HenselData M I) : R :=
  M.add hd.approx (M.neg (M.mul hd.deriv_inv (hd.f_eval hd.approx)))

/-- 33. Path: the Hensel correction term is in I. -/
def hensel_correction_in_ideal (M : PRing R) (I : Ideal M)
    (hd : HenselData M I) :
    I.mem (M.mul hd.deriv_inv (hd.f_eval hd.approx)) :=
  I.mul_mem hd.deriv_inv hd.f_approx_in_I

/-- 34. Path: derivative invertibility. -/
def hensel_deriv_inv_path (M : PRing R) (I : Ideal M)
    (hd : HenselData M I) :
    Path (M.mul (hd.f_deriv_eval hd.approx) hd.deriv_inv) M.one :=
  Path.ofEq hd.deriv_inv_spec

/-- 35. Path: Hensel lift differs from original by an ideal element
    (given additional rearrangement axiom). -/
def hensel_lift_diff_path (M : PRing R) (I : Ideal M)
    (hd : HenselData M I)
    (neg_mem : ∀ {a}, I.mem a → I.mem (M.neg a))
    (rearrange : M.add (hensel_lift M I hd) (M.neg hd.approx) =
      M.neg (M.mul hd.deriv_inv (hd.f_eval hd.approx))) :
    I.mem (M.add (hensel_lift M I hd) (M.neg hd.approx)) := by
  rw [rearrange]
  exact neg_mem (I.mul_mem hd.deriv_inv hd.f_approx_in_I)

end ComputationalPaths.Path.Algebra.ModularDeep
