/-
# Lens Space Algebra

This module develops algebraic structures associated with lens spaces
in the computational-path framework. We build upon the fundamental group
model π₁(L(p,q)) ≅ ℤ/p from the LensSpace module and add:

- Group structure on ℤ/p with Path coherence
- Lens space loop group structure
- Covering space degree data
- Loop power coherence
- SimpleEquiv coherence
- Path.stepChain coherence witnesses throughout
-/

import ComputationalPaths.Path.CompPath.LensSpace

namespace ComputationalPaths
namespace Path
namespace CompPath
namespace LensSpaceAlgebra

universe u

/-! ## Modular arithmetic helpers -/

theorem mod_add_mod (a b p : Nat) : (a % p + b) % p = (a + b) % p := by
  have h := Nat.add_mod a b p
  rw [Nat.add_mod (a % p) b p]
  rw [Nat.mod_mod_of_dvd a ⟨1, (Nat.mul_one p).symm⟩]
  exact h.symm

theorem add_mod_mod (a b p : Nat) : (a + b % p) % p = (a + b) % p := by
  rw [Nat.add_comm, mod_add_mod, Nat.add_comm]

/-! ## Group operations on ℤ/p -/

/-- Addition in ℤ/p. -/
def zpAdd (p : Nat) (hp : p > 0) (a b : Zp p) : Zp p :=
  ⟨(a.val + b.val) % p, Nat.mod_lt _ hp⟩

/-- Zero in ℤ/p. -/
def zpZero (p : Nat) (hp : p > 0) : Zp p :=
  ⟨0, hp⟩

/-- Negation in ℤ/p. -/
def zpNeg (p : Nat) (hp : p > 0) (a : Zp p) : Zp p :=
  ⟨(p - a.val) % p, Nat.mod_lt _ hp⟩

/-- Right identity for ℤ/p addition. -/
theorem zpAdd_zero_right (p : Nat) (hp : p > 0) (a : Zp p) :
    zpAdd p hp a (zpZero p hp) = a := by
  simp [zpAdd, zpZero]
  exact Fin.ext (Nat.mod_eq_of_lt a.isLt)

/-- Left identity for ℤ/p addition. -/
theorem zpAdd_zero_left (p : Nat) (hp : p > 0) (a : Zp p) :
    zpAdd p hp (zpZero p hp) a = a := by
  simp [zpAdd, zpZero]
  exact Fin.ext (Nat.mod_eq_of_lt a.isLt)

/-- Path witness for right identity. -/
def zpAdd_zero_right_path (p : Nat) (hp : p > 0) (a : Zp p) :
    Path (zpAdd p hp a (zpZero p hp)) a :=
  Path.stepChain (zpAdd_zero_right p hp a)

/-- Path witness for left identity. -/
def zpAdd_zero_left_path (p : Nat) (hp : p > 0) (a : Zp p) :
    Path (zpAdd p hp (zpZero p hp) a) a :=
  Path.stepChain (zpAdd_zero_left p hp a)

/-- Commutativity of ℤ/p addition. -/
theorem zpAdd_comm (p : Nat) (hp : p > 0) (a b : Zp p) :
    zpAdd p hp a b = zpAdd p hp b a := by
  unfold zpAdd
  exact Fin.ext (by simp [Nat.add_comm])

/-- Path witness for commutativity. -/
def zpAdd_comm_path (p : Nat) (hp : p > 0) (a b : Zp p) :
    Path (zpAdd p hp a b) (zpAdd p hp b a) :=
  Path.stepChain (zpAdd_comm p hp a b)

/-- Associativity of ℤ/p addition. -/
theorem zpAdd_assoc (p : Nat) (hp : p > 0) (a b c : Zp p) :
    zpAdd p hp (zpAdd p hp a b) c = zpAdd p hp a (zpAdd p hp b c) := by
  unfold zpAdd
  exact Fin.ext (by show ((a.val + b.val) % p + c.val) % p = (a.val + (b.val + c.val) % p) % p
                    rw [mod_add_mod, add_mod_mod, Nat.add_assoc])

/-- Path witness for associativity. -/
def zpAdd_assoc_path (p : Nat) (hp : p > 0) (a b c : Zp p) :
    Path (zpAdd p hp (zpAdd p hp a b) c) (zpAdd p hp a (zpAdd p hp b c)) :=
  Path.stepChain (zpAdd_assoc p hp a b c)

/-! ## Multiplication on ℤ/p -/

/-- Multiplication in ℤ/p. -/
def zpMul (p : Nat) (hp : p > 0) (a b : Zp p) : Zp p :=
  ⟨(a.val * b.val) % p, Nat.mod_lt _ hp⟩

/-- Multiplication by zero gives zero. -/
theorem zpMul_zero_right (p : Nat) (hp : p > 0) (a : Zp p) :
    zpMul p hp a (zpZero p hp) = zpZero p hp := by
  simp [zpMul, zpZero]

/-- Path witness for multiplication by zero. -/
def zpMul_zero_path (p : Nat) (hp : p > 0) (a : Zp p) :
    Path (zpMul p hp a (zpZero p hp)) (zpZero p hp) :=
  Path.stepChain (zpMul_zero_right p hp a)

/-- Commutativity of ℤ/p multiplication. -/
theorem zpMul_comm (p : Nat) (hp : p > 0) (a b : Zp p) :
    zpMul p hp a b = zpMul p hp b a := by
  unfold zpMul
  exact Fin.ext (by simp [Nat.mul_comm])

/-- Path witness for multiplicative commutativity. -/
def zpMul_comm_path (p : Nat) (hp : p > 0) (a b : Zp p) :
    Path (zpMul p hp a b) (zpMul p hp b a) :=
  Path.stepChain (zpMul_comm p hp a b)

/-! ## Lens space loop group structure -/

/-- The loop group operation: concatenation of loops at the lens space basepoint. -/
def loopMul (p q : Nat) (α β : lensSpaceLoopSpace p q) : lensSpaceLoopSpace p q :=
  Path.trans α β

/-- The identity loop. -/
def loopId (p q : Nat) : lensSpaceLoopSpace p q :=
  Path.refl (lensSpaceBase p q)

/-- The inverse loop. -/
def loopInv (p q : Nat) (α : lensSpaceLoopSpace p q) : lensSpaceLoopSpace p q :=
  Path.symm α

/-- Left identity for loop multiplication. -/
theorem loopMul_id_left (p q : Nat) (α : lensSpaceLoopSpace p q) :
    loopMul p q (loopId p q) α = α := by
  unfold loopMul loopId; exact Path.trans_refl_left α

/-- Right identity for loop multiplication. -/
theorem loopMul_id_right (p q : Nat) (α : lensSpaceLoopSpace p q) :
    loopMul p q α (loopId p q) = α := by
  unfold loopMul loopId; exact Path.trans_refl_right α

/-- Path witness for left identity. -/
def loopMul_id_left_path (p q : Nat) (α : lensSpaceLoopSpace p q) :
    Path (loopMul p q (loopId p q) α) α :=
  Path.stepChain (loopMul_id_left p q α)

/-- Path witness for right identity. -/
def loopMul_id_right_path (p q : Nat) (α : lensSpaceLoopSpace p q) :
    Path (loopMul p q α (loopId p q)) α :=
  Path.stepChain (loopMul_id_right p q α)

/-- Associativity of loop multiplication. -/
theorem loopMul_assoc (p q : Nat) (α β γ : lensSpaceLoopSpace p q) :
    loopMul p q (loopMul p q α β) γ = loopMul p q α (loopMul p q β γ) := by
  unfold loopMul; exact Path.trans_assoc α β γ

/-- Path witness for loop associativity. -/
def loopMul_assoc_path (p q : Nat) (α β γ : lensSpaceLoopSpace p q) :
    Path (loopMul p q (loopMul p q α β) γ)
         (loopMul p q α (loopMul p q β γ)) :=
  Path.stepChain (loopMul_assoc p q α β γ)

/-- Left inverse for loops (at the toEq level). -/
theorem loopMul_inv_left_toEq (p q : Nat) (α : lensSpaceLoopSpace p q) :
    (loopMul p q (loopInv p q α) α).toEq = (loopId p q).toEq := by
  unfold loopMul loopInv loopId; simp

/-- Right inverse for loops (at the toEq level). -/
theorem loopMul_inv_right_toEq (p q : Nat) (α : lensSpaceLoopSpace p q) :
    (loopMul p q α (loopInv p q α)).toEq = (loopId p q).toEq := by
  unfold loopMul loopInv loopId; simp

/-- Inverse distributes over composition. -/
theorem loopInv_mul (p q : Nat) (α β : lensSpaceLoopSpace p q) :
    loopInv p q (loopMul p q α β) = loopMul p q (loopInv p q β) (loopInv p q α) := by
  unfold loopInv loopMul; exact Path.symm_trans α β

/-- Path for inverse distribution. -/
def loopInv_mul_path (p q : Nat) (α β : lensSpaceLoopSpace p q) :
    Path (loopInv p q (loopMul p q α β))
         (loopMul p q (loopInv p q β) (loopInv p q α)) :=
  Path.stepChain (loopInv_mul p q α β)

/-- Double inverse. -/
theorem loopInv_inv (p q : Nat) (α : lensSpaceLoopSpace p q) :
    loopInv p q (loopInv p q α) = α := by
  unfold loopInv; exact Path.symm_symm α

/-- Path for double inverse. -/
def loopInv_inv_path (p q : Nat) (α : lensSpaceLoopSpace p q) :
    Path (loopInv p q (loopInv p q α)) α :=
  Path.stepChain (loopInv_inv p q α)

/-! ## Specific lens spaces -/

/-- L(2,1) ≅ RP³: the real projective 3-space. -/
def rp3AsLens_h1 : Zp 2 := ⟨1, by omega⟩

/-- The H₁ of RP³ has order 2. -/
theorem rp3_h1_order : zpAdd 2 (by omega) rp3AsLens_h1 rp3AsLens_h1 = zpZero 2 (by omega) := by
  simp [rp3AsLens_h1, zpAdd, zpZero]

/-- Path witness for H₁(RP³) having order 2. -/
def rp3_h1_order_path :
    Path (zpAdd 2 (by omega) rp3AsLens_h1 rp3AsLens_h1) (zpZero 2 (by omega)) :=
  Path.stepChain rp3_h1_order

/-- L(3,1): a lens space with ℤ/3 fundamental group. -/
def l31_h1 : Zp 3 := ⟨1, by omega⟩

/-- The generator of ℤ/3 has order 3. -/
theorem l31_h1_order :
    zpAdd 3 (by omega) (zpAdd 3 (by omega) l31_h1 l31_h1) l31_h1 =
      zpZero 3 (by omega) := by
  simp [l31_h1, zpAdd, zpZero]

/-- Path for ℤ/3 order. -/
def l31_h1_order_path :
    Path (zpAdd 3 (by omega) (zpAdd 3 (by omega) l31_h1 l31_h1) l31_h1)
         (zpZero 3 (by omega)) :=
  Path.stepChain l31_h1_order

/-- L(5,1): generator of ℤ/5 has order 5. -/
def l51_gen : Zp 5 := ⟨1, by omega⟩

/-- 5 * generator = 0 in ℤ/5. -/
theorem l51_order :
    zpAdd 5 (by omega) (zpAdd 5 (by omega) (zpAdd 5 (by omega)
      (zpAdd 5 (by omega) l51_gen l51_gen) l51_gen) l51_gen) l51_gen =
    zpZero 5 (by omega) := by
  native_decide

/-- Path for ℤ/5 order. -/
def l51_order_path :
    Path (zpAdd 5 (by omega) (zpAdd 5 (by omega) (zpAdd 5 (by omega)
      (zpAdd 5 (by omega) l51_gen l51_gen) l51_gen) l51_gen) l51_gen)
    (zpZero 5 (by omega)) :=
  Path.stepChain l51_order

/-! ## Covering space data -/

/-- A covering space of L(p,q) has degree dividing p. -/
structure LensCovering (p q : Nat) (hp : p > 0) where
  /-- Number of sheets. -/
  sheets : Nat
  /-- Sheets is positive. -/
  sheets_pos : sheets > 0
  /-- Sheets divides p. -/
  divides : p % sheets = 0

/-- The universal cover of L(p,q) has p sheets. -/
def universalCover (p q : Nat) (hp : p > 0) : LensCovering p q hp where
  sheets := p
  sheets_pos := hp
  divides := Nat.mod_self p

/-- The trivial (identity) cover has 1 sheet. -/
def trivialCover (p q : Nat) (hp : p > 0) : LensCovering p q hp where
  sheets := 1
  sheets_pos := by omega
  divides := Nat.mod_one p

/-- Path: universal cover has p sheets. -/
def universalCover_sheets_path (p q : Nat) (hp : p > 0) :
    Path (universalCover p q hp).sheets p :=
  Path.refl p

/-- Path: trivial cover has 1 sheet. -/
def trivialCover_sheets_path (p q : Nat) (hp : p > 0) :
    Path (trivialCover p q hp).sheets 1 :=
  Path.refl 1

/-! ## Loop power coherence -/

/-- Iterated loop is path composition. -/
theorem lensSpaceLoopPow_succ (p q n : Nat) :
    lensSpaceLoopPow p q (n + 1) =
      Path.trans (lensSpaceLoop p q) (lensSpaceLoopPow p q n) := rfl

/-- Loop power zero is refl. -/
theorem lensSpaceLoopPow_zero (p q : Nat) :
    lensSpaceLoopPow p q 0 = Path.refl (lensSpaceBase p q) := rfl

/-- Path witness for loop power zero. -/
def lensSpaceLoopPow_zero_path (p q : Nat) :
    Path (lensSpaceLoopPow p q 0) (Path.refl (lensSpaceBase p q)) :=
  Path.stepChain (lensSpaceLoopPow_zero p q)

/-- Path witness for loop power successor. -/
def lensSpaceLoopPow_succ_path (p q n : Nat) :
    Path (lensSpaceLoopPow p q (n + 1))
         (Path.trans (lensSpaceLoop p q) (lensSpaceLoopPow p q n)) :=
  Path.stepChain (lensSpaceLoopPow_succ p q n)

/-- Loop decode at zero gives refl. -/
theorem lensSpaceDecodePath_zero (p q : Nat) (_hp : p > 0) :
    lensSpaceDecodePath p q (zpZero p _hp) = Path.refl (lensSpaceBase p q) := by
  simp [lensSpaceDecodePath, zpZero]

/-- Path witness for decode at zero. -/
def lensSpaceDecodePath_zero_path (p q : Nat) (hp : p > 0) :
    Path (lensSpaceDecodePath p q (zpZero p hp))
         (Path.refl (lensSpaceBase p q)) :=
  Path.stepChain (lensSpaceDecodePath_zero p q hp)

/-! ## SimpleEquiv coherence -/

/-- The equivalence lensSpacePiOneEquivZp is the identity. -/
theorem lensSpacePiOneEquivZp_is_id (p : Nat) (x : lensSpacePiOne p) :
    (lensSpacePiOneEquivZp p).toFun x = x := rfl

/-- The inverse is also the identity. -/
theorem lensSpacePiOneEquivZp_inv_is_id (p : Nat) (x : Zp p) :
    (lensSpacePiOneEquivZp p).invFun x = x := rfl

/-- Path witness for forward direction. -/
def lensSpacePiOneEquivZp_path (p : Nat) (x : lensSpacePiOne p) :
    Path ((lensSpacePiOneEquivZp p).toFun x) x :=
  Path.refl x

/-- Path witness for backward direction. -/
def lensSpacePiOneEquivZp_inv_path (p : Nat) (x : Zp p) :
    Path ((lensSpacePiOneEquivZp p).invFun x) x :=
  Path.refl x

/-- Round-trip coherence. -/
theorem lensSpacePiOneEquivZp_roundtrip (p : Nat) (x : lensSpacePiOne p) :
    (lensSpacePiOneEquivZp p).invFun ((lensSpacePiOneEquivZp p).toFun x) = x := rfl

/-- Path for round-trip. -/
def lensSpacePiOneEquivZp_roundtrip_path (p : Nat) (x : lensSpacePiOne p) :
    Path ((lensSpacePiOneEquivZp p).invFun ((lensSpacePiOneEquivZp p).toFun x)) x :=
  Path.refl x

/-! ## Euler characteristic of lens spaces -/

/-- Euler characteristic of an odd-dimensional lens space L(p,q) is 0. -/
def lensEulerChar (_p : Nat) (_hp : _p > 0) : Int := 0

/-- Euler characteristic of L(p,q) is always 0. -/
theorem lensEulerChar_zero (p : Nat) (hp : p > 0) :
    lensEulerChar p hp = 0 := rfl

/-- Path witness for lens space Euler characteristic. -/
def lensEulerChar_path (p : Nat) (hp : p > 0) :
    Path (lensEulerChar p hp) 0 :=
  Path.refl 0

/-! ## Loop space iterated structure -/

/-- Loop power one equals the fundamental loop. -/
theorem lensSpaceLoopPow_one (p q : Nat) :
    lensSpaceLoopPow p q 1 =
      Path.trans (lensSpaceLoop p q) (Path.refl (lensSpaceBase p q)) := rfl

/-- Path for loop power one. -/
def lensSpaceLoopPow_one_path (p q : Nat) :
    Path (lensSpaceLoopPow p q 1)
         (Path.trans (lensSpaceLoop p q) (Path.refl (lensSpaceBase p q))) :=
  Path.refl _

/-- toEq of loop power is always rfl (PUnit). -/
theorem lensSpaceLoopPow_toEq (p q n : Nat) :
    (lensSpaceLoopPow p q n).toEq = rfl := by
  induction n with
  | zero => simp
  | succ _ _ => simp

/-- The fundamental loop has trivial toEq (PUnit). -/
theorem lensSpaceLoop_toEq (p q : Nat) :
    (lensSpaceLoop p q).toEq = rfl := by simp

end LensSpaceAlgebra
end CompPath
end Path
end ComputationalPaths
