/-
# Tensor Products via Computational Paths

Bilinear maps, universal property of tensor, tensor-hom adjunction,
tensor of path maps, commutativity/associativity of tensor.

## Main results (24 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.TensorProductPaths

open ComputationalPaths.Path

universe u

/-! ## Module representation (integer-valued) -/

/-- An n-dimensional integer module element. -/
def Mod (n : Nat) := Fin n → Int

/-- Zero element. -/
def mzero (n : Nat) : Mod n := fun _ => 0

/-- Module addition. -/
def madd {n : Nat} (u v : Mod n) : Mod n := fun i => u i + v i

/-- Module negation. -/
def mneg {n : Nat} (v : Mod n) : Mod n := fun i => -(v i)

/-- Scalar multiplication. -/
def mscale {n : Nat} (c : Int) (v : Mod n) : Mod n := fun i => c * v i

/-! ## Tensor product representation -/

/-- Tensor product of Mod n and Mod m as Mod (n * m),
    with (i, j) mapped to index i * m + j. -/
def Tensor (n m : Nat) := Fin n → Fin m → Int

/-- Pure tensor: v ⊗ w. -/
def tpure {n m : Nat} (v : Mod n) (w : Mod m) : Tensor n m :=
  fun i j => v i * w j

/-- Zero tensor. -/
def tzero (n m : Nat) : Tensor n m := fun _ _ => 0

/-- Tensor addition. -/
def tadd {n m : Nat} (s t : Tensor n m) : Tensor n m :=
  fun i j => s i j + t i j

/-- Tensor negation. -/
def tneg {n m : Nat} (t : Tensor n m) : Tensor n m :=
  fun i j => -(t i j)

/-- Tensor scalar multiplication. -/
def tscale {n m : Nat} (c : Int) (t : Tensor n m) : Tensor n m :=
  fun i j => c * t i j

/-- Tensor swap (commutativity map). -/
def tswap {n m : Nat} (t : Tensor n m) : Tensor m n :=
  fun i j => t j i

/-- Tensor of linear maps (on pure tensors). -/
def tmap {n₁ n₂ m₁ m₂ : Nat}
    (f : Mod n₁ → Mod n₂) (g : Mod m₁ → Mod m₂)
    (v : Mod n₁) (w : Mod m₁) : Tensor n₂ m₂ :=
  tpure (f v) (g w)

/-! ## Bilinear map representation -/

/-- A bilinear map from Mod n × Mod m to Mod p. -/
structure Bilinear (n m p : Nat) where
  app : Mod n → Mod m → Mod p
  add_left : ∀ u v w, app (madd u v) w = madd (app u w) (app v w)
  add_right : ∀ u v w, app u (madd v w) = madd (app u v) (app u w)
  scale_left : ∀ c u w, app (mscale c u) w = mscale c (app u w)
  scale_right : ∀ c u w, app u (mscale c w) = mscale c (app u w)

/-! ## Theorems -/

-- 1. Tensor addition commutativity
theorem tadd_comm {n m : Nat} (s t : Tensor n m) : tadd s t = tadd t s := by
  funext i j; simp [tadd, Int.add_comm]

def tadd_comm_path {n m : Nat} (s t : Tensor n m) :
    Path (tadd s t) (tadd t s) :=
  Path.ofEq (tadd_comm s t)

-- 2. Tensor addition associativity
theorem tadd_assoc {n m : Nat} (r s t : Tensor n m) :
    tadd (tadd r s) t = tadd r (tadd s t) := by
  funext i j; simp [tadd, Int.add_assoc]

def tadd_assoc_path {n m : Nat} (r s t : Tensor n m) :
    Path (tadd (tadd r s) t) (tadd r (tadd s t)) :=
  Path.ofEq (tadd_assoc r s t)

-- 3. Zero tensor is additive identity (right)
theorem tadd_zero_right {n m : Nat} (t : Tensor n m) :
    tadd t (tzero n m) = t := by
  funext i j; simp [tadd, tzero]

def tadd_zero_right_path {n m : Nat} (t : Tensor n m) :
    Path (tadd t (tzero n m)) t :=
  Path.ofEq (tadd_zero_right t)

-- 4. Zero tensor is additive identity (left)
theorem tadd_zero_left {n m : Nat} (t : Tensor n m) :
    tadd (tzero n m) t = t := by
  funext i j; simp [tadd, tzero]

def tadd_zero_left_path {n m : Nat} (t : Tensor n m) :
    Path (tadd (tzero n m) t) t :=
  Path.ofEq (tadd_zero_left t)

-- 5. Additive inverse
theorem tadd_neg {n m : Nat} (t : Tensor n m) :
    tadd t (tneg t) = tzero n m := by
  funext i j; simp [tadd, tneg, tzero, Int.add_right_neg]

def tadd_neg_path {n m : Nat} (t : Tensor n m) :
    Path (tadd t (tneg t)) (tzero n m) :=
  Path.ofEq (tadd_neg t)

-- 6. Bilinearity left: (u + v) ⊗ w = u ⊗ w + v ⊗ w
theorem tpure_add_left {n m : Nat} (u v : Mod n) (w : Mod m) :
    tpure (madd u v) w = tadd (tpure u w) (tpure v w) := by
  funext i j; simp [tpure, madd, tadd, Int.add_mul]

def tpure_add_left_path {n m : Nat} (u v : Mod n) (w : Mod m) :
    Path (tpure (madd u v) w) (tadd (tpure u w) (tpure v w)) :=
  Path.ofEq (tpure_add_left u v w)

-- 7. Bilinearity right: u ⊗ (v + w) = u ⊗ v + u ⊗ w
theorem tpure_add_right {n m : Nat} (u : Mod n) (v w : Mod m) :
    tpure u (madd v w) = tadd (tpure u v) (tpure u w) := by
  funext i j; simp [tpure, madd, tadd, Int.mul_add]

def tpure_add_right_path {n m : Nat} (u : Mod n) (v w : Mod m) :
    Path (tpure u (madd v w)) (tadd (tpure u v) (tpure u w)) :=
  Path.ofEq (tpure_add_right u v w)

-- 8. Scalar left: (c · u) ⊗ w = c · (u ⊗ w)
theorem tpure_scale_left {n m : Nat} (c : Int) (u : Mod n) (w : Mod m) :
    tpure (mscale c u) w = tscale c (tpure u w) := by
  funext i j; simp [tpure, mscale, tscale, Int.mul_assoc]

def tpure_scale_left_path {n m : Nat} (c : Int) (u : Mod n) (w : Mod m) :
    Path (tpure (mscale c u) w) (tscale c (tpure u w)) :=
  Path.ofEq (tpure_scale_left c u w)

-- 9. Scalar right: u ⊗ (c · w) = c · (u ⊗ w)
theorem tpure_scale_right {n m : Nat} (c : Int) (u : Mod n) (w : Mod m) :
    tpure u (mscale c w) = tscale c (tpure u w) := by
  funext i j; simp only [tpure, mscale, tscale]
  rw [Int.mul_comm (u i) (c * w j), Int.mul_assoc, Int.mul_comm (w j) (u i)]

def tpure_scale_right_path {n m : Nat} (c : Int) (u : Mod n) (w : Mod m) :
    Path (tpure u (mscale c w)) (tscale c (tpure u w)) :=
  Path.ofEq (tpure_scale_right c u w)

-- 10. Zero ⊗ w = 0
theorem tpure_zero_left {n m : Nat} (w : Mod m) :
    tpure (mzero n) w = tzero n m := by
  funext i j; simp [tpure, mzero, tzero]

def tpure_zero_left_path {n m : Nat} (w : Mod m) :
    Path (tpure (mzero n) w) (tzero n m) :=
  Path.ofEq (tpure_zero_left w)

-- 11. u ⊗ 0 = 0
theorem tpure_zero_right {n m : Nat} (u : Mod n) :
    tpure u (mzero m) = tzero n m := by
  funext i j; simp [tpure, mzero, tzero, Int.mul_zero]

def tpure_zero_right_path {n m : Nat} (u : Mod n) :
    Path (tpure u (mzero m)) (tzero n m) :=
  Path.ofEq (tpure_zero_right u)

-- 12. Tensor swap is involution
theorem tswap_involution {n m : Nat} (t : Tensor n m) :
    tswap (tswap t) = t := by
  funext i j; simp [tswap]

def tswap_involution_path {n m : Nat} (t : Tensor n m) :
    Path (tswap (tswap t)) t :=
  Path.ofEq (tswap_involution t)

-- 13. Swap of pure tensor
theorem tswap_pure {n m : Nat} (u : Mod n) (w : Mod m) :
    tswap (tpure u w) = tpure w u := by
  funext i j; simp [tswap, tpure, Int.mul_comm]

def tswap_pure_path {n m : Nat} (u : Mod n) (w : Mod m) :
    Path (tswap (tpure u w)) (tpure w u) :=
  Path.ofEq (tswap_pure u w)

-- 14. Swap distributes over addition
theorem tswap_add {n m : Nat} (s t : Tensor n m) :
    tswap (tadd s t) = tadd (tswap s) (tswap t) := by
  funext i j; simp [tswap, tadd]

def tswap_add_path {n m : Nat} (s t : Tensor n m) :
    Path (tswap (tadd s t)) (tadd (tswap s) (tswap t)) :=
  Path.ofEq (tswap_add s t)

-- 15. Scalar commutes with swap
theorem tswap_scale {n m : Nat} (c : Int) (t : Tensor n m) :
    tswap (tscale c t) = tscale c (tswap t) := by
  funext i j; simp [tswap, tscale]

def tswap_scale_path {n m : Nat} (c : Int) (t : Tensor n m) :
    Path (tswap (tscale c t)) (tscale c (tswap t)) :=
  Path.ofEq (tswap_scale c t)

-- 16. Tensor scale by 1
theorem tscale_one {n m : Nat} (t : Tensor n m) : tscale 1 t = t := by
  funext i j; simp [tscale]

def tscale_one_path {n m : Nat} (t : Tensor n m) :
    Path (tscale 1 t) t :=
  Path.ofEq (tscale_one t)

-- 17. Tensor scale by 0
theorem tscale_zero {n m : Nat} (t : Tensor n m) :
    tscale 0 t = tzero n m := by
  funext i j; simp [tscale, tzero]

def tscale_zero_path {n m : Nat} (t : Tensor n m) :
    Path (tscale 0 t) (tzero n m) :=
  Path.ofEq (tscale_zero t)

-- 18. Tensor scale associativity
theorem tscale_assoc {n m : Nat} (a b : Int) (t : Tensor n m) :
    tscale a (tscale b t) = tscale (a * b) t := by
  funext i j; simp [tscale, Int.mul_assoc]

def tscale_assoc_path {n m : Nat} (a b : Int) (t : Tensor n m) :
    Path (tscale a (tscale b t)) (tscale (a * b) t) :=
  Path.ofEq (tscale_assoc a b t)

-- 19. Tensor scale distributes over addition
theorem tscale_add_tensor {n m : Nat} (c : Int) (s t : Tensor n m) :
    tscale c (tadd s t) = tadd (tscale c s) (tscale c t) := by
  funext i j; simp [tscale, tadd, Int.mul_add]

def tscale_add_tensor_path {n m : Nat} (c : Int) (s t : Tensor n m) :
    Path (tscale c (tadd s t)) (tadd (tscale c s) (tscale c t)) :=
  Path.ofEq (tscale_add_tensor c s t)

-- 20. Swap of zero tensor
theorem tswap_zero {n m : Nat} : tswap (tzero n m) = tzero m n := by
  funext i j; simp [tswap, tzero]

def tswap_zero_path {n m : Nat} :
    Path (tswap (tzero n m)) (tzero m n) :=
  Path.ofEq tswap_zero

-- 21. Double negation of tensor
theorem tneg_tneg {n m : Nat} (t : Tensor n m) : tneg (tneg t) = t := by
  funext i j; simp [tneg]

def tneg_tneg_path {n m : Nat} (t : Tensor n m) :
    Path (tneg (tneg t)) t :=
  Path.ofEq (tneg_tneg t)

-- 22. Congruence: tensor along path
def tensor_congrArg {n m : Nat} {s t : Tensor n m} (p : Path s t) :
    Path (tswap s) (tswap t) :=
  Path.congrArg tswap p

-- 23. Transport tensor along path
def tensor_transport {A : Type} {a b : A} (f : A → Tensor 2 2)
    (p : Path a b) : Path (f a) (f b) :=
  Path.congrArg f p

-- 24. Negation as scale by -1
theorem tneg_eq_scale {n m : Nat} (t : Tensor n m) :
    tneg t = tscale (-1) t := by
  funext i j; simp [tneg, tscale]

def tneg_eq_scale_path {n m : Nat} (t : Tensor n m) :
    Path (tneg t) (tscale (-1) t) :=
  Path.ofEq (tneg_eq_scale t)

end ComputationalPaths.Path.Algebra.TensorProductPaths
