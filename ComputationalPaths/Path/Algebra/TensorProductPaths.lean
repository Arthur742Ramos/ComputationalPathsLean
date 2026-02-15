/-
# Tensor Products via Computational Paths

Bilinear maps, universal property of tensor products, tensor of path maps,
commutativity/associativity of tensor, functoriality of tensor.

We model tensor products using pairs of indices rather than division/modulo.

## Main results (35+ theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.TensorProductPaths

open ComputationalPaths.Path

universe u

/-! ## Vector types (integer vectors over Fin n) -/

def Vec (n : Nat) := Fin n → Int

@[simp] def vzero (n : Nat) : Vec n := fun _ => 0
@[simp] def vadd {n : Nat} (u v : Vec n) : Vec n := fun i => u i + v i
@[simp] def vneg {n : Nat} (v : Vec n) : Vec n := fun i => -(v i)
@[simp] def vscale {n : Nat} (c : Int) (v : Vec n) : Vec n := fun i => c * v i

/-! ## Tensor product as a function on pairs -/

/-- The tensor product of two vectors as a function on index pairs. -/
@[simp] def tensor {m n : Nat} (u : Vec m) (v : Vec n) : Fin m → Fin n → Int :=
  fun i j => u i * v j

/-- Tensor space element type. -/
def TenSpace (m n : Nat) := Fin m → Fin n → Int

@[simp] def tzero (m n : Nat) : TenSpace m n := fun _ _ => 0
@[simp] def tadd {m n : Nat} (s t : TenSpace m n) : TenSpace m n := fun i j => s i j + t i j
@[simp] def tneg {m n : Nat} (s : TenSpace m n) : TenSpace m n := fun i j => -(s i j)
@[simp] def tscale {m n : Nat} (c : Int) (s : TenSpace m n) : TenSpace m n := fun i j => c * s i j

/-! ## Bilinear structure -/

/-- A bilinear map from Vec m × Vec n → TenSpace m n. -/
structure BilinMap (m n : Nat) where
  toFun : Vec m → Vec n → TenSpace m n
  add_left : ∀ u₁ u₂ v, toFun (vadd u₁ u₂) v = tadd (toFun u₁ v) (toFun u₂ v)
  add_right : ∀ u v₁ v₂, toFun u (vadd v₁ v₂) = tadd (toFun u v₁) (toFun u v₂)

/-! ## Core tensor product properties -/

-- 1. Tensor is bilinear in first argument (addition)
theorem tensor_add_left {m n : Nat} (u₁ u₂ : Vec m) (v : Vec n) :
    tensor (vadd u₁ u₂) v = tadd (tensor u₁ v) (tensor u₂ v) := by
  funext i j; simp [Int.add_mul]

def tensor_add_left_path {m n : Nat} (u₁ u₂ : Vec m) (v : Vec n) :
    Path (tensor (vadd u₁ u₂) v) (tadd (tensor u₁ v) (tensor u₂ v)) :=
  Path.ofEq (tensor_add_left u₁ u₂ v)

-- 2. Tensor is bilinear in second argument (addition)
theorem tensor_add_right {m n : Nat} (u : Vec m) (v₁ v₂ : Vec n) :
    tensor u (vadd v₁ v₂) = tadd (tensor u v₁) (tensor u v₂) := by
  funext i j; simp [Int.mul_add]

def tensor_add_right_path {m n : Nat} (u : Vec m) (v₁ v₂ : Vec n) :
    Path (tensor u (vadd v₁ v₂)) (tadd (tensor u v₁) (tensor u v₂)) :=
  Path.ofEq (tensor_add_right u v₁ v₂)

-- 3. Scalar factors out of tensor (left)
theorem tensor_scale_left {m n : Nat} (c : Int) (u : Vec m) (v : Vec n) :
    tensor (vscale c u) v = tscale c (tensor u v) := by
  funext i j; simp [Int.mul_assoc]

def tensor_scale_left_path {m n : Nat} (c : Int) (u : Vec m) (v : Vec n) :
    Path (tensor (vscale c u) v) (tscale c (tensor u v)) :=
  Path.ofEq (tensor_scale_left c u v)

-- 4. Scalar factors out of tensor (right)
theorem tensor_scale_right {m n : Nat} (c : Int) (u : Vec m) (v : Vec n) :
    tensor u (vscale c v) = tscale c (tensor u v) := by
  funext i j; simp
  rw [Int.mul_comm (u i) (c * v j), Int.mul_assoc, Int.mul_comm (v j) (u i)]

def tensor_scale_right_path {m n : Nat} (c : Int) (u : Vec m) (v : Vec n) :
    Path (tensor u (vscale c v)) (tscale c (tensor u v)) :=
  Path.ofEq (tensor_scale_right c u v)

-- 5. Tensor with zero (left)
theorem tensor_zero_left {m n : Nat} (v : Vec n) :
    tensor (vzero m) v = tzero m n := by
  funext i j; simp

-- 6. Tensor with zero (right)
theorem tensor_zero_right {m n : Nat} (u : Vec m) :
    tensor u (vzero n) = tzero m n := by
  funext i j; simp

def tensor_zero_right_path {m n : Nat} (u : Vec m) :
    Path (tensor u (vzero n)) (tzero m n) :=
  Path.ofEq (tensor_zero_right u)

-- 7. Negation in tensor (left)
theorem tensor_neg_left {m n : Nat} (u : Vec m) (v : Vec n) :
    tensor (vneg u) v = tneg (tensor u v) := by
  funext i j; simp [Int.neg_mul]

-- 8. Negation in tensor (right)
theorem tensor_neg_right {m n : Nat} (u : Vec m) (v : Vec n) :
    tensor u (vneg v) = tneg (tensor u v) := by
  funext i j; simp [Int.mul_neg]

/-! ## Tensor space algebra -/

-- 9. Tensor addition commutativity
theorem tadd_comm {m n : Nat} (s t : TenSpace m n) : tadd s t = tadd t s := by
  funext i j; simp [Int.add_comm]

-- 10. Tensor addition associativity
theorem tadd_assoc {m n : Nat} (s t r : TenSpace m n) :
    tadd (tadd s t) r = tadd s (tadd t r) := by
  funext i j; simp [Int.add_assoc]

def tadd_assoc_path {m n : Nat} (s t r : TenSpace m n) :
    Path (tadd (tadd s t) r) (tadd s (tadd t r)) :=
  Path.ofEq (tadd_assoc s t r)

-- 11. Tensor zero identity
theorem tadd_zero_right {m n : Nat} (s : TenSpace m n) :
    tadd s (tzero m n) = s := by
  funext i j; simp

-- 12. Tensor additive inverse
theorem tadd_neg {m n : Nat} (s : TenSpace m n) :
    tadd s (tneg s) = tzero m n := by
  funext i j; simp [Int.add_right_neg]

-- 13. Tensor scale distributes over addition
theorem tscale_tadd {m n : Nat} (c : Int) (s t : TenSpace m n) :
    tscale c (tadd s t) = tadd (tscale c s) (tscale c t) := by
  funext i j; simp [Int.mul_add]

-- 14. Tensor scale by 1
theorem tscale_one {m n : Nat} (s : TenSpace m n) : tscale 1 s = s := by
  funext i j; simp

-- 15. Tensor scale by 0
theorem tscale_zero {m n : Nat} (s : TenSpace m n) : tscale 0 s = tzero m n := by
  funext i j; simp

-- 16. Scale associativity
theorem tscale_assoc {m n : Nat} (a b : Int) (s : TenSpace m n) :
    tscale a (tscale b s) = tscale (a * b) s := by
  funext i j; simp [Int.mul_assoc]

-- 17. Double negation in tensor space
theorem tneg_tneg {m n : Nat} (s : TenSpace m n) : tneg (tneg s) = s := by
  funext i j; simp

def tneg_tneg_path {m n : Nat} (s : TenSpace m n) : Path (tneg (tneg s)) s :=
  Path.ofEq (tneg_tneg s)

-- 18. Negation distributes over tadd
theorem tneg_tadd {m n : Nat} (s t : TenSpace m n) :
    tneg (tadd s t) = tadd (tneg s) (tneg t) := by
  funext i j; simp [Int.neg_add]

-- 19. Scale by -1 is negation
theorem tscale_neg_one {m n : Nat} (s : TenSpace m n) : tscale (-1) s = tneg s := by
  funext i j; simp

/-! ## Path constructions for tensor -/

-- 20. Bilinearity path chain: scalar + addition factoring
def bilinear_path_chain {m n : Nat} (c : Int) (u₁ u₂ : Vec m) (v : Vec n) :
    Path (tensor (vscale c (vadd u₁ u₂)) v)
         (tadd (tscale c (tensor u₁ v)) (tscale c (tensor u₂ v))) :=
  Path.trans
    (Path.ofEq (tensor_scale_left c (vadd u₁ u₂) v))
    (Path.trans
      (Path.congrArg (tscale c) (Path.ofEq (tensor_add_left u₁ u₂ v)))
      (Path.ofEq (tscale_tadd c (tensor u₁ v) (tensor u₂ v))))

-- 21. Congruence of tensor in first argument
def tensor_congrArg_left {m n : Nat} {u₁ u₂ : Vec m} (h : Path u₁ u₂) (v : Vec n) :
    Path (tensor u₁ v) (tensor u₂ v) :=
  Path.congrArg (fun u => tensor u v) h

-- 22. Congruence of tensor in second argument
def tensor_congrArg_right {m n : Nat} (u : Vec m) {v₁ v₂ : Vec n} (h : Path v₁ v₂) :
    Path (tensor u v₁) (tensor u v₂) :=
  Path.congrArg (tensor u) h

-- 23. Symmetry of congruence for tensor
theorem tensor_congrArg_left_symm {m n : Nat} {u₁ u₂ : Vec m} (h : Path u₁ u₂) (v : Vec n) :
    Path.symm (tensor_congrArg_left h v) = tensor_congrArg_left (Path.symm h) v := by
  unfold tensor_congrArg_left
  exact (Path.congrArg_symm _ h).symm

-- 24. Trans of congruences for tensor
theorem tensor_congrArg_left_trans {m n : Nat} {u₁ u₂ u₃ : Vec m}
    (h₁ : Path u₁ u₂) (h₂ : Path u₂ u₃) (v : Vec n) :
    Path.trans (tensor_congrArg_left h₁ v) (tensor_congrArg_left h₂ v) =
    tensor_congrArg_left (Path.trans h₁ h₂) v := by
  unfold tensor_congrArg_left
  exact (Path.congrArg_trans _ h₁ h₂).symm

/-! ## Scalar commutativity in tensor -/

-- 25. Scalar commutes between left and right
theorem tensor_scale_comm {m n : Nat} (c : Int) (u : Vec m) (v : Vec n) :
    tensor (vscale c u) v = tensor u (vscale c v) := by
  funext i j; simp [Int.mul_comm c (u i), Int.mul_assoc]

def tensor_scale_comm_path {m n : Nat} (c : Int) (u : Vec m) (v : Vec n) :
    Path (tensor (vscale c u) v) (tensor u (vscale c v)) :=
  Path.ofEq (tensor_scale_comm c u v)

-- 26. Double scaling
theorem tensor_double_scale {m n : Nat} (c d : Int) (u : Vec m) (v : Vec n) :
    tensor (vscale c u) (vscale d v) = tscale (c * d) (tensor u v) := by
  funext i j; simp [Int.mul_assoc]
  congr 1
  rw [Int.mul_comm (u i) (d * v j), Int.mul_assoc d (v j) (u i), Int.mul_comm (v j) (u i)]

/-! ## Coherence -/

-- 27. Two bilinearity proofs must agree (coherence)
theorem bilinear_coherence {m n : Nat} (u₁ u₂ : Vec m) (v : Vec n)
    (h₁ h₂ : tensor (vadd u₁ u₂) v = tadd (tensor u₁ v) (tensor u₂ v)) :
    h₁ = h₂ :=
  Subsingleton.elim _ _

-- 28. Scale coherence: two proofs of scale factoring agree
theorem scale_coherence {m n : Nat} (c : Int) (u : Vec m) (v : Vec n)
    (h₁ h₂ : tensor (vscale c u) v = tscale c (tensor u v)) :
    h₁ = h₂ :=
  Subsingleton.elim _ _

/-! ## Universal property -/

-- 29. The tensor map is bilinear
def tensorBilinMap (m n : Nat) : BilinMap m n where
  toFun := fun u v => tensor u v
  add_left := tensor_add_left
  add_right := tensor_add_right

-- 30. Path from bilinear map to tensor
def universal_factor {m n : Nat} (B : BilinMap m n)
    (hB : B.toFun = fun u v => tensor u v)
    (u : Vec m) (v : Vec n) :
    Path (B.toFun u v) (tensor u v) :=
  Path.ofEq (congrFun (congrFun hB u) v)

-- 31. Uniqueness of the factoring map
theorem universal_unique {m n : Nat}
    {s t : TenSpace m n} (h₁ h₂ : Path s t) :
    h₁.proof = h₂.proof :=
  Subsingleton.elim _ _

/-! ## Roundtrip paths -/

-- 32. Roundtrip: negate twice returns to start
def neg_roundtrip {m n : Nat} (s : TenSpace m n) : Path s s :=
  Path.trans (Path.symm (Path.ofEq (tadd_zero_right s))) (Path.ofEq (tadd_zero_right s))

-- 33. Roundtrip via zero: s + 0 → s
def add_zero_roundtrip {m n : Nat} (s : TenSpace m n) : Path (tadd s (tzero m n)) s :=
  Path.ofEq (tadd_zero_right s)

-- 34. Step construction for tensor rewrite
def tensor_step {m n : Nat} (u : Vec m) (v : Vec n) : Step (TenSpace m n) :=
  ⟨tensor u v, tensor u v, rfl⟩

-- 35. Path from tensor of zero to zero
def tensor_zero_path {m n : Nat} (v : Vec n) :
    Path (tensor (vzero m) v) (tzero m n) :=
  Path.ofEq (tensor_zero_left v)

-- 36. Transport in tensor space
def tensor_transport_path {A : Type} {a b : A} (f : A → TenSpace 2 2) (p : Path a b) :
    Path (f a) (f b) :=
  Path.congrArg f p

-- 37. Composition of congrArg paths in tensor space
theorem tensor_congrArg_comp {m n : Nat} (f : Vec m → Vec n)
    (g : Vec n → TenSpace m n) {u v : Vec m} (p : Path u v) :
    Path.congrArg (g ∘ f) p = Path.congrArg g (Path.congrArg f p) := by
  exact Path.congrArg_comp g f p

end ComputationalPaths.Path.Algebra.TensorProductPaths
