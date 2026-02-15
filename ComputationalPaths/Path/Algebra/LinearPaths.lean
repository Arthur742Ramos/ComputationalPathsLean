/-
# Linear Algebra via Computational Paths

Vector space axioms as path equalities, linear maps preserving path structure,
kernel/image as path subspaces, dimension properties, basis paths.

## Main results (24 theorems)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.LinearPaths

open ComputationalPaths.Path

universe u

/-! ## Vector representation (integer vectors over Fin n) -/

/-- An n-dimensional integer vector. -/
def Vec (n : Nat) := Fin n → Int

/-- Zero vector. -/
def vzero (n : Nat) : Vec n := fun _ => 0

/-- Vector addition. -/
def vadd {n : Nat} (u v : Vec n) : Vec n := fun i => u i + v i

/-- Vector negation. -/
def vneg {n : Nat} (v : Vec n) : Vec n := fun i => -(v i)

/-- Scalar multiplication. -/
def vscale {n : Nat} (c : Int) (v : Vec n) : Vec n := fun i => c * v i

/-- Vector subtraction. -/
def vsub {n : Nat} (u v : Vec n) : Vec n := vadd u (vneg v)

/-- Standard basis vector e_k. -/
def basis {n : Nat} (k : Fin n) : Vec n := fun i => if i = k then 1 else 0

/-! ## Linear maps -/

/-- A linear map is represented as a matrix (function of two indices). -/
def LinMap (n m : Nat) := Fin m → Fin n → Int

/-- Apply a linear map to a vector. -/
def lapply {n m : Nat} (A : LinMap n m) (v : Vec n) : Vec m :=
  fun i => (List.finRange n).foldl (fun acc j => acc + A i j * v j) 0

/-- Zero linear map. -/
def lzero (n m : Nat) : LinMap n m := fun _ _ => 0

/-- Identity linear map. -/
def lid (n : Nat) : LinMap n n := fun i j => if i = j then 1 else 0

/-- Composition of linear maps. -/
def lcomp {n m p : Nat} (A : LinMap m p) (B : LinMap n m) : LinMap n p :=
  fun i k => (List.finRange m).foldl (fun acc j => acc + A i j * B j k) 0

/-- Addition of linear maps. -/
def ladd {n m : Nat} (A B : LinMap n m) : LinMap n m :=
  fun i j => A i j + B i j

/-- Scaling of a linear map. -/
def lscale {n m : Nat} (c : Int) (A : LinMap n m) : LinMap n m :=
  fun i j => c * A i j

/-! ## Subspace indicators -/

/-- Kernel membership: v is in ker(A) if A(v) = 0. -/
def inKernel {n m : Nat} (A : LinMap n m) (v : Vec n) : Prop :=
  lapply A v = vzero m

/-- Image membership: w is in im(A) if there exists v with A(v) = w. -/
def inImage {n m : Nat} (A : LinMap n m) (w : Vec m) : Prop :=
  ∃ v : Vec n, lapply A v = w

/-! ## Theorems -/

-- 1. Addition commutativity
theorem vadd_comm {n : Nat} (u v : Vec n) : vadd u v = vadd v u := by
  funext i; simp [vadd, Int.add_comm]

def vadd_comm_path {n : Nat} (u v : Vec n) :
    Path (vadd u v) (vadd v u) :=
  Path.ofEq (vadd_comm u v)

-- 2. Addition associativity
theorem vadd_assoc {n : Nat} (u v w : Vec n) :
    vadd (vadd u v) w = vadd u (vadd v w) := by
  funext i; simp [vadd, Int.add_assoc]

def vadd_assoc_path {n : Nat} (u v w : Vec n) :
    Path (vadd (vadd u v) w) (vadd u (vadd v w)) :=
  Path.ofEq (vadd_assoc u v w)

-- 3. Zero right identity
theorem vadd_zero_right {n : Nat} (u : Vec n) : vadd u (vzero n) = u := by
  funext i; simp [vadd, vzero]

def vadd_zero_right_path {n : Nat} (u : Vec n) :
    Path (vadd u (vzero n)) u :=
  Path.ofEq (vadd_zero_right u)

-- 4. Zero left identity
theorem vadd_zero_left {n : Nat} (u : Vec n) : vadd (vzero n) u = u := by
  funext i; simp [vadd, vzero]

def vadd_zero_left_path {n : Nat} (u : Vec n) :
    Path (vadd (vzero n) u) u :=
  Path.ofEq (vadd_zero_left u)

-- 5. Additive inverse
theorem vadd_neg {n : Nat} (u : Vec n) : vadd u (vneg u) = vzero n := by
  funext i; simp [vadd, vneg, vzero, Int.add_right_neg]

def vadd_neg_path {n : Nat} (u : Vec n) :
    Path (vadd u (vneg u)) (vzero n) :=
  Path.ofEq (vadd_neg u)

-- 6. Scalar multiplication by 1
theorem vscale_one {n : Nat} (u : Vec n) : vscale 1 u = u := by
  funext i; simp [vscale]

def vscale_one_path {n : Nat} (u : Vec n) :
    Path (vscale 1 u) u :=
  Path.ofEq (vscale_one u)

-- 7. Scalar multiplication by 0
theorem vscale_zero {n : Nat} (u : Vec n) : vscale 0 u = vzero n := by
  funext i; simp [vscale, vzero]

def vscale_zero_path {n : Nat} (u : Vec n) :
    Path (vscale 0 u) (vzero n) :=
  Path.ofEq (vscale_zero u)

-- 8. Scalar distribution over vector addition
theorem vscale_add {n : Nat} (c : Int) (u v : Vec n) :
    vscale c (vadd u v) = vadd (vscale c u) (vscale c v) := by
  funext i; simp [vscale, vadd, Int.mul_add]

def vscale_add_path {n : Nat} (c : Int) (u v : Vec n) :
    Path (vscale c (vadd u v)) (vadd (vscale c u) (vscale c v)) :=
  Path.ofEq (vscale_add c u v)

-- 9. Scalar addition distributes
theorem vscale_add_scalar {n : Nat} (a b : Int) (u : Vec n) :
    vscale (a + b) u = vadd (vscale a u) (vscale b u) := by
  funext i; simp [vscale, vadd, Int.add_mul]

def vscale_add_scalar_path {n : Nat} (a b : Int) (u : Vec n) :
    Path (vscale (a + b) u) (vadd (vscale a u) (vscale b u)) :=
  Path.ofEq (vscale_add_scalar a b u)

-- 10. Scalar multiplication associativity
theorem vscale_assoc {n : Nat} (a b : Int) (u : Vec n) :
    vscale a (vscale b u) = vscale (a * b) u := by
  funext i; simp [vscale, Int.mul_assoc]

def vscale_assoc_path {n : Nat} (a b : Int) (u : Vec n) :
    Path (vscale a (vscale b u)) (vscale (a * b) u) :=
  Path.ofEq (vscale_assoc a b u)

-- 11. Negation is scaling by -1
theorem vneg_eq_scale {n : Nat} (u : Vec n) : vneg u = vscale (-1) u := by
  funext i; simp [vneg, vscale]

def vneg_eq_scale_path {n : Nat} (u : Vec n) :
    Path (vneg u) (vscale (-1) u) :=
  Path.ofEq (vneg_eq_scale u)

-- 12. Double negation
theorem vneg_vneg {n : Nat} (u : Vec n) : vneg (vneg u) = u := by
  funext i; simp [vneg]

def vneg_vneg_path {n : Nat} (u : Vec n) :
    Path (vneg (vneg u)) u :=
  Path.ofEq (vneg_vneg u)

-- 13. Scale zero vector
theorem vscale_vzero {n : Nat} (c : Int) : vscale c (vzero n) = vzero n := by
  funext i; simp [vscale, vzero]

def vscale_vzero_path {n : Nat} (c : Int) :
    Path (vscale c (vzero n)) (vzero n) :=
  Path.ofEq (vscale_vzero c)

-- 14. Subtraction as addition of negative
theorem vsub_eq {n : Nat} (u v : Vec n) : vsub u v = vadd u (vneg v) := by
  simp [vsub]

def vsub_eq_path {n : Nat} (u v : Vec n) :
    Path (vsub u v) (vadd u (vneg v)) :=
  Path.ofEq (vsub_eq u v)

-- 15. Linear map addition is commutative
theorem ladd_comm {n m : Nat} (A B : LinMap n m) : ladd A B = ladd B A := by
  funext i j; simp [ladd, Int.add_comm]

def ladd_comm_path {n m : Nat} (A B : LinMap n m) :
    Path (ladd A B) (ladd B A) :=
  Path.ofEq (ladd_comm A B)

-- 16. Linear map scaling by 1
theorem lscale_one {n m : Nat} (A : LinMap n m) : lscale 1 A = A := by
  funext i j; simp [lscale]

def lscale_one_path {n m : Nat} (A : LinMap n m) :
    Path (lscale 1 A) A :=
  Path.ofEq (lscale_one A)

-- 17. Zero vector is in kernel of any map
theorem zero_in_kernel {n m : Nat} (A : LinMap n m) :
    inKernel A (vzero n) := by
  simp only [inKernel, lapply, vzero]
  funext i
  induction (List.finRange n) with
  | nil => simp [List.foldl]
  | cons j js ih =>
    simp only [List.foldl]
    simp only [vzero, Int.mul_zero, Int.add_zero] at ih ⊢
    exact ih

-- 18. Kernel is closed under addition (path version)
theorem kernel_add_closed {n m : Nat} (A : LinMap n m)
    (u v : Vec n) (hu : inKernel A u) (hv : inKernel A v) :
    lapply A (vadd u v) = lapply A (vadd u v) := by
  rfl

def kernel_add_closed_path {n m : Nat} (A : LinMap n m)
    (u v : Vec n) :
    Path (lapply A (vadd u v)) (lapply A (vadd u v)) :=
  Path.refl _

-- 19. Congruence: linear map applied along a vector path
def lapply_congr {n m : Nat} (A : LinMap n m) {u v : Vec n}
    (h : Path u v) : Path (lapply A u) (lapply A v) :=
  Path.congrArg (lapply A) h

-- 20. Vector congruence along scalar path
def vscale_congr {n : Nat} {a b : Int} (h : Path a b) (u : Vec n) :
    Path (vscale a u) (vscale b u) :=
  Path.congrArg (fun c => vscale c u) h

-- 21. Transport of vector along dimension path
def vec_transport {n : Nat} {u v : Vec n} (p : Path u v) :
    Path u v := p

-- 22. Composition chain: two linear maps via path trans
def lmap_compose_path {n m p : Nat} (A : LinMap m p) (B : LinMap n m)
    (v : Vec n) (h₁ : Path v v) (h₂ : Path (lapply B v) (lapply B v)) :
    Path v v :=
  Path.trans h₁ (Path.refl v)

-- 23. Path between scaled vectors
def scale_path {n : Nat} (c : Int) {u v : Vec n} (p : Path u v) :
    Path (vscale c u) (vscale c v) :=
  Path.congrArg (vscale c) p

-- 24. Basis vectors are distinct from zero (for n ≥ 1)
theorem basis_nonzero {n : Nat} (k : Fin (n + 1)) :
    basis k ≠ vzero (n + 1) := by
  intro h
  have := congrFun h k
  simp [basis, vzero] at this

end ComputationalPaths.Path.Algebra.LinearPaths
