/-
# Module Theory of Computational Paths

R-modules with Nat scalars, module homomorphisms, kernel/image as path
predicates, exact sequences, direct sums, scalar action laws — all built
from `Path`, `Step`, `trans`, `symm`.

## Main results (25+ theorems/defs)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ModulePathPaths

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Path R-Module structure -/

/-- An R-module structure over paths, with Nat scalars. -/
structure PathModule (M : Type u) where
  zero : M
  add  : M → M → M
  smul : Nat → M → M
  add_comm  : ∀ x y : M, add x y = add y x
  add_assoc : ∀ x y z : M, add (add x y) z = add x (add y z)
  add_zero  : ∀ x : M, add x zero = x
  zero_add  : ∀ x : M, add zero x = x
  smul_zero_eq : ∀ x : M, smul 0 x = zero
  smul_zero_r : ∀ n : Nat, smul n zero = zero
  smul_one  : ∀ x : M, smul 1 x = x
  smul_add  : ∀ (n : Nat) (x y : M), smul n (add x y) = add (smul n x) (smul n y)
  smul_smul : ∀ (m n : Nat) (x : M), smul m (smul n x) = smul (m * n) x

/-- Path witnessing `add x zero = x`. -/
def add_zero_path (PM : PathModule A) (x : A) : Path (PM.add x PM.zero) x :=
  Path.ofEq (PM.add_zero x)

/-- Path witnessing `zero + x = x`. -/
def zero_add_path (PM : PathModule A) (x : A) : Path (PM.add PM.zero x) x :=
  Path.ofEq (PM.zero_add x)

/-- Path witnessing commutativity of addition. -/
def add_comm_path (PM : PathModule A) (x y : A) :
    Path (PM.add x y) (PM.add y x) :=
  Path.ofEq (PM.add_comm x y)

/-- Path witnessing associativity of addition. -/
def add_assoc_path (PM : PathModule A) (x y z : A) :
    Path (PM.add (PM.add x y) z) (PM.add x (PM.add y z)) :=
  Path.ofEq (PM.add_assoc x y z)

/-- Path witnessing `0 • x = 0`. -/
def smul_zero_path (PM : PathModule A) (x : A) :
    Path (PM.smul 0 x) PM.zero :=
  Path.ofEq (PM.smul_zero_eq x)

/-- Path witnessing `1 • x = x`. -/
def smul_one_path (PM : PathModule A) (x : A) :
    Path (PM.smul 1 x) x :=
  Path.ofEq (PM.smul_one x)

/-- Path witnessing scalar distributes over addition. -/
def smul_add_path (PM : PathModule A) (n : Nat) (x y : A) :
    Path (PM.smul n (PM.add x y)) (PM.add (PM.smul n x) (PM.smul n y)) :=
  Path.ofEq (PM.smul_add n x y)

/-- Path witnessing scalar associativity. -/
def smul_smul_path (PM : PathModule A) (m n : Nat) (x : A) :
    Path (PM.smul m (PM.smul n x)) (PM.smul (m * n) x) :=
  Path.ofEq (PM.smul_smul m n x)

/-! ## Module Homomorphisms -/

/-- A module homomorphism between two path modules. -/
structure PathModuleHom (PM₁ : PathModule A) (PM₂ : PathModule B) where
  toFun : A → B
  map_add  : ∀ x y : A, toFun (PM₁.add x y) = PM₂.add (toFun x) (toFun y)
  map_smul : ∀ (n : Nat) (x : A), toFun (PM₁.smul n x) = PM₂.smul n (toFun x)
  map_zero : toFun PM₁.zero = PM₂.zero

/-- Path witnessing that a homomorphism preserves addition. -/
def hom_add_path {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (x y : A) :
    Path (f.toFun (PM₁.add x y)) (PM₂.add (f.toFun x) (f.toFun y)) :=
  Path.ofEq (f.map_add x y)

/-- Path witnessing that a homomorphism preserves scalars. -/
def hom_smul_path {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (n : Nat) (x : A) :
    Path (f.toFun (PM₁.smul n x)) (PM₂.smul n (f.toFun x)) :=
  Path.ofEq (f.map_smul n x)

/-- Path witnessing that a homomorphism preserves zero. -/
def hom_zero_path {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) :
    Path (f.toFun PM₁.zero) PM₂.zero :=
  Path.ofEq f.map_zero

/-! ## Kernel and Image -/

/-- An element is in the kernel of f if f(x) = 0. -/
def InKernel {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (x : A) : Prop :=
  f.toFun x = PM₂.zero

/-- An element is in the image of f if there exists a preimage. -/
def InImage {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (y : B) : Prop :=
  ∃ x : A, f.toFun x = y

/-- Zero is always in the kernel. -/
theorem zero_in_kernel {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) : InKernel f PM₁.zero := by
  unfold InKernel
  exact f.map_zero

/-- Zero is always in the image. -/
theorem zero_in_image {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) : InImage f PM₂.zero := by
  unfold InImage
  exact ⟨PM₁.zero, f.map_zero⟩

/-- Kernel is closed under addition. -/
theorem kernel_add_closed {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (x y : A)
    (hx : InKernel f x) (hy : InKernel f y) :
    InKernel f (PM₁.add x y) := by
  unfold InKernel at *
  rw [f.map_add, hx, hy, PM₂.add_zero]

/-- Kernel is closed under scalar multiplication. -/
theorem kernel_smul_closed {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (n : Nat) (x : A)
    (hx : InKernel f x) : InKernel f (PM₁.smul n x) := by
  unfold InKernel at *
  rw [f.map_smul, hx]
  exact PM₂.smul_zero_r n

/-- Path from f(x+y) to zero when x,y in kernel. -/
def kernel_add_path {PM₁ : PathModule A} {PM₂ : PathModule B}
    (f : PathModuleHom PM₁ PM₂) (x y : A)
    (hx : InKernel f x) (hy : InKernel f y) :
    Path (f.toFun (PM₁.add x y)) PM₂.zero :=
  Path.ofEq (kernel_add_closed f x y hx hy)

/-! ## Exact Sequences -/

/-- A pair (f, g) is exact at B if image(f) = kernel(g). -/
structure ExactAt {PM₁ : PathModule A} {PM₂ : PathModule B} {PM₃ : PathModule C}
    (f : PathModuleHom PM₁ PM₂) (g : PathModuleHom PM₂ PM₃) where
  im_sub_ker : ∀ x : A, InKernel g (f.toFun x)
  ker_sub_im : ∀ y : B, InKernel g y → InImage f y

/-- In an exact sequence, composing gives zero. -/
theorem exact_comp_zero {PM₁ : PathModule A} {PM₂ : PathModule B} {PM₃ : PathModule C}
    {f : PathModuleHom PM₁ PM₂} {g : PathModuleHom PM₂ PM₃}
    (ex : ExactAt f g) (x : A) :
    g.toFun (f.toFun x) = PM₃.zero :=
  ex.im_sub_ker x

/-- Path witnessing exactness: g(f(x)) = 0. -/
def exact_zero_path {PM₁ : PathModule A} {PM₂ : PathModule B} {PM₃ : PathModule C}
    {f : PathModuleHom PM₁ PM₂} {g : PathModuleHom PM₂ PM₃}
    (ex : ExactAt f g) (x : A) :
    Path (g.toFun (f.toFun x)) PM₃.zero :=
  Path.ofEq (exact_comp_zero ex x)

/-! ## Direct Sum -/

/-- Direct sum of two modules as a product type. -/
def DirectSum (PM₁ : PathModule A) (PM₂ : PathModule B) : PathModule (A × B) where
  zero := (PM₁.zero, PM₂.zero)
  add p q := (PM₁.add p.1 q.1, PM₂.add p.2 q.2)
  smul n p := (PM₁.smul n p.1, PM₂.smul n p.2)
  add_comm p q := by
    exact Prod.ext (PM₁.add_comm p.1 q.1) (PM₂.add_comm p.2 q.2)
  add_assoc p q r := by
    exact Prod.ext (PM₁.add_assoc p.1 q.1 r.1) (PM₂.add_assoc p.2 q.2 r.2)
  add_zero p := by
    exact Prod.ext (PM₁.add_zero p.1) (PM₂.add_zero p.2)
  zero_add p := by
    exact Prod.ext (PM₁.zero_add p.1) (PM₂.zero_add p.2)
  smul_zero_eq p := by
    exact Prod.ext (PM₁.smul_zero_eq p.1) (PM₂.smul_zero_eq p.2)
  smul_zero_r n := by
    exact Prod.ext (PM₁.smul_zero_r n) (PM₂.smul_zero_r n)
  smul_one p := by
    exact Prod.ext (PM₁.smul_one p.1) (PM₂.smul_one p.2)
  smul_add n p q := by
    exact Prod.ext (PM₁.smul_add n p.1 q.1) (PM₂.smul_add n p.2 q.2)
  smul_smul m n p := by
    exact Prod.ext (PM₁.smul_smul m n p.1) (PM₂.smul_smul m n p.2)

/-- First projection is a module homomorphism. -/
def fstHom (PM₁ : PathModule A) (PM₂ : PathModule B) :
    PathModuleHom (DirectSum PM₁ PM₂) PM₁ where
  toFun p := p.1
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_zero := rfl

/-- Second projection is a module homomorphism. -/
def sndHom (PM₁ : PathModule A) (PM₂ : PathModule B) :
    PathModuleHom (DirectSum PM₁ PM₂) PM₂ where
  toFun p := p.2
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_zero := rfl

/-- Inclusion of first component. -/
def inlHom (PM₁ : PathModule A) (PM₂ : PathModule B) :
    PathModuleHom PM₁ (DirectSum PM₁ PM₂) where
  toFun x := (x, PM₂.zero)
  map_add x y := by
    simp only [DirectSum]
    exact Prod.ext rfl (PM₂.add_zero PM₂.zero).symm
  map_smul n x := by
    simp only [DirectSum]
    exact Prod.ext rfl (PM₂.smul_zero_r n).symm
  map_zero := rfl

/-- Inclusion of second component. -/
def inrHom (PM₁ : PathModule A) (PM₂ : PathModule B) :
    PathModuleHom PM₂ (DirectSum PM₁ PM₂) where
  toFun y := (PM₁.zero, y)
  map_add x y := by
    simp only [DirectSum]
    exact Prod.ext (PM₁.add_zero PM₁.zero).symm rfl
  map_smul n x := by
    simp only [DirectSum]
    exact Prod.ext (PM₁.smul_zero_r n).symm rfl
  map_zero := rfl

/-- Path: fst ∘ inl = id. -/
theorem fst_inl (PM₁ : PathModule A) (PM₂ : PathModule B) (x : A) :
    (fstHom PM₁ PM₂).toFun ((inlHom PM₁ PM₂).toFun x) = x := rfl

/-- Path: snd ∘ inr = id. -/
theorem snd_inr (PM₁ : PathModule A) (PM₂ : PathModule B) (y : B) :
    (sndHom PM₁ PM₂).toFun ((inrHom PM₁ PM₂).toFun y) = y := rfl

/-- Path witnessing fst ∘ inl = id. -/
def fst_inl_path (PM₁ : PathModule A) (PM₂ : PathModule B) (x : A) :
    Path ((fstHom PM₁ PM₂).toFun ((inlHom PM₁ PM₂).toFun x)) x :=
  Path.refl x

/-- Path witnessing snd ∘ inr = id. -/
def snd_inr_path (PM₁ : PathModule A) (PM₂ : PathModule B) (y : B) :
    Path ((sndHom PM₁ PM₂).toFun ((inrHom PM₁ PM₂).toFun y)) y :=
  Path.refl y

/-! ## Scalar path composition laws -/

/-- Composing smul paths: `n • (m • x) ~> (n*m) • x`. -/
def smul_comp_path (PM : PathModule A) (m n : Nat) (x : A) :
    Path (PM.smul m (PM.smul n x)) (PM.smul (m * n) x) :=
  Path.ofEq (PM.smul_smul m n x)

/-- Double scalar: `2 • x = x + x` path. -/
def smul_two_path (PM : PathModule A) (x : A)
    (h : PM.smul 2 x = PM.add x x) :
    Path (PM.smul 2 x) (PM.add x x) :=
  Path.ofEq h

/-- Path from commutativity and then zero-add. -/
def comm_then_zero (PM : PathModule A) (x : A) :
    Path (PM.add x PM.zero) x :=
  Path.ofEq (PM.add_zero x)

/-- Symmetry: reversing add_comm path. -/
def add_comm_symm_path (PM : PathModule A) (x y : A) :
    Path (PM.add y x) (PM.add x y) :=
  Path.symm (add_comm_path PM x y)

/-- Transitivity: add_assoc followed by add_comm on inner pair. -/
def assoc_then_comm_path (PM : PathModule A) (x y z : A)
    (h : PM.add x (PM.add y z) = PM.add x (PM.add z y)) :
    Path (PM.add (PM.add x y) z) (PM.add x (PM.add z y)) :=
  Path.trans (add_assoc_path PM x y z) (Path.ofEq h)

/-! ## Homomorphism composition -/

/-- Composition of two module homomorphisms. -/
def compHom {PM₁ : PathModule A} {PM₂ : PathModule B} {PM₃ : PathModule C}
    (f : PathModuleHom PM₁ PM₂) (g : PathModuleHom PM₂ PM₃) :
    PathModuleHom PM₁ PM₃ where
  toFun x := g.toFun (f.toFun x)
  map_add x y := by rw [f.map_add, g.map_add]
  map_smul n x := by rw [f.map_smul, g.map_smul]
  map_zero := by rw [f.map_zero, g.map_zero]

/-- Path witnessing (g ∘ f)(x+y) = g(f(x)) + g(f(y)). -/
def comp_add_path {PM₁ : PathModule A} {PM₂ : PathModule B} {PM₃ : PathModule C}
    (f : PathModuleHom PM₁ PM₂) (g : PathModuleHom PM₂ PM₃) (x y : A) :
    Path ((compHom f g).toFun (PM₁.add x y))
         (PM₃.add ((compHom f g).toFun x) ((compHom f g).toFun y)) :=
  Path.ofEq ((compHom f g).map_add x y)

end ComputationalPaths.Path.Algebra.ModulePathPaths
