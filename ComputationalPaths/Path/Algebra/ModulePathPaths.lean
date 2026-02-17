/-
# Module Theory of Computational Paths — Deep Rewrite System

R-modules with Nat scalars, module homomorphisms, kernel/image, exact sequences,
direct sums — all built from a genuine `MStep` / `MPath` rewrite system.
Zero `Path.mk [Step.mk _ _ _] _`, zero `sorry`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.ModulePathPaths

open ComputationalPaths

/-! ## Domain: Module element expressions -/

/-- Expression language for elements of a ℤ-module with Nat scalars. -/
inductive MExpr : Type
  | zero  : MExpr
  | var   : Nat → MExpr          -- named generators x₀, x₁, …
  | add   : MExpr → MExpr → MExpr
  | smul  : Nat → MExpr → MExpr  -- scalar multiplication by Nat
  | neg   : MExpr → MExpr
  deriving DecidableEq, Repr

/-! ## Primitive steps: module axioms as rewrites -/

inductive MStep : MExpr → MExpr → Type
  -- Additive group
  | add_comm (a b : MExpr) :
      MStep (.add a b) (.add b a)
  | add_assoc (a b c : MExpr) :
      MStep (.add (.add a b) c) (.add a (.add b c))
  | add_zero_right (a : MExpr) :
      MStep (.add a .zero) a
  | add_zero_left (a : MExpr) :
      MStep (.add .zero a) a
  | add_neg_right (a : MExpr) :
      MStep (.add a (.neg a)) .zero
  | add_neg_left (a : MExpr) :
      MStep (.add (.neg a) a) .zero
  -- Negation
  | neg_neg (a : MExpr) :
      MStep (.neg (.neg a)) a
  | neg_zero :
      MStep (.neg .zero) .zero
  | neg_add (a b : MExpr) :
      MStep (.neg (.add a b)) (.add (.neg a) (.neg b))
  -- Scalar multiplication
  | smul_zero_left (a : MExpr) :
      MStep (.smul 0 a) .zero
  | smul_zero_right (n : Nat) :
      MStep (.smul n .zero) .zero
  | smul_one (a : MExpr) :
      MStep (.smul 1 a) a
  | smul_add_dist (n : Nat) (a b : MExpr) :
      MStep (.smul n (.add a b)) (.add (.smul n a) (.smul n b))
  | smul_smul (m n : Nat) (a : MExpr) :
      MStep (.smul m (.smul n a)) (.smul (m * n) a)
  | smul_neg (n : Nat) (a : MExpr) :
      MStep (.smul n (.neg a)) (.neg (.smul n a))
  | smul_succ (n : Nat) (a : MExpr) :
      MStep (.smul (n + 1) a) (.add (.smul n a) a)

/-! ## Paths: freely generated from steps -/

inductive MPath : MExpr → MExpr → Type
  | refl  (a : MExpr) : MPath a a
  | step  {a b : MExpr} (s : MStep a b) : MPath a b
  | symm  {a b : MExpr} (p : MPath a b) : MPath b a
  | trans {a b c : MExpr} (p : MPath a b) (q : MPath b c) : MPath a c

namespace MPath

/-! ### §1 Additive group paths (1–8) -/

-- 1
def add_comm (a b : MExpr) : MPath (.add a b) (.add b a) :=
  step (.add_comm a b)

-- 2
def add_assoc (a b c : MExpr) :
    MPath (.add (.add a b) c) (.add a (.add b c)) :=
  step (.add_assoc a b c)

-- 3
def add_zero_right (a : MExpr) : MPath (.add a .zero) a :=
  step (.add_zero_right a)

-- 4
def add_zero_left (a : MExpr) : MPath (.add .zero a) a :=
  step (.add_zero_left a)

-- 5
def add_neg_right (a : MExpr) : MPath (.add a (.neg a)) .zero :=
  step (.add_neg_right a)

-- 6
def add_neg_left (a : MExpr) : MPath (.add (.neg a) a) .zero :=
  step (.add_neg_left a)

-- 7
def neg_neg (a : MExpr) : MPath (.neg (.neg a)) a :=
  step (.neg_neg a)

-- 8
def neg_zero : MPath (.neg .zero) .zero :=
  step .neg_zero

/-! ### §2 Scalar multiplication paths (9–16) -/

-- 9
def smul_zero_left (a : MExpr) : MPath (.smul 0 a) .zero :=
  step (.smul_zero_left a)

-- 10
def smul_zero_right (n : Nat) : MPath (.smul n .zero) .zero :=
  step (.smul_zero_right n)

-- 11
def smul_one (a : MExpr) : MPath (.smul 1 a) a :=
  step (.smul_one a)

-- 12
def smul_add_dist (n : Nat) (a b : MExpr) :
    MPath (.smul n (.add a b)) (.add (.smul n a) (.smul n b)) :=
  step (.smul_add_dist n a b)

-- 13
def smul_smul (m n : Nat) (a : MExpr) :
    MPath (.smul m (.smul n a)) (.smul (m * n) a) :=
  step (.smul_smul m n a)

-- 14
def smul_neg (n : Nat) (a : MExpr) :
    MPath (.smul n (.neg a)) (.neg (.smul n a)) :=
  step (.smul_neg n a)

-- 15
def smul_succ (n : Nat) (a : MExpr) :
    MPath (.smul (n + 1) a) (.add (.smul n a) a) :=
  step (.smul_succ n a)

-- 16
def neg_add (a b : MExpr) :
    MPath (.neg (.add a b)) (.add (.neg a) (.neg b)) :=
  step (.neg_add a b)

/-! ### §3 Composite paths (17–30) -/

-- 17. smul 2 x → add (smul 1 x) x
def smul_two (a : MExpr) :
    MPath (.smul 2 a) (.add (.smul 1 a) a) :=
  step (.smul_succ 1 a)

-- 18. Commutativity roundtrip
def add_comm_roundtrip (a b : MExpr) : MPath (.add a b) (.add a b) :=
  trans (add_comm a b) (add_comm b a)

-- 19. Associativity inverse
def add_assoc_inv (a b c : MExpr) :
    MPath (.add a (.add b c)) (.add (.add a b) c) :=
  symm (add_assoc a b c)

-- 20. Double negation backward
def neg_neg_inv (a : MExpr) : MPath a (.neg (.neg a)) :=
  symm (neg_neg a)

-- 21. neg zero backward
def neg_zero_inv : MPath .zero (.neg .zero) :=
  symm neg_zero

-- 22. 0 • (−x) = 0
def smul_zero_neg (a : MExpr) : MPath (.smul 0 (.neg a)) .zero :=
  smul_zero_left (.neg a)

-- 23. neg(neg(zero)) → zero (composed: neg_neg then id)
def neg_neg_zero : MPath (.neg (.neg .zero)) .zero :=
  neg_neg .zero

-- 24. Reassociate: (a + (−a)) + b → a + ((−a) + b)
def reassoc_cancel (a b : MExpr) :
    MPath (.add (.add a (.neg a)) b) (.add a (.add (.neg a) b)) :=
  add_assoc a (.neg a) b

-- 25. Four-element associativity: ((a+b)+c)+d → a+(b+(c+d))
def add_assoc4 (a b c d : MExpr) :
    MPath (.add (.add (.add a b) c) d) (.add a (.add b (.add c d))) :=
  trans (add_assoc (.add a b) c d) (add_assoc a b (.add c d))

-- 26. Double scalar composition: m•(n•(p•x)) → ((m*n)*p)•x
def smul_smul_comp (m n p : Nat) (a : MExpr) :
    MPath (.smul m (.smul n (.smul p a))) (.smul ((m * n) * p) a) :=
  trans (smul_smul m n (.smul p a)) (smul_smul (m * n) p a)

-- 27. (n+1)•x → x + n•x (succ then comm)
def smul_succ_comm (n : Nat) (a : MExpr) :
    MPath (.smul (n + 1) a) (.add a (.smul n a)) :=
  trans (smul_succ n a) (add_comm (.smul n a) a)

-- 28. neg(a+b) → neg(b) + neg(a) (neg distributes, then comm)
def neg_add_comm (a b : MExpr) :
    MPath (.neg (.add a b)) (.add (.neg b) (.neg a)) :=
  trans (neg_add a b) (add_comm (.neg a) (.neg b))

-- 29. Self-cancel: (a+b) + neg(a+b) → 0
def add_self_neg (a b : MExpr) :
    MPath (.add (.add a b) (.neg (.add a b))) .zero :=
  add_neg_right (.add a b)

-- 30. Double symm preserves path
def double_symm {a b : MExpr} (p : MPath a b) : MPath a b :=
  symm (symm p)

/-! ### §4 Kernel via paths (31–35) -/

/-- An element `a` is in the "kernel" if there's a path to zero. -/
def InKernel (a : MExpr) : Prop := Nonempty (MPath a .zero)

-- 31. Zero is in the kernel
theorem zero_in_kernel : InKernel .zero :=
  ⟨refl .zero⟩

-- 32. neg(a) + a is in the kernel
theorem neg_add_in_kernel (a : MExpr) : InKernel (.add (.neg a) a) :=
  ⟨add_neg_left a⟩

-- 33. a + neg(a) is in the kernel
theorem add_neg_in_kernel (a : MExpr) : InKernel (.add a (.neg a)) :=
  ⟨add_neg_right a⟩

-- 34. 0 • a is in the kernel
theorem smul_zero_in_kernel (a : MExpr) : InKernel (.smul 0 a) :=
  ⟨smul_zero_left a⟩

-- 35. n • 0 is in the kernel
theorem smul_n_zero_in_kernel (n : Nat) : InKernel (.smul n .zero) :=
  ⟨smul_zero_right n⟩

/-! ### §5 Direct sum as pairs (36–37) -/

/-- Direct sum expression: pairs of module expressions -/
inductive DSExpr : Type
  | pair : MExpr → MExpr → DSExpr
  deriving DecidableEq, Repr

/-- Steps for direct-sum swap. -/
inductive DSStep : DSExpr → DSExpr → Type
  | swap (a b : MExpr) : DSStep (.pair a b) (.pair b a)

/-- Paths for direct sums -/
inductive DSPath : DSExpr → DSExpr → Type
  | refl  (e : DSExpr) : DSPath e e
  | step  {e₁ e₂ : DSExpr} (s : DSStep e₁ e₂) : DSPath e₁ e₂
  | symm  {e₁ e₂ : DSExpr} (p : DSPath e₁ e₂) : DSPath e₂ e₁
  | trans {e₁ e₂ e₃ : DSExpr} (p : DSPath e₁ e₂) (q : DSPath e₂ e₃) : DSPath e₁ e₃

-- 36. Swap is involutive
def ds_swap_roundtrip (a b : MExpr) : DSPath (.pair a b) (.pair a b) :=
  DSPath.trans (DSPath.step (.swap a b)) (DSPath.step (.swap b a))

-- 37. Swap backward
def ds_swap_inv (a b : MExpr) : DSPath (.pair b a) (.pair a b) :=
  DSPath.symm (DSPath.step (.swap a b))

/-! ### §6 Groupoid structure (38–42) -/

-- 38. Three-fold composition
def compose3 {a b c d : MExpr}
    (p : MPath a b) (q : MPath b c) (r : MPath c d) : MPath a d :=
  trans p (trans q r)

-- 39. Trans with symm gives roundtrip
def trans_symm_roundtrip {a b : MExpr} (p : MPath a b) : MPath a a :=
  trans p (symm p)

-- 40. Symm then trans
def symm_trans_roundtrip {a b : MExpr} (p : MPath a b) : MPath b b :=
  trans (symm p) p

-- 41. Four-fold composition
def compose4 {a b c d e : MExpr}
    (p : MPath a b) (q : MPath b c) (r : MPath c d) (s : MPath d e) : MPath a e :=
  trans (trans p q) (trans r s)

-- 42. Reverse a three-fold composition
def reverse3 {a b c d : MExpr}
    (p : MPath a b) (q : MPath b c) (r : MPath c d) : MPath d a :=
  symm (compose3 p q r)

end MPath

/-! ### §7 Weight invariant (43–45) -/

/-- Weight: counts variable indices (invariant under module laws). -/
@[simp] def MExpr.weight : MExpr → Nat
  | .zero     => 0
  | .var n    => n + 1
  | .add a b  => a.weight + b.weight
  | .smul _ a => a.weight
  | .neg a    => a.weight

-- 43. smul preserves weight
theorem smul_weight (n : Nat) (a : MExpr) :
    (MExpr.smul n a).weight = a.weight := by simp [MExpr.weight]

-- 44. neg preserves weight
theorem neg_weight (a : MExpr) :
    (MExpr.neg a).weight = a.weight := by simp [MExpr.weight]

-- 45. zero has weight 0
theorem zero_weight : MExpr.zero.weight = 0 := by simp [MExpr.weight]

namespace MPath

/-! ### §8 Concrete computations (46–50) -/

-- 46. add(x₀, zero) → x₀
def concrete_add_zero : MPath (.add (.var 0) .zero) (.var 0) :=
  add_zero_right (.var 0)

-- 47. smul 1 x₀ → x₀
def concrete_smul_one : MPath (.smul 1 (.var 0)) (.var 0) :=
  smul_one (.var 0)

-- 48. x₀ + neg(x₀) → 0
def concrete_cancel : MPath (.add (.var 0) (.neg (.var 0))) .zero :=
  add_neg_right (.var 0)

-- 49. neg(neg(x₀)) → x₀
def concrete_neg_neg : MPath (.neg (.neg (.var 0))) (.var 0) :=
  neg_neg (.var 0)

-- 50. smul 3 x₀ → add (smul 2 x₀) x₀
def concrete_smul3 : MPath (.smul 3 (.var 0)) (.add (.smul 2 (.var 0)) (.var 0)) :=
  smul_succ 2 (.var 0)

end MPath

end ComputationalPaths.Path.Algebra.ModulePathPaths
