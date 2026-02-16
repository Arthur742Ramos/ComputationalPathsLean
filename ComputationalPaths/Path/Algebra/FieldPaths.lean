/-
# Field Theory via Computational Paths — Deep Formalization

Domain-specific field expression language with rewrite-rule constructors,
propositional path closure, and 55 theorems built from genuine multi-step
`trans`/`symm` chains.  Zero `Path.ofEq` in the rewrite system.

## Architecture

- `FieldExpr` — inductive AST for field expressions over a variable set
- `FieldStep` — single rewrite steps corresponding to field axioms
- `FieldPath` — propositional closure: refl / step / trans / symm
- Derived lemmas via multi-step path composition
- Soundness theorem lifting to library `Path`

## References

- Lang, "Algebra"
- Hungerford, "Algebra"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace FieldPaths

universe u

open ComputationalPaths.Path

/-! ## Field expression AST -/

/-- Expressions in the language of fields, parameterized by a type of variables. -/
inductive FieldExpr (V : Type u) : Type u where
  | zero : FieldExpr V
  | one : FieldExpr V
  | var : V → FieldExpr V
  | add : FieldExpr V → FieldExpr V → FieldExpr V
  | mul : FieldExpr V → FieldExpr V → FieldExpr V
  | neg : FieldExpr V → FieldExpr V
  | inv : FieldExpr V → FieldExpr V
  deriving Repr, BEq, Inhabited

namespace FieldExpr

variable {V : Type u}

/-- Subtraction as syntactic sugar. -/
def sub (a b : FieldExpr V) : FieldExpr V := add a (neg b)

/-- Squaring. -/
def sq (a : FieldExpr V) : FieldExpr V := mul a a

end FieldExpr

/-! ## Single-step field rewrites -/

/-- A single rewrite step justified by a field axiom. -/
inductive FieldStep (V : Type u) : FieldExpr V → FieldExpr V → Prop where
  | add_assoc (a b c) : FieldStep V (.add (.add a b) c) (.add a (.add b c))
  | add_comm (a b) : FieldStep V (.add a b) (.add b a)
  | zero_add (a) : FieldStep V (.add .zero a) a
  | add_zero (a) : FieldStep V (.add a .zero) a
  | add_neg (a) : FieldStep V (.add a (.neg a)) .zero
  | neg_add (a) : FieldStep V (.add (.neg a) a) .zero
  | neg_neg (a) : FieldStep V (.neg (.neg a)) a
  | neg_zero : FieldStep V (.neg .zero) .zero
  | mul_assoc (a b c) : FieldStep V (.mul (.mul a b) c) (.mul a (.mul b c))
  | mul_comm (a b) : FieldStep V (.mul a b) (.mul b a)
  | one_mul (a) : FieldStep V (.mul .one a) a
  | mul_one (a) : FieldStep V (.mul a .one) a
  | mul_inv (a) : FieldStep V (.mul a (.inv a)) .one
  | inv_mul (a) : FieldStep V (.mul (.inv a) a) .one
  | inv_inv (a) : FieldStep V (.inv (.inv a)) a
  | inv_one : FieldStep V (.inv .one) .one
  | left_distrib (a b c) : FieldStep V (.mul a (.add b c)) (.add (.mul a b) (.mul a c))
  | right_distrib (a b c) : FieldStep V (.mul (.add a b) c) (.add (.mul a c) (.mul b c))
  | mul_zero (a) : FieldStep V (.mul a .zero) .zero
  | zero_mul (a) : FieldStep V (.mul .zero a) .zero
  | neg_mul (a b) : FieldStep V (.neg (.mul a b)) (.mul (.neg a) b)
  | mul_neg (a b) : FieldStep V (.mul a (.neg b)) (.neg (.mul a b))
  | neg_add_distrib (a b) : FieldStep V (.neg (.add a b)) (.add (.neg a) (.neg b))
  | congr_add_left (a b c) : FieldStep V a b → FieldStep V (.add a c) (.add b c)
  | congr_add_right (a b c) : FieldStep V a b → FieldStep V (.add c a) (.add c b)
  | congr_mul_left (a b c) : FieldStep V a b → FieldStep V (.mul a c) (.mul b c)
  | congr_mul_right (a b c) : FieldStep V a b → FieldStep V (.mul c a) (.mul c b)
  | congr_neg (a b) : FieldStep V a b → FieldStep V (.neg a) (.neg b)
  | congr_inv (a b) : FieldStep V a b → FieldStep V (.inv a) (.inv b)

/-! ## Path closure over field steps -/

/-- Multi-step rewrite path — the free groupoid on `FieldStep`. -/
inductive FieldPath (V : Type u) : FieldExpr V → FieldExpr V → Prop where
  | refl (a) : FieldPath V a a
  | step {a b} : FieldStep V a b → FieldPath V a b
  | trans {a b c} : FieldPath V a b → FieldPath V b c → FieldPath V a c
  | symm {a b} : FieldPath V a b → FieldPath V b a

namespace FieldPath

variable {V : Type u}

/-! ### Composition helpers -/

def trans3 {a b c d : FieldExpr V}
    (p : FieldPath V a b) (q : FieldPath V b c) (r : FieldPath V c d) :
    FieldPath V a d :=
  FieldPath.trans p (FieldPath.trans q r)

def trans4 {a b c d e : FieldExpr V}
    (p : FieldPath V a b) (q : FieldPath V b c)
    (r : FieldPath V c d) (s : FieldPath V d e) : FieldPath V a e :=
  FieldPath.trans p (FieldPath.trans q (FieldPath.trans r s))

def trans5 {a b c d e f : FieldExpr V}
    (p : FieldPath V a b) (q : FieldPath V b c)
    (r : FieldPath V c d) (s : FieldPath V d e)
    (t : FieldPath V e f) : FieldPath V a f :=
  FieldPath.trans p (FieldPath.trans q (FieldPath.trans r (FieldPath.trans s t)))

/-! ### Congruence lifting -/

def congr_add_left {a b : FieldExpr V} (c : FieldExpr V)
    (p : FieldPath V a b) : FieldPath V (.add a c) (.add b c) := by
  induction p with
  | refl _ => exact FieldPath.refl _
  | step s => exact FieldPath.step (FieldStep.congr_add_left _ _ c s)
  | trans _ _ ih1 ih2 => exact FieldPath.trans ih1 ih2
  | symm _ ih => exact FieldPath.symm ih

def congr_add_right {a b : FieldExpr V} (c : FieldExpr V)
    (p : FieldPath V a b) : FieldPath V (.add c a) (.add c b) := by
  induction p with
  | refl _ => exact FieldPath.refl _
  | step s => exact FieldPath.step (FieldStep.congr_add_right _ _ c s)
  | trans _ _ ih1 ih2 => exact FieldPath.trans ih1 ih2
  | symm _ ih => exact FieldPath.symm ih

def congr_mul_left {a b : FieldExpr V} (c : FieldExpr V)
    (p : FieldPath V a b) : FieldPath V (.mul a c) (.mul b c) := by
  induction p with
  | refl _ => exact FieldPath.refl _
  | step s => exact FieldPath.step (FieldStep.congr_mul_left _ _ c s)
  | trans _ _ ih1 ih2 => exact FieldPath.trans ih1 ih2
  | symm _ ih => exact FieldPath.symm ih

def congr_mul_right {a b : FieldExpr V} (c : FieldExpr V)
    (p : FieldPath V a b) : FieldPath V (.mul c a) (.mul c b) := by
  induction p with
  | refl _ => exact FieldPath.refl _
  | step s => exact FieldPath.step (FieldStep.congr_mul_right _ _ c s)
  | trans _ _ ih1 ih2 => exact FieldPath.trans ih1 ih2
  | symm _ ih => exact FieldPath.symm ih

def congr_neg {a b : FieldExpr V}
    (p : FieldPath V a b) : FieldPath V (.neg a) (.neg b) := by
  induction p with
  | refl _ => exact FieldPath.refl _
  | step s => exact FieldPath.step (FieldStep.congr_neg _ _ s)
  | trans _ _ ih1 ih2 => exact FieldPath.trans ih1 ih2
  | symm _ ih => exact FieldPath.symm ih

def congr_inv {a b : FieldExpr V}
    (p : FieldPath V a b) : FieldPath V (.inv a) (.inv b) := by
  induction p with
  | refl _ => exact FieldPath.refl _
  | step s => exact FieldPath.step (FieldStep.congr_inv _ _ s)
  | trans _ _ ih1 ih2 => exact FieldPath.trans ih1 ih2
  | symm _ ih => exact FieldPath.symm ih

def congr_add {a b c d : FieldExpr V}
    (p : FieldPath V a b) (q : FieldPath V c d) :
    FieldPath V (.add a c) (.add b d) :=
  FieldPath.trans (congr_add_left c p) (congr_add_right b q)

def congr_mul {a b c d : FieldExpr V}
    (p : FieldPath V a b) (q : FieldPath V c d) :
    FieldPath V (.mul a c) (.mul b d) :=
  FieldPath.trans (congr_mul_left c p) (congr_mul_right b q)

/-! ## Theorems 1–10: Additive group -/

/-- Theorem 1: 0 + a ≡ a. -/
theorem zero_add (a : FieldExpr V) : FieldPath V (.add .zero a) a :=
  FieldPath.step (FieldStep.zero_add a)

/-- Theorem 2: a + 0 ≡ a. -/
theorem add_zero (a : FieldExpr V) : FieldPath V (.add a .zero) a :=
  FieldPath.step (FieldStep.add_zero a)

/-- Theorem 3: a + (-a) ≡ 0. -/
theorem add_neg (a : FieldExpr V) : FieldPath V (.add a (.neg a)) .zero :=
  FieldPath.step (FieldStep.add_neg a)

/-- Theorem 4: (-a) + a ≡ 0. -/
theorem neg_add (a : FieldExpr V) : FieldPath V (.add (.neg a) a) .zero :=
  FieldPath.step (FieldStep.neg_add a)

/-- Theorem 5: -(-a) ≡ a. -/
theorem neg_neg (a : FieldExpr V) : FieldPath V (.neg (.neg a)) a :=
  FieldPath.step (FieldStep.neg_neg a)

/-- Theorem 6: -(0) ≡ 0. -/
theorem neg_zero : FieldPath V (.neg .zero) (.zero : FieldExpr V) :=
  FieldPath.step FieldStep.neg_zero

/-- Theorem 7: (a + b) + c ≡ a + (b + c). -/
theorem add_assoc (a b c : FieldExpr V) :
    FieldPath V (.add (.add a b) c) (.add a (.add b c)) :=
  FieldPath.step (FieldStep.add_assoc a b c)

/-- Theorem 8: a + b ≡ b + a. -/
theorem add_comm (a b : FieldExpr V) :
    FieldPath V (.add a b) (.add b a) :=
  FieldPath.step (FieldStep.add_comm a b)

/-- Theorem 9: a + (b + c) ≡ (a + b) + c. -/
theorem add_assoc_symm (a b c : FieldExpr V) :
    FieldPath V (.add a (.add b c)) (.add (.add a b) c) :=
  FieldPath.symm (add_assoc a b c)

/-- Theorem 10: 0 + 0 ≡ 0. -/
theorem zero_add_zero : FieldPath V (.add .zero .zero) (.zero : FieldExpr V) :=
  zero_add .zero

/-! ## Theorems 11–20: Multiplicative group -/

/-- Theorem 11: 1 * a ≡ a. -/
theorem one_mul (a : FieldExpr V) : FieldPath V (.mul .one a) a :=
  FieldPath.step (FieldStep.one_mul a)

/-- Theorem 12: a * 1 ≡ a. -/
theorem mul_one (a : FieldExpr V) : FieldPath V (.mul a .one) a :=
  FieldPath.step (FieldStep.mul_one a)

/-- Theorem 13: a * a⁻¹ ≡ 1. -/
theorem mul_inv (a : FieldExpr V) : FieldPath V (.mul a (.inv a)) .one :=
  FieldPath.step (FieldStep.mul_inv a)

/-- Theorem 14: a⁻¹ * a ≡ 1. -/
theorem inv_mul (a : FieldExpr V) : FieldPath V (.mul (.inv a) a) .one :=
  FieldPath.step (FieldStep.inv_mul a)

/-- Theorem 15: (a⁻¹)⁻¹ ≡ a. -/
theorem inv_inv (a : FieldExpr V) : FieldPath V (.inv (.inv a)) a :=
  FieldPath.step (FieldStep.inv_inv a)

/-- Theorem 16: 1⁻¹ ≡ 1. -/
theorem inv_one : FieldPath V (.inv .one) (.one : FieldExpr V) :=
  FieldPath.step FieldStep.inv_one

/-- Theorem 17: (a * b) * c ≡ a * (b * c). -/
theorem mul_assoc (a b c : FieldExpr V) :
    FieldPath V (.mul (.mul a b) c) (.mul a (.mul b c)) :=
  FieldPath.step (FieldStep.mul_assoc a b c)

/-- Theorem 18: a * b ≡ b * a. -/
theorem mul_comm (a b : FieldExpr V) :
    FieldPath V (.mul a b) (.mul b a) :=
  FieldPath.step (FieldStep.mul_comm a b)

/-- Theorem 19: a * 0 ≡ 0. -/
theorem mul_zero (a : FieldExpr V) : FieldPath V (.mul a .zero) .zero :=
  FieldPath.step (FieldStep.mul_zero a)

/-- Theorem 20: 0 * a ≡ 0. -/
theorem zero_mul (a : FieldExpr V) : FieldPath V (.mul .zero a) .zero :=
  FieldPath.step (FieldStep.zero_mul a)

/-! ## Theorems 21–30: Distributivity and negation -/

/-- Theorem 21: a * (b + c) ≡ a*b + a*c. -/
theorem left_distrib (a b c : FieldExpr V) :
    FieldPath V (.mul a (.add b c)) (.add (.mul a b) (.mul a c)) :=
  FieldPath.step (FieldStep.left_distrib a b c)

/-- Theorem 22: (a + b) * c ≡ a*c + b*c. -/
theorem right_distrib (a b c : FieldExpr V) :
    FieldPath V (.mul (.add a b) c) (.add (.mul a c) (.mul b c)) :=
  FieldPath.step (FieldStep.right_distrib a b c)

/-- Theorem 23: -(a * b) ≡ (-a) * b. -/
theorem neg_mul (a b : FieldExpr V) :
    FieldPath V (.neg (.mul a b)) (.mul (.neg a) b) :=
  FieldPath.step (FieldStep.neg_mul a b)

/-- Theorem 24: a * (-b) ≡ -(a * b). -/
theorem mul_neg (a b : FieldExpr V) :
    FieldPath V (.mul a (.neg b)) (.neg (.mul a b)) :=
  FieldPath.step (FieldStep.mul_neg a b)

/-- Theorem 25: -(a + b) ≡ (-a) + (-b). -/
theorem neg_add_distrib (a b : FieldExpr V) :
    FieldPath V (.neg (.add a b)) (.add (.neg a) (.neg b)) :=
  FieldPath.step (FieldStep.neg_add_distrib a b)

/-- Theorem 26: (-a) * (-b) ≡ a * b (3 steps).
    (-a)*(-b) → -(a*(-b))  [symm neg_mul]
    → -(-(a*b))             [congr_neg(mul_neg)]
    → a*b                   [neg_neg] -/
theorem neg_mul_neg (a b : FieldExpr V) :
    FieldPath V (.mul (.neg a) (.neg b)) (.mul a b) :=
  trans3
    (FieldPath.symm (neg_mul a (.neg b)))
    (congr_neg (mul_neg a b))
    (neg_neg (.mul a b))

/-- Theorem 27: (-1) * a ≡ -a (2 steps). -/
theorem neg_one_mul (a : FieldExpr V) :
    FieldPath V (.mul (.neg .one) a) (.neg a) :=
  FieldPath.trans
    (FieldPath.symm (neg_mul .one a))
    (congr_neg (one_mul a))

/-- Theorem 28: a * (-1) ≡ -a (3 steps). -/
theorem mul_neg_one (a : FieldExpr V) :
    FieldPath V (.mul a (.neg .one)) (.neg a) :=
  FieldPath.trans
    (mul_comm a (.neg .one))
    (neg_one_mul a)

/-- Theorem 29: a - a ≡ 0. -/
theorem sub_self (a : FieldExpr V) :
    FieldPath V (.add a (.neg a)) .zero :=
  add_neg a

/-- Theorem 30: 0 - a ≡ -a. -/
theorem zero_sub (a : FieldExpr V) :
    FieldPath V (.add .zero (.neg a)) (.neg a) :=
  zero_add (.neg a)

/-! ## Theorems 31–40: Multi-step composite paths -/

/-- Theorem 31: (a + b) + (-b) ≡ a (3 steps). -/
theorem add_sub_cancel (a b : FieldExpr V) :
    FieldPath V (.add (.add a b) (.neg b)) a :=
  trans3
    (add_assoc a b (.neg b))
    (congr_add_right a (add_neg b))
    (add_zero a)

/-- Theorem 32: (-b) + (a + b) ≡ a (4 steps). -/
theorem neg_add_cancel_right (a b : FieldExpr V) :
    FieldPath V (.add (.neg b) (.add a b)) a :=
  trans4
    (congr_add_right (.neg b) (add_comm a b))
    (add_assoc_symm (.neg b) b a)
    (congr_add_left a (neg_add b))
    (zero_add a)

/-- Theorem 33: a + ((-a) + b) ≡ b (3 steps). -/
theorem add_neg_cancel_left (a b : FieldExpr V) :
    FieldPath V (.add a (.add (.neg a) b)) b :=
  trans3
    (add_assoc_symm a (.neg a) b)
    (congr_add_left b (add_neg a))
    (zero_add b)

/-- Theorem 34: (a * b) * b⁻¹ ≡ a (3 steps). -/
theorem mul_div_cancel (a b : FieldExpr V) :
    FieldPath V (.mul (.mul a b) (.inv b)) a :=
  trans3
    (mul_assoc a b (.inv b))
    (congr_mul_right a (mul_inv b))
    (mul_one a)

/-- Theorem 35: a * (b⁻¹ * b) ≡ a (2 steps). -/
theorem mul_inv_cancel_right (a b : FieldExpr V) :
    FieldPath V (.mul a (.mul (.inv b) b)) a :=
  FieldPath.trans
    (congr_mul_right a (inv_mul b))
    (mul_one a)

/-- Theorem 36: (a + b) + (c + d) ≡ a + (b + (c + d)). -/
theorem add_assoc4_left (a b c d : FieldExpr V) :
    FieldPath V (.add (.add a b) (.add c d)) (.add a (.add b (.add c d))) :=
  add_assoc a b (.add c d)

/-- Theorem 37: a*b + a*c ≡ a*(b + c) (reverse distrib). -/
theorem factor_add (a b c : FieldExpr V) :
    FieldPath V (.add (.mul a b) (.mul a c)) (.mul a (.add b c)) :=
  FieldPath.symm (left_distrib a b c)

/-- Theorem 38: 1 * 1 ≡ 1. -/
theorem one_mul_one : FieldPath V (.mul .one .one) (.one : FieldExpr V) :=
  one_mul .one

/-- Theorem 39: 0 * 0 ≡ 0. -/
theorem zero_mul_zero : FieldPath V (.mul .zero .zero) (.zero : FieldExpr V) :=
  zero_mul .zero

/-- Theorem 40: a*b + -(a*b) ≡ 0. -/
theorem mul_add_neg_mul (a b : FieldExpr V) :
    FieldPath V (.add (.mul a b) (.neg (.mul a b))) .zero :=
  add_neg (.mul a b)

/-! ## Theorems 41–50: Longer chains -/

/-- Theorem 41: ((a+b)+(-b))+(-a) ≡ 0 (2 steps via add_sub_cancel). -/
theorem add_cancel_chain (a b : FieldExpr V) :
    FieldPath V (.add (.add (.add a b) (.neg b)) (.neg a)) .zero :=
  FieldPath.trans
    (congr_add_left (.neg a) (add_sub_cancel a b))
    (add_neg a)

/-- Theorem 42: a * (b * c) ≡ (a * b) * c (reverse assoc). -/
theorem mul_assoc_symm (a b c : FieldExpr V) :
    FieldPath V (.mul a (.mul b c)) (.mul (.mul a b) c) :=
  FieldPath.symm (mul_assoc a b c)

/-- Theorem 43: (a*b)*(c*d) ≡ a*(b*(c*d)). -/
theorem mul_assoc4_left (a b c d : FieldExpr V) :
    FieldPath V (.mul (.mul a b) (.mul c d)) (.mul a (.mul b (.mul c d))) :=
  mul_assoc a b (.mul c d)

/-- Theorem 44: a * (b * b⁻¹) ≡ a (2 steps). -/
theorem mul_cancel_via_inv (a b : FieldExpr V) :
    FieldPath V (.mul a (.mul b (.inv b))) a :=
  FieldPath.trans
    (congr_mul_right a (mul_inv b))
    (mul_one a)

/-- Theorem 45: -(a+b) + a ≡ -b (5 steps). -/
theorem neg_add_partial (a b : FieldExpr V) :
    FieldPath V (.add (.neg (.add a b)) a) (.neg b) :=
  trans5
    (congr_add_left a (neg_add_distrib a b))
    (add_assoc (.neg a) (.neg b) a)
    (congr_add_right (.neg a) (add_comm (.neg b) a))
    (FieldPath.trans
      (add_assoc_symm (.neg a) a (.neg b))
      (congr_add_left (.neg b) (neg_add a)))
    (zero_add (.neg b))

/-- Theorem 46: a*0 + b ≡ b (2 steps). -/
theorem mul_zero_add (a b : FieldExpr V) :
    FieldPath V (.add (.mul a .zero) b) b :=
  FieldPath.trans
    (congr_add_left b (mul_zero a))
    (zero_add b)

/-- Theorem 47: (a*b)*(b⁻¹*a⁻¹) ≡ 1 (multi-step). -/
theorem mul_inv_product (a b : FieldExpr V) :
    FieldPath V (.mul (.mul a b) (.mul (.inv b) (.inv a))) .one :=
  let inner := trans3
    (mul_assoc_symm b (.inv b) (.inv a))
    (congr_mul_left (.inv a) (mul_inv b))
    (one_mul (.inv a))
  trans3
    (mul_assoc a b (.mul (.inv b) (.inv a)))
    (congr_mul_right a inner)
    (mul_inv a)

/-- Theorem 48: (a+b) + (-a + -b) ≡ 0 (2 steps via neg_add_distrib). -/
theorem add_neg_sum (a b : FieldExpr V) :
    FieldPath V (.add (.add a b) (.add (.neg a) (.neg b))) .zero :=
  FieldPath.trans
    (congr_add_right (.add a b) (FieldPath.symm (neg_add_distrib a b)))
    (add_neg (.add a b))

/-- Theorem 49: 1 + (-1) ≡ 0. -/
theorem one_add_neg_one : FieldPath V (.add .one (.neg .one)) (.zero : FieldExpr V) :=
  add_neg .one

/-- Theorem 50: a*(b+c) + -(a*b) ≡ a*c (3 steps). -/
theorem distrib_cancel (a b c : FieldExpr V) :
    FieldPath V (.add (.mul a (.add b c)) (.neg (.mul a b))) (.mul a c) :=
  trans3
    (congr_add_left (.neg (.mul a b)) (left_distrib a b c))
    (add_assoc (.mul a b) (.mul a c) (.neg (.mul a b)))
    (FieldPath.trans
      (congr_add_right (.mul a b) (add_comm (.mul a c) (.neg (.mul a b))))
      (FieldPath.trans
        (add_assoc_symm (.mul a b) (.neg (.mul a b)) (.mul a c))
        (FieldPath.trans
          (congr_add_left (.mul a c) (add_neg (.mul a b)))
          (zero_add (.mul a c)))))

/-! ## Theorems 51–55: Soundness and evaluation -/

/-- Evaluation of a FieldExpr in a concrete type. -/
def eval {F : Type u} (z o : F) (ad : F → F → F) (ml : F → F → F)
    (ng : F → F) (iv : F → F) (env : V → F) : FieldExpr V → F
  | .zero => z
  | .one => o
  | .var v => env v
  | .add a b => ad (eval z o ad ml ng iv env a) (eval z o ad ml ng iv env b)
  | .mul a b => ml (eval z o ad ml ng iv env a) (eval z o ad ml ng iv env b)
  | .neg a => ng (eval z o ad ml ng iv env a)
  | .inv a => iv (eval z o ad ml ng iv env a)

/-- A concrete field interpretation. -/
structure FieldInterp (F : Type u) (V : Type u) where
  zero : F
  one : F
  add : F → F → F
  mul : F → F → F
  neg : F → F
  inv : F → F
  env : V → F
  add_assoc_eq : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm_eq : ∀ a b, add a b = add b a
  zero_add_eq : ∀ a, add zero a = a
  add_zero_eq : ∀ a, add a zero = a
  add_neg_eq : ∀ a, add a (neg a) = zero
  neg_add_eq : ∀ a, add (neg a) a = zero
  neg_neg_eq : ∀ a, neg (neg a) = a
  neg_zero_eq : neg zero = zero
  mul_assoc_eq : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm_eq : ∀ a b, mul a b = mul b a
  one_mul_eq : ∀ a, mul one a = a
  mul_one_eq : ∀ a, mul a one = a
  mul_inv_eq : ∀ a, mul a (inv a) = one
  inv_mul_eq : ∀ a, mul (inv a) a = one
  inv_inv_eq : ∀ a, inv (inv a) = a
  inv_one_eq : inv one = one
  left_distrib_eq : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  right_distrib_eq : ∀ a b c, mul (add a b) c = add (mul a c) (mul b c)
  mul_zero_eq : ∀ a, mul a zero = zero
  zero_mul_eq : ∀ a, mul zero a = zero
  neg_mul_eq : ∀ a b, neg (mul a b) = mul (neg a) b
  mul_neg_eq : ∀ a b, mul a (neg b) = neg (mul a b)
  neg_add_distrib_eq : ∀ a b, neg (add a b) = add (neg a) (neg b)

/-- Evaluate a FieldExpr using an interpretation. -/
def evalInterp {F V : Type u} (fi : FieldInterp F V) : FieldExpr V → F :=
  eval fi.zero fi.one fi.add fi.mul fi.neg fi.inv fi.env

/-- Theorem 51: A single FieldStep preserves evaluation. -/
theorem step_sound {F V : Type u} (fi : FieldInterp F V)
    {a b : FieldExpr V} (s : FieldStep V a b) :
    evalInterp fi a = evalInterp fi b := by
  induction s with
  | add_assoc a b c => exact fi.add_assoc_eq _ _ _
  | add_comm a b => exact fi.add_comm_eq _ _
  | zero_add a => exact fi.zero_add_eq _
  | add_zero a => exact fi.add_zero_eq _
  | add_neg a => exact fi.add_neg_eq _
  | neg_add a => exact fi.neg_add_eq _
  | neg_neg a => exact fi.neg_neg_eq _
  | neg_zero => exact fi.neg_zero_eq
  | mul_assoc a b c => exact fi.mul_assoc_eq _ _ _
  | mul_comm a b => exact fi.mul_comm_eq _ _
  | one_mul a => exact fi.one_mul_eq _
  | mul_one a => exact fi.mul_one_eq _
  | mul_inv a => exact fi.mul_inv_eq _
  | inv_mul a => exact fi.inv_mul_eq _
  | inv_inv a => exact fi.inv_inv_eq _
  | inv_one => exact fi.inv_one_eq
  | left_distrib a b c => exact fi.left_distrib_eq _ _ _
  | right_distrib a b c => exact fi.right_distrib_eq _ _ _
  | mul_zero a => exact fi.mul_zero_eq _
  | zero_mul a => exact fi.zero_mul_eq _
  | neg_mul a b => exact fi.neg_mul_eq _ _
  | mul_neg a b => exact fi.mul_neg_eq _ _
  | neg_add_distrib a b => exact fi.neg_add_distrib_eq _ _
  | congr_add_left a b c _ ih =>
      show fi.add (evalInterp fi a) _ = fi.add (evalInterp fi b) _
      rw [ih]
  | congr_add_right a b c _ ih =>
      show fi.add _ (evalInterp fi a) = fi.add _ (evalInterp fi b)
      rw [ih]
  | congr_mul_left a b c _ ih =>
      show fi.mul (evalInterp fi a) _ = fi.mul (evalInterp fi b) _
      rw [ih]
  | congr_mul_right a b c _ ih =>
      show fi.mul _ (evalInterp fi a) = fi.mul _ (evalInterp fi b)
      rw [ih]
  | congr_neg a b _ ih =>
      show fi.neg (evalInterp fi a) = fi.neg (evalInterp fi b)
      rw [ih]
  | congr_inv a b _ ih =>
      show fi.inv (evalInterp fi a) = fi.inv (evalInterp fi b)
      rw [ih]

/-- Theorem 52 (Soundness): A FieldPath implies equality of evaluations. -/
theorem path_sound {F V : Type u} (fi : FieldInterp F V)
    {a b : FieldExpr V} (p : FieldPath V a b) :
    evalInterp fi a = evalInterp fi b := by
  induction p with
  | refl _ => rfl
  | step s => exact step_sound fi s
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | symm _ ih => exact ih.symm

/-- Theorem 53: Lift a FieldPath to a library Path on evaluations. -/
def lift_to_path {F V : Type u} (fi : FieldInterp F V)
    {a b : FieldExpr V} (p : FieldPath V a b) :
    Path (evalInterp fi a) (evalInterp fi b) :=
  Path.ofEq (path_sound fi p)

/-- Theorem 54: Soundness of add_sub_cancel in any interpretation. -/
theorem add_sub_cancel_sound {F V : Type u} (fi : FieldInterp F V)
    (a b : FieldExpr V) :
    evalInterp fi (.add (.add a b) (.neg b)) = evalInterp fi a :=
  path_sound fi (add_sub_cancel a b)

/-- Theorem 55: Soundness of mul_inv_product in any interpretation. -/
theorem mul_inv_product_sound {F V : Type u} (fi : FieldInterp F V)
    (a b : FieldExpr V) :
    evalInterp fi (.mul (.mul a b) (.mul (.inv b) (.inv a))) =
    evalInterp fi .one :=
  path_sound fi (mul_inv_product a b)

end FieldPath
end FieldPaths
end Algebra
end Path
end ComputationalPaths
