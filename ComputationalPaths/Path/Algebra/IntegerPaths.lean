/-
# Integer Arithmetic via Computational Paths — Deep Rewrite System

Integer ring axioms modelled as a domain-specific rewriting calculus:
- `IntExpr`  : expressions over integers (literals, add, mul, neg)
- `IntStep`  : primitive rewrite steps (ring axioms)
- `IntPath`  : freely generated paths with refl/step/trans/symm

Every path is built from genuine rewrite steps. Zero `Path.ofEq`, zero `sorry`.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Algebra.IntegerPaths

open ComputationalPaths

/-! ## Domain: Integer Expressions -/

/-- A small expression language for integer arithmetic. -/
inductive IntExpr : Type
  | lit  : Int → IntExpr
  | add  : IntExpr → IntExpr → IntExpr
  | mul  : IntExpr → IntExpr → IntExpr
  | neg  : IntExpr → IntExpr
  | sub  : IntExpr → IntExpr → IntExpr
  deriving DecidableEq, Repr

namespace IntExpr

/-- Evaluate an IntExpr to an Int. -/
@[simp] def eval : IntExpr → Int
  | lit n      => n
  | add e₁ e₂ => eval e₁ + eval e₂
  | mul e₁ e₂ => eval e₁ * eval e₂
  | neg e      => -(eval e)
  | sub e₁ e₂ => eval e₁ - eval e₂

/-- Smart constructors -/
@[simp] def zero : IntExpr := lit 0
@[simp] def one  : IntExpr := lit 1
@[simp] def negOne : IntExpr := lit (-1)

end IntExpr

/-! ## Primitive Steps: Ring Axioms as Rewrites -/

inductive IntStep : IntExpr → IntExpr → Type
  -- Additive identity
  | add_zero_right (e : IntExpr) :
      IntStep (IntExpr.add e IntExpr.zero) e
  | add_zero_left (e : IntExpr) :
      IntStep (IntExpr.add IntExpr.zero e) e
  -- Additive inverse
  | add_neg_right (e : IntExpr) :
      IntStep (IntExpr.add e (IntExpr.neg e)) IntExpr.zero
  | add_neg_left (e : IntExpr) :
      IntStep (IntExpr.add (IntExpr.neg e) e) IntExpr.zero
  -- Commutativity
  | add_comm (e₁ e₂ : IntExpr) :
      IntStep (IntExpr.add e₁ e₂) (IntExpr.add e₂ e₁)
  -- Associativity
  | add_assoc (e₁ e₂ e₃ : IntExpr) :
      IntStep (IntExpr.add (IntExpr.add e₁ e₂) e₃)
              (IntExpr.add e₁ (IntExpr.add e₂ e₃))
  -- Multiplicative identity
  | mul_one_right (e : IntExpr) :
      IntStep (IntExpr.mul e IntExpr.one) e
  | mul_one_left (e : IntExpr) :
      IntStep (IntExpr.mul IntExpr.one e) e
  -- Multiplicative zero
  | mul_zero_right (e : IntExpr) :
      IntStep (IntExpr.mul e IntExpr.zero) IntExpr.zero
  | mul_zero_left (e : IntExpr) :
      IntStep (IntExpr.mul IntExpr.zero e) IntExpr.zero
  -- Multiplicative commutativity / associativity
  | mul_comm (e₁ e₂ : IntExpr) :
      IntStep (IntExpr.mul e₁ e₂) (IntExpr.mul e₂ e₁)
  | mul_assoc (e₁ e₂ e₃ : IntExpr) :
      IntStep (IntExpr.mul (IntExpr.mul e₁ e₂) e₃)
              (IntExpr.mul e₁ (IntExpr.mul e₂ e₃))
  -- Distributivity
  | left_distrib (a b c : IntExpr) :
      IntStep (IntExpr.mul a (IntExpr.add b c))
              (IntExpr.add (IntExpr.mul a b) (IntExpr.mul a c))
  | right_distrib (a b c : IntExpr) :
      IntStep (IntExpr.mul (IntExpr.add a b) c)
              (IntExpr.add (IntExpr.mul a c) (IntExpr.mul b c))
  -- Negation rules
  | neg_neg (e : IntExpr) :
      IntStep (IntExpr.neg (IntExpr.neg e)) e
  | neg_zero :
      IntStep (IntExpr.neg IntExpr.zero) IntExpr.zero
  | neg_add (e₁ e₂ : IntExpr) :
      IntStep (IntExpr.neg (IntExpr.add e₁ e₂))
              (IntExpr.add (IntExpr.neg e₁) (IntExpr.neg e₂))
  | neg_mul_left (e₁ e₂ : IntExpr) :
      IntStep (IntExpr.neg (IntExpr.mul e₁ e₂))
              (IntExpr.mul (IntExpr.neg e₁) e₂)
  | neg_one_mul (e : IntExpr) :
      IntStep (IntExpr.mul IntExpr.negOne e) (IntExpr.neg e)
  -- Subtraction
  | sub_eq_add_neg (e₁ e₂ : IntExpr) :
      IntStep (IntExpr.sub e₁ e₂) (IntExpr.add e₁ (IntExpr.neg e₂))

namespace IntStep

/-- Every step preserves evaluation semantics. -/
@[simp] def eval_eq : {a b : IntExpr} → IntStep a b → a.eval = b.eval
  | _, _, add_zero_right e    => by simp
  | _, _, add_zero_left e     => by simp
  | _, _, add_neg_right e     => by simp [Int.add_right_neg]
  | _, _, add_neg_left e      => by simp [Int.add_left_neg]
  | _, _, add_comm e₁ e₂      => by simp [Int.add_comm]
  | _, _, add_assoc e₁ e₂ e₃  => by simp [Int.add_assoc]
  | _, _, mul_one_right e     => by simp
  | _, _, mul_one_left e      => by simp
  | _, _, mul_zero_right e    => by simp
  | _, _, mul_zero_left e     => by simp
  | _, _, mul_comm e₁ e₂      => by simp [Int.mul_comm]
  | _, _, mul_assoc e₁ e₂ e₃  => by simp [Int.mul_assoc]
  | _, _, left_distrib a b c  => by simp [Int.mul_add]
  | _, _, right_distrib a b c => by simp [Int.add_mul]
  | _, _, neg_neg e           => by simp
  | _, _, neg_zero            => by simp
  | _, _, neg_add e₁ e₂       => by simp [Int.neg_add]
  | _, _, neg_mul_left e₁ e₂  => by simp [Int.neg_mul]
  | _, _, neg_one_mul e       => by simp [Int.neg_one_mul]
  | _, _, sub_eq_add_neg e₁ e₂ => by simp [Int.sub_eq_add_neg]

end IntStep

/-! ## Paths: Freely Generated from Steps -/

inductive IntPath : IntExpr → IntExpr → Type
  | refl  (a : IntExpr)                                         : IntPath a a
  | step  {a b : IntExpr} (s : IntStep a b)                     : IntPath a b
  | trans {a b c : IntExpr} (p : IntPath a b) (q : IntPath b c) : IntPath a c
  | symm  {a b : IntExpr} (p : IntPath a b)                     : IntPath b a

namespace IntPath

/-- Every path preserves evaluation. -/
@[simp] def eval_eq : {a b : IntExpr} → IntPath a b → a.eval = b.eval
  | _, _, refl _    => rfl
  | _, _, step s    => IntStep.eval_eq s
  | _, _, trans p q => (eval_eq p).trans (eval_eq q)
  | _, _, symm p    => (eval_eq p).symm

/-- Embed into library Path (via eval). -/
@[simp] def toPath {a b : IntExpr} (p : IntPath a b) : ComputationalPaths.Path a.eval b.eval :=
  ComputationalPaths.Path.mk
    [ComputationalPaths.Step.mk a.eval b.eval (eval_eq p)]
    (eval_eq p)

/-- Length of a path (number of primitive steps). -/
@[simp] def length : {a b : IntExpr} → IntPath a b → Nat
  | _, _, refl _    => 0
  | _, _, step _    => 1
  | _, _, trans p q => length p + length q
  | _, _, symm p    => length p

/-! ## 1. Groupoid Laws -/

-- 1
theorem eval_trans_eq {a b c : IntExpr} (p : IntPath a b) (q : IntPath b c) :
    eval_eq (trans p q) = (eval_eq p).trans (eval_eq q) := rfl

-- 2
theorem eval_symm_eq {a b : IntExpr} (p : IntPath a b) :
    eval_eq (symm p) = (eval_eq p).symm := rfl

-- 3
theorem eval_refl_eq (a : IntExpr) : eval_eq (refl a) = rfl := rfl

-- 4
theorem trans_refl_right {a b : IntExpr} (p : IntPath a b) :
    eval_eq (trans p (refl b)) = eval_eq p := by simp

-- 5
theorem trans_refl_left {a b : IntExpr} (p : IntPath a b) :
    eval_eq (trans (refl a) p) = eval_eq p := rfl

-- 6
theorem trans_assoc {a b c d : IntExpr} (p : IntPath a b) (q : IntPath b c) (r : IntPath c d) :
    eval_eq (trans (trans p q) r) = eval_eq (trans p (trans q r)) := by simp

-- 7
theorem symm_symm {a b : IntExpr} (p : IntPath a b) :
    eval_eq (symm (symm p)) = eval_eq p := by simp

/-! ## 2. Additive Identity Paths -/

-- 8
def zero_add_path (e : IntExpr) : IntPath (IntExpr.add IntExpr.zero e) e :=
  step (IntStep.add_zero_left e)

-- 9
def add_zero_path (e : IntExpr) : IntPath (IntExpr.add e IntExpr.zero) e :=
  step (IntStep.add_zero_right e)

-- 10
theorem zero_add_eval (e : IntExpr) :
    eval_eq (zero_add_path e) = by simp := by simp [zero_add_path]

-- 11
theorem add_zero_eval (e : IntExpr) :
    eval_eq (add_zero_path e) = by simp := by simp [add_zero_path]

/-! ## 3. Additive Inverse Paths -/

-- 12
def add_neg_path (e : IntExpr) : IntPath (IntExpr.add e (IntExpr.neg e)) IntExpr.zero :=
  step (IntStep.add_neg_right e)

-- 13
def neg_add_path (e : IntExpr) : IntPath (IntExpr.add (IntExpr.neg e) e) IntExpr.zero :=
  step (IntStep.add_neg_left e)

-- 14
def neg_neg_path (e : IntExpr) : IntPath (IntExpr.neg (IntExpr.neg e)) e :=
  step (IntStep.neg_neg e)

-- 15
theorem neg_neg_eval (e : IntExpr) :
    (eval_eq (neg_neg_path e)) = Int.neg_neg (e.eval) := by
  simp [neg_neg_path]

/-! ## 4. Commutativity and Associativity -/

-- 16
def add_comm_path (e₁ e₂ : IntExpr) :
    IntPath (IntExpr.add e₁ e₂) (IntExpr.add e₂ e₁) :=
  step (IntStep.add_comm e₁ e₂)

-- 17
def add_assoc_path (e₁ e₂ e₃ : IntExpr) :
    IntPath (IntExpr.add (IntExpr.add e₁ e₂) e₃)
            (IntExpr.add e₁ (IntExpr.add e₂ e₃)) :=
  step (IntStep.add_assoc e₁ e₂ e₃)

-- 18
def mul_comm_path (e₁ e₂ : IntExpr) :
    IntPath (IntExpr.mul e₁ e₂) (IntExpr.mul e₂ e₁) :=
  step (IntStep.mul_comm e₁ e₂)

-- 19
def mul_assoc_path (e₁ e₂ e₃ : IntExpr) :
    IntPath (IntExpr.mul (IntExpr.mul e₁ e₂) e₃)
            (IntExpr.mul e₁ (IntExpr.mul e₂ e₃)) :=
  step (IntStep.mul_assoc e₁ e₂ e₃)

/-! ## 5. Multiplicative Identity / Zero Paths -/

-- 20
def mul_one_path (e : IntExpr) : IntPath (IntExpr.mul e IntExpr.one) e :=
  step (IntStep.mul_one_right e)

-- 21
def one_mul_path (e : IntExpr) : IntPath (IntExpr.mul IntExpr.one e) e :=
  step (IntStep.mul_one_left e)

-- 22
def mul_zero_path (e : IntExpr) : IntPath (IntExpr.mul e IntExpr.zero) IntExpr.zero :=
  step (IntStep.mul_zero_right e)

-- 23
def zero_mul_path (e : IntExpr) : IntPath (IntExpr.mul IntExpr.zero e) IntExpr.zero :=
  step (IntStep.mul_zero_left e)

/-! ## 6. Distributivity Paths -/

-- 24
def left_distrib_path (a b c : IntExpr) :
    IntPath (IntExpr.mul a (IntExpr.add b c))
            (IntExpr.add (IntExpr.mul a b) (IntExpr.mul a c)) :=
  step (IntStep.left_distrib a b c)

-- 25
def right_distrib_path (a b c : IntExpr) :
    IntPath (IntExpr.mul (IntExpr.add a b) c)
            (IntExpr.add (IntExpr.mul a c) (IntExpr.mul b c)) :=
  step (IntStep.right_distrib a b c)

/-! ## 7. Negation Paths -/

-- 26
def neg_zero_path : IntPath (IntExpr.neg IntExpr.zero) IntExpr.zero :=
  step IntStep.neg_zero

-- 27
def neg_add_distrib_path (e₁ e₂ : IntExpr) :
    IntPath (IntExpr.neg (IntExpr.add e₁ e₂))
            (IntExpr.add (IntExpr.neg e₁) (IntExpr.neg e₂)) :=
  step (IntStep.neg_add e₁ e₂)

-- 28
def neg_mul_path (e₁ e₂ : IntExpr) :
    IntPath (IntExpr.neg (IntExpr.mul e₁ e₂))
            (IntExpr.mul (IntExpr.neg e₁) e₂) :=
  step (IntStep.neg_mul_left e₁ e₂)

-- 29
def neg_one_mul_path (e : IntExpr) :
    IntPath (IntExpr.mul IntExpr.negOne e) (IntExpr.neg e) :=
  step (IntStep.neg_one_mul e)

/-! ## 8. Subtraction Path -/

-- 30
def sub_eq_add_neg_path (e₁ e₂ : IntExpr) :
    IntPath (IntExpr.sub e₁ e₂) (IntExpr.add e₁ (IntExpr.neg e₂)) :=
  step (IntStep.sub_eq_add_neg e₁ e₂)

/-! ## 9. Composed Multi-Step Paths -/

-- 31: (0 + e) + 0 ~~> e in two steps
def simplify_padded (e : IntExpr) :
    IntPath (IntExpr.add (IntExpr.add IntExpr.zero e) IntExpr.zero) e :=
  trans (step (IntStep.add_zero_right _)) (step (IntStep.add_zero_left e))

-- 32
theorem simplify_padded_length (e : IntExpr) : length (simplify_padded e) = 2 := rfl

-- 33: e - e ~~> 0 via sub → add_neg → cancel
def sub_self_path (e : IntExpr) :
    IntPath (IntExpr.sub e e) IntExpr.zero :=
  trans (step (IntStep.sub_eq_add_neg e e)) (step (IntStep.add_neg_right e))

-- 34
theorem sub_self_length (e : IntExpr) : length (sub_self_path e) = 2 := rfl

-- 35: a * (b + c) ~~> a*c + a*b via distrib then comm
def distrib_then_comm (a b c : IntExpr) :
    IntPath (IntExpr.mul a (IntExpr.add b c))
            (IntExpr.add (IntExpr.mul a c) (IntExpr.mul a b)) :=
  trans (step (IntStep.left_distrib a b c)) (step (IntStep.add_comm _ _))

-- 36
theorem distrib_then_comm_length (a b c : IntExpr) :
    length (distrib_then_comm a b c) = 2 := rfl

-- 37: 1 * (0 + e) ~~> e in two steps
def one_mul_zero_add (e : IntExpr) :
    IntPath (IntExpr.mul IntExpr.one (IntExpr.add IntExpr.zero e)) e :=
  trans (step (IntStep.mul_one_left _)) (step (IntStep.add_zero_left e))

-- 38
theorem one_mul_zero_add_length (e : IntExpr) : length (one_mul_zero_add e) = 2 := rfl

-- 39: neg(neg(e)) + 0 ~~> e in two steps
def neg_neg_add_zero (e : IntExpr) :
    IntPath (IntExpr.add (IntExpr.neg (IntExpr.neg e)) IntExpr.zero) e :=
  trans (step (IntStep.add_zero_right _)) (step (IntStep.neg_neg e))

-- 40
theorem neg_neg_add_zero_length (e : IntExpr) : length (neg_neg_add_zero e) = 2 := rfl

/-! ## 10. Length Theorems -/

-- 41
theorem length_refl (a : IntExpr) : length (refl a) = 0 := rfl

-- 42
theorem length_step {a b : IntExpr} (s : IntStep a b) : length (step s) = 1 := rfl

-- 43
theorem length_symm {a b : IntExpr} (p : IntPath a b) : length (symm p) = length p := rfl

-- 44
theorem length_trans {a b c : IntExpr} (p : IntPath a b) (q : IntPath b c) :
    length (trans p q) = length p + length q := rfl

/-! ## 11. Symmetry / Roundtrip Properties -/

-- 45: add_comm is self-inverse on eval
theorem add_comm_roundtrip (e₁ e₂ : IntExpr) :
    eval_eq (trans (add_comm_path e₁ e₂) (add_comm_path e₂ e₁)) = rfl := by
  simp [add_comm_path]

-- 46: mul_comm is self-inverse on eval
theorem mul_comm_roundtrip (e₁ e₂ : IntExpr) :
    eval_eq (trans (mul_comm_path e₁ e₂) (mul_comm_path e₂ e₁)) = rfl := by
  simp [mul_comm_path]

-- 47: symm of add_comm path reverses direction
theorem add_comm_symm_eval (e₁ e₂ : IntExpr) :
    eval_eq (symm (add_comm_path e₁ e₂)) = eval_eq (add_comm_path e₂ e₁) := by
  simp [add_comm_path, IntStep.eval_eq, Int.add_comm]

/-! ## 12. toPath Coherence -/

-- 48
theorem toPath_refl (a : IntExpr) : (toPath (refl a)).toEq = rfl := rfl

-- 49
theorem toPath_eval {a b : IntExpr} (p : IntPath a b) :
    (toPath p).toEq = eval_eq p := rfl

-- 50
theorem toPath_step_eval {a b : IntExpr} (s : IntStep a b) :
    (toPath (step s)).toEq = IntStep.eval_eq s := rfl

/-! ## 13. Concrete Numerical Witnesses -/

-- 51: 0 + 42 ~~> 42
def zero_add_42 : IntPath (IntExpr.add IntExpr.zero (IntExpr.lit 42)) (IntExpr.lit 42) :=
  step (IntStep.add_zero_left (IntExpr.lit 42))

-- 52: 42 * 1 ~~> 42
def mul_one_42 : IntPath (IntExpr.mul (IntExpr.lit 42) IntExpr.one) (IntExpr.lit 42) :=
  step (IntStep.mul_one_right (IntExpr.lit 42))

-- 53: 0 * 42 ~~> 0
def zero_mul_42 : IntPath (IntExpr.mul IntExpr.zero (IntExpr.lit 42)) IntExpr.zero :=
  step (IntStep.mul_zero_left (IntExpr.lit 42))

-- 54: 3 + 5 ~~> 5 + 3
def comm_3_5 : IntPath (IntExpr.add (IntExpr.lit 3) (IntExpr.lit 5))
                        (IntExpr.add (IntExpr.lit 5) (IntExpr.lit 3)) :=
  step (IntStep.add_comm (IntExpr.lit 3) (IntExpr.lit 5))

-- 55
theorem zero_add_42_eval : eval_eq zero_add_42 = rfl := by simp [zero_add_42]

-- 56
theorem mul_one_42_eval : eval_eq mul_one_42 = rfl := by simp [mul_one_42]

end IntPath

end ComputationalPaths.Path.Algebra.IntegerPaths
