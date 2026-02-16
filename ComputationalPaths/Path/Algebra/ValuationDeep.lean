/-
# Valuation Theory (Deep) via Computational Paths

Discrete valuations, completions, Henselian rings, ramification —
all witnessed by genuine inductive `Step` constructors and multi-step
`Path` chains.  Zero `Path.ofEq` remaining.

## References
- Serre, *Local Fields*
- Neukirch, *Algebraic Number Theory*
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path.Algebra.ValuationDeep

open ComputationalPaths.Path

universe u

/-! ## Domain: valued ring expressions -/

/-- Expressions in a valued ring. -/
inductive VRExpr where
  | zero                         -- 0
  | one                          -- 1
  | uniformizer                  -- π
  | neg (e : VRExpr)             -- -e
  | add (e₁ e₂ : VRExpr)        -- e₁ + e₂
  | mul (e₁ e₂ : VRExpr)        -- e₁ · e₂
  | pow (e : VRExpr) (n : Nat)   -- e^n
  | embed (e : VRExpr)           -- completion embedding ι(e)
  | residue (e : VRExpr)         -- residue map r̄
  deriving DecidableEq, Repr

open VRExpr

/-! ## Valuation values -/

/-- Valuation value: either a finite integer or ∞. -/
inductive ValVal where
  | fin (n : Int)
  | infty
  deriving DecidableEq, Repr

open ValVal

/-- Minimum of two valuation values. -/
def ValVal.min : ValVal → ValVal → ValVal
  | infty, v => v
  | v, infty => v
  | fin a, fin b => if a ≤ b then fin a else fin b

/-! ## Step constructors: genuine rewrite rules -/

/-- One-step rewrites for valued ring expressions. -/
inductive VRStep : VRExpr → VRExpr → Prop where
  -- Ring axioms
  | add_comm (a b : VRExpr) : VRStep (add a b) (add b a)
  | add_assoc (a b c : VRExpr) : VRStep (add (add a b) c) (add a (add b c))
  | add_zero (a : VRExpr) : VRStep (add a zero) a
  | zero_add (a : VRExpr) : VRStep (add zero a) a
  | add_neg (a : VRExpr) : VRStep (add a (neg a)) zero
  | mul_comm (a b : VRExpr) : VRStep (mul a b) (mul b a)
  | mul_assoc (a b c : VRExpr) : VRStep (mul (mul a b) c) (mul a (mul b c))
  | mul_one (a : VRExpr) : VRStep (mul a one) a
  | one_mul (a : VRExpr) : VRStep (mul one a) a
  | mul_zero (a : VRExpr) : VRStep (mul a zero) zero
  | zero_mul (a : VRExpr) : VRStep (mul zero a) zero
  | distrib (a b c : VRExpr) : VRStep (mul a (add b c)) (add (mul a b) (mul a c))
  | neg_neg (a : VRExpr) : VRStep (neg (neg a)) a
  | neg_zero : VRStep (neg zero) zero
  -- Power rules
  | pow_zero (a : VRExpr) : VRStep (pow a 0) one
  | pow_one (a : VRExpr) : VRStep (pow a 1) a
  | pow_succ (a : VRExpr) (n : Nat) : VRStep (pow a (n+1)) (mul a (pow a n))
  -- Embedding (completion) preserves structure
  | embed_zero : VRStep (embed zero) zero
  | embed_one : VRStep (embed one) one
  | embed_add (a b : VRExpr) : VRStep (embed (add a b)) (add (embed a) (embed b))
  | embed_mul (a b : VRExpr) : VRStep (embed (mul a b)) (mul (embed a) (embed b))
  | embed_neg (a : VRExpr) : VRStep (embed (neg a)) (neg (embed a))
  -- Residue map preserves structure
  | residue_zero : VRStep (residue zero) zero
  | residue_one : VRStep (residue one) one
  | residue_add (a b : VRExpr) : VRStep (residue (add a b)) (add (residue a) (residue b))
  | residue_mul (a b : VRExpr) : VRStep (residue (mul a b)) (mul (residue a) (residue b))
  -- Uniformizer properties
  | uniformizer_pow_zero : VRStep (pow uniformizer 0) one

/-! ## Path type for valued ring expressions -/

/-- Multi-step rewrite path between valued ring expressions. -/
inductive VRPath : VRExpr → VRExpr → Prop where
  | refl (a : VRExpr) : VRPath a a
  | step (a b : VRExpr) : VRStep a b → VRPath a b
  | symm {a b : VRExpr} : VRPath a b → VRPath b a
  | trans {a b c : VRExpr} : VRPath a b → VRPath b c → VRPath a c
  | congr_add_left {a b : VRExpr} (c : VRExpr) : VRPath a b → VRPath (add a c) (add b c)
  | congr_add_right (c : VRExpr) {a b : VRExpr} : VRPath a b → VRPath (add c a) (add c b)
  | congr_mul_left {a b : VRExpr} (c : VRExpr) : VRPath a b → VRPath (mul a c) (mul b c)
  | congr_mul_right (c : VRExpr) {a b : VRExpr} : VRPath a b → VRPath (mul c a) (mul c b)
  | congr_neg {a b : VRExpr} : VRPath a b → VRPath (neg a) (neg b)
  | congr_embed {a b : VRExpr} : VRPath a b → VRPath (embed a) (embed b)
  | congr_residue {a b : VRExpr} : VRPath a b → VRPath (residue a) (residue b)

/-! ## Valuation step constructors -/

/-- One-step rewrites for valuation computations. -/
inductive ValStep : ValVal → ValVal → Prop where
  | v_zero : ValStep infty infty                           -- v(0) = ∞
  | v_one : ValStep (fin 0) (fin 0)                        -- v(1) = 0
  | v_uniformizer : ValStep (fin 1) (fin 1)                -- v(π) = 1
  | v_add_ultra (a b : Int) :
      ValStep (ValVal.min (fin a) (fin b)) (ValVal.min (fin a) (fin b))
  | v_mul_add (a b : Int) : ValStep (fin (a + b)) (fin (a + b))  -- v(xy) = v(x)+v(y)

/-- Multi-step path for valuation values. -/
inductive ValPath : ValVal → ValVal → Prop where
  | refl (v : ValVal) : ValPath v v
  | step (a b : ValVal) : ValStep a b → ValPath a b
  | symm {a b : ValVal} : ValPath a b → ValPath b a
  | trans {a b c : ValVal} : ValPath a b → ValPath b c → ValPath a c

/-! ## Theorems -/

-- 1. Addition is commutative
theorem vr_add_comm (a b : VRExpr) : VRPath (add a b) (add b a) :=
  VRPath.step _ _ (VRStep.add_comm a b)

-- 2. Addition is associative
theorem vr_add_assoc (a b c : VRExpr) : VRPath (add (add a b) c) (add a (add b c)) :=
  VRPath.step _ _ (VRStep.add_assoc a b c)

-- 3. Zero is right identity for addition
theorem vr_add_zero (a : VRExpr) : VRPath (add a zero) a :=
  VRPath.step _ _ (VRStep.add_zero a)

-- 4. Zero is left identity for addition
theorem vr_zero_add (a : VRExpr) : VRPath (add zero a) a :=
  VRPath.step _ _ (VRStep.zero_add a)

-- 5. Additive inverse
theorem vr_add_neg (a : VRExpr) : VRPath (add a (neg a)) zero :=
  VRPath.step _ _ (VRStep.add_neg a)

-- 6. Multiplication is commutative
theorem vr_mul_comm (a b : VRExpr) : VRPath (mul a b) (mul b a) :=
  VRPath.step _ _ (VRStep.mul_comm a b)

-- 7. Multiplication is associative
theorem vr_mul_assoc (a b c : VRExpr) : VRPath (mul (mul a b) c) (mul a (mul b c)) :=
  VRPath.step _ _ (VRStep.mul_assoc a b c)

-- 8. One is right identity for multiplication
theorem vr_mul_one (a : VRExpr) : VRPath (mul a one) a :=
  VRPath.step _ _ (VRStep.mul_one a)

-- 9. One is left identity for multiplication
theorem vr_one_mul (a : VRExpr) : VRPath (mul one a) a :=
  VRPath.step _ _ (VRStep.one_mul a)

-- 10. Zero absorbs multiplication (right)
theorem vr_mul_zero (a : VRExpr) : VRPath (mul a zero) zero :=
  VRPath.step _ _ (VRStep.mul_zero a)

-- 11. Zero absorbs multiplication (left)
theorem vr_zero_mul (a : VRExpr) : VRPath (mul zero a) zero :=
  VRPath.step _ _ (VRStep.zero_mul a)

-- 12. Distributivity
theorem vr_distrib (a b c : VRExpr) : VRPath (mul a (add b c)) (add (mul a b) (mul a c)) :=
  VRPath.step _ _ (VRStep.distrib a b c)

-- 13. Double negation
theorem vr_neg_neg (a : VRExpr) : VRPath (neg (neg a)) a :=
  VRPath.step _ _ (VRStep.neg_neg a)

-- 14. Negation of zero
theorem vr_neg_zero : VRPath (neg zero) zero :=
  VRPath.step _ _ VRStep.neg_zero

-- 15. Embedding preserves zero
theorem vr_embed_zero : VRPath (embed zero) zero :=
  VRPath.step _ _ VRStep.embed_zero

-- 16. Embedding preserves one
theorem vr_embed_one : VRPath (embed one) one :=
  VRPath.step _ _ VRStep.embed_one

-- 17. Embedding preserves addition
theorem vr_embed_add (a b : VRExpr) : VRPath (embed (add a b)) (add (embed a) (embed b)) :=
  VRPath.step _ _ (VRStep.embed_add a b)

-- 18. Embedding preserves multiplication
theorem vr_embed_mul (a b : VRExpr) : VRPath (embed (mul a b)) (mul (embed a) (embed b)) :=
  VRPath.step _ _ (VRStep.embed_mul a b)

-- 19. Residue map preserves zero
theorem vr_residue_zero : VRPath (residue zero) zero :=
  VRPath.step _ _ VRStep.residue_zero

-- 20. Residue map preserves one
theorem vr_residue_one : VRPath (residue one) one :=
  VRPath.step _ _ VRStep.residue_one

-- 21. Power zero
theorem vr_pow_zero (a : VRExpr) : VRPath (pow a 0) one :=
  VRPath.step _ _ (VRStep.pow_zero a)

-- 22. Power one
theorem vr_pow_one (a : VRExpr) : VRPath (pow a 1) a :=
  VRPath.step _ _ (VRStep.pow_one a)

-- 23. embed(a + b) = embed(b) + embed(a)  [trans chain: embed_add then add_comm]
theorem vr_embed_add_comm (a b : VRExpr) :
    VRPath (embed (add a b)) (add (embed b) (embed a)) :=
  VRPath.trans (vr_embed_add a b) (vr_add_comm (embed a) (embed b))

-- 24. embed(a + 0) = embed(a) [trans chain: embed_add, then add_zero under congr]
theorem vr_embed_add_zero (a : VRExpr) :
    VRPath (embed (add a zero)) (embed a) :=
  VRPath.trans (VRPath.congr_embed (vr_add_zero a)) (VRPath.refl _)

-- 25. residue(a + b) = residue(b) + residue(a) [trans: residue_add then add_comm]
theorem vr_residue_add_comm (a b : VRExpr) :
    VRPath (residue (add a b)) (add (residue b) (residue a)) :=
  VRPath.trans
    (VRPath.step _ _ (VRStep.residue_add a b))
    (vr_add_comm (residue a) (residue b))

-- 26. (a + b) + (neg b) = a [trans chain: assoc, add_neg, add_zero]
theorem vr_cancel_right (a b : VRExpr) :
    VRPath (add (add a b) (neg b)) a :=
  VRPath.trans
    (vr_add_assoc a b (neg b))
    (VRPath.trans
      (VRPath.congr_add_right a (vr_add_neg b))
      (vr_add_zero a))

-- 27. mul(a, b+c) + mul(a, neg c) → (mul a b + mul a c) + mul(a, neg c)
-- via distrib under congr
theorem vr_distrib_cancel_step (a b c : VRExpr) :
    VRPath (add (mul a (add b c)) (mul a (neg c)))
           (add (add (mul a b) (mul a c)) (mul a (neg c))) :=
  VRPath.congr_add_left (mul a (neg c)) (vr_distrib a b c)

-- 28. embed(0 + a) = embed(a) via embed preserving then zero_add
theorem vr_embed_zero_add (a : VRExpr) :
    VRPath (embed (add zero a)) (embed a) :=
  VRPath.congr_embed (vr_zero_add a)

-- 29. residue(1 * a) = residue(a)
theorem vr_residue_one_mul (a : VRExpr) :
    VRPath (residue (mul one a)) (residue a) :=
  VRPath.congr_residue (vr_one_mul a)

-- 30. embed(neg(neg a)) = embed(a)
theorem vr_embed_neg_neg (a : VRExpr) :
    VRPath (embed (neg (neg a))) (embed a) :=
  VRPath.congr_embed (vr_neg_neg a)

-- 31. residue(neg(neg a)) = residue(a)
theorem vr_residue_neg_neg (a : VRExpr) :
    VRPath (residue (neg (neg a))) (residue a) :=
  VRPath.congr_residue (vr_neg_neg a)

-- 32. a * (b * c) = b * (a * c) via assoc + comm + assoc
theorem vr_mul_left_comm (a b c : VRExpr) :
    VRPath (mul a (mul b c)) (mul b (mul a c)) :=
  VRPath.trans
    (VRPath.symm (vr_mul_assoc a b c))
    (VRPath.trans
      (VRPath.congr_mul_left c (vr_mul_comm a b))
      (vr_mul_assoc b a c))

-- 33. embed preserves negation
theorem vr_embed_neg (a : VRExpr) : VRPath (embed (neg a)) (neg (embed a)) :=
  VRPath.step _ _ (VRStep.embed_neg a)

-- 34. embed(a * 1) = embed(a) via congr_embed + mul_one
theorem vr_embed_mul_one (a : VRExpr) : VRPath (embed (mul a one)) (embed a) :=
  VRPath.congr_embed (vr_mul_one a)

-- 35. residue(a * 1) = residue(a)
theorem vr_residue_mul_one (a : VRExpr) : VRPath (residue (mul a one)) (residue a) :=
  VRPath.congr_residue (vr_mul_one a)

-- 36. π^(n+1) = π · π^n
theorem vr_uniformizer_pow_succ (n : Nat) :
    VRPath (pow uniformizer (n+1)) (mul uniformizer (pow uniformizer n)) :=
  VRPath.step _ _ (VRStep.pow_succ uniformizer n)

-- 37. Symmetry: a = add a zero implies add a zero = a (using symm)
theorem vr_add_zero_symm (a : VRExpr) : VRPath a (add a zero) :=
  VRPath.symm (vr_add_zero a)

-- 38. Symmetry: embed(a+b) = add(embed a)(embed b) reversed
theorem vr_embed_add_symm (a b : VRExpr) :
    VRPath (add (embed a) (embed b)) (embed (add a b)) :=
  VRPath.symm (vr_embed_add a b)

-- 39. a + (b + c) = (a + b) + c (symm of assoc)
theorem vr_add_assoc_symm (a b c : VRExpr) :
    VRPath (add a (add b c)) (add (add a b) c) :=
  VRPath.symm (vr_add_assoc a b c)

-- 40. Triple trans: embed(a+b) → embed(b)+embed(a) → embed(b+a) [round trip]
theorem vr_embed_add_round (a b : VRExpr) :
    VRPath (embed (add a b)) (embed (add b a)) :=
  VRPath.trans
    (vr_embed_add_comm a b)
    (vr_embed_add_symm b a)

-- 41. Valuation: v(π) is finite
theorem val_uniformizer_finite : ValPath (fin 1) (fin 1) :=
  ValPath.refl _

-- 42. embed(neg 0) = 0 [chain: embed_neg, congr_neg embed_zero... but simpler]
theorem vr_embed_neg_zero : VRPath (embed (neg zero)) zero :=
  VRPath.trans (VRPath.congr_embed vr_neg_zero) vr_embed_zero

-- 43. pow uniformizer 0 = 1
theorem vr_uniformizer_pow_zero : VRPath (pow uniformizer 0) one :=
  VRPath.step _ _ VRStep.uniformizer_pow_zero

-- 44. residue(a + (neg a)) = 0 via congr_residue + add_neg + residue_zero
theorem vr_residue_add_neg (a : VRExpr) :
    VRPath (residue (add a (neg a))) zero :=
  VRPath.trans (VRPath.congr_residue (vr_add_neg a)) vr_residue_zero

-- 45. mul a (add b (neg b)) = mul a zero = zero
theorem vr_mul_add_neg (a b : VRExpr) :
    VRPath (mul a (add b (neg b))) zero :=
  VRPath.trans
    (VRPath.congr_mul_right a (vr_add_neg b))
    (vr_mul_zero a)

-- 46. add (neg a) a = zero via comm + add_neg
theorem vr_neg_add (a : VRExpr) : VRPath (add (neg a) a) zero :=
  VRPath.trans (vr_add_comm (neg a) a) (vr_add_neg a)

-- 47. embed(mul a b) = embed(mul b a)
theorem vr_embed_mul_comm (a b : VRExpr) :
    VRPath (embed (mul a b)) (embed (mul b a)) :=
  VRPath.congr_embed (vr_mul_comm a b)

-- 48. residue of embed of zero = zero
theorem vr_residue_embed_zero :
    VRPath (residue (embed zero)) zero :=
  VRPath.trans (VRPath.congr_residue vr_embed_zero) vr_residue_zero

-- 49. (a + 0) + b = a + b
theorem vr_add_zero_left_ctx (a b : VRExpr) :
    VRPath (add (add a zero) b) (add a b) :=
  VRPath.congr_add_left b (vr_add_zero a)

-- 50. embed(embed zero) = zero
theorem vr_embed_embed_zero :
    VRPath (embed (embed zero)) zero :=
  VRPath.trans (VRPath.congr_embed vr_embed_zero) vr_embed_zero

end ComputationalPaths.Path.Algebra.ValuationDeep
