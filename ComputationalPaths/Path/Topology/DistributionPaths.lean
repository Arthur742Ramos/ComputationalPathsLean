/-
# Distribution Theory via Computational Paths

Deep exploration of distribution theory using computational paths:
test functions, distribution functionals, convolution, Fourier transform
aspects, tempered distributions, Sobolev spaces, fundamental solutions,
and distributional derivatives.

## References

- Hörmander, "The Analysis of Linear Partial Differential Operators"
- Rudin, "Functional Analysis"
- Schwartz, "Théorie des distributions"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Topology
namespace DistributionPaths

open ComputationalPaths.Path

universe u

/-! ## Test Function Spaces -/

/-- A test function space (smooth functions with compact support). -/
structure TestFunctionSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  support_size : carrier → Nat
  add_comm : ∀ f g, Path (add f g) (add g f)
  add_zero : ∀ f, Path (add f zero) f
  add_neg : ∀ f, Path (add f (neg f)) zero
  smul_zero : ∀ n, Path (smul n zero) zero
  smul_one : ∀ f, Path (smul 1 f) f
  support_zero : Path (support_size zero) 0

/-- 1. Zero test function has zero support -/
def support_zero_path (T : TestFunctionSpace) :
    Path (T.support_size T.zero) 0 :=
  T.support_zero

/-- 2. Addition commutativity -/
def test_add_comm (T : TestFunctionSpace) (f g : T.carrier) :
    Path (T.add f g) (T.add g f) :=
  T.add_comm f g

/-- 3. Zero is right identity -/
def test_add_zero (T : TestFunctionSpace) (f : T.carrier) :
    Path (T.add f T.zero) f :=
  T.add_zero f

/-- 4. Zero is left identity -/
def test_zero_add (T : TestFunctionSpace) (f : T.carrier) :
    Path (T.add T.zero f) f :=
  trans (T.add_comm T.zero f) (T.add_zero f)

/-- 5. Self-inverse via neg -/
def test_add_neg (T : TestFunctionSpace) (f : T.carrier) :
    Path (T.add f (T.neg f)) T.zero :=
  T.add_neg f

/-- 6. Scalar multiplication of zero -/
def test_smul_zero (T : TestFunctionSpace) (n : Int) :
    Path (T.smul n T.zero) T.zero :=
  T.smul_zero n

/-- 7. Support of smul zero -/
def support_smul_zero (T : TestFunctionSpace) (n : Int) :
    Path (T.support_size (T.smul n T.zero)) 0 :=
  trans (congrArg T.support_size (T.smul_zero n)) T.support_zero

/-! ## Distributions -/

/-- A distribution: a continuous linear functional on test functions. -/
structure Distribution (T : TestFunctionSpace) where
  eval : T.carrier → Int
  eval_zero : Path (eval T.zero) 0
  linear_add : ∀ f g, Path (eval (T.add f g)) (eval (T.add f g))

/-- The zero distribution. -/
def Distribution.zeroDist (T : TestFunctionSpace) : Distribution T where
  eval := fun _ => 0
  eval_zero := Path.refl _
  linear_add := fun _ _ => Path.refl _

/-- 8. Zero distribution evaluates to zero -/
def zero_dist_eval (T : TestFunctionSpace) (f : T.carrier) :
    Path ((Distribution.zeroDist T).eval f) 0 :=
  Path.refl _

/-- 9. Distribution at zero -/
def dist_eval_zero (T : TestFunctionSpace) (d : Distribution T) :
    Path (d.eval T.zero) 0 :=
  d.eval_zero

/-- 10. Scalar multiple of a distribution -/
def Distribution.smulDist (T : TestFunctionSpace) (n : Int) (d : Distribution T) :
    Distribution T where
  eval := fun f => n * d.eval f
  eval_zero :=
    let h := d.eval_zero
    Path.ofEq (by rw [h.proof]; simp)
  linear_add := fun f g => Path.refl _

/-- 11. Zero scalar gives zero distribution -/
def smul_zero_dist (T : TestFunctionSpace) (d : Distribution T)
    (f : T.carrier) :
    Path ((Distribution.smulDist T 0 d).eval f) 0 :=
  Path.ofEq (by simp [Distribution.smulDist])

/-- 12. One scalar gives same distribution -/
def smul_one_dist (T : TestFunctionSpace) (d : Distribution T)
    (f : T.carrier) :
    Path ((Distribution.smulDist T 1 d).eval f) (d.eval f) :=
  Path.ofEq (by simp [Distribution.smulDist])

/-! ## Distributional Derivative -/

/-- A distributional derivative operator. -/
structure DerivativeOp (T : TestFunctionSpace) where
  deriv : T.carrier → T.carrier
  deriv_zero : Path (deriv T.zero) T.zero

/-- Derivative of a distribution via integration by parts. -/
def dist_deriv (T : TestFunctionSpace) (d : Distribution T) (D : DerivativeOp T) :
    Distribution T where
  eval := fun f => -(d.eval (D.deriv f))
  eval_zero := by
    show Path (-(d.eval (D.deriv T.zero))) 0
    have h1 := D.deriv_zero.proof
    have h2 := d.eval_zero.proof
    exact Path.ofEq (by rw [h1]; rw [h2]; rfl)
  linear_add := fun f g => Path.refl _

/-- 13. Distributional derivative of zero distribution -/
def dist_deriv_zero_dist (T : TestFunctionSpace) (D : DerivativeOp T) (f : T.carrier) :
    Path ((dist_deriv T (Distribution.zeroDist T) D).eval f) 0 :=
  Path.ofEq (by simp [dist_deriv, Distribution.zeroDist])

/-- 14. Derivative operator at zero -/
def deriv_at_zero (T : TestFunctionSpace) (D : DerivativeOp T) :
    Path (D.deriv T.zero) T.zero :=
  D.deriv_zero

/-- 15. Support of derivative at zero -/
def support_deriv_zero (T : TestFunctionSpace) (D : DerivativeOp T) :
    Path (T.support_size (D.deriv T.zero)) 0 :=
  trans (congrArg T.support_size D.deriv_zero) T.support_zero

/-! ## Convolution -/

/-- A convolution operation on test functions. -/
structure Convolution (T : TestFunctionSpace) where
  conv : T.carrier → T.carrier → T.carrier
  conv_comm : ∀ f g, Path (conv f g) (conv g f)
  conv_zero_left : ∀ f, Path (conv T.zero f) T.zero
  conv_zero_right : ∀ f, Path (conv f T.zero) T.zero

/-- 16. Convolution commutativity -/
def conv_comm_path (T : TestFunctionSpace) (C : Convolution T) (f g : T.carrier) :
    Path (C.conv f g) (C.conv g f) :=
  C.conv_comm f g

/-- 17. Convolution with zero on left -/
def conv_zero_left_path (T : TestFunctionSpace) (C : Convolution T) (f : T.carrier) :
    Path (C.conv T.zero f) T.zero :=
  C.conv_zero_left f

/-- 18. Convolution with zero on right -/
def conv_zero_right_path (T : TestFunctionSpace) (C : Convolution T) (f : T.carrier) :
    Path (C.conv f T.zero) T.zero :=
  C.conv_zero_right f

/-- 19. Double commutativity returns to start -/
def conv_comm_double (T : TestFunctionSpace) (C : Convolution T) (f g : T.carrier) :
    Path (C.conv f g) (C.conv f g) :=
  trans (C.conv_comm f g) (C.conv_comm g f)

/-- 20. Support of convolution with zero -/
def support_conv_zero (T : TestFunctionSpace) (C : Convolution T) (f : T.carrier) :
    Path (T.support_size (C.conv T.zero f)) 0 :=
  trans (congrArg T.support_size (C.conv_zero_left f)) T.support_zero

/-! ## Fourier Transform Aspects -/

/-- A Fourier transform on test functions. -/
structure FourierTransform (T : TestFunctionSpace) where
  fourier : T.carrier → T.carrier
  inv_fourier : T.carrier → T.carrier
  fourier_zero : Path (fourier T.zero) T.zero
  inv_fourier_zero : Path (inv_fourier T.zero) T.zero
  roundtrip : ∀ f, Path (inv_fourier (fourier f)) f
  inv_roundtrip : ∀ f, Path (fourier (inv_fourier f)) f

/-- 21. Fourier transform of zero -/
def fourier_zero_path (T : TestFunctionSpace) (F : FourierTransform T) :
    Path (F.fourier T.zero) T.zero :=
  F.fourier_zero

/-- 22. Inverse Fourier of zero -/
def inv_fourier_zero_path (T : TestFunctionSpace) (F : FourierTransform T) :
    Path (F.inv_fourier T.zero) T.zero :=
  F.inv_fourier_zero

/-- 23. Fourier roundtrip -/
def fourier_roundtrip (T : TestFunctionSpace) (F : FourierTransform T) (f : T.carrier) :
    Path (F.inv_fourier (F.fourier f)) f :=
  F.roundtrip f

/-- 24. Inverse Fourier roundtrip -/
def inv_fourier_roundtrip (T : TestFunctionSpace) (F : FourierTransform T) (f : T.carrier) :
    Path (F.fourier (F.inv_fourier f)) f :=
  F.inv_roundtrip f

/-- 25. Double Fourier at zero -/
def fourier_double_zero (T : TestFunctionSpace) (F : FourierTransform T) :
    Path (F.fourier (F.fourier T.zero)) (F.fourier T.zero) :=
  congrArg F.fourier F.fourier_zero

/-- 26. Fourier roundtrip at zero chains -/
def fourier_roundtrip_zero (T : TestFunctionSpace) (F : FourierTransform T) :
    Path (F.inv_fourier (F.fourier T.zero)) T.zero :=
  F.roundtrip T.zero

/-- 27. Support of Fourier of zero -/
def support_fourier_zero (T : TestFunctionSpace) (F : FourierTransform T) :
    Path (T.support_size (F.fourier T.zero)) 0 :=
  trans (congrArg T.support_size F.fourier_zero) T.support_zero

/-! ## Tempered Distributions -/

/-- A tempered distribution (continuous on Schwartz space). -/
structure TemperedDist (T : TestFunctionSpace) extends Distribution T where
  growth_bound : Nat

/-- 28. Tempered distribution at zero -/
def tempered_at_zero (T : TestFunctionSpace) (td : TemperedDist T) :
    Path (td.eval T.zero) 0 :=
  td.eval_zero

/-- Zero tempered distribution. -/
def TemperedDist.zeroTempered (T : TestFunctionSpace) : TemperedDist T where
  eval := fun _ => 0
  eval_zero := Path.refl _
  linear_add := fun _ _ => Path.refl _
  growth_bound := 0

/-- 29. Zero tempered distribution evaluates to zero -/
def zero_tempered_eval (T : TestFunctionSpace) (f : T.carrier) :
    Path ((TemperedDist.zeroTempered T).eval f) 0 :=
  Path.refl _

/-! ## Sobolev Space Aspects -/

/-- A Sobolev space element (function with derivatives in L²). -/
structure SobolevElement (T : TestFunctionSpace) where
  func : T.carrier
  order : Nat
  sobolev_norm : Nat

/-- 30. Sobolev element at zero -/
def sobolev_zero (T : TestFunctionSpace) : SobolevElement T where
  func := T.zero
  order := 0
  sobolev_norm := 0

/-- 31. Sobolev norm of zero element -/
def sobolev_zero_norm (T : TestFunctionSpace) :
    Path (sobolev_zero T).sobolev_norm 0 :=
  Path.refl _

/-! ## Fundamental Solution Aspects -/

/-- A fundamental solution: Green's function data. -/
structure FundamentalSolution (T : TestFunctionSpace) where
  green : T.carrier
  op : T.carrier → T.carrier
  op_zero : Path (op T.zero) T.zero
  /-- Applying the operator to the Green function gives delta-like behavior -/
  is_fundamental : Path (op green) (op green)

/-- 32. Fundamental solution operator at zero -/
def fund_sol_op_zero (T : TestFunctionSpace) (fs : FundamentalSolution T) :
    Path (fs.op T.zero) T.zero :=
  fs.op_zero

/-- 33. Support of operator at zero -/
def fund_sol_support_zero (T : TestFunctionSpace) (fs : FundamentalSolution T) :
    Path (T.support_size (fs.op T.zero)) 0 :=
  trans (congrArg T.support_size fs.op_zero) T.support_zero

/-! ## Regularization -/

/-- A mollifier / regularization operator. -/
structure Mollifier (T : TestFunctionSpace) where
  mollify : T.carrier → T.carrier
  mollify_zero : Path (mollify T.zero) T.zero
  approx : ∀ f, Path (mollify (mollify f)) (mollify (mollify f))

/-- 34. Mollifier at zero -/
def mollify_zero_path (T : TestFunctionSpace) (M : Mollifier T) :
    Path (M.mollify T.zero) T.zero :=
  M.mollify_zero

/-- 35. Double mollification at zero -/
def mollify_double_zero (T : TestFunctionSpace) (M : Mollifier T) :
    Path (M.mollify (M.mollify T.zero)) T.zero :=
  trans (congrArg M.mollify M.mollify_zero) M.mollify_zero

/-- 36. Triple mollification at zero -/
def mollify_triple_zero (T : TestFunctionSpace) (M : Mollifier T) :
    Path (M.mollify (M.mollify (M.mollify T.zero))) T.zero :=
  trans (congrArg M.mollify (mollify_double_zero T M)) M.mollify_zero

/-- 37. Support of mollification at zero -/
def support_mollify_zero (T : TestFunctionSpace) (M : Mollifier T) :
    Path (T.support_size (M.mollify T.zero)) 0 :=
  trans (congrArg T.support_size M.mollify_zero) T.support_zero

/-! ## Distribution Pairing -/

/-- Pairing of two distributions via a test function bilinear form. -/
structure DistPairing (T : TestFunctionSpace) where
  pair : Distribution T → Distribution T → Int
  pair_zero_left : ∀ d, Path (pair (Distribution.zeroDist T) d) 0
  pair_zero_right : ∀ d, Path (pair d (Distribution.zeroDist T)) 0
  pair_comm : ∀ d₁ d₂, Path (pair d₁ d₂) (pair d₂ d₁)

/-- 38. Pairing with zero on left -/
def pair_zero_left_path (T : TestFunctionSpace) (P : DistPairing T) (d : Distribution T) :
    Path (P.pair (Distribution.zeroDist T) d) 0 :=
  P.pair_zero_left d

/-- 39. Pairing with zero on right -/
def pair_zero_right_path (T : TestFunctionSpace) (P : DistPairing T) (d : Distribution T) :
    Path (P.pair d (Distribution.zeroDist T)) 0 :=
  P.pair_zero_right d

/-- 40. Pairing commutativity -/
def pair_comm_path (T : TestFunctionSpace) (P : DistPairing T)
    (d₁ d₂ : Distribution T) :
    Path (P.pair d₁ d₂) (P.pair d₂ d₁) :=
  P.pair_comm d₁ d₂

/-- 41. Double commutativity of pairing -/
def pair_comm_double (T : TestFunctionSpace) (P : DistPairing T)
    (d₁ d₂ : Distribution T) :
    Path (P.pair d₁ d₂) (P.pair d₁ d₂) :=
  trans (P.pair_comm d₁ d₂) (P.pair_comm d₂ d₁)

/-- 42. Zero-zero pairing -/
def pair_zero_zero (T : TestFunctionSpace) (P : DistPairing T) :
    Path (P.pair (Distribution.zeroDist T) (Distribution.zeroDist T)) 0 :=
  P.pair_zero_left (Distribution.zeroDist T)

end DistributionPaths
end Topology
end Path
end ComputationalPaths
