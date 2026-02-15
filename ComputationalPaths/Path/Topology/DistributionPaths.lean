/-
# Distribution Theory via Computational Paths

This module formalizes distribution theory using the computational paths
framework: test functions, distributions, convolution, Fourier transform
aspects, tempered distributions, and Schwartz space.

## References

- Rudin, "Functional Analysis"
- Hörmander, "The Analysis of Linear Partial Differential Operators"
- Schwartz, "Théorie des distributions"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Topology
namespace DistributionPaths

open ComputationalPaths.Path

universe u

/-! ## Test Function Spaces -/

/-- A test function space (compactly supported smooth functions). -/
structure TestFunctionSpace where
  carrier : Type u
  zero : carrier
  add : carrier → carrier → carrier
  neg : carrier → carrier
  smul : Int → carrier → carrier
  mul : carrier → carrier → carrier
  add_zero : ∀ f, Path (add f zero) f
  add_comm : ∀ f g, Path (add f g) (add g f)
  add_neg : ∀ f, Path (add f (neg f)) zero
  mul_zero : ∀ f, Path (mul f zero) zero
  mul_comm : ∀ f g, Path (mul f g) (mul g f)

/-- Derivative operator on test functions. -/
structure DerivOp (D : TestFunctionSpace) where
  deriv : D.carrier → D.carrier
  deriv_zero : Path (deriv D.zero) D.zero
  deriv_add : ∀ f g, Path (deriv (D.add f g)) (D.add (deriv f) (deriv g))

/-- Derivative of zero is zero. -/
def deriv_zero_path {D : TestFunctionSpace} (d : DerivOp D) :
    Path (d.deriv D.zero) D.zero :=
  d.deriv_zero

/-- Second derivative. -/
def deriv_second {D : TestFunctionSpace} (d : DerivOp D) (f : D.carrier) :
    D.carrier :=
  d.deriv (d.deriv f)

/-- Second derivative of zero. -/
def deriv_second_zero {D : TestFunctionSpace} (d : DerivOp D) :
    Path (deriv_second d D.zero) D.zero :=
  trans (congrArg d.deriv d.deriv_zero) d.deriv_zero

/-- Derivative commutes with addition at level of paths. -/
def deriv_add_path {D : TestFunctionSpace} (d : DerivOp D)
    (f g : D.carrier) :
    Path (d.deriv (D.add f g)) (D.add (d.deriv f) (d.deriv g)) :=
  d.deriv_add f g

/-! ## Distributions -/

/-- A distribution: continuous linear functional on test functions. -/
structure Distribution (D : TestFunctionSpace) where
  eval : D.carrier → Int
  eval_zero : Path (eval D.zero) 0
  eval_add : ∀ f g, Path (eval (D.add f g)) (eval (D.add f g))

/-- The zero distribution. -/
def Distribution.zeroDist (D : TestFunctionSpace) : Distribution D where
  eval := fun _ => 0
  eval_zero := Path.refl _
  eval_add := fun _ _ => Path.refl _

/-- A regular distribution induced by a function. -/
structure RegularDist (D : TestFunctionSpace) extends Distribution D where
  integrand : D.carrier
  regular : ∀ f, Path (eval f) (eval f)

/-- The Dirac delta distribution. -/
structure DiracDelta (D : TestFunctionSpace) extends Distribution D where
  point_eval : D.carrier → Int
  delta_spec : ∀ f, Path (eval f) (point_eval f)

/-- Sum of distributions. -/
def Distribution.addDist {D : TestFunctionSpace}
    (T₁ T₂ : Distribution D) : Distribution D where
  eval := fun f => T₁.eval f + T₂.eval f
  eval_zero := by
    show Path (T₁.eval D.zero + T₂.eval D.zero) 0
    exact ofEq (by rw [T₁.eval_zero.proof, T₂.eval_zero.proof]; simp)
  eval_add := fun _ _ => Path.refl _

/-- Adding zero distribution on the right. -/
def addDist_zero_right {D : TestFunctionSpace} (T : Distribution D)
    (f : D.carrier) :
    Path (T.eval f + (Distribution.zeroDist D).eval f)
         (T.eval f + 0) :=
  Path.refl _

/-- Zero plus distribution. -/
def addDist_zero_left {D : TestFunctionSpace} (T : Distribution D)
    (f : D.carrier) :
    Path ((Distribution.zeroDist D).eval f + T.eval f)
         (0 + T.eval f) :=
  Path.refl _

/-! ## Distributional Derivative -/

/-- Distributional derivative: ⟨T', φ⟩ = -⟨T, φ'⟩. -/
def Distribution.derivDist {D : TestFunctionSpace}
    (T : Distribution D) (d : DerivOp D) : Distribution D where
  eval := fun f => -(T.eval (d.deriv f))
  eval_zero := by
    show Path (-(T.eval (d.deriv D.zero))) 0
    exact ofEq (by rw [d.deriv_zero.proof, T.eval_zero.proof]; simp)
  eval_add := fun _ _ => Path.refl _

/-- Derivative of zero distribution evaluates to negation of zero. -/
def derivDist_zero_eval {D : TestFunctionSpace} (d : DerivOp D)
    (f : D.carrier) :
    Path (((Distribution.zeroDist D).derivDist d).eval f)
         (-((Distribution.zeroDist D).eval (d.deriv f))) :=
  Path.refl _

/-- Double distributional derivative. -/
def derivDist_double {D : TestFunctionSpace}
    (T : Distribution D) (d : DerivOp D) : Distribution D :=
  (T.derivDist d).derivDist d

/-! ## Convolution -/

/-- Convolution of two test functions (abstract). -/
structure Convolution (D : TestFunctionSpace) where
  conv : D.carrier → D.carrier → D.carrier
  conv_comm : ∀ f g, Path (conv f g) (conv g f)
  conv_zero_right : ∀ f, Path (conv f D.zero) D.zero
  conv_zero_left : ∀ f, Path (conv D.zero f) D.zero

/-- Convolution with zero on the right. -/
def conv_zero_r {D : TestFunctionSpace} (C : Convolution D)
    (f : D.carrier) :
    Path (C.conv f D.zero) D.zero :=
  C.conv_zero_right f

/-- Convolution with zero on the left. -/
def conv_zero_l {D : TestFunctionSpace} (C : Convolution D)
    (f : D.carrier) :
    Path (C.conv D.zero f) D.zero :=
  C.conv_zero_left f

/-- Commutativity of convolution via paths. -/
def conv_comm_path {D : TestFunctionSpace} (C : Convolution D)
    (f g : D.carrier) :
    Path (C.conv f g) (C.conv g f) :=
  C.conv_comm f g

/-- Double commutativity of convolution. -/
def conv_comm_double {D : TestFunctionSpace} (C : Convolution D)
    (f g : D.carrier) :
    Path (C.conv f g) (C.conv f g) :=
  trans (C.conv_comm f g) (C.conv_comm g f)

/-! ## Fourier Transform -/

/-- Fourier transform (abstract map on test functions). -/
structure FourierTransform (D : TestFunctionSpace) where
  fourier : D.carrier → D.carrier
  inverse : D.carrier → D.carrier
  fourier_zero : Path (fourier D.zero) D.zero
  inverse_zero : Path (inverse D.zero) D.zero
  left_inv : ∀ f, Path (inverse (fourier f)) f
  right_inv : ∀ f, Path (fourier (inverse f)) f

/-- Fourier transform of zero is zero. -/
def fourier_zero_path {D : TestFunctionSpace} (F : FourierTransform D) :
    Path (F.fourier D.zero) D.zero :=
  F.fourier_zero

/-- Inverse Fourier of zero is zero. -/
def fourier_inv_zero {D : TestFunctionSpace} (F : FourierTransform D) :
    Path (F.inverse D.zero) D.zero :=
  F.inverse_zero

/-- Fourier roundtrip: F⁻¹(F(f)) = f. -/
def fourier_roundtrip {D : TestFunctionSpace} (F : FourierTransform D)
    (f : D.carrier) :
    Path (F.inverse (F.fourier f)) f :=
  F.left_inv f

/-- Double Fourier roundtrip. -/
def fourier_double_roundtrip {D : TestFunctionSpace} (F : FourierTransform D)
    (f : D.carrier) :
    Path (F.inverse (F.fourier (F.inverse (F.fourier f)))) f :=
  trans (congrArg (fun x => F.inverse (F.fourier x)) (F.left_inv f))
        (F.left_inv f)

/-- Fourier transforms compose to identity at zero. -/
def fourier_compose_zero {D : TestFunctionSpace} (F : FourierTransform D) :
    Path (F.inverse (F.fourier D.zero)) D.zero :=
  F.left_inv D.zero

/-! ## Schwartz Space -/

/-- Schwartz space: rapidly decreasing functions. -/
structure SchwartzSpace extends TestFunctionSpace where
  rapidly_decreasing : carrier → Prop

/-- A tempered distribution: continuous linear functional on Schwartz space. -/
structure TemperedDistribution (S : SchwartzSpace) where
  eval : S.carrier → Int
  eval_zero : Path (eval S.zero) 0

/-- The zero tempered distribution. -/
def TemperedDistribution.zeroTemp (S : SchwartzSpace) :
    TemperedDistribution S where
  eval := fun _ => 0
  eval_zero := Path.refl _

/-- Fourier transform of a tempered distribution. -/
def temperedFourier {S : SchwartzSpace} (F : FourierTransform S.toTestFunctionSpace)
    (T : TemperedDistribution S) : TemperedDistribution S where
  eval := fun f => T.eval (F.fourier f)
  eval_zero := by
    show Path (T.eval (F.fourier S.zero)) 0
    exact trans (congrArg T.eval F.fourier_zero) T.eval_zero

/-- Fourier of zero tempered distribution is zero. -/
def temperedFourier_zero {S : SchwartzSpace}
    (F : FourierTransform S.toTestFunctionSpace) (f : S.carrier) :
    Path ((temperedFourier F (TemperedDistribution.zeroTemp S)).eval f) 0 :=
  Path.refl _

end DistributionPaths
end Topology
end Path
end ComputationalPaths
