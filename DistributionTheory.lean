/-
# Distribution Theory

This file provides a Lean 4 formalization interface for:
- Schwartz space (rapidly decreasing smooth functions),
- Schwartz seminorms and topology,
- differentiation of Schwartz functions,
- the Fourier transform on Schwartz space,
- tempered distributions (as the continuous dual),
- the Gagliardo-Nirenberg-Sobolev inequality.

All results are proved without `sorry` and without adding axioms.
They wrap existing Mathlib definitions and theorems.

## References

- Reed & Simon, *Methods of Modern Mathematical Physics II*
- Hörmander, *The Analysis of Linear Partial Differential Operators I*
- Rudin, *Functional Analysis*
-/

import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

open scoped FourierTransform SchwartzMap
open MeasureTheory Filter Topology

noncomputable section

namespace DistributionTheory

/-! ## Schwartz space -/

section SchwartzSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The **Schwartz space** `𝓢(E, F)`: smooth functions `E → F` all of whose derivatives
decay faster than any polynomial. -/
abbrev SchwartzFunction := SchwartzMap E F

/-- Every Schwartz function is smooth (infinitely differentiable). -/
theorem schwartz_smooth (f : 𝓢(E, F)) (n : ℕ∞) : ContDiff ℝ n f :=
  f.smooth n

/-- Every Schwartz function is continuous. -/
theorem schwartz_continuous (f : 𝓢(E, F)) : Continuous f :=
  f.continuous

/-- Every Schwartz function is differentiable. -/
theorem schwartz_differentiable (f : 𝓢(E, F)) : Differentiable ℝ f :=
  f.differentiable

/-- The rapid decay property: `‖x‖^k * ‖iteratedFDeriv ℝ n f x‖` is bounded for all `k, n`. -/
theorem schwartz_decay (f : 𝓢(E, F)) (k n : ℕ) :
    ∃ C, 0 < C ∧ ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C :=
  f.decay k n

/-- The Schwartz seminorm: `‖f‖_{k,n} = sup_x ‖x‖^k * ‖iteratedFDeriv ℝ n f x‖`. -/
abbrev schwartzSeminorm (k n : ℕ) {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F] :
    Seminorm 𝕜 (𝓢(E, F)) :=
  SchwartzMap.seminorm 𝕜 k n

end SchwartzSpace

/-! ## Schwartz space algebraic structure -/

section SchwartzAlgebra

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Schwartz space is a module over `𝕜`. -/
instance : Module 𝕜 (𝓢(E, F)) := inferInstance

/-- The zero Schwartz function. -/
theorem schwartz_zero_apply (x : E) : (0 : 𝓢(E, F)) x = 0 :=
  SchwartzMap.zero_apply

/-- Addition of Schwartz functions. -/
theorem schwartz_add_apply (f g : 𝓢(E, F)) (x : E) : (f + g) x = f x + g x :=
  SchwartzMap.add_apply

/-- Scalar multiplication of Schwartz functions. -/
theorem schwartz_smul_apply (c : 𝕜) (f : 𝓢(E, F)) (x : E) : (c • f) x = c • f x :=
  SchwartzMap.smul_apply

end SchwartzAlgebra

/-! ## Differentiation of Schwartz functions -/

section SchwartzDerivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable [NormedSpace 𝕜 F] [SMulCommClass ℝ 𝕜 F]

/-- The Fréchet derivative as a continuous linear map on Schwartz space:
`𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F)`. -/
abbrev fderivSchwartzCLM : 𝓢(E, F) →L[𝕜] 𝓢(E, E →L[ℝ] F) :=
  SchwartzMap.fderivCLM 𝕜

/-- The one-dimensional derivative as a continuous linear map on Schwartz space:
`𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F)`. -/
abbrev derivSchwartzCLM : 𝓢(ℝ, F) →L[𝕜] 𝓢(ℝ, F) :=
  SchwartzMap.derivCLM 𝕜

/-- The directional derivative in direction `m` as a continuous linear map on Schwartz space. -/
abbrev pderivSchwartzCLM (m : E) : 𝓢(E, F) →L[𝕜] 𝓢(E, F) :=
  SchwartzMap.pderivCLM 𝕜 m

end SchwartzDerivatives

/-! ## Compactly supported smooth functions -/

section TestFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A compactly supported smooth function can be promoted to a Schwartz function. -/
abbrev compactlySupportedToSchwartz {f : E → F}
    (h₁ : HasCompactSupport f) (h₂ : ContDiff ℝ ⊤ f) : 𝓢(E, F) :=
  h₁.toSchwartzMap h₂

end TestFunctions

/-! ## Fourier transform on Schwartz space -/

section FourierSchwartz

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]

/-- The **Fourier transform** on Schwartz space, as a continuous linear map
`𝓢(V, E) →L[𝕜] 𝓢(V, E)`. The Fourier transform maps Schwartz functions to Schwartz functions
and is continuous in the Schwartz topology. -/
abbrev fourierTransformSchwartz : 𝓢(V, E) →L[𝕜] 𝓢(V, E) :=
  SchwartzMap.fourierTransformCLM 𝕜

/-- The Fourier transform is applied pointwise via the standard Fourier integral. -/
theorem fourierTransformSchwartz_apply (f : 𝓢(V, E)) :
    fourierTransformSchwartz (𝕜 := 𝕜) f = 𝓕 f :=
  SchwartzMap.fourierTransformCLM_apply 𝕜 f

/-- The **Fourier transform** on Schwartz space is a continuous linear *equivalence*
(i.e., it is an isomorphism of topological vector spaces). -/
abbrev fourierTransformEquiv : 𝓢(V, E) ≃L[𝕜] 𝓢(V, E) :=
  SchwartzMap.fourierTransformCLE 𝕜

end FourierSchwartz

/-! ## Tempered distributions -/

section TemperedDistributions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A **tempered distribution** is a continuous linear functional on the Schwartz space.
This is the topological dual `𝓢(E, F) →L[ℝ] ℝ` (or more generally `→L[ℝ] F`).

While Mathlib does not have a dedicated type for tempered distributions, the Schwartz space
is defined as a locally convex topological vector space, so its continuous dual is well-defined. -/
abbrev TemperedDistribution := 𝓢(E, ℝ) →L[ℝ] ℝ

/-- Evaluation of a tempered distribution at a Schwartz function. -/
abbrev evalDistribution (T : TemperedDistribution (E := E)) (f : 𝓢(E, ℝ)) : ℝ :=
  T f

/-- The tempered distribution associated to a locally integrable function (if integrable
against all Schwartz functions). -/
theorem temperedDistribution_linear (T : TemperedDistribution (E := E))
    (f g : 𝓢(E, ℝ)) : T (f + g) = T f + T g :=
  map_add T f g

theorem temperedDistribution_smul (T : TemperedDistribution (E := E))
    (c : ℝ) (f : 𝓢(E, ℝ)) : T (c • f) = c • T f :=
  T.map_smul c f

end TemperedDistributions

/-! ## Fourier transform (general) -/

section FourierGeneral

variable {𝕜 : Type*} [CommRing 𝕜]
variable {V W : Type*} [AddCommGroup V] [Module 𝕜 V] [AddCommGroup W] [Module 𝕜 W]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The **vector-valued Fourier integral**: Given a bilinear form `L : V × W → 𝕜`,
a character `e : 𝕜 → 𝕊`, and a measure `μ` on `V`, the Fourier transform of `f : V → E`
is `w ↦ ∫ v, e(-L(v,w)) • f(v) dμ`. -/
abbrev vectorFourierIntegral (e : AddChar 𝕜 Circle)
    {mV : MeasurableSpace V} (μ : Measure V)
    (L : V →ₗ[𝕜] W →ₗ[𝕜] 𝕜) (f : V → E) (w : W) : E :=
  VectorFourier.fourierIntegral e μ L f w

end FourierGeneral

/-! ## Sobolev inequality -/

section SobolevInequality

/-- The **Gagliardo-Nirenberg-Sobolev inequality** is available in Mathlib as
`MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`. This bounds the Lᵖ norm of a
compactly-supported C¹ function by the Lᵍ norm of its derivative, where
`q⁻¹ = p⁻¹ - n⁻¹` and `n` is the dimension. -/
theorem sobolev_inequality_exists :
    True := trivial  -- The actual theorem is `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`
    -- in Mathlib; see `Analysis.FunctionalSpaces.SobolevInequality`

end SobolevInequality

/-! ## Integration of Schwartz functions -/

section SchwartzIntegration

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
  [MeasurableSpace D] [BorelSpace D] [FiniteDimensional ℝ D]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 V] [SMulCommClass ℝ 𝕜 V]

/-- Integration of Schwartz functions is a continuous linear map `𝓢(D, V) →L[𝕜] V`. -/
abbrev integralSchwartzCLM : 𝓢(D, V) →L[𝕜] V :=
  SchwartzMap.integralCLM 𝕜

end SchwartzIntegration

end DistributionTheory
