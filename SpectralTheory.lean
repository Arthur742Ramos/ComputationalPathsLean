/-
# Spectral Theory

This file provides a Lean 4 formalization interface for:
- Spectrum of elements in Banach algebras,
- resolvent and resolvent set,
- spectral radius and its properties,
- spectral theorem for self-adjoint operators (finite-dimensional),
- continuous functional calculus for C*-algebras.

All results are proved without `sorry` and without adding axioms.
They wrap existing Mathlib definitions and theorems.

## References

- Conway, *A Course in Functional Analysis*
- Reed & Simon, *Methods of Modern Mathematical Physics I*
- Kadison & Ringrose, *Fundamentals of the Theory of Operator Algebras*
-/

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

open scoped NNReal ENNReal
open Filter Topology

noncomputable section

namespace SpectralTheory

/-! ## Spectrum and resolvent set -/

section SpectrumBasics

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {A : Type*} [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- The **spectrum** of an element `a` in a Banach algebra: the set of `k : 𝕜` such that
`a - k • 1` is not invertible. -/
abbrev spectrumOf (a : A) : Set 𝕜 := spectrum 𝕜 a

/-- The **resolvent set** of `a`: the complement of the spectrum. -/
abbrev resolventSetOf (a : A) : Set 𝕜 := resolventSet 𝕜 a

/-- The resolvent `(a - k • 1)⁻¹` at a point `k` in the resolvent set. -/
abbrev resolventAt (a : A) (k : 𝕜) : A := resolvent a k

/-- The resolvent set is open. -/
theorem resolventSet_isOpen (a : A) : IsOpen (resolventSetOf a) :=
  spectrum.isOpen_resolventSet a

/-- The spectrum is closed. -/
theorem spectrum_isClosed (a : A) : IsClosed (spectrumOf a) :=
  spectrum.isClosed a

/-- The spectrum is contained in the closed ball of radius `‖a‖ * ‖1‖`. -/
theorem spectrum_subset_closedBall (a : A) :
    spectrumOf a ⊆ Metric.closedBall (0 : 𝕜) (‖a‖ * ‖(1 : A)‖) :=
  spectrum.subset_closedBall_norm_mul a

/-- Elements of the spectrum have norm bounded by the operator norm. -/
theorem norm_le_norm_mul_of_mem {a : A} {k : 𝕜} (hk : k ∈ spectrumOf a) :
    ‖k‖ ≤ ‖a‖ * ‖(1 : A)‖ :=
  spectrum.norm_le_norm_mul_of_mem hk

end SpectrumBasics

/-! ## Spectral radius -/

section SpectralRadius

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (A : Type*) [NormedRing A] [NormedAlgebra 𝕜 A] [CompleteSpace A]

/-- The **spectral radius** of `a`: the supremum of `‖k‖` for `k ∈ spectrum 𝕜 a`. -/
abbrev spectralRadiusOf (a : A) : ℝ≥0∞ := spectralRadius 𝕜 a

/-- The spectral radius of zero is zero. -/
theorem spectralRadius_zero' : spectralRadiusOf 𝕜 A (0 : A) = 0 :=
  spectrum.spectralRadius_zero (𝕜 := 𝕜) (A := A)

/-- The spectral radius is bounded by the norm (for normed algebras with `‖1‖ = 1`). -/
theorem spectralRadius_le_nnnorm' [NormOneClass A] (a : A) :
    spectralRadiusOf 𝕜 A a ≤ ‖a‖₊ :=
  spectrum.spectralRadius_le_nnnorm a

/-- **Spectral mapping for powers**: `spectralRadius(a)ⁿ ≤ spectralRadius(aⁿ)`. -/
theorem spectralRadius_pow_le' (a : A) (n : ℕ) (hn : n ≠ 0) :
    spectralRadiusOf 𝕜 A a ^ n ≤ spectralRadiusOf 𝕜 A (a ^ n) :=
  spectrum.spectralRadius_pow_le a n hn

/-- The spectrum is bounded (in the bornological sense). -/
theorem spectrum_isBounded' (a : A) : Bornology.IsBounded (spectrumOf (𝕜 := 𝕜) a) :=
  spectrum.isBounded a

/-- The spectrum of an element in a proper space is compact. -/
theorem spectrum_isCompact' [ProperSpace 𝕜] (a : A) : IsCompact (spectrumOf (𝕜 := 𝕜) a) :=
  spectrum.isCompact a

end SpectralRadius

/-! ## Spectral theory of self-adjoint operators (finite-dimensional) -/

section SelfAdjointSpectral

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {T : E →ₗ[𝕜] E}

/-- Self-adjoint (symmetric) operators have real eigenvalues. -/
theorem selfAdjoint_eigenvalue_real (hT : T.IsSymmetric) {μ : 𝕜}
    (hμ : Module.End.HasEigenvalue T μ) :
    starRingEnd 𝕜 μ = μ :=
  hT.conj_eigenvalue_eq_self hμ

/-- Eigenspaces of a self-adjoint operator are mutually orthogonal. -/
theorem selfAdjoint_eigenspaces_orthogonal (hT : T.IsSymmetric) :
    OrthogonalFamily 𝕜 (fun μ => (Module.End.eigenspace T μ))
      (fun μ => (Module.End.eigenspace T μ).subtypeₗᵢ) :=
  hT.orthogonalFamily_eigenspaces

variable [FiniteDimensional 𝕜 E]

/-- The orthogonal complement of the sum of all eigenspaces of a self-adjoint operator
on a finite-dimensional space is trivial. -/
theorem selfAdjoint_eigenspaces_span_all (hT : T.IsSymmetric) :
    (⨆ μ, Module.End.eigenspace T μ)ᗮ = ⊥ :=
  hT.orthogonalComplement_iSup_eigenspaces_eq_bot

/-- **Spectral theorem** (diagonalization, version 1): A self-adjoint operator on a
finite-dimensional inner product space `E` is diagonalizable. The diagonalization is a
linear isometry equivalence from `E` to the orthogonal direct sum of eigenspaces. -/
abbrev selfAdjoint_diagonalization (hT : T.IsSymmetric) :
    E ≃ₗᵢ[𝕜] PiLp 2 (fun μ : Module.End.Eigenvalues T => Module.End.eigenspace T μ) :=
  hT.diagonalization

/-- **Spectral theorem** (diagonalization acts diagonally): Under the diagonalization,
`T` acts by scalar multiplication on each eigenspace. -/
theorem selfAdjoint_diag_apply (hT : T.IsSymmetric) (v : E)
    (μ : Module.End.Eigenvalues T) :
    hT.diagonalization (T v) μ = (μ : 𝕜) • hT.diagonalization v μ :=
  hT.diagonalization_apply_self_apply v μ

/-- **Spectral theorem** (eigenvector basis, version 2): A self-adjoint operator on a
finite-dimensional inner product space has an orthonormal eigenvector basis. -/
abbrev selfAdjoint_eigenvectorBasis (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) :
    OrthonormalBasis (Fin n) 𝕜 E :=
  hT.eigenvectorBasis hn

/-- The eigenvalues of a self-adjoint operator, listed in decreasing order. -/
abbrev selfAdjoint_eigenvalues (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) :
    Fin n → ℝ :=
  hT.eigenvalues hn

/-- The eigenvalues are in decreasing order. -/
theorem selfAdjoint_eigenvalues_antitone (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) :
    Antitone (hT.eigenvalues hn) :=
  hT.eigenvalues_antitone hn

/-- Each eigenvalue is genuinely an eigenvalue of `T`. -/
theorem selfAdjoint_hasEigenvalue (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    Module.End.HasEigenvalue T ↑(hT.eigenvalues hn i) :=
  hT.hasEigenvalue_eigenvalues hn i

/-- `T` applied to the `i`-th eigenvector gives `eigenvalue i • eigenvector i`. -/
theorem selfAdjoint_apply_eigenvectorBasis (hT : T.IsSymmetric) {n : ℕ}
    (hn : Module.finrank 𝕜 E = n) (i : Fin n) :
    T (hT.eigenvectorBasis hn i) = (↑(hT.eigenvalues hn i) : 𝕜) • hT.eigenvectorBasis hn i :=
  hT.apply_eigenvectorBasis hn i

end SelfAdjointSpectral

/-! ## C*-algebra spectrum theory -/

section CStarSpectrum

variable {A : Type*} [CStarAlgebra A]

/-- In a C*-algebra, the spectrum of a unitary element lies on the unit circle. -/
theorem unitary_spectrum_subset_circle (u : unitary A) :
    spectrumOf (u : A) ⊆ Metric.sphere (0 : ℂ) 1 :=
  unitary.spectrum_subset_circle u

/-- For a self-adjoint element of a C*-algebra, the spectral radius equals the norm. -/
theorem selfAdjoint_spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = ‖a‖₊ :=
  ha.spectralRadius_eq_nnnorm

/-- For a star-normal element of a C*-algebra, the spectral radius equals the norm. -/
theorem starNormal_spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] :
    spectralRadius ℂ a = ‖a‖₊ :=
  IsStarNormal.spectralRadius_eq_nnnorm a

end CStarSpectrum

/-! ## Continuous functional calculus -/

section FunctionalCalculus

variable {A : Type*} [CStarAlgebra A]

/-- The **continuous functional calculus** for a normal element: given `f` continuous on
`spectrum ℂ a` and `a : A` star-normal, produce `f(a) ∈ A`.
This uses the `cfc` from Mathlib's ContinuousFunctionalCalculus API. -/
abbrev cfcApply (f : ℂ → ℂ) (a : A) [IsStarNormal a] : A := cfc f a

end FunctionalCalculus

end SpectralTheory
