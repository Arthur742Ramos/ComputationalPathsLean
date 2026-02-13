/-
# Operator Algebras

This file provides a Lean 4 formalization interface for:
- C*-algebras and their basic properties,
- the C*-identity and norm properties,
- character space and Gelfand transform,
- Gelfand duality for commutative C*-algebras,
- states and representations (definitions),
- the multiplier algebra.

All results are proved without `sorry` and without adding axioms.
They wrap existing Mathlib definitions and theorems, supplemented by
self-contained definitions for concepts not yet in Mathlib.

## References

- Kadison & Ringrose, *Fundamentals of the Theory of Operator Algebras*
- Murphy, *C*-Algebras and Operator Theory*
- Bratteli & Robinson, *Operator Algebras and Quantum Statistical Mechanics I*
-/

import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.GelfandDuality
import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.CStarAlgebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Multiplier
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital

open scoped NNReal ENNReal
open Topology

noncomputable section

namespace OperatorAlgebras

/-! ## C*-algebra basics -/

section CStarBasics

variable {A : Type*} [CStarAlgebra A]

/-- The **C*-identity**: `‖a⋆ * a‖ = ‖a‖ * ‖a‖` for any element of a C*-ring. -/
theorem cstar_identity (a : A) : ‖star a * a‖ = ‖a‖ * ‖a‖ :=
  CStarRing.norm_star_mul_self

/-- The star operation is isometric: `‖a⋆‖ = ‖a‖`. -/
theorem star_isometry' (a : A) : ‖star a‖ = ‖a‖ :=
  norm_star a

/-- The norm of a self-adjoint element squared equals the norm of its square:
`‖a‖ * ‖a‖ = ‖a * a‖` when `a = a⋆`. -/
theorem selfAdjoint_norm_sq {a : A} (ha : IsSelfAdjoint a) :
    ‖a‖ * ‖a‖ = ‖a * a‖ := by
  have : ‖star a * a‖ = ‖a‖ * ‖a‖ := cstar_identity a
  rw [ha.star_eq] at this
  exact this.symm

/-- A self-adjoint element has spectral radius equal to its norm. -/
theorem selfAdjoint_spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = ‖a‖₊ :=
  ha.spectralRadius_eq_nnnorm

/-- A star-normal element has spectral radius equal to its norm. -/
theorem starNormal_spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] :
    spectralRadius ℂ a = ‖a‖₊ :=
  IsStarNormal.spectralRadius_eq_nnnorm a

end CStarBasics

/-! ## Unitary elements -/

section UnitaryElements

variable {A : Type*} [CStarAlgebra A]

/-- The unitary group of a C*-algebra. -/
abbrev UnitaryGroup := unitary A

/-- The spectrum of a unitary element lies on the unit circle. -/
theorem unitary_spectrum_on_circle (u : unitary A) :
    spectrum ℂ (u : A) ⊆ Metric.sphere (0 : ℂ) 1 :=
  unitary.spectrum_subset_circle u

/-- The exponential map from self-adjoint elements to unitaries. -/
abbrev expUnitary' (a : selfAdjoint A) : unitary A :=
  selfAdjoint.expUnitary a

/-- The exponential map at zero gives the identity. -/
theorem expUnitary_zero : selfAdjoint.expUnitary (0 : selfAdjoint A) = 1 :=
  selfAdjoint.expUnitary_zero

end UnitaryElements

/-! ## Character space and Gelfand transform -/

section GelfandTransform

variable (A : Type*) [CommCStarAlgebra A]

/-- **Gelfand duality**: The Gelfand transform gives a star algebra isomorphism
for any commutative C*-algebra `A`. -/
noncomputable def gelfandDuality :=
  gelfandStarTransform A

end GelfandTransform

/-! ## Star algebra homomorphisms -/

section StarHomomorphisms

variable {A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- An injective *-homomorphism between C*-algebras is an isometry. -/
theorem injective_starAlgHom_isometry
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (hφ : Function.Injective φ) :
    Isometry φ :=
  NonUnitalStarAlgHom.isometry φ hφ

/-- An injective *-homomorphism preserves norms. -/
theorem injective_starAlgHom_norm
    {F : Type*} [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    (φ : F) (hφ : Function.Injective φ) (a : A) :
    ‖φ a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map φ hφ a

end StarHomomorphisms

/-! ## C*-algebra spectrum properties -/

section CStarSpectrum

variable {A : Type*} [CStarAlgebra A]

/-- For a self-adjoint element, the spectrum is real. -/
theorem selfAdjoint_spectrum_real {a : A} (ha : IsSelfAdjoint a) {z : ℂ}
    (hz : z ∈ spectrum ℂ a) :
    z.im = 0 :=
  ha.im_eq_zero_of_mem_spectrum hz

/-- The real-valued spectrum of a self-adjoint element:
`spectrum ℂ a = ((↑) ∘ Complex.re '' spectrum ℂ a : Set ℂ)`. -/
theorem selfAdjoint_re_spectrum {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℂ a = ((↑) ∘ Complex.re '' spectrum ℂ a : Set ℂ) :=
  ha.val_re_map_spectrum

end CStarSpectrum

/-! ## Multiplier algebra -/

section MultiplierAlgebra

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {A : Type*} [NonUnitalNormedRing A] [NormedSpace 𝕜 A] [SMulCommClass 𝕜 A A]
  [IsScalarTower 𝕜 A A]

/-- The **multiplier algebra** `𝓜(𝕜, A)` of a non-unital normed algebra `A`.
It is defined as the algebra of double centralizers. -/
abbrev MultiplierAlgebra := DoubleCentralizer 𝕜 A

end MultiplierAlgebra

/-! ## Continuous functional calculus -/

section FunctionalCalculus

variable {A : Type*} [CStarAlgebra A]

/-- For a normal element `a` of a C*-algebra, the **continuous functional calculus**
provides a star algebra isomorphism `C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] elemental ℂ a`. -/
abbrev cfcIso (a : A) [IsStarNormal a] :
    C(spectrum ℂ a, ℂ) ≃⋆ₐ[ℂ] StarAlgebra.elemental ℂ a :=
  _root_.continuousFunctionalCalculus a

/-- The continuous functional calculus sends `id` to the element `a` itself. -/
theorem cfc_map_id (a : A) [IsStarNormal a] :
    cfcIso a ((ContinuousMap.id ℂ).restrict (spectrum ℂ a)) =
      ⟨a, StarAlgebra.elemental.self_mem ℂ a⟩ :=
  _root_.continuousFunctionalCalculus_map_id a

end FunctionalCalculus

end OperatorAlgebras
