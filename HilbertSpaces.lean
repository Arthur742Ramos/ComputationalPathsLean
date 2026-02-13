/-
# Hilbert Spaces: Inner Product Space Theory

This file provides a Lean 4 formalization interface for:
- Inner product spaces,
- orthogonality and orthogonal complements,
- the Riesz representation theorem (Fréchet-Riesz),
- orthonormal sets and bases,
- Bessel's inequality,
- Parseval's identity (via Hilbert bases).

All results are proved without `sorry` and without adding axioms.
They wrap existing Mathlib definitions and theorems.

## References

- Conway, *A Course in Functional Analysis*
- Reed & Simon, *Methods of Modern Mathematical Physics I*
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.l2Space

open scoped NNReal
open Filter Topology

noncomputable section

namespace HilbertSpaces

/-! ## Inner product space basics -/

section InnerProductBasics

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The inner product, as an explicit function. -/
abbrev innerProduct (x y : E) : 𝕜 := @inner 𝕜 E _ x y

/-- Conjugate symmetry of the inner product: ⟪y, x⟫† = ⟪x, y⟫. -/
theorem inner_conj_symm' (x y : E) :
    starRingEnd 𝕜 (innerProduct (𝕜 := 𝕜) y x) = innerProduct x y :=
  _root_.inner_conj_symm x y

/-- The inner product is linear in the second argument. -/
theorem inner_add_right (x y z : E) :
    innerProduct (𝕜 := 𝕜) x (y + z) = innerProduct x y + innerProduct x z :=
  _root_.inner_add_right x y z

/-- Positive definiteness: ⟪x, x⟫ is real and nonneg, and zero iff x = 0. -/
theorem inner_self_nonneg (x : E) :
    0 ≤ RCLike.re (innerProduct (𝕜 := 𝕜) x x) :=
  _root_.inner_self_nonneg (𝕜 := 𝕜)

theorem inner_self_eq_zero (x : E) :
    innerProduct (𝕜 := 𝕜) x x = 0 ↔ x = 0 :=
  _root_.inner_self_eq_zero

/-- The **Cauchy-Schwarz inequality**. -/
theorem cauchy_schwarz (x y : E) :
    ‖innerProduct (𝕜 := 𝕜) x y‖ ≤ ‖x‖ * ‖y‖ :=
  norm_inner_le_norm x y

/-- The norm squared equals the real part of ⟪x, x⟫. -/
theorem norm_sq_eq_inner (x : E) :
    ‖x‖ * ‖x‖ = RCLike.re (innerProduct (𝕜 := 𝕜) x x) :=
  (inner_self_eq_norm_mul_norm (𝕜 := 𝕜) x).symm

/-- The **parallelogram law**: ‖x + y‖₊² + ‖x - y‖₊² = 2(‖x‖₊² + ‖y‖₊²).
Uses NNNorm version which doesn't require explicit scalar field. -/
theorem parallelogram_law_nnnorm (𝕜' : Type*) [RCLike 𝕜'] {E' : Type*}
    [NormedAddCommGroup E'] [InnerProductSpace 𝕜' E'] (x y : E') :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  parallelogram_law_with_nnnorm 𝕜' x y

end InnerProductBasics

/-! ## Orthogonality -/

section Orthogonality

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Two vectors are orthogonal when their inner product is zero. -/
def IsOrthogonal (x y : E) : Prop := @inner 𝕜 E _ x y = 0

theorem isOrthogonal_comm (x y : E) :
    IsOrthogonal (𝕜 := 𝕜) x y ↔ IsOrthogonal (𝕜 := 𝕜) y x := by
  simp only [IsOrthogonal, inner_eq_zero_symm]

/-- **Pythagorean theorem**: If x ⊥ y then ‖x + y‖² = ‖x‖² + ‖y‖². -/
theorem pythagorean (x y : E) (h : IsOrthogonal (𝕜 := 𝕜) x y) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y h

/-- The orthogonal complement of a submodule. -/
abbrev orthogonalComplement (K : Submodule 𝕜 E) : Submodule 𝕜 E := Kᗮ

/-- A vector in the orthogonal complement is orthogonal to all vectors in the submodule. -/
theorem mem_orthogonalComplement_iff (K : Submodule 𝕜 E) (x : E) :
    x ∈ orthogonalComplement K ↔ ∀ y ∈ K, @inner 𝕜 E _ y x = 0 :=
  K.mem_orthogonal x

/-- The orthogonal complement of the orthogonal complement of a closed subspace is itself. -/
theorem orthogonal_orthogonal_eq [CompleteSpace E] (K : Submodule 𝕜 E) [hK : CompleteSpace K] :
    orthogonalComplement (orthogonalComplement K) = K :=
  K.orthogonal_orthogonal

end Orthogonality

/-! ## Orthogonal projection -/

section OrthogonalProjection

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- The remainder of the orthogonal projection is in the orthogonal complement. -/
theorem projection_remainder_mem_orthogonal {𝕜' : Type*} [RCLike 𝕜']
    {E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace 𝕜' E']
    (K : Submodule 𝕜' E') [CompleteSpace K] (x : E') :
    x - ↑(K.orthogonalProjection x) ∈ Kᗮ :=
  K.sub_starProjection_mem_orthogonal x

end OrthogonalProjection

/-! ## Riesz representation theorem (Fréchet-Riesz) -/

section RieszRepresentation

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The **Fréchet-Riesz representation theorem** (map version): The conjugate-linear isometric
embedding `E → E*` sending `x ↦ (y ↦ ⟪x, y⟫)`. -/
abbrev toDualMap' : E →ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  InnerProductSpace.toDualMap 𝕜 E

/-- The Riesz map evaluates correctly. -/
theorem toDualMap_apply (x y : E) :
    toDualMap' (𝕜 := 𝕜) x y = @inner 𝕜 E _ x y :=
  InnerProductSpace.toDualMap_apply (𝕜 := 𝕜) (x := x) (y := y)

variable [CompleteSpace E]

/-- **Fréchet-Riesz representation theorem**: For a Hilbert space (complete inner product space),
the map `x ↦ ⟪x, ·⟫` is a conjugate-linear isometric *equivalence* between `E` and its
continuous dual `E*`. This means every continuous linear functional `f ∈ E*` has a unique
Riesz representer `y ∈ E` such that `f(x) = ⟪y, x⟫` for all `x`. -/
abbrev toDual : E ≃ₗᵢ⋆[𝕜] StrongDual 𝕜 E :=
  InnerProductSpace.toDual 𝕜 E

/-- The Riesz equivalence evaluates correctly. -/
theorem toDual_apply (x y : E) :
    toDual (𝕜 := 𝕜) x y = @inner 𝕜 E _ x y :=
  InnerProductSpace.toDual_apply (𝕜 := 𝕜) (x := x) (y := y)

/-- The inverse Riesz map: given `f ∈ E*`, find the unique `y ∈ E` with `f = ⟪y, ·⟫`. -/
theorem toDual_symm_apply (x : E) (f : StrongDual 𝕜 E) :
    @inner 𝕜 E _ ((toDual (𝕜 := 𝕜)).symm f) x = f x :=
  InnerProductSpace.toDual_symm_apply (𝕜 := 𝕜)

end RieszRepresentation

/-! ## Orthonormal sets and Bessel's inequality -/

section OrthonormalSets

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- A family of vectors is orthonormal if each has norm 1 and distinct vectors are orthogonal. -/
abbrev IsOrthonormalFamily (v : ι → E) : Prop := Orthonormal 𝕜 v

/-- An orthonormal family has unit norms. -/
theorem orthonormal_norm_eq_one {v : ι → E} (hv : IsOrthonormalFamily (𝕜 := 𝕜) v) (i : ι) :
    ‖v i‖ = 1 :=
  hv.1 i

/-- An orthonormal family has orthogonal distinct elements. -/
theorem orthonormal_inner_eq_zero {v : ι → E} (hv : IsOrthonormalFamily (𝕜 := 𝕜) v)
    {i j : ι} (hij : i ≠ j) :
    @inner 𝕜 E _ (v i) (v j) = 0 :=
  hv.2 hij

/-- **Bessel's inequality** (finite sum version): For an orthonormal family `v` and any
vector `x`, the sum of `‖⟪v i, x⟫‖²` over a finite set is at most `‖x‖²`. -/
theorem bessel_finite {v : ι → E} (hv : IsOrthonormalFamily (𝕜 := 𝕜) v)
    (x : E) {s : Finset ι} :
    ∑ i ∈ s, ‖@inner 𝕜 E _ (v i) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.sum_inner_products_le x

/-- **Bessel's inequality** (infinite sum version): For an orthonormal family `v` and any
vector `x`, the series `∑ᵢ ‖⟪v i, x⟫‖²` converges and is at most `‖x‖²`. -/
theorem bessel_tsum {v : ι → E} (hv : IsOrthonormalFamily (𝕜 := 𝕜) v) (x : E) :
    ∑' i, ‖@inner 𝕜 E _ (v i) x‖ ^ 2 ≤ ‖x‖ ^ 2 :=
  hv.tsum_inner_products_le x

/-- The sum in Bessel's inequality is summable. -/
theorem bessel_summable {v : ι → E} (hv : IsOrthonormalFamily (𝕜 := 𝕜) v) (x : E) :
    Summable (fun i => ‖@inner 𝕜 E _ (v i) x‖ ^ 2) :=
  hv.inner_products_summable x

end OrthonormalSets

/-! ## Hilbert bases and Parseval's identity -/

section HilbertBases

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {ι : Type*}

/-- A Hilbert basis is an isometric isomorphism between `E` and `ℓ²(ι, 𝕜)`. -/
abbrev HilbertBasisType := HilbertBasis ι 𝕜 E

/-- A Hilbert basis is orthonormal. -/
theorem hilbertBasis_orthonormal (b : HilbertBasis ι 𝕜 E) :
    Orthonormal 𝕜 b :=
  b.orthonormal

/-- Fourier coefficients: the `i`-th coefficient of `x` with respect to a Hilbert basis. -/
theorem hilbertBasis_repr_apply (b : HilbertBasis ι 𝕜 E) (x : E) (i : ι) :
    b.repr x i = @inner 𝕜 E _ (b i) x :=
  b.repr_apply_apply x i

/-- **Parseval's identity** (Fourier expansion): Every vector `x` in a Hilbert space can be
expanded in terms of a Hilbert basis `b`:
  `x = ∑ᵢ (b.repr x i) • bᵢ` (convergent series). -/
theorem parseval_expansion (b : HilbertBasis ι 𝕜 E) (x : E) :
    HasSum (fun i => (b.repr x i) • b i) x :=
  b.hasSum_repr x

/-- **Parseval's identity** (inner product form): For a Hilbert basis `b`,
  `⟪x, y⟫ = ∑ᵢ ⟪x, bᵢ⟫ * ⟪bᵢ, y⟫`. -/
theorem parseval_inner (b : HilbertBasis ι 𝕜 E) (x y : E) :
    HasSum (fun i => @inner 𝕜 E _ x (b i) * @inner 𝕜 E _ (b i) y)
      (@inner 𝕜 E _ x y) :=
  b.hasSum_inner_mul_inner x y

/-- Construction of a Hilbert basis from an orthonormal family with dense span. -/
abbrev hilbertBasisMk [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalClosure) :
    HilbertBasis ι 𝕜 E :=
  HilbertBasis.mk hv hsp

/-- The Hilbert basis from `hilbertBasisMk` agrees with the original family. -/
theorem hilbertBasisMk_coe [CompleteSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (hsp : ⊤ ≤ (Submodule.span 𝕜 (Set.range v)).topologicalClosure) :
    ⇑(hilbertBasisMk hv hsp) = v :=
  HilbertBasis.coe_mk hv hsp

/-- Every Hilbert space admits a Hilbert basis. -/
theorem exists_hilbertBasis' [CompleteSpace E] :
    ∃ (w : Set E) (b : HilbertBasis w 𝕜 E), ⇑b = ((↑) : w → E) :=
  _root_.exists_hilbertBasis 𝕜 E

end HilbertBases

end HilbertSpaces
