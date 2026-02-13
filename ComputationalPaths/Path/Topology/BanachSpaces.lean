/-
# Banach Spaces: Functional Analysis Foundations

This file provides a Lean 4 formalization interface for:
- Banach spaces (complete normed spaces),
- bounded linear operators,
- the Hahn-Banach extension theorem,
- the open mapping theorem (Banach's theorem),
- the closed graph theorem,
- the uniform boundedness principle (Banach-Steinhaus).

All results are proved without `sorry` and without adding axioms.
They wrap existing Mathlib definitions and theorems.

## References

- Conway, *A Course in Functional Analysis*
- Rudin, *Functional Analysis*
- Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*
-/

import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Completeness

open scoped NNReal ENNReal
open Filter Topology

noncomputable section

namespace BanachSpaces

/-! ## Banach space basics -/

section BanachBasics

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A Banach space is a complete normed vector space. -/
abbrev IsBanachSpace : Prop := CompleteSpace E

/-- The norm on a normed space, as an explicit function. -/
abbrev normOf (x : E) : ℝ := ‖x‖

@[simp]
theorem normOf_zero : normOf (0 : E) = 0 := norm_zero

theorem normOf_nonneg (x : E) : 0 ≤ normOf x := norm_nonneg x

theorem normOf_triangle (x y : E) : normOf (x + y) ≤ normOf x + normOf y :=
  norm_add_le x y

theorem normOf_smul (c : 𝕜) (x : E) : normOf (c • x) = ‖c‖ * normOf x :=
  norm_smul c x

end BanachBasics

/-! ## Bounded linear operators -/

section BoundedLinearOperators

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The type of bounded (continuous) linear maps `E →L[𝕜] F` between normed spaces. -/
abbrev BoundedLinearMap' (𝕜 : Type*) (E : Type*) (F : Type*) [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] : Type _ := E →L[𝕜] F

/-- The operator norm of a bounded linear map. -/
abbrev opNormOf (f : E →L[𝕜] F) : ℝ := ‖f‖

theorem opNorm_nonneg (f : E →L[𝕜] F) : 0 ≤ opNormOf f :=
  norm_nonneg f

theorem le_opNorm (f : E →L[𝕜] F) (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_opNorm x

theorem opNorm_comp_le {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
    (f : F →L[𝕜] G) (g : E →L[𝕜] F) :
    ‖f.comp g‖ ≤ ‖f‖ * ‖g‖ :=
  ContinuousLinearMap.opNorm_comp_le f g

/-- The operator norm satisfies submultiplicativity under composition. -/
theorem opNorm_comp_sub (f : E →L[𝕜] F) (g : E →L[𝕜] F) :
    ‖f - g‖ = ‖g - f‖ := by rw [norm_sub_rev]

end BoundedLinearOperators

/-! ## Hahn-Banach theorem -/

section HahnBanach

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Hahn-Banach theorem** (real case): A continuous linear functional on a subspace of a
normed space over `ℝ` can be extended to the whole space preserving the norm. -/
theorem hahnBanach_real (p : Subspace ℝ E) (f : StrongDual ℝ p) :
    ∃ g : StrongDual ℝ E, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  Real.exists_extension_norm_eq p f

variable {𝕜 : Type*} [RCLike 𝕜]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Hahn-Banach theorem** (general case for `ℝ` or `ℂ`): A continuous linear functional on a
subspace can be extended to the whole space with the same norm. -/
theorem hahnBanach_rclike (p : Subspace 𝕜 F) (f : StrongDual 𝕜 p) :
    ∃ g : StrongDual 𝕜 F, (∀ x : p, g x = f x) ∧ ‖g‖ = ‖f‖ :=
  exists_extension_norm_eq p f

/-- **Existence of norming functionals**: For any nonzero `x`, there exists a continuous
linear functional `g` of norm 1 with `g x = ‖x‖`. -/
theorem exists_norming_functional (x : F) (hx : x ≠ 0) :
    ∃ g : StrongDual 𝕜 F, ‖g‖ = 1 ∧ g x = ‖x‖ :=
  exists_dual_vector 𝕜 x hx

end HahnBanach

/-! ## Open mapping theorem -/

section OpenMapping

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Banach open mapping theorem**: A surjective bounded linear map between Banach spaces
is an open map. -/
theorem open_mapping (f : E →L[𝕜] F) (hsurj : Function.Surjective f) :
    IsOpenMap f :=
  f.isOpenMap hsurj

/-- **Banach open mapping theorem** (quotient form): A surjective bounded linear map between
Banach spaces is a quotient map. -/
theorem surjective_isQuotientMap (f : E →L[𝕜] F) (hsurj : Function.Surjective f) :
    IsQuotientMap f :=
  f.isQuotientMap hsurj

/-- **Bounded right inverse**: A surjective bounded linear map between Banach spaces has a
bounded (nonlinear) right inverse. -/
theorem exists_bounded_right_inverse (f : E →L[𝕜] F)
    (hsurj : LinearMap.range f = ⊤) :
    ∃ fsymm : f.NonlinearRightInverse, 0 < fsymm.nnnorm :=
  f.exists_nonlinearRightInverse_of_surjective hsurj

/-- **Bounded inverse theorem**: A bijective bounded linear map between Banach spaces
has a bounded inverse and is thus a topological isomorphism. -/
theorem bounded_inverse (f : E →L[𝕜] F)
    (hinj : LinearMap.ker f = ⊥) (hsurj : LinearMap.range f = ⊤) :
    ∃ e : E ≃L[𝕜] F, (e : E →L[𝕜] F) = f :=
  ⟨ContinuousLinearEquiv.ofBijective f hinj hsurj, by ext; rfl⟩

/-- Interior of preimage under a surjective bounded linear map. -/
theorem interior_preimage_surjective (f : E →L[𝕜] F) (hsurj : Function.Surjective f)
    (s : Set F) :
    interior (f ⁻¹' s) = f ⁻¹' interior s :=
  f.interior_preimage hsurj s

/-- Closure of preimage under a surjective bounded linear map. -/
theorem closure_preimage_surjective (f : E →L[𝕜] F) (hsurj : Function.Surjective f)
    (s : Set F) :
    closure (f ⁻¹' s) = f ⁻¹' closure s :=
  f.closure_preimage hsurj s

end OpenMapping

/-! ## Closed graph theorem -/

section ClosedGraphTheorem

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- **Closed graph theorem**: A linear map between Banach spaces whose graph is closed
is continuous. -/
theorem closed_graph_theorem (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) :
    Continuous g :=
  g.continuous_of_isClosed_graph hg

/-- **Closed graph theorem** (sequential version): A linear map `g` between Banach spaces
is continuous if whenever `uₙ → x` and `g(uₙ) → y` implies `y = g(x)`. -/
theorem closed_graph_sequential (g : E →ₗ[𝕜] F)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    Continuous g :=
  g.continuous_of_seq_closed_graph hg

/-- Upgrade a linear map with closed graph to a continuous linear map. -/
abbrev continuousLinearMapOfClosedGraph (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) : E →L[𝕜] F :=
  ContinuousLinearMap.ofIsClosedGraph hg

@[simp]
theorem coe_continuousLinearMapOfClosedGraph (g : E →ₗ[𝕜] F)
    (hg : IsClosed (g.graph : Set (E × F))) :
    ⇑(continuousLinearMapOfClosedGraph g hg) = g :=
  ContinuousLinearMap.coeFn_ofIsClosedGraph hg

/-- Upgrade a linear map satisfying the sequential closed graph condition. -/
abbrev continuousLinearMapOfSeqClosedGraph (g : E →ₗ[𝕜] F)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) : E →L[𝕜] F :=
  ContinuousLinearMap.ofSeqClosedGraph hg

@[simp]
theorem coe_continuousLinearMapOfSeqClosedGraph (g : E →ₗ[𝕜] F)
    (hg : ∀ (u : ℕ → E) (x : E) (y : F),
      Tendsto u atTop (𝓝 x) → Tendsto (g ∘ u) atTop (𝓝 y) → y = g x) :
    ⇑(continuousLinearMapOfSeqClosedGraph g hg) = g :=
  ContinuousLinearMap.coeFn_ofSeqClosedGraph hg

end ClosedGraphTheorem

/-! ## Uniform boundedness principle (Banach-Steinhaus) -/

section UniformBoundedness

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Uniform boundedness principle / Banach-Steinhaus theorem**: If a family of continuous
linear maps from a Banach space into a normed space is pointwise bounded, then the operator
norms are uniformly bounded. -/
theorem uniform_boundedness {ι : Type*} [CompleteSpace E] (g : ι → E →L[𝕜] F)
    (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' :=
  banach_steinhaus h

/-- **Banach-Steinhaus** (NNNorm / ENNReal version): If a family of continuous linear maps
from a Banach space is pointwise bounded (in the `ℝ≥0∞` sense), then the supremum of
their norms is finite. -/
theorem uniform_boundedness_iSup_nnnorm {ι : Type*} [CompleteSpace E] (g : ι → E →L[𝕜] F)
    (h : ∀ x, (⨆ i, (‖g i x‖₊ : ℝ≥0∞)) < ∞) :
    (⨆ i, (‖g i‖₊ : ℝ≥0∞)) < ∞ :=
  banach_steinhaus_iSup_nnnorm h

/-- **Pointwise limit of bounded linear maps**: Given a sequence of bounded linear maps from
a Banach space which converges pointwise, the limit is also a bounded linear map. -/
abbrev continuousLinearMapOfPointwiseLimit {α : Type*} [CompleteSpace E]
    [T2Space F] {l : Filter α} [l.IsCountablyGenerated] [l.NeBot]
    (g : α → E →L[𝕜] F) {f : E → F}
    (h : Tendsto (fun n x => g n x) l (𝓝 f)) : E →L[𝕜] F :=
  continuousLinearMapOfTendsto g h

end UniformBoundedness

end BanachSpaces
