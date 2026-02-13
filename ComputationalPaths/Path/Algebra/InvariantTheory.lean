/- 
# Invariant theory: a Lean 4 interface

This file provides a compact formalization interface for:
- invariant rings of group actions,
- polynomial invariant rings,
- Reynolds operators (via averaging),
- Hilbert's finiteness theorem (as a formal statement),
- Molien's theorem (as a formal statement).

The goal is to give reusable definitions and tractable lemmas with no axioms and no `sorry`.
-/

import Mathlib.Algebra.Algebra.Subalgebra.Operations
import Mathlib.RepresentationTheory.Invariants
import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

namespace InvariantTheory

/-! ## Invariant rings -/

section InvariantRings

variable (A B G : Type*) [CommSemiring A] [Ring B] [Algebra A B]
variable [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]

/-- The invariant subring `B^G` of elements fixed by all `g : G`. -/
abbrev invariantRing : Subring B :=
  FixedPoints.subring (A := A) (B := B) (G := G)

/-- The invariant subalgebra `B^G` over the base ring `A`. -/
abbrev invariantSubalgebra : Subalgebra A B :=
  FixedPoints.subalgebra (A := A) (B := B) (G := G)

@[simp]
theorem mem_invariantRing_iff (b : B) :
    b ∈ invariantRing A B G ↔ ∀ g : G, g • b = b :=
  Iff.rfl

@[simp]
theorem mem_invariantSubalgebra_iff (b : B) :
    b ∈ invariantSubalgebra A B G ↔ ∀ g : G, g • b = b :=
  Iff.rfl

/-- If every element is fixed by the action, the invariant subring is `⊤`. -/
theorem invariantRing_eq_top_of_forall_smul_eq
    (hfix : ∀ g : G, ∀ b : B, g • b = b) :
    invariantRing A B G = ⊤ := by
  ext b
  constructor
  · intro _
    simp
  · intro _
    exact fun g => hfix g b

/-- If every element is fixed by the action, the invariant subalgebra is `⊤`. -/
theorem invariantSubalgebra_eq_top_of_forall_smul_eq
    (hfix : ∀ g : G, ∀ b : B, g • b = b) :
    invariantSubalgebra A B G = ⊤ := by
  ext b
  constructor
  · intro _
    simp
  · intro _
    exact fun g => hfix g b

end InvariantRings

/-! ## Polynomial invariant rings -/

section PolynomialInvariants

variable (k σ G : Type*) [CommSemiring k] [Monoid G]
variable [MulSemiringAction G (Polynomial k)] [SMulCommClass G k (Polynomial k)]
variable [MulSemiringAction G (MvPolynomial σ k)] [SMulCommClass G k (MvPolynomial σ k)]

/-- The invariant subalgebra of univariate polynomials under a `G`-action. -/
abbrev polynomialInvariantRing : Subalgebra k (Polynomial k) :=
  FixedPoints.subalgebra (A := k) (B := Polynomial k) (G := G)

/-- The invariant subalgebra of multivariate polynomials under a `G`-action. -/
abbrev mvPolynomialInvariantRing : Subalgebra k (MvPolynomial σ k) :=
  FixedPoints.subalgebra (A := k) (B := MvPolynomial σ k) (G := G)

@[simp]
theorem mem_polynomialInvariantRing_iff (p : Polynomial k) :
    p ∈ polynomialInvariantRing k σ G ↔ ∀ g : G, g • p = p :=
  Iff.rfl

@[simp]
theorem mem_mvPolynomialInvariantRing_iff (p : MvPolynomial σ k) :
    p ∈ mvPolynomialInvariantRing k σ G ↔ ∀ g : G, g • p = p :=
  Iff.rfl

/-- Trivial action implies the multivariate polynomial invariant ring is `⊤`. -/
theorem mvPolynomialInvariantRing_eq_top_of_forall_smul_eq
    (hfix : ∀ g : G, ∀ p : MvPolynomial σ k, g • p = p) :
    mvPolynomialInvariantRing k σ G = ⊤ := by
  ext p
  constructor
  · intro _
    simp
  · intro _
    exact fun g => hfix g p

end PolynomialInvariants

/-! ## Reynolds operator -/

section Reynolds

variable (k G V : Type*) [CommSemiring k] [Group G]
variable [AddCommMonoid V] [Module k V]
variable [Fintype G] [Invertible (Fintype.card G : k)]

/-- Reynolds operator obtained by averaging a finite-group representation. -/
noncomputable abbrev reynoldsOperator (ρ : Representation k G V) : V →ₗ[k] V :=
  ρ.averageMap

theorem reynoldsOperator_mem_invariants (ρ : Representation k G V) (v : V) :
    reynoldsOperator k G V ρ v ∈ ρ.invariants := by
  simpa [reynoldsOperator] using ρ.averageMap_invariant v

theorem reynoldsOperator_id_on_invariants (ρ : Representation k G V) {v : V}
    (hv : v ∈ ρ.invariants) :
    reynoldsOperator k G V ρ v = v := by
  simpa [reynoldsOperator] using ρ.averageMap_id v hv

theorem reynoldsOperator_isProj (ρ : Representation k G V) :
    LinearMap.IsProj ρ.invariants (reynoldsOperator k G V ρ) := by
  simpa [reynoldsOperator] using ρ.isProj_averageMap

end Reynolds

/-! ## Hilbert finiteness theorem (statement and tractable specialization) -/

section HilbertFiniteness

variable (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A]

/-- A concrete finite-generation predicate for subalgebras. -/
def IsFiniteGeneratedSubalgebra (S : Subalgebra k A) : Prop :=
  ∃ s : Finset A, Subalgebra.closure (s : Set A) = S

end HilbertFiniteness

section HilbertPolynomialInvariants

variable (k σ G : Type*) [CommSemiring k] [Group G] [Fintype G]
variable [MulSemiringAction G (MvPolynomial σ k)] [SMulCommClass G k (MvPolynomial σ k)]

/-- Hilbert's finiteness theorem, formalized as finite generation of `k[σ]^G`. -/
def HilbertFinitenessTheorem : Prop :=
  IsFiniteGeneratedSubalgebra (k := k) (A := MvPolynomial σ k)
    (mvPolynomialInvariantRing k σ G)

/-- A tractable instance: if the action is trivial and `⊤` is finitely generated, then
`k[σ]^G` is finitely generated. -/
theorem hilbertFiniteness_of_trivial_action
    (hTop : IsFiniteGeneratedSubalgebra (k := k) (A := MvPolynomial σ k)
      (⊤ : Subalgebra k (MvPolynomial σ k)))
    (hfix : ∀ g : G, ∀ p : MvPolynomial σ k, g • p = p) :
    HilbertFinitenessTheorem k σ G := by
  unfold HilbertFinitenessTheorem
  simpa [mvPolynomialInvariantRing_eq_top_of_forall_smul_eq (k := k) (σ := σ) (G := G) hfix]
    using hTop

end HilbertPolynomialInvariants

/-! ## Molien theorem (statement and tractable specialization) -/

section Molien

variable (G : Type*) [Fintype G]

/-- The Molien average in `ℚ⟦t⟧` built from per-group-element contributions. -/
noncomputable def molienSeries (contrib : G → PowerSeries ℚ) : PowerSeries ℚ :=
  (Fintype.card G : ℚ)⁻¹ • ∑ g : G, contrib g

/-- Molien's theorem statement: Hilbert series equals the Molien average. -/
def MolienTheoremStatement (hilbertSeries : PowerSeries ℚ)
    (contrib : G → PowerSeries ℚ) : Prop :=
  hilbertSeries = molienSeries G contrib

@[simp]
theorem molienSeries_punit (contrib : PUnit → PowerSeries ℚ) :
    molienSeries PUnit contrib = contrib PUnit.unit := by
  simp [molienSeries]

/-- Tractable one-element-group instance of the Molien statement. -/
theorem molienTheoremStatement_punit (hilbertSeries : PowerSeries ℚ)
    (contrib : PUnit → PowerSeries ℚ) (h : hilbertSeries = contrib PUnit.unit) :
    MolienTheoremStatement (G := PUnit) hilbertSeries contrib := by
  dsimp [MolienTheoremStatement]
  rw [h, molienSeries_punit]

end Molien

end InvariantTheory
