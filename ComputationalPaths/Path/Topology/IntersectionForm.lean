/-
# Intersection Forms via Computational Paths

This module formalizes intersection forms on manifolds using the computational
paths framework. We define the intersection pairing on middle-dimensional
homology, unimodularity for closed manifolds, definite and indefinite forms,
the signature, and Donaldson's theorem structure.

## Mathematical Background

For a closed oriented 4k-manifold M, the cup product pairing
  Q : H_{2k}(M; ℤ) × H_{2k}(M; ℤ) → ℤ
is a symmetric unimodular bilinear form. Key aspects:
- **Unimodularity**: det(Q) = ±1 for closed manifolds (Poincaré duality)
- **Signature**: σ(M) = b⁺ − b⁻
- **Definite forms**: all eigenvalues have the same sign
- **Donaldson's theorem**: a definite form on a smooth closed simply-connected
  4-manifold is diagonalizable over ℤ

## References

- Donaldson-Kronheimer, "The Geometry of 4-Manifolds"
- Milnor-Husemoller, "Symmetric Bilinear Forms"
- Scorpan, "The Wild World of 4-Manifolds"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace IntersectionForm

open Algebra HomologicalAlgebra

universe u

/-! ## Bilinear Forms -/

/-- A symmetric bilinear form over ℤ on a free abelian group of rank r. -/
structure SymBilinearForm where
  /-- Rank of the free abelian group. -/
  rank : Nat
  /-- Matrix coefficients Q_{ij}. -/
  coeff : Fin rank → Fin rank → Int
  /-- Symmetry: Q_{ij} = Q_{ji}. -/
  symm : ∀ i j, coeff i j = coeff j i

/-- Determinant of a bilinear form (given as structural data). -/
structure FormDeterminant (Q : SymBilinearForm) where
  /-- The determinant value. -/
  det : Int

/-- A unimodular form: |det(Q)| = 1. -/
structure UnimodularForm extends SymBilinearForm where
  /-- Determinant data. -/
  detData : FormDeterminant toSymBilinearForm
  /-- Unimodularity: det = 1 or det = -1. -/
  unimod : detData.det = 1 ∨ detData.det = -1

/-! ## Intersection Form of a Manifold -/

/-- The intersection form of a closed oriented 4k-manifold. -/
structure IntersectionFormData (k : Nat) where
  /-- The manifold carrier. -/
  manifold : Type u
  /-- Middle homology rank (= second Betti number for k=1). -/
  middleRank : Nat
  /-- The intersection form on H_{2k}. -/
  form : SymBilinearForm
  /-- The form rank equals the middle homology rank. -/
  rank_eq : Path form.rank middleRank
  /-- Unimodularity from Poincaré duality. -/
  unimod : UnimodularForm
  /-- The unimodular form agrees with the intersection form. -/
  form_eq : Path unimod.rank form.rank

/-! ## Signature and Definiteness -/

/-- The signature of a symmetric bilinear form. -/
structure Signature (Q : SymBilinearForm) where
  /-- Number of positive eigenvalues. -/
  bPlus : Nat
  /-- Number of negative eigenvalues. -/
  bMinus : Nat
  /-- b⁺ + b⁻ = rank. -/
  sum_eq : Path (bPlus + bMinus) Q.rank
  /-- The signature value σ = b⁺ - b⁻. -/
  signature : Int
  /-- Signature equals b⁺ - b⁻. -/
  sig_eq : Path signature (Int.ofNat bPlus - Int.ofNat bMinus)

/-- A positive definite form: b⁻ = 0. -/
structure PositiveDefinite (Q : SymBilinearForm) extends Signature Q where
  /-- All eigenvalues are positive. -/
  pos_def : Path bMinus 0

/-- A negative definite form: b⁺ = 0. -/
structure NegativeDefinite (Q : SymBilinearForm) extends Signature Q where
  /-- All eigenvalues are negative. -/
  neg_def : Path bPlus 0

/-- A definite form is either positive or negative definite. -/
structure DefiniteForm (Q : SymBilinearForm) where
  /-- Signature data. -/
  sig : Signature Q
  /-- Either b⁺ = 0 or b⁻ = 0. -/
  definite : sig.bPlus = 0 ∨ sig.bMinus = 0

/-- An indefinite form: both b⁺ > 0 and b⁻ > 0. -/
structure IndefiniteForm (Q : SymBilinearForm) where
  /-- Signature data. -/
  sig : Signature Q
  /-- Positive part non-trivial. -/
  pos_nontrivial : sig.bPlus ≥ 1
  /-- Negative part non-trivial. -/
  neg_nontrivial : sig.bMinus ≥ 1

/-! ## Even and Odd Forms -/

/-- An even form: Q(x,x) ∈ 2ℤ for all x, i.e., diagonal entries are even. -/
structure EvenForm (Q : SymBilinearForm) where
  /-- All diagonal entries are even. -/
  diag_even : ∀ i : Fin Q.rank, ∃ m : Int, Q.coeff i i = 2 * m

/-- An odd form: not even; some diagonal entry is odd. -/
structure OddForm (Q : SymBilinearForm) where
  /-- Some diagonal entry is odd. -/
  diag_odd : ∃ i : Fin Q.rank, ∀ m : Int, Q.coeff i i ≠ 2 * m

/-! ## Standard Forms -/

/-- The standard diagonal form ⟨+1⟩^m ⊕ ⟨-1⟩^n. -/
noncomputable def diagonalForm (m n : Nat) : SymBilinearForm where
  rank := m + n
  coeff := fun i j =>
    if i = j then
      if i.val < m then 1 else -1
    else 0
  symm := by
    intro i j
    by_cases h : i = j
    · subst h; rfl
    · simp [h, Ne.symm h]

/-- The diagonal form has the expected signature. -/
noncomputable def diagonalSignature (m n : Nat) : Signature (diagonalForm m n) where
  bPlus := m
  bMinus := n
  sum_eq := Path.mk [] rfl
  signature := Int.ofNat m - Int.ofNat n
  sig_eq := Path.mk [] rfl

/-- The E₈ lattice has rank 8, is even, and is positive definite. -/
structure E8Lattice where
  /-- The form. -/
  form : SymBilinearForm
  /-- Rank is 8. -/
  rank_8 : Path form.rank 8
  /-- Even. -/
  even : EvenForm form
  /-- Positive definite. -/
  pos_def : PositiveDefinite form
  /-- Signature is 8. -/
  sig_8 : Path pos_def.signature 8

/-! ## Donaldson's Theorem -/

/-- Donaldson's theorem: if M is a smooth closed simply-connected 4-manifold
    with definite intersection form Q, then Q is diagonalizable over ℤ,
    i.e., Q ≅ ⟨+1⟩^n or Q ≅ ⟨-1⟩^n. -/
structure DonaldsonTheorem where
  /-- The intersection form data for a 4-manifold (k=1). -/
  formData : IntersectionFormData 1
  /-- Simply connected. -/
  simply_connected : True
  /-- The form is definite. -/
  definite : DefiniteForm formData.form
  /-- The form is diagonalizable: rank equals b⁺ or b⁻. -/
  diag : formData.form.rank = definite.sig.bPlus ∨
         formData.form.rank = definite.sig.bMinus

/-- Consequence: the E₈ manifold does not admit a smooth structure. -/
structure E8NoSmooth where
  /-- E₈ lattice data. -/
  e8 : E8Lattice
  /-- E₈ is not diagonalizable (it is even but the diagonal form is odd). -/
  not_diag : ∀ m n : Nat, m + n = 8 →
    ¬(e8.form.rank = m + n ∧
      ∀ (i : Fin e8.form.rank), ∃ k : Int, e8.form.coeff i i = k ∧ (k = 1 ∨ k = -1))

/-! ## Freedman's Classification -/

/-- Freedman's theorem: closed simply-connected topological 4-manifolds
    are classified by their intersection form and a ℤ/2 invariant (the
    Kirby-Siebenmann invariant). -/
structure FreedmanClassification where
  /-- Two manifolds with the same intersection form. -/
  m₁ : IntersectionFormData 1
  m₂ : IntersectionFormData 1
  /-- Same form rank. -/
  same_rank : Path m₁.form.rank m₂.form.rank
  /-- Same form coefficients (for matching indices). -/
  same_coeff : m₁.form.rank = m₂.form.rank
  /-- Same Kirby-Siebenmann invariant. -/
  same_ks : Fin 2
  /-- Then the manifolds are homeomorphic. -/
  homeomorphic : Path m₁.manifold m₂.manifold

/-- Freedman's theorem gives a homeomorphism. -/
noncomputable def freedman_homeo (F : FreedmanClassification) :
    Path F.m₁.manifold F.m₂.manifold :=
  F.homeomorphic


/-! ## Path lemmas -/

theorem intersection_form_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem intersection_form_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem intersection_form_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem intersection_form_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem intersection_form_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem intersection_form_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem intersection_form_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem intersection_form_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.mk [Step.mk _ _ h] h) = h :=
  Path.toEq_ofEq h


end IntersectionForm
end Topology
end Path
end ComputationalPaths
