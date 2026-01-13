/-
# Derived Product and Sigma Type Theorems

This module provides axiom-free, sorry-free theorems about product and sigma
types in the computational paths framework. All results are derived from
the primitive rewrite steps.

## Main Results

### Product Theorems
- `rweq_prodMk_trans`: Product path composition factors through components
- `rweq_prodMk_symm`: Product path inversion factors through components
- `rweq_prod_rec_comp`: Product recursor composition
- `rweq_prodMk_unique`: Uniqueness of product paths

### Sigma Theorems
- `rweq_sigmaMk_unique`: Uniqueness of sigma paths from projections
- `rweq_sigmaFst_sigmaMk`: First projection of sigma constructor

### Naturality
- `rweq_fst_natural`: Naturality of first projection
- `rweq_snd_natural`: Naturality of second projection

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.GroupoidDerived

namespace ComputationalPaths
namespace Path
namespace ProductSigmaDerived

open Step

universe u

variable {A : Type u} {B : Type u}

/-! ## Product Composition Laws

These theorems describe how product paths interact with composition. -/

/-- Product paths respect composition: expanded form.
    `prodMk (p · q) (r · s) ≈ mapLeft Prod.mk p b₁ · mapLeft Prod.mk q b₁ · mapRight Prod.mk a₃ r · mapRight Prod.mk a₃ s` -/
theorem rweq_prodMk_trans_expanded
    {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (p : Path a₁ a₂) (q : Path a₂ a₃)
    (r : Path b₁ b₂) (s : Path b₂ b₃) :
    RwEq (prodMk (trans p q) (trans r s))
         (trans (mapLeft Prod.mk p b₁)
           (trans (mapLeft Prod.mk q b₁)
             (trans (mapRight Prod.mk a₃ r) (mapRight Prod.mk a₃ s)))) := by
  simp only [prodMk]
  exact rweq_map2_trans Prod.mk p q r s

/-- Product paths respect symmetry componentwise.
    `symm (prodMk p q) ≈ prodMk (symm p) (symm q)` -/
theorem rweq_prodMk_symm_components
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (symm (prodMk p q))
         (prodMk (symm p) (symm q)) :=
  rweq_of_step (Step.prod_mk_symm p q)

/-- Reflexivity of product is product of reflexivities.
    `refl (a, b) = prodMk (refl a) (refl b)` -/
theorem rweq_prodMk_refl_refl (a : A) (b : B) :
    RwEq (prodMk (refl a) (refl b)) (refl (a, b)) :=
  rweq_of_eq (prodMk_refl_refl a b)

/-! ## Product Beta Laws

These theorems express the computation rules for product projections. -/

/-- First projection of product path equals first component.
    `fst (prodMk p q) ≈ p` -/
theorem rweq_fst_of_prodMk
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (fst (prodMk p q)) p :=
  rweq_fst_prodMk p q

/-- Second projection of product path equals second component.
    `snd (prodMk p q) ≈ q` -/
theorem rweq_snd_of_prodMk
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (snd (prodMk p q)) q :=
  rweq_snd_prodMk p q

/-- Product eta: reconstructing a product path from projections.
    `prodMk (fst p) (snd p) ≈ p` -/
theorem rweq_prodMk_fst_snd
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (prodMk (fst p) (snd p)) p :=
  rweq_prod_eta p

/-! ## Product Congruence Laws

These theorems show that RwEq is respected by product operations. -/

/-- Product constructor respects RwEq in first component. -/
theorem rweq_prodMk_congr_left
    {a₁ a₂ : A} {b₁ b₂ : B}
    {p p' : Path a₁ a₂} (q : Path b₁ b₂)
    (hp : RwEq p p') :
    RwEq (prodMk p q) (prodMk p' q) :=
  rweq_map2_of_rweq Prod.mk hp (RwEq.refl q)

/-- Product constructor respects RwEq in second component. -/
theorem rweq_prodMk_congr_right
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) {q q' : Path b₁ b₂}
    (hq : RwEq q q') :
    RwEq (prodMk p q) (prodMk p q') :=
  rweq_map2_of_rweq Prod.mk (RwEq.refl p) hq

/-- Product constructor respects RwEq in both components. -/
theorem rweq_prodMk_congr
    {a₁ a₂ : A} {b₁ b₂ : B}
    {p p' : Path a₁ a₂} {q q' : Path b₁ b₂}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (prodMk p q) (prodMk p' q') :=
  rweq_map2_of_rweq Prod.mk hp hq

/-! ## Product Projection Naturality

These theorems show projections commute with path operations. -/

/-- First projection is natural with respect to composition.
    `fst (p · q) ≈ fst p · fst q` -/
theorem rweq_fst_trans
    {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (p : Path (a₁, b₁) (a₂, b₂))
    (q : Path (a₂, b₂) (a₃, b₃)) :
    RwEq (fst (trans p q)) (trans (fst p) (fst q)) :=
  rweq_of_eq (congrArg_trans Prod.fst p q)

/-- Second projection is natural with respect to composition.
    `snd (p · q) ≈ snd p · snd q` -/
theorem rweq_snd_trans
    {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (p : Path (a₁, b₁) (a₂, b₂))
    (q : Path (a₂, b₂) (a₃, b₃)) :
    RwEq (snd (trans p q)) (trans (snd p) (snd q)) :=
  rweq_of_eq (congrArg_trans Prod.snd p q)

/-- First projection is natural with respect to symmetry.
    `fst (symm p) ≈ symm (fst p)` -/
theorem rweq_fst_symm
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (fst (symm p)) (symm (fst p)) :=
  rweq_of_eq (congrArg_symm Prod.fst p)

/-- Second projection is natural with respect to symmetry.
    `snd (symm p) ≈ symm (snd p)` -/
theorem rweq_snd_symm
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (snd (symm p)) (symm (snd p)) :=
  rweq_of_eq (congrArg_symm Prod.snd p)

/-! ## Sigma Type Laws

These theorems describe sigma (dependent pair) path properties. -/

variable {C : A → Type u}

/-- Sigma eta: reconstructing a sigma path from projections.
    `sigmaMk (sigmaFst p) (sigmaSnd p) ≈ p` -/
theorem rweq_sigmaMk_sigmaFst_sigmaSnd
    {a₁ a₂ : A} {c₁ : C a₁} {c₂ : C a₂}
    (p : Path (⟨a₁, c₁⟩ : Sigma C) ⟨a₂, c₂⟩) :
    RwEq (sigmaMk (sigmaFst p) (sigmaSnd p)) p :=
  rweq_sigma_eta p

/-- First projection beta for sigma.
    `sigmaFst (sigmaMk p q) ≈ ofEq p.toEq` -/
theorem rweq_sigmaFst_of_sigmaMk
    {a₁ a₂ : A} {c₁ : C a₁} {c₂ : C a₂}
    (p : Path a₁ a₂)
    (q : Path (transport p c₁) c₂) :
    RwEq (sigmaFst (sigmaMk (B := C) p q)) (ofEq p.toEq) :=
  rweq_sigma_fst_beta p q

/-! ## Mixed Product-Sigma Laws

Cross-cutting theorems involving both product and sigma types. -/

/-! ## Map2 Decomposition

Theorems about how map2 decomposes into mapLeft and mapRight. -/

/-- Map2 decomposition: map2 f p q factors through mapLeft and mapRight.
    `map2 f p q = mapLeft f p b₁ · mapRight f a₂ q` (by definition) -/
theorem rweq_map2_def
    {D : Type u} (f : A → B → D)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (map2 f p q)
         (trans (mapLeft f p b₁) (mapRight f a₂ q)) := by
  simp only [map2]
  apply RwEq.refl

/-- First projection of map2 Prod.mk equals first path.
    `fst (map2 Prod.mk p q) ≈ p` -/
theorem rweq_fst_map2_prodMk
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (fst (map2 Prod.mk p q)) p := by
  simp only [fst, map2]
  exact rweq_fst_prodMk p q

/-- Second projection of map2 Prod.mk equals second path.
    `snd (map2 Prod.mk p q) ≈ q` -/
theorem rweq_snd_map2_prodMk
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (snd (map2 Prod.mk p q)) q := by
  simp only [snd, map2]
  exact rweq_snd_prodMk p q

/-! ## Product Function Application

Theorems about applying functions to product paths. -/

/-- Uncurried function application respects product paths.
    `congrArg (uncurry f) (prodMk p q) ≈ map2 f p q` -/
theorem rweq_uncurry_prodMk
    {D : Type u} (f : A → B → D)
    {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (congrArg (Function.uncurry f) (prodMk p q))
         (map2 f p q) :=
  rweq_of_step (Step.prod_rec_beta f p q)

end ProductSigmaDerived
end Path
end ComputationalPaths
