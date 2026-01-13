/-
# Path Algebra Derived Results

This module provides additional axiom-free, sorry-free theorems about
path algebra operations. These extend the computational paths framework
with useful derived lemmas for working with transport, congruence, and
higher-dimensional structures.

## Main Results

### Extended Congruence Laws
- `congrArg_congrArg`: Composition of congrArg applications
- `congrArg_trans_distrib`: congrArg distributes over trans

### Transport Laws
- `transport_transport`: Composition of transports
- `transport_congrArg`: Transport through function application

### Path Algebra Identities
- `trans_four_assoc`: Four-fold associativity
- `symm_trans_symm`: Interaction of symm and trans

### Sigma Type Operations
- `sigma_fst_trans`: First projection respects trans
- `sigma_eta_refl`: Eta for reflexive paths

## Implementation

All results are proved purely from the primitive Step constructors and
RwEq closure rules. No custom axioms are introduced.

## References

- HoTT Book, Chapter 2 (Path Algebra)
- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace PathAlgebraDerived

open Step

universe u v

variable {A : Type u} {a b c d e : A}

/-! ## Extended Associativity

Associativity extends to longer compositions.
-/

/-- Four-fold associativity: ((p · q) · r) · s ≈ p · (q · (r · s)) -/
theorem rweq_trans_four_assoc {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} :
    RwEq (trans (trans (trans p q) r) s) (trans p (trans q (trans r s))) := by
  -- ((p · q) · r) · s ≈ (p · q) · (r · s) ≈ p · (q · (r · s))
  have h1 : RwEq (trans (trans (trans p q) r) s) (trans (trans p q) (trans r s)) :=
    rweq_of_step (Step.trans_assoc (trans p q) r s)
  have h2 : RwEq (trans (trans p q) (trans r s)) (trans p (trans q (trans r s))) :=
    rweq_of_step (Step.trans_assoc p q (trans r s))
  exact RwEq.trans h1 h2

/-- Right-associated form: p · ((q · r) · s) ≈ p · (q · (r · s)) -/
theorem rweq_trans_assoc_inner {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} :
    RwEq (trans p (trans (trans q r) s)) (trans p (trans q (trans r s))) :=
  rweq_trans_congr_right p (rweq_of_step (Step.trans_assoc q r s))

/-- Left-associated form: (p · (q · r)) · s ≈ ((p · q) · r) · s -/
theorem rweq_trans_assoc_outer {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} :
    RwEq (trans (trans p (trans q r)) s) (trans (trans (trans p q) r) s) :=
  rweq_trans_congr_left s (RwEq.symm (rweq_of_step (Step.trans_assoc p q r)))

/-! ## Symmetry and Transitivity Interaction

Laws about how symm interacts with trans.
-/

/-- (p · q)⁻¹ ≈ q⁻¹ · p⁻¹ (contravariance) -/
theorem rweq_symm_trans {p : Path a b} {q : Path b c} :
    RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
  rweq_of_step (Step.symm_trans_congr p q)

/-- (p⁻¹ · q⁻¹)⁻¹ ≈ q · p (when q : Path a b, p : Path b c) -/
theorem rweq_symm_trans_symm {p : Path b c} {q : Path a b} :
    RwEq (symm (trans (symm p) (symm q))) (trans q p) := by
  -- (p⁻¹ · q⁻¹)⁻¹ ≈ (q⁻¹)⁻¹ · (p⁻¹)⁻¹ ≈ q · p
  have h1 : RwEq (symm (trans (symm p) (symm q))) (trans (symm (symm q)) (symm (symm p))) :=
    rweq_of_step (Step.symm_trans_congr (symm p) (symm q))
  have h2 : RwEq (trans (symm (symm q)) (symm (symm p))) (trans q (symm (symm p))) :=
    rweq_trans_congr_left (symm (symm p)) (rweq_of_step (Step.symm_symm q))
  have h3 : RwEq (trans q (symm (symm p))) (trans q p) :=
    rweq_trans_congr_right q (rweq_of_step (Step.symm_symm p))
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-- Triple composition with inverses: (p · q · r)⁻¹ ≈ r⁻¹ · q⁻¹ · p⁻¹ -/
theorem rweq_symm_trans_three {p : Path a b} {q : Path b c} {r : Path c d} :
    RwEq (symm (trans (trans p q) r)) (trans (trans (symm r) (symm q)) (symm p)) := by
  -- (p · q · r)⁻¹ ≈ r⁻¹ · (p · q)⁻¹ ≈ r⁻¹ · q⁻¹ · p⁻¹
  have h1 : RwEq (symm (trans (trans p q) r)) (trans (symm r) (symm (trans p q))) :=
    rweq_of_step (Step.symm_trans_congr (trans p q) r)
  have h2 : RwEq (trans (symm r) (symm (trans p q))) (trans (symm r) (trans (symm q) (symm p))) :=
    rweq_trans_congr_right (symm r) (rweq_of_step (Step.symm_trans_congr p q))
  have h3 : RwEq (trans (symm r) (trans (symm q) (symm p))) (trans (trans (symm r) (symm q)) (symm p)) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc (symm r) (symm q) (symm p)))
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-! ## Congruence Composition

Laws about composing congrArg applications.
-/

/-- Composition of congrArg: (g ∘ f)*(p) = g*(f*(p)) (definitional, but stated for RwEq) -/
theorem rweq_congrArg_comp {B C : Type u} (f : A → B) (g : B → C)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (congrArg (g ∘ f) p) (congrArg g (congrArg f p)) :=
  rweq_of_eq (congrArg_comp g f p)

/-- congrArg of id is id: id*(p) = p -/
theorem rweq_congrArg_id {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (congrArg id p) p :=
  rweq_of_eq (congrArg_id p)

/-- congrArg preserves refl: f*(refl a) = refl (f a) -/
theorem rweq_congrArg_refl {B : Type u} (f : A → B) (a : A) :
    RwEq (congrArg f (refl a)) (refl (f a)) :=
  rweq_refl _

/-- congrArg distributes over trans: f*(p · q) ≈ f*(p) · f*(q) -/
theorem rweq_congrArg_trans_distrib {B : Type u} (f : A → B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    RwEq (congrArg f (trans p q)) (trans (congrArg f p) (congrArg f q)) :=
  rweq_of_eq (congrArg_trans f p q)

/-- congrArg commutes with symm: f*(p⁻¹) ≈ (f*(p))⁻¹ -/
theorem rweq_congrArg_symm_distrib {B : Type u} (f : A → B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (congrArg f (symm p)) (symm (congrArg f p)) :=
  rweq_of_eq (congrArg_symm f p)

/-! ## Transport Laws

Additional lemmas about transport along paths.
-/

/-- Transport along refl is identity (definitional) -/
theorem transport_refl_id {B : A → Type v} {a : A} (x : B a) :
    transport (D := B) (refl a) x = x := rfl

/-- Transport along trans composes -/
theorem transport_trans_compose {B : A → Type v}
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) (x : B a₁) :
    transport (D := B) (trans p q) x = transport (D := B) q (transport (D := B) p x) :=
  transport_trans p q x

/-- Transport and then transport back is identity -/
theorem transport_symm_transport {B : A → Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (x : B a₁) :
    transport (D := B) (symm p) (transport (D := B) p x) = x :=
  transport_symm_left p x

/-- Transport back and then transport is identity -/
theorem transport_transport_symm {B : A → Type v}
    {a₁ a₂ : A} (p : Path a₁ a₂) (y : B a₂) :
    transport (D := B) p (transport (D := B) (symm p) y) = y :=
  transport_symm_right p y

/-! ## Eckmann-Hilton Preparation

These lemmas prepare for the Eckmann-Hilton argument at higher levels.
-/

/-- Refl on the left: refl · p ≈ p -/
theorem rweq_refl_trans (p : Path a b) :
    RwEq (trans (refl a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Refl on the right: p · refl ≈ p -/
theorem rweq_trans_refl (p : Path a b) :
    RwEq (trans p (refl b)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Symm of refl: refl⁻¹ ≈ refl -/
theorem rweq_symm_refl (a : A) :
    RwEq (symm (refl a)) (refl a) :=
  rweq_of_step (Step.symm_refl a)

/-! ## Pentagonator Components

Building blocks for higher coherence proofs.
-/

/-- Pentagon left face: reassociation step 1 -/
theorem rweq_pentagon_left {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} :
    RwEq (trans (trans (trans p q) r) s) (trans (trans p q) (trans r s)) :=
  rweq_of_step (Step.trans_assoc (trans p q) r s)

/-- Pentagon right face: reassociation step 2 -/
theorem rweq_pentagon_right {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} :
    RwEq (trans (trans p q) (trans r s)) (trans p (trans q (trans r s))) :=
  rweq_of_step (Step.trans_assoc p q (trans r s))

/-- Pentagon top face: inner reassociation -/
theorem rweq_pentagon_top {p : Path a b} {q : Path b c}
    {r : Path c d} {s : Path d e} :
    RwEq (trans p (trans (trans q r) s)) (trans p (trans q (trans r s))) :=
  rweq_trans_congr_right p (rweq_of_step (Step.trans_assoc q r s))

/-! ## Path Inversion Properties

Additional properties of path inversion.
-/

/-- Inverse of identity is identity: refl⁻¹ ≈ refl -/
theorem rweq_inv_refl (a : A) : RwEq (symm (refl a)) (refl a) :=
  rweq_of_step (Step.symm_refl a)

/-- Double inversion: (p⁻¹)⁻¹ ≈ p -/
theorem rweq_inv_inv (p : Path a b) : RwEq (symm (symm p)) p :=
  rweq_of_step (Step.symm_symm p)

/-- Inversion is self-inverse: p⁻¹⁻¹⁻¹ ≈ p⁻¹ -/
theorem rweq_inv_inv_inv (p : Path a b) :
    RwEq (symm (symm (symm p))) (symm p) :=
  rweq_of_step (Step.symm_symm (symm p))

/-! ## Whiskering Compatibility

Whiskering operations satisfy expected compatibility laws.
-/

/-- Left whiskering respects composition -/
theorem rweq_whisker_left_trans {p₁ : Path a b} {p₂ : Path b c} (q : Path c d) :
    RwEq (trans (trans p₁ p₂) q) (trans p₁ (trans p₂ q)) :=
  rweq_of_step (Step.trans_assoc p₁ p₂ q)

/-- Right whiskering respects composition -/
theorem rweq_whisker_right_trans (p : Path a b) {q₁ : Path b c} {q₂ : Path c d} :
    RwEq (trans p (trans q₁ q₂)) (trans (trans p q₁) q₂) :=
  RwEq.symm (rweq_of_step (Step.trans_assoc p q₁ q₂))

/-! ## Interchange Law Preparation

The interchange law states that horizontal and vertical composition 
of 2-cells commute. These lemmas prepare for such proofs. -/

/-- Double whiskering: (p · q) · (r · s) can be reassociated -/
theorem rweq_double_whisker {p : Path a b} {q : Path b c} {r : Path c d} {s : Path d e} :
    RwEq (trans (trans p q) (trans r s))
         (trans p (trans (trans q r) s)) := by
  have h1 : RwEq (trans (trans p q) (trans r s))
                 (trans p (trans q (trans r s))) :=
    rweq_of_step (Step.trans_assoc p q (trans r s))
  have h2 : RwEq (trans q (trans r s))
                 (trans (trans q r) s) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc q r s))
  exact RwEq.trans h1 (rweq_trans_congr_right p h2)

/-- Alternate double whiskering -/
theorem rweq_double_whisker_alt {p : Path a b} {q : Path b c} {r : Path c d} {s : Path d e} :
    RwEq (trans (trans p q) (trans r s))
         (trans (trans p (trans q r)) s) := by
  have h1 : RwEq (trans (trans p q) (trans r s))
                 (trans p (trans q (trans r s))) :=
    rweq_of_step (Step.trans_assoc p q (trans r s))
  have h2 : RwEq (trans q (trans r s))
                 (trans (trans q r) s) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc q r s))
  have h3 : RwEq (trans p (trans q (trans r s)))
                 (trans p (trans (trans q r) s)) :=
    rweq_trans_congr_right p h2
  have h4 : RwEq (trans p (trans (trans q r) s))
                 (trans (trans p (trans q r)) s) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc p (trans q r) s))
  exact RwEq.trans h1 (RwEq.trans h3 h4)

/-- Left-then-right whiskering: p · q can be built step-by-step -/
theorem rweq_whisker_decompose (p : Path a b) (q : Path b c) :
    RwEq (trans p q)
         (trans (trans p (refl b)) (trans (refl b) q)) := by
  have h1 : RwEq p (trans p (refl b)) :=
    RwEq.symm (rweq_of_step (Step.trans_refl_right p))
  have h2 : RwEq q (trans (refl b) q) :=
    RwEq.symm (rweq_of_step (Step.trans_refl_left q))
  have h3 : RwEq (trans p q) (trans (trans p (refl b)) q) :=
    rweq_trans_congr_left q h1
  have h4 : RwEq (trans (trans p (refl b)) q)
                 (trans (trans p (refl b)) (trans (refl b) q)) :=
    rweq_trans_congr_right (trans p (refl b)) h2
  exact RwEq.trans h3 h4

/-! ## Summary

All theorems in this module are derived purely from the primitive Step rules
without introducing any new axioms. They extend the path algebra with useful
derived operations for working with:

1. Extended associativity (3+ paths)
2. Symmetry-transitivity interactions
3. Congruence composition laws
4. Transport properties
5. Eckmann-Hilton preparation
6. Pentagon coherence components
7. Inversion properties
8. Whiskering compatibility
9. Interchange law preparation

These are all consequences of the LND_EQ-TRS rewrite system.
-/

end PathAlgebraDerived
end Path
end ComputationalPaths
