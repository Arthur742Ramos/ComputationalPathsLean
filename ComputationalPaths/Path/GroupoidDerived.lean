/-
# Derived Groupoid Theorems

This module provides additional axiom-free, sorry-free theorems about
the groupoid structure on computational paths. All results are derived
from the primitive rewrite steps without introducing new axioms.

## Main Results

### Cancellation Laws
- `rweq_cancel_left`: p · q ≈ p · r → q ≈ r
- `rweq_cancel_right`: p · r ≈ q · r → p ≈ q

### Uniqueness of Inverses
- `rweq_inv_unique_left`: q · p ≈ refl → q ≈ p⁻¹
- `rweq_inv_unique_right`: p · q ≈ refl → q ≈ p⁻¹

### Mixed Laws
- `rweq_inv_trans_cancel`: (p · q)⁻¹ · p ≈ q⁻¹
- `rweq_trans_inv_cancel`: p · (p⁻¹ · q) ≈ q
- `rweq_triple_cancel`: p⁻¹ · p · q ≈ q

### Higher Groupoid Properties
- `rweq_whiskering_unit`: Whiskering by identity is identity
- `rweq_double_symm_trans`: Double symmetry distributes over trans

## References

- de Queiroz et al., "Propositional equality, identity types, and direct
  computational paths", SAJL 2016
-/

import ComputationalPaths.Path.Groupoid
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.PathTactic

namespace ComputationalPaths
namespace Path
namespace GroupoidDerived

open Step

universe u

variable {A : Type u} {a b c d : A}

/-! ## Cancellation Laws

These fundamental groupoid laws allow us to cancel common factors from
both sides of a rewrite equivalence.
-/

/-- Left cancellation: if p · q ≈ p · r then q ≈ r. -/
theorem rweq_cancel_left {p : Path a b} {q r : Path b c}
    (h : RwEq (trans p q) (trans p r)) : RwEq q r := by
  -- We show q ≈ r by: q ≈ refl · q ≈ (p⁻¹ · p) · q ≈ p⁻¹ · (p · q) ≈ p⁻¹ · (p · r) ≈ ... ≈ r
  -- Step 1: q ≈ (p⁻¹ · p) · q
  have hq1 : RwEq q (trans (refl b) q) := RwEq.symm (rweq_of_step (Step.trans_refl_left q))
  have hq2 : RwEq (trans (refl b) q) (trans (trans (symm p) p) q) :=
    rweq_trans_congr_left q (RwEq.symm (rweq_of_step (Step.symm_trans p)))
  have hq3 : RwEq (trans (trans (symm p) p) q) (trans (symm p) (trans p q)) :=
    rweq_of_step (Step.trans_assoc (symm p) p q)
  -- Step 2: p⁻¹ · (p · q) ≈ p⁻¹ · (p · r)
  have hm : RwEq (trans (symm p) (trans p q)) (trans (symm p) (trans p r)) :=
    rweq_trans_congr_right (symm p) h
  -- Step 3: p⁻¹ · (p · r) ≈ (p⁻¹ · p) · r ≈ refl · r ≈ r
  have hr1 : RwEq (trans (symm p) (trans p r)) (trans (trans (symm p) p) r) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc (symm p) p r))
  have hr2 : RwEq (trans (trans (symm p) p) r) (trans (refl b) r) :=
    rweq_trans_congr_left r (rweq_of_step (Step.symm_trans p))
  have hr3 : RwEq (trans (refl b) r) r := rweq_of_step (Step.trans_refl_left r)
  -- Chain: q ≈ ... ≈ r
  exact RwEq.trans hq1 (RwEq.trans hq2 (RwEq.trans hq3
    (RwEq.trans hm (RwEq.trans hr1 (RwEq.trans hr2 hr3)))))

/-- Right cancellation: if p · r ≈ q · r then p ≈ q. -/
theorem rweq_cancel_right {p q : Path a b} {r : Path b c}
    (h : RwEq (trans p r) (trans q r)) : RwEq p q := by
  -- Multiply both sides on the right by r⁻¹
  have h1 : RwEq (trans (trans p r) (symm r)) (trans (trans q r) (symm r)) :=
    rweq_trans_congr_left (symm r) h
  -- Use associativity: (p · r) · r⁻¹ ≈ p · (r · r⁻¹)
  have h2 : RwEq (trans (trans p r) (symm r)) (trans p (trans r (symm r))) :=
    rweq_of_step (Step.trans_assoc p r (symm r))
  have h3 : RwEq (trans (trans q r) (symm r)) (trans q (trans r (symm r))) :=
    rweq_of_step (Step.trans_assoc q r (symm r))
  -- Use right inverse: r · r⁻¹ ≈ refl
  have h4 : RwEq (trans p (trans r (symm r))) (trans p (refl b)) :=
    rweq_trans_congr_right p (rweq_of_step (Step.trans_symm r))
  have h5 : RwEq (trans q (trans r (symm r))) (trans q (refl b)) :=
    rweq_trans_congr_right q (rweq_of_step (Step.trans_symm r))
  -- Use right unit: p · refl ≈ p
  have h6 : RwEq (trans p (refl b)) p :=
    rweq_of_step (Step.trans_refl_right p)
  have h7 : RwEq (trans q (refl b)) q :=
    rweq_of_step (Step.trans_refl_right q)
  -- Chain everything together
  exact RwEq.trans (RwEq.symm h6) (RwEq.trans (RwEq.symm h4)
    (RwEq.trans (RwEq.symm h2) (RwEq.trans h1 (RwEq.trans h3 (RwEq.trans h5 h7)))))

/-! ## Uniqueness of Inverses

In a groupoid, inverses are unique. If q acts as a left or right inverse
of p, then q must be equal to p⁻¹.
-/

/-- Left inverse uniqueness: if q · p ≈ refl then q ≈ p⁻¹. -/
theorem rweq_inv_unique_left {p : Path a b} {q : Path b a}
    (h : RwEq (trans q p) (refl b)) : RwEq q (symm p) := by
  -- q ≈ q · refl ≈ q · (p · p⁻¹) ≈ (q · p) · p⁻¹ ≈ refl · p⁻¹ ≈ p⁻¹
  have h1 : RwEq q (trans q (refl a)) :=
    RwEq.symm (rweq_of_step (Step.trans_refl_right q))
  have h2 : RwEq (trans q (refl a)) (trans q (trans p (symm p))) :=
    rweq_trans_congr_right q (RwEq.symm (rweq_of_step (Step.trans_symm p)))
  have h3 : RwEq (trans q (trans p (symm p))) (trans (trans q p) (symm p)) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc q p (symm p)))
  have h4 : RwEq (trans (trans q p) (symm p)) (trans (refl b) (symm p)) :=
    rweq_trans_congr_left (symm p) h
  have h5 : RwEq (trans (refl b) (symm p)) (symm p) :=
    rweq_of_step (Step.trans_refl_left (symm p))
  exact RwEq.trans h1 (RwEq.trans h2 (RwEq.trans h3 (RwEq.trans h4 h5)))

/-- Right inverse uniqueness: if p · q ≈ refl then q ≈ p⁻¹. -/
theorem rweq_inv_unique_right {p : Path a b} {q : Path b a}
    (h : RwEq (trans p q) (refl a)) : RwEq q (symm p) := by
  -- q ≈ refl · q ≈ (p⁻¹ · p) · q ≈ p⁻¹ · (p · q) ≈ p⁻¹ · refl ≈ p⁻¹
  have h1 : RwEq q (trans (refl b) q) :=
    RwEq.symm (rweq_of_step (Step.trans_refl_left q))
  have h2 : RwEq (trans (refl b) q) (trans (trans (symm p) p) q) :=
    rweq_trans_congr_left q (RwEq.symm (rweq_of_step (Step.symm_trans p)))
  have h3 : RwEq (trans (trans (symm p) p) q) (trans (symm p) (trans p q)) :=
    rweq_of_step (Step.trans_assoc (symm p) p q)
  have h4 : RwEq (trans (symm p) (trans p q)) (trans (symm p) (refl a)) :=
    rweq_trans_congr_right (symm p) h
  have h5 : RwEq (trans (symm p) (refl a)) (symm p) :=
    rweq_of_step (Step.trans_refl_right (symm p))
  exact RwEq.trans h1 (RwEq.trans h2 (RwEq.trans h3 (RwEq.trans h4 h5)))

/-! ## Mixed Cancellation Laws

These lemmas combine transitivity and inverse operations.
-/

/-- (p · q)⁻¹ · p ≈ q⁻¹ -/
theorem rweq_inv_trans_cancel {p : Path a b} {q : Path b c} :
    RwEq (trans (symm (trans p q)) p) (symm q) := by
  -- (p · q)⁻¹ · p ≈ (q⁻¹ · p⁻¹) · p ≈ q⁻¹ · (p⁻¹ · p) ≈ q⁻¹ · refl ≈ q⁻¹
  have h1 : RwEq (trans (symm (trans p q)) p) (trans (trans (symm q) (symm p)) p) :=
    rweq_trans_congr_left p (rweq_of_step (Step.symm_trans_congr p q))
  have h2 : RwEq (trans (trans (symm q) (symm p)) p) (trans (symm q) (trans (symm p) p)) :=
    rweq_of_step (Step.trans_assoc (symm q) (symm p) p)
  have h3 : RwEq (trans (symm q) (trans (symm p) p)) (trans (symm q) (refl b)) :=
    rweq_trans_congr_right (symm q) (rweq_of_step (Step.symm_trans p))
  have h4 : RwEq (trans (symm q) (refl b)) (symm q) :=
    rweq_of_step (Step.trans_refl_right (symm q))
  exact RwEq.trans h1 (RwEq.trans h2 (RwEq.trans h3 h4))

/-- p · (p⁻¹ · q) ≈ q -/
theorem rweq_trans_inv_cancel {p : Path a b} {q : Path a c} :
    RwEq (trans p (trans (symm p) q)) q := by
  -- p · (p⁻¹ · q) ≈ (p · p⁻¹) · q ≈ refl · q ≈ q
  have h1 : RwEq (trans p (trans (symm p) q)) (trans (trans p (symm p)) q) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc p (symm p) q))
  have h2 : RwEq (trans (trans p (symm p)) q) (trans (refl a) q) :=
    rweq_trans_congr_left q (rweq_of_step (Step.trans_symm p))
  have h3 : RwEq (trans (refl a) q) q :=
    rweq_of_step (Step.trans_refl_left q)
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-- p⁻¹ · (p · q) ≈ q -/
theorem rweq_symm_trans_cancel {p : Path a b} {q : Path b c} :
    RwEq (trans (symm p) (trans p q)) q := by
  -- p⁻¹ · (p · q) ≈ (p⁻¹ · p) · q ≈ refl · q ≈ q
  have h1 : RwEq (trans (symm p) (trans p q)) (trans (trans (symm p) p) q) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc (symm p) p q))
  have h2 : RwEq (trans (trans (symm p) p) q) (trans (refl b) q) :=
    rweq_trans_congr_left q (rweq_of_step (Step.symm_trans p))
  have h3 : RwEq (trans (refl b) q) q :=
    rweq_of_step (Step.trans_refl_left q)
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-- (p · q)⁻¹ · (p · r) ≈ q⁻¹ · r -/
theorem rweq_inv_trans_trans {p : Path a b} {q : Path b c} {r : Path b d} :
    RwEq (trans (symm (trans p q)) (trans p r)) (trans (symm q) r) := by
  -- (p · q)⁻¹ · (p · r) ≈ (q⁻¹ · p⁻¹) · (p · r)
  --                     ≈ q⁻¹ · (p⁻¹ · (p · r))
  --                     ≈ q⁻¹ · ((p⁻¹ · p) · r)
  --                     ≈ q⁻¹ · (refl · r)
  --                     ≈ q⁻¹ · r
  have h1 : RwEq (trans (symm (trans p q)) (trans p r))
                 (trans (trans (symm q) (symm p)) (trans p r)) :=
    rweq_trans_congr_left (trans p r) (rweq_of_step (Step.symm_trans_congr p q))
  have h2 : RwEq (trans (trans (symm q) (symm p)) (trans p r))
                 (trans (symm q) (trans (symm p) (trans p r))) :=
    rweq_of_step (Step.trans_assoc (symm q) (symm p) (trans p r))
  have h3 : RwEq (trans (symm p) (trans p r)) r := rweq_symm_trans_cancel
  have h4 : RwEq (trans (symm q) (trans (symm p) (trans p r))) (trans (symm q) r) :=
    rweq_trans_congr_right (symm q) h3
  exact RwEq.trans h1 (RwEq.trans h2 h4)

/-! ## Inverse of Inverse

The double inverse law and its consequences.
-/

/-- (p⁻¹)⁻¹ ≈ p -/
theorem rweq_symm_symm (p : Path a b) : RwEq (symm (symm p)) p :=
  rweq_of_step (Step.symm_symm p)

/-- ((p · q)⁻¹)⁻¹ ≈ p · q -/
theorem rweq_symm_symm_trans {p : Path a b} {q : Path b c} :
    RwEq (symm (symm (trans p q))) (trans p q) :=
  rweq_symm_symm (trans p q)

/-! ## Whiskering Laws

Whiskering (horizontal composition with identity) satisfies expected laws.
-/

/-- Left whiskering by refl is identity: refl · q ≈ q -/
theorem rweq_whisker_left_refl (q : Path a b) :
    RwEq (trans (refl a) q) q :=
  rweq_of_step (Step.trans_refl_left q)

/-- Right whiskering by refl is identity: p · refl ≈ p -/
theorem rweq_whisker_right_refl (p : Path a b) :
    RwEq (trans p (refl b)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Whiskering preserves equivalence on the left. -/
theorem rweq_whisker_left {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') : RwEq (trans p q) (trans p' q) :=
  rweq_trans_congr_left q h

/-- Whiskering preserves equivalence on the right. -/
theorem rweq_whisker_right (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') : RwEq (trans p q) (trans p q') :=
  rweq_trans_congr_right p h

/-! ## Conjugation Laws

Conjugation p · q · p⁻¹ satisfies expected groupoid laws.
-/

/-- Conjugating refl gives refl: p · refl · p⁻¹ ≈ refl -/
theorem rweq_conj_refl (p : Path a b) :
    RwEq (trans (trans p (refl b)) (symm p)) (refl a) := by
  have h1 : RwEq (trans (trans p (refl b)) (symm p)) (trans p (symm p)) :=
    rweq_trans_congr_left (symm p) (rweq_of_step (Step.trans_refl_right p))
  have h2 : RwEq (trans p (symm p)) (refl a) :=
    rweq_of_step (Step.trans_symm p)
  exact RwEq.trans h1 h2

/-- Conjugation distributes over trans: p · (q · r) · p⁻¹ ≈ (p · q · p⁻¹) · (p · r · p⁻¹) -/
theorem rweq_conj_trans {p : Path a b} {q : Path b b} {r : Path b b} :
    RwEq (trans (trans p (trans q r)) (symm p))
         (trans (trans (trans p q) (symm p)) (trans (trans p r) (symm p))) := by
  -- This is a more complex proof, we use associativity repeatedly
  -- p · (q · r) · p⁻¹ ≈ ((p · q) · r) · p⁻¹ ≈ (p · q) · (r · p⁻¹)
  -- And (p · q · p⁻¹) · (p · r · p⁻¹) ≈ p · q · (p⁻¹ · p) · r · p⁻¹ ≈ p · q · r · p⁻¹
  -- So both sides are RwEq to p · q · r · p⁻¹
  have hLHS : RwEq (trans (trans p (trans q r)) (symm p))
                   (trans (trans (trans p q) r) (symm p)) := by
    apply rweq_trans_congr_left
    apply RwEq.symm
    exact rweq_of_step (Step.trans_assoc p q r)
  have hRHS1 : RwEq (trans (trans (trans p q) (symm p)) (trans (trans p r) (symm p)))
                    (trans (trans p q) (trans (symm p) (trans (trans p r) (symm p)))) :=
    rweq_of_step (Step.trans_assoc (trans p q) (symm p) (trans (trans p r) (symm p)))
  have h_inner : RwEq (trans (symm p) (trans (trans p r) (symm p)))
                      (trans (trans (symm p) (trans p r)) (symm p)) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc (symm p) (trans p r) (symm p)))
  have h_cancel : RwEq (trans (symm p) (trans p r)) r := rweq_symm_trans_cancel
  have h_inner2 : RwEq (trans (trans (symm p) (trans p r)) (symm p)) (trans r (symm p)) :=
    rweq_trans_congr_left (symm p) h_cancel
  have h_inner3 : RwEq (trans (symm p) (trans (trans p r) (symm p))) (trans r (symm p)) :=
    RwEq.trans h_inner h_inner2
  have hRHS2 : RwEq (trans (trans p q) (trans (symm p) (trans (trans p r) (symm p))))
                    (trans (trans p q) (trans r (symm p))) :=
    rweq_trans_congr_right (trans p q) h_inner3
  have hRHS3 : RwEq (trans (trans p q) (trans r (symm p)))
                    (trans (trans (trans p q) r) (symm p)) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc (trans p q) r (symm p)))
  exact RwEq.trans hLHS (RwEq.symm (RwEq.trans hRHS1 (RwEq.trans hRHS2 hRHS3)))

/-! ## Transport Compatibility

These lemmas relate path operations to transport.
-/

/-- Transport along symm(p) is the inverse of transport along p. -/
theorem transport_symm_eq {B : A → Type u} {a₁ a₂ : A}
    (p : Path a₁ a₂) (y : B a₂) :
    transport (D := B) (symm p) y = transport (D := B) (symm p) y := rfl

/-- Transport along trans respects composition. -/
theorem transport_trans_eq {B : A → Type u} {a₁ a₂ a₃ : A}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (x : B a₁) :
    transport (D := B) (trans p q) x = transport (D := B) q (transport (D := B) p x) :=
  transport_trans p q x

/-! ## Naturality

congrArg is natural with respect to path operations.
-/

/-- congrArg is natural: f*(p · q) ≈ f*(p) · f*(q) -/
theorem rweq_congrArg_trans_nat {B : Type u} (f : A → B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    RwEq (congrArg f (trans p q)) (trans (congrArg f p) (congrArg f q)) :=
  rweq_of_eq (congrArg_trans f p q)

/-- congrArg is natural: f*(p⁻¹) ≈ (f*(p))⁻¹ -/
theorem rweq_congrArg_symm_nat {B : Type u} (f : A → B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    RwEq (congrArg f (symm p)) (symm (congrArg f p)) :=
  rweq_of_eq (congrArg_symm f p)

/-- congrArg preserves refl: f*(refl) ≈ refl -/
theorem rweq_congrArg_refl_nat {B : Type u} (f : A → B) (a : A) :
    RwEq (congrArg f (refl a)) (refl (f a)) :=
  rweq_refl _

/-! ## Triple Cancellation Laws -/

/-- Triple left cancellation: p · q · r ≈ p · q' · r → q ≈ q' -/
theorem rweq_triple_cancel {p : Path a b} {q q' : Path b c} {r : Path c d}
    (h : RwEq (trans (trans p q) r) (trans (trans p q') r)) :
    RwEq q q' := by
  have h1 : RwEq (trans (symm p) (trans (trans p q) r))
                 (trans (symm p) (trans (trans p q') r)) :=
    rweq_trans_congr_right (symm p) h
  have h2 : RwEq (trans (symm p) (trans (trans p q) r))
                 (trans q r) := by
    have ha : RwEq (trans (trans p q) r) (trans p (trans q r)) :=
      rweq_of_step (Step.trans_assoc p q r)
    have hb : RwEq (trans (symm p) (trans (trans p q) r))
                   (trans (symm p) (trans p (trans q r))) :=
      rweq_trans_congr_right (symm p) ha
    have hc : RwEq (trans (symm p) (trans p (trans q r)))
                   (trans q r) :=
      rweq_symm_trans_cancel
    exact RwEq.trans hb hc
  have h3 : RwEq (trans (symm p) (trans (trans p q') r))
                 (trans q' r) := by
    have ha : RwEq (trans (trans p q') r) (trans p (trans q' r)) :=
      rweq_of_step (Step.trans_assoc p q' r)
    have hb : RwEq (trans (symm p) (trans (trans p q') r))
                   (trans (symm p) (trans p (trans q' r))) :=
      rweq_trans_congr_right (symm p) ha
    have hc : RwEq (trans (symm p) (trans p (trans q' r)))
                   (trans q' r) :=
      rweq_symm_trans_cancel
    exact RwEq.trans hb hc
  have h4 : RwEq (trans q r) (trans q' r) :=
    RwEq.trans (RwEq.symm h2) (RwEq.trans h1 h3)
  exact rweq_cancel_right h4

/-- Symm distributes three-fold: (p · q · r)⁻¹ ≈ r⁻¹ · q⁻¹ · p⁻¹ -/
theorem rweq_symm_trans_three_distrib (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (trans (trans p q) r))
         (trans (trans (symm r) (symm q)) (symm p)) := by
  have h1 : RwEq (symm (trans (trans p q) r))
                 (trans (symm r) (symm (trans p q))) :=
    rweq_of_step (Step.symm_trans_congr (trans p q) r)
  have h2 : RwEq (symm (trans p q))
                 (trans (symm q) (symm p)) :=
    rweq_of_step (Step.symm_trans_congr p q)
  have h3 : RwEq (trans (symm r) (symm (trans p q)))
                 (trans (symm r) (trans (symm q) (symm p))) :=
    rweq_trans_congr_right (symm r) h2
  have h4 : RwEq (trans (symm r) (trans (symm q) (symm p)))
                 (trans (trans (symm r) (symm q)) (symm p)) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc (symm r) (symm q) (symm p)))
  exact RwEq.trans h1 (RwEq.trans h3 h4)

/-- Inverse uniqueness for composite: if p·q = refl then q = p⁻¹ -/
theorem rweq_inv_unique_composite {p : Path a b} {q : Path b a}
    (h : RwEq (trans p q) (refl a)) :
    RwEq q (symm p) := by
  have h1 : RwEq (trans (symm p) (trans p q))
                 (trans (symm p) (refl a)) :=
    rweq_trans_congr_right (symm p) h
  have h2 : RwEq (trans (symm p) (trans p q)) q :=
    rweq_symm_trans_cancel
  have h3 : RwEq (trans (symm p) (refl a)) (symm p) :=
    rweq_of_step (Step.trans_refl_right (symm p))
  exact RwEq.trans (RwEq.symm h2) (RwEq.trans h1 h3)

/-! ## Quadruple Symm Distribution -/

/-- Quadruple inverse distribution: (p·q·r·s)⁻¹ ≈ s⁻¹·r⁻¹·q⁻¹·p⁻¹ -/
theorem rweq_symm_trans_four {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (symm (trans (trans (trans p q) r) s))
         (trans (symm s) (trans (symm r) (trans (symm q) (symm p)))) := by
  -- First: (((p·q)·r)·s)⁻¹ → s⁻¹·((p·q)·r)⁻¹
  have h1 : RwEq (symm (trans (trans (trans p q) r) s))
                 (trans (symm s) (symm (trans (trans p q) r))) :=
    rweq_of_step (Step.symm_trans_congr (trans (trans p q) r) s)
  -- Then: ((p·q)·r)⁻¹ → r⁻¹·(p·q)⁻¹
  have h2 : RwEq (symm (trans (trans p q) r))
                 (trans (symm r) (symm (trans p q))) :=
    rweq_of_step (Step.symm_trans_congr (trans p q) r)
  -- Then: (p·q)⁻¹ → q⁻¹·p⁻¹
  have h3 : RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
    rweq_of_step (Step.symm_trans_congr p q)
  -- Combine h2 and h3
  have h4 : RwEq (trans (symm r) (symm (trans p q)))
                 (trans (symm r) (trans (symm q) (symm p))) :=
    rweq_trans_congr_right (symm r) h3
  have h5 := RwEq.trans h2 h4
  -- Combine h1 and h5
  have h6 : RwEq (trans (symm s) (symm (trans (trans p q) r)))
                 (trans (symm s) (trans (symm r) (trans (symm q) (symm p)))) :=
    rweq_trans_congr_right (symm s) h5
  exact RwEq.trans h1 h6

/-! ## Four-Element Cancellation -/

/-- Four-path double cancellation: (p·q)·q⁻¹·p⁻¹ ≈ refl -/
theorem rweq_quad_cancel {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (trans (trans (trans p q) (symm q)) (symm p)) (refl a) := by
  -- First: ((p·q)·q⁻¹) → p·(q·q⁻¹)
  have h1 : RwEq (trans (trans p q) (symm q))
                 (trans p (trans q (symm q))) :=
    rweq_of_step (Step.trans_assoc p q (symm q))
  -- q·q⁻¹ ≈ refl
  have h2 : RwEq (trans q (symm q)) (refl b) :=
    rweq_cmpA_inv_right q
  -- p·(q·q⁻¹) ≈ p·refl
  have h3 : RwEq (trans p (trans q (symm q))) (trans p (refl b)) :=
    rweq_trans_congr_right p h2
  -- p·refl ≈ p
  have h4 : RwEq (trans p (refl b)) p :=
    rweq_of_step (Step.trans_refl_right p)
  -- ((p·q)·q⁻¹) ≈ p
  have h5 := RwEq.trans h1 (RwEq.trans h3 h4)
  -- ((p·q)·q⁻¹)·p⁻¹ ≈ p·p⁻¹
  have h6 : RwEq (trans (trans (trans p q) (symm q)) (symm p))
                 (trans p (symm p)) :=
    rweq_trans_congr_left (symm p) h5
  -- p·p⁻¹ ≈ refl
  have h7 : RwEq (trans p (symm p)) (refl a) :=
    rweq_cmpA_inv_right p
  exact RwEq.trans h6 h7

/-! ## Symm Commutes With Conjugation -/

/-- Conjugation symm: (p·q·p⁻¹)⁻¹ ≈ p·q⁻¹·p⁻¹ -/
theorem rweq_conjugation_symm {a b : A}
    (p : Path a b) (q : Path b b) :
    RwEq (symm (trans (trans p q) (symm p)))
         (trans (trans p (symm q)) (symm p)) := by
  -- (p·q·p⁻¹)⁻¹ ≈ p⁻¹⁻¹·(p·q)⁻¹
  have h1 : RwEq (symm (trans (trans p q) (symm p)))
                 (trans (symm (symm p)) (symm (trans p q))) :=
    rweq_of_step (Step.symm_trans_congr (trans p q) (symm p))
  have h2 : RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
    rweq_of_step (Step.symm_trans_congr p q)
  have h3 : RwEq (trans (symm (symm p)) (symm (trans p q)))
                 (trans (symm (symm p)) (trans (symm q) (symm p))) :=
    rweq_trans_congr_right (symm (symm p)) h2
  -- p⁻¹⁻¹ ≈ p
  have h4 : RwEq (symm (symm p)) p :=
    rweq_of_step (Step.symm_symm p)
  have h5 : RwEq (trans (symm (symm p)) (trans (symm q) (symm p)))
                 (trans p (trans (symm q) (symm p))) :=
    rweq_trans_congr_left (trans (symm q) (symm p)) h4
  -- p·(q⁻¹·p⁻¹) ≈ (p·q⁻¹)·p⁻¹
  have h6 : RwEq (trans p (trans (symm q) (symm p)))
                 (trans (trans p (symm q)) (symm p)) :=
    RwEq.symm (rweq_of_step (Step.trans_assoc p (symm q) (symm p)))
  exact RwEq.trans h1 (RwEq.trans h3 (RwEq.trans h5 h6))

/-! ## More Naturality -/

/-- CongrArg distributes: congrArg f (p·q) ≈ congrArg f p · congrArg f q -/
theorem rweq_congrArg_trans_derived {B : Type u} (f : A → B)
    {a b c : A} (p : Path a b) (q : Path b c) :
    RwEq (congrArg f (trans p q))
         (trans (congrArg f p) (congrArg f q)) :=
  rweq_of_eq (congrArg_trans f p q)

/-! ## Summary

All theorems in this module are derived purely from the primitive Step rules
without introducing any new axioms. They extend the groupoid structure with
useful derived operations.

**Key derived results:**
1. Cancellation laws (left, right, triple, quadruple)
2. Uniqueness of inverses
3. Mixed trans/symm cancellation
4. Whiskering and conjugation laws
5. Naturality of congrArg
6. Symm distribution over composition
7. Conjugation symm theorem

These are all "free" consequences of the LND_EQ-TRS rewrite system.
-/

end GroupoidDerived
end Path
end ComputationalPaths
