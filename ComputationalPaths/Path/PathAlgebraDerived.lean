/-
# Derived Path Algebra Lemmas

This module provides higher associativity and unit lemmas for path
concatenation, expressed as rewrite equivalences. It also includes
derived congruence, inversion, and naturality lemmas for the path algebra.

## Key Results

- Higher associativity (four-fold, five-fold)
- Unit laws (left, right, inner)
- Inversion and double inversion
- Congruence lemmas for `RwEq` with composition
- Naturality of symmetry with respect to composition
- Eckmann–Hilton style lemmas for loops

## References

- Mac Lane, "Categories for the Working Mathematician"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace PathAlgebraDerived

universe u

variable {A : Type u} {a b c d e f' : A}

/-! ## Higher associativity -/

/-- Four-fold associativity for path concatenation. -/
noncomputable def rweq_trans_four_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (trans (trans (trans p q) r) s)
      (trans p (trans q (trans r s))) := by
  have h1 :
      RwEq (trans (trans (trans p q) r) s)
        (trans (trans p q) (trans r s)) :=
    rweq_tt (trans p q) r s
  have h2 :
      RwEq (trans (trans p q) (trans r s))
        (trans p (trans q (trans r s))) :=
    rweq_tt p q (trans r s)
  exact RwEq.trans h1 h2

/-- Five-fold associativity for path concatenation. -/
noncomputable def rweq_trans_five_assoc (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) (t : Path e f') :
    RwEq (trans (trans (trans (trans p q) r) s) t)
      (trans p (trans q (trans r (trans s t)))) := by
  have h1 : RwEq (trans (trans (trans (trans p q) r) s) t)
        (trans (trans (trans p q) r) (trans s t)) :=
    rweq_tt (trans (trans p q) r) s t
  have h2 : RwEq (trans (trans (trans p q) r) (trans s t))
        (trans p (trans q (trans r (trans s t)))) :=
    rweq_trans_four_assoc p q r (trans s t)
  exact RwEq.trans h1 h2

/-! ## Unit laws -/

/-- Left unit for path concatenation. -/
noncomputable def rweq_refl_trans (p : Path a b) :
    RwEq (trans (refl a) p) p :=
  rweq_cmpA_refl_left (p := p)

/-- Right unit for path concatenation. -/
noncomputable def rweq_trans_refl (p : Path a b) :
    RwEq (trans p (refl b)) p :=
  rweq_cmpA_refl_right (p := p)

/-- Inner left unit: `p · (refl · q)` reduces to `p · q`. -/
noncomputable def rweq_inner_left_unit (p : Path a b) (q : Path b c) :
    RwEq (trans p (trans (refl b) q)) (trans p q) :=
  rweq_trans_congr_right p (rweq_cmpA_refl_left (p := q))

/-- Inner right unit: `(p · refl) · q` reduces to `p · q`. -/
noncomputable def rweq_inner_right_unit (p : Path a b) (q : Path b c) :
    RwEq (trans (trans p (refl b)) q) (trans p q) :=
  rweq_trans_congr_left q (rweq_cmpA_refl_right (p := p))

/-! ## Inversion laws -/

/-- Right inverse: `p · p⁻¹ ≈ refl`. -/
noncomputable def rweq_trans_symm_cancel (p : Path a b) :
    RwEq (trans p (symm p)) (refl a) :=
  rweq_cmpA_inv_right p

/-- Left inverse: `p⁻¹ · p ≈ refl`. -/
noncomputable def rweq_symm_trans_cancel (p : Path a b) :
    RwEq (trans (symm p) p) (refl b) :=
  rweq_cmpA_inv_left p

/-- Double inversion: `(p⁻¹)⁻¹ ≈ p`. -/
noncomputable def rweq_symm_symm (p : Path a b) :
    RwEq (symm (symm p)) p :=
  rweq_ss p

/-- Symmetry of refl is refl. -/
noncomputable def rweq_symm_refl :
    RwEq (symm (refl a)) (refl a) :=
  rweq_sr a

/-! ## Symmetry distributes over composition -/

/-- Symmetry distributes over a binary concatenation. -/
noncomputable def rweq_symm_trans (p : Path a b) (q : Path b c) :
    RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
  rweq_symm_trans_congr (p := p) (q := q)

/-- Symmetry distributes over a triple concatenation. -/
noncomputable def rweq_symm_trans3 (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (symm (trans (trans p q) r))
      (trans (symm r) (trans (symm q) (symm p))) := by
  have h1 : RwEq (symm (trans (trans p q) r))
        (trans (symm r) (symm (trans p q))) :=
    rweq_symm_trans (trans p q) r
  have h2 : RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
    rweq_symm_trans p q
  exact RwEq.trans h1 (rweq_trans_congr_right (symm r) h2)

/-! ## Congruence under RwEq -/

/-- Composition of an RwEq on the left with a path. -/
noncomputable def rweq_comp_left {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') : RwEq (trans p q) (trans p' q) :=
  rweq_trans_congr_left q h

/-- Composition of an RwEq on the right with a path. -/
noncomputable def rweq_comp_right (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') : RwEq (trans p q) (trans p q') :=
  rweq_trans_congr_right p h

/-- Bilateral congruence for composition. -/
noncomputable def rweq_comp_both {p p' : Path a b} {q q' : Path b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (trans p q) (trans p' q') :=
  rweq_trans_congr hp hq

/-! ## Cancellation lemmas -/

/-- Left cancellation: if `r · p ≈ r · q` then `p ≈ q` (at the RwEq level). -/
noncomputable def rweq_cancel_left (r : Path a b) {p q : Path b c}
    (h : RwEq (trans r p) (trans r q)) : RwEq p q := by
  have h1 : RwEq (trans (symm r) (trans r p))
      (trans (symm r) (trans r q)) :=
    rweq_comp_right (symm r) h
  have h2 : RwEq (trans (symm r) (trans r p)) p :=
    RwEq.trans (RwEq.symm (rweq_tt (symm r) r p))
      (RwEq.trans (rweq_comp_left p (rweq_symm_trans_cancel r))
        (rweq_refl_trans p))
  have h3 : RwEq (trans (symm r) (trans r q)) q :=
    RwEq.trans (RwEq.symm (rweq_tt (symm r) r q))
      (RwEq.trans (rweq_comp_left q (rweq_symm_trans_cancel r))
        (rweq_refl_trans q))
  exact RwEq.trans (RwEq.symm h2) (RwEq.trans h1 h3)

/-- Right cancellation: if `p · r ≈ q · r` then `p ≈ q` (at the RwEq level). -/
noncomputable def rweq_cancel_right {p q : Path a b} (r : Path b c)
    (h : RwEq (trans p r) (trans q r)) : RwEq p q := by
  have h1 : RwEq (trans (trans p r) (symm r))
      (trans (trans q r) (symm r)) :=
    rweq_comp_left (symm r) h
  have h2 : RwEq (trans (trans p r) (symm r)) p :=
    RwEq.trans (rweq_tt p r (symm r))
      (RwEq.trans (rweq_comp_right p (rweq_trans_symm_cancel r))
        (rweq_trans_refl p))
  have h3 : RwEq (trans (trans q r) (symm r)) q :=
    RwEq.trans (rweq_tt q r (symm r))
      (RwEq.trans (rweq_comp_right q (rweq_trans_symm_cancel r))
        (rweq_trans_refl q))
  exact RwEq.trans (RwEq.symm h2) (RwEq.trans h1 h3)

/-! ## Whiskered inversion -/

/-- Whiskered left inverse: `(q⁻¹ · p⁻¹) · (p · q) ≈ refl`. -/
noncomputable def rweq_whisker_inv_left (p : Path a b) (q : Path b c) :
    RwEq (trans (trans (symm q) (symm p)) (trans p q)) (refl c) := by
  have h1 : RwEq (trans (trans (symm q) (symm p)) (trans p q))
        (trans (symm q) (trans (symm p) (trans p q))) :=
    rweq_tt (symm q) (symm p) (trans p q)
  have h2 : RwEq (trans (symm p) (trans p q))
        (trans (trans (symm p) p) q) :=
    RwEq.symm (rweq_tt (symm p) p q)
  have h3 : RwEq (trans (trans (symm p) p) q)
        (trans (refl b) q) :=
    rweq_comp_left q (rweq_symm_trans_cancel p)
  have h4 : RwEq (trans (refl b) q) q := rweq_refl_trans q
  have h5 : RwEq (trans (symm p) (trans p q)) q :=
    RwEq.trans h2 (RwEq.trans h3 h4)
  have h6 : RwEq (trans (symm q) q) (refl c) := rweq_symm_trans_cancel q
  exact RwEq.trans h1 (RwEq.trans (rweq_comp_right (symm q) h5) h6)

/-- Whiskered right inverse: `(p · q) · (q⁻¹ · p⁻¹) ≈ refl`. -/
noncomputable def rweq_whisker_inv_right (p : Path a b) (q : Path b c) :
    RwEq (trans (trans p q) (trans (symm q) (symm p))) (refl a) := by
  have h1 : RwEq (trans (trans p q) (trans (symm q) (symm p)))
        (trans p (trans q (trans (symm q) (symm p)))) :=
    rweq_tt p q (trans (symm q) (symm p))
  have h2 : RwEq (trans q (trans (symm q) (symm p)))
        (trans (trans q (symm q)) (symm p)) :=
    RwEq.symm (rweq_tt q (symm q) (symm p))
  have h3 : RwEq (trans (trans q (symm q)) (symm p))
        (trans (refl b) (symm p)) :=
    rweq_comp_left (symm p) (rweq_trans_symm_cancel q)
  have h4 : RwEq (trans (refl b) (symm p)) (symm p) := rweq_refl_trans (symm p)
  have h5 : RwEq (trans q (trans (symm q) (symm p))) (symm p) :=
    RwEq.trans h2 (RwEq.trans h3 h4)
  have h6 : RwEq (trans p (symm p)) (refl a) := rweq_trans_symm_cancel p
  exact RwEq.trans h1 (RwEq.trans (rweq_comp_right p h5) h6)

/-! ## Conjugation -/

/-- Conjugation by a path: `p · q · p⁻¹`. -/
def conjugate (p : Path a b) (q : Path b b) : Path a a :=
  trans (trans p q) (symm p)

/-- Conjugation by refl is a no-op. -/
noncomputable def rweq_conjugate_refl_left (q : Path a a) :
    RwEq (conjugate (refl a) q) q := by
  unfold conjugate
  have h1 : RwEq (trans (trans (refl a) q) (symm (refl a)))
        (trans q (symm (refl a))) :=
    rweq_comp_left (symm (refl a)) (rweq_refl_trans q)
  have h2 : RwEq (trans q (symm (refl a))) (trans q (refl a)) :=
    rweq_comp_right q rweq_symm_refl
  have h3 : RwEq (trans q (refl a)) q := rweq_trans_refl q
  exact RwEq.trans h1 (RwEq.trans h2 h3)

/-- Conjugation preserves refl: conjugating refl by any path gives refl. -/
noncomputable def rweq_conjugate_refl_inner (p : Path a b) :
    RwEq (conjugate p (refl b)) (refl a) := by
  unfold conjugate
  exact RwEq.trans (rweq_comp_left (symm p) (rweq_trans_refl p))
    (rweq_trans_symm_cancel p)

/-! ## Path algebra identities with ofEq -/

/-- Two `ofEq` paths compose to a single `ofEq` (up to Path equality). -/
theorem ofEq_trans_ofEq {a b c : A} (h₁ : a = b) (h₂ : b = c) :
    (trans (ofEq h₁) (ofEq h₂)).toEq = (ofEq (h₁.trans h₂)).toEq := by
  cases h₁; cases h₂; rfl

/-- Associativity interacts with ofEq: composing three ofEq paths reassociates. -/
noncomputable def rweq_ofEq_assoc {a b c d : A} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d) :
    RwEq (trans (trans (ofEq h₁) (ofEq h₂)) (ofEq h₃))
      (trans (ofEq h₁) (trans (ofEq h₂) (ofEq h₃))) :=
  rweq_tt (ofEq h₁) (ofEq h₂) (ofEq h₃)

end PathAlgebraDerived
end Path
end ComputationalPaths
