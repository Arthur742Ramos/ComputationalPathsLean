/- 
# Functor composition coherence via computational paths

This module packages core path-level coherence lemmas used by functorial
composition arguments.  The witnesses are expressed directly as `RwEq`
proofs over `Path.trans` and `Path.symm`.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Functor
namespace CompositionCoherence

open Path

universe u

section PathCoherence

variable {A : Type u}
variable {a b c d : A}

/-- Left unit inside a triple composition. -/
noncomputable def tripleComp_leftUnit (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans (Path.refl a) p) q) (Path.trans p q) :=
  rweq_trans_congr_left q (rweq_cmpA_refl_left p)

/-- Right unit inside a triple composition. -/
noncomputable def tripleComp_rightUnit (p : Path a b) (q : Path b c) :
    RwEq (Path.trans p (Path.trans q (Path.refl c))) (Path.trans p q) :=
  rweq_trans_congr_right p (rweq_cmpA_refl_right q)

/-- Associativity rebracketing. -/
noncomputable def assoc_step (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  rweq_tt (p := p) (q := q) (r := r)

/-- Left-to-right rebracketing helper. -/
noncomputable def rebracket_left (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans p (Path.trans q r)) :=
  assoc_step p q r

/-- Right-to-left rebracketing helper. -/
noncomputable def rebracket_right (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans p (Path.trans q r)) (Path.trans (Path.trans p q) r) :=
  rweq_symm (assoc_step p q r)

/-- Double symmetry normalizes. -/
noncomputable def symm_symm_id (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p :=
  rweq_of_step (Path.Step.symm_symm p)

/-- Symmetry distributes over composition. -/
noncomputable def symm_trans_distrib (p : Path a b) (q : Path b c) :
    RwEq (Path.symm (Path.trans p q)) (Path.trans (Path.symm q) (Path.symm p)) :=
  rweq_of_step (Path.Step.symm_trans_congr p q)

/-- Right inverse law. -/
noncomputable def trans_symm_cancel (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right p

/-- Left inverse law. -/
noncomputable def symm_trans_cancel (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_cmpA_inv_left p

/-- Triangle collapse `(p · q) · q⁻¹ ≈ p`. -/
noncomputable def triangle_full_collapse (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p q) (Path.symm q)) p :=
  rweq_trans
    (rweq_tt (p := p) (q := q) (r := Path.symm q))
    (rweq_trans
      (rweq_trans_congr_right p (rweq_cmpA_inv_right q))
      (rweq_cmpA_refl_right p))

/-- Left congruence for `trans`. -/
noncomputable def congr_left_preserves_rweq
    {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') : RwEq (Path.trans p q) (Path.trans p' q) :=
  rweq_trans_congr_left q h

/-- Right congruence for `trans`. -/
noncomputable def congr_right_preserves_rweq
    (p : Path a b) {q q' : Path b c}
    (h : RwEq q q') : RwEq (Path.trans p q) (Path.trans p q') :=
  rweq_trans_congr_right p h

/-- Two-sided congruence for `trans`. -/
noncomputable def congr_both_preserves_rweq
    {p p' : Path a b} {q q' : Path b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (Path.trans p q) (Path.trans p' q') :=
  rweq_trans_congr hp hq

/-- Congruence under symmetry. -/
noncomputable def symm_congr_preserves_rweq {p q : Path a b}
    (h : RwEq p q) : RwEq (Path.symm p) (Path.symm q) :=
  rweq_symm_congr h

/-- Substitute equivalent left edge in a triangle reduction. -/
noncomputable def triangle_subst {p p' : Path a b} (q : Path b c)
    (h : RwEq p p') :
    RwEq
      (Path.trans (Path.trans p q) (Path.symm q))
      (Path.trans (Path.trans p' q) (Path.symm q)) :=
  rweq_trans_congr_left (Path.symm q) (rweq_trans_congr_left q h)

/-- Substitute equivalent middle edge and its inverse in a triangle reduction. -/
noncomputable def triangle_subst_inv {p : Path a b} {q q' : Path b c}
    (hq : RwEq q q') :
    RwEq
      (Path.trans p (Path.trans q (Path.symm q)))
      (Path.trans p (Path.trans q' (Path.symm q'))) :=
  rweq_trans_congr_right p (rweq_trans_congr hq (rweq_symm_congr hq))

/-- Refl inserted in the middle (left-associated) is harmless. -/
noncomputable def refl_middle_left (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q) (Path.trans p q) :=
  rweq_trans_congr_left q (rweq_cmpA_refl_right p)

/-- Refl inserted in the middle (right-associated) is harmless. -/
noncomputable def refl_middle_right (p : Path a b) (q : Path b c) :
    RwEq (Path.trans p (Path.trans (Path.refl b) q)) (Path.trans p q) :=
  rweq_trans_congr_right p (rweq_cmpA_refl_left q)

/-- Triangle coherence `(p · refl) · q ≈ p · q`. -/
noncomputable def triangle_coherence (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q) (Path.trans p q) :=
  refl_middle_left p q

/-- Naturality of associativity under substitutions in each component. -/
noncomputable def assoc_natural
    {p p' : Path a b} {q q' : Path b c} {r r' : Path c d}
    (hp : RwEq p p') (hq : RwEq q q') (hr : RwEq r r') :
    RwEq (Path.trans (Path.trans p q) r) (Path.trans (Path.trans p' q') r') :=
  rweq_trans
    (rweq_trans_congr_left r (rweq_trans_congr hp hq))
    (rweq_trans_congr_right (Path.trans p' q') hr)

end PathCoherence

end CompositionCoherence
end Functor
end ComputationalPaths

