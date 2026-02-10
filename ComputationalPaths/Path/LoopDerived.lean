/-
# Derived Loop Space Lemmas

This module packages basic loop-space rewrite equivalences needed by higher
homotopy constructions, expressed purely in terms of `RwEq`.
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace LoopDerived

universe u

variable {A : Type u} {a : A}

/-! ## Unit and inverse laws -/

/-- Right unit for loops. -/
theorem rweq_loop_unit_right (p : LoopSpace A a) :
    RwEq (Path.trans p (Path.refl a)) p :=
  rweq_cmpA_refl_right (p := p)

/-- Right inverse for loops. -/
theorem rweq_loop_inv_right (p : LoopSpace A a) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right (p := p)

/-! ## Conjugation -/

/-- Conjugation by the reflexive loop is trivial. -/
theorem rweq_loop_conj_refl (q : LoopSpace A a) :
    RwEq (Path.trans (Path.trans (Path.refl a) q)
      (Path.symm (Path.refl a))) q := by
  have h1 :
      RwEq (Path.trans (Path.trans (Path.refl a) q) (Path.symm (Path.refl a)))
        (Path.trans q (Path.symm (Path.refl a))) :=
    rweq_trans_congr_left (Path.symm (Path.refl a))
      (rweq_cmpA_refl_left (p := q))
  have h2 : RwEq (Path.symm (Path.refl a)) (Path.refl a) :=
    rweq_sr (A := A) (a := a)
  have h3 :
      RwEq (Path.trans q (Path.symm (Path.refl a)))
        (Path.trans q (Path.refl a)) :=
    rweq_trans_congr_right q h2
  have h4 : RwEq (Path.trans q (Path.refl a)) q :=
    rweq_cmpA_refl_right (p := q)
  exact RwEq.trans h1 (RwEq.trans h3 h4)

/-! ## Self commutator -/

/-- The self-commutator of a loop is trivial. -/
theorem rweq_loop_self_commutator (p : LoopSpace A a) :
    RwEq (Path.trans (Path.trans (Path.trans p p) (Path.symm p)) (Path.symm p))
      (Path.refl a) := by
  have h1 :
      RwEq
        (Path.trans (Path.trans (Path.trans p p) (Path.symm p)) (Path.symm p))
        (Path.trans (Path.trans p (Path.trans p (Path.symm p))) (Path.symm p)) :=
    rweq_trans_congr_left (Path.symm p) (rweq_tt p p (Path.symm p))
  have h2 :
      RwEq (Path.trans p (Path.trans p (Path.symm p)))
        (Path.trans p (Path.refl a)) :=
    rweq_trans_congr_right p (rweq_cmpA_inv_right (p := p))
  have h3 :
      RwEq (Path.trans p (Path.refl a)) p :=
    rweq_cmpA_refl_right (p := p)
  have h4 :
      RwEq (Path.trans p (Path.trans p (Path.symm p))) p :=
    RwEq.trans h2 h3
  have h5 :
      RwEq (Path.trans (Path.trans p (Path.trans p (Path.symm p))) (Path.symm p))
        (Path.trans p (Path.symm p)) :=
    rweq_trans_congr_left (Path.symm p) h4
  have h6 : RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
    rweq_cmpA_inv_right (p := p)
  exact RwEq.trans h1 (RwEq.trans h5 h6)

end LoopDerived
end Path
end ComputationalPaths
