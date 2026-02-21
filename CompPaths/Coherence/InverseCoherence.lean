import CompPaths.Core

namespace CompPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

universe u

variable {A : Type u}
variable {a b c : A}

noncomputable def symm_weak_inverse_left (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_cmpA_inv_left p

noncomputable def symm_weak_inverse_right (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right p

noncomputable def zig_identity (p : Path a b) (q : Path a c) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) q) q :=
  rweq_trans
    (rweq_trans_congr_left q (symm_weak_inverse_right p))
    (rweq_cmpA_refl_left q)

noncomputable def zag_identity {d : A} (p : Path a b) (q : Path d b) :
    RwEq (Path.trans q (Path.trans (Path.symm p) p)) q :=
  rweq_trans
    (rweq_trans_congr_right q (symm_weak_inverse_left p))
    (rweq_cmpA_refl_right q)

/-- Coherence: both cancellation routes agree at the `toEq` level (UIP). -/
theorem inverse_associativity_coherence_toEq (p : Path a b) :
    rweq_toEq (rweq_trans
      (rweq_tt p (Path.symm p) p)
      (rweq_trans
        (rweq_trans_congr_right p (symm_weak_inverse_left p))
        (rweq_cmpA_refl_right p))) =
    rweq_toEq (rweq_trans
      (rweq_trans_congr_left p (symm_weak_inverse_right p))
      (rweq_cmpA_refl_left p)) := by
  rfl

end CompPaths.Coherence
