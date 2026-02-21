import CompPaths.Core

namespace CompPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

universe u

variable {A : Type u}
variable {a b : A}

@[simp] theorem symm_weak_inverse_right (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_cmpA_inv_right p

@[simp] theorem symm_weak_inverse_left (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_cmpA_inv_left p

theorem zig_zag_associative (p : Path a b) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) p)
      (Path.trans p (Path.trans (Path.symm p) p)) :=
  rweq_tt p (Path.symm p) p

theorem zag_zig_associative (p : Path a b) :
    RwEq (Path.trans (Path.symm p) (Path.trans p (Path.symm p)))
      (Path.trans (Path.trans (Path.symm p) p) (Path.symm p)) := by
  exact RwEq.symm (rweq_tt (Path.symm p) p (Path.symm p))

theorem zig_identity (p : Path a b) :
    RwEq (Path.trans (Path.trans p (Path.symm p)) p) p := by
  exact RwEq.trans
    (zig_zag_associative p)
    (RwEq.trans
      (rweq_trans_congr_right p (symm_weak_inverse_left p))
      (rweq_cmpA_refl_right p))

theorem zag_identity (p : Path a b) :
    RwEq (Path.trans (Path.symm p) (Path.trans p (Path.symm p)))
      (Path.symm p) := by
  exact RwEq.trans
    (zag_zig_associative p)
    (RwEq.trans
      (rweq_trans_congr_left (Path.symm p) (symm_weak_inverse_left p))
      (rweq_cmpA_refl_left (Path.symm p)))

end CompPaths.Coherence
