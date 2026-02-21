import CompPaths.Core

namespace CompPaths.Coherence

open ComputationalPaths
open ComputationalPaths.Path

universe u

variable {A : Type u}
variable {a b c : A}

noncomputable def trans_refl_left (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_cmpA_refl_left p

noncomputable def trans_refl_right (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_cmpA_refl_right p

noncomputable def triangle_identity (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q)
      (Path.trans p (Path.trans (Path.refl b) q)) :=
  rweq_tt p (Path.refl b) q

noncomputable def triangle_identity_unit (p : Path a b) (q : Path b c) :
    RwEq (Path.trans (Path.trans p (Path.refl b)) q) (Path.trans p q) := by
  exact RwEq.trans (triangle_identity p q)
    (rweq_trans_congr_right p (trans_refl_left q))

end CompPaths.Coherence
