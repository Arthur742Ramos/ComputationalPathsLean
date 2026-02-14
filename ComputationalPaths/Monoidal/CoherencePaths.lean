import ComputationalPaths.Path.MonoidalCoherence
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Step-based monoidal coherence paths

This module gives explicit `Step`-based rewrite paths for the monoidal
coherence identities on computational paths.

## Key results
- `pentagon_left_steps`, `pentagon_right_steps`: explicit pentagon routes.
- `triangle_assoc_left_unitor`, `triangle_right_unitor_whisker`: explicit
  triangle routes showing associator/unitor interaction.
- `pentagon_identity`, `triangle_identity`: coherence statements as `RwEq`.
-/

namespace ComputationalPaths
namespace Monoidal

open Path
open Path.MonoidalCoherence
open Path.Step

universe u

variable {A : Type u}
variable {a b c d e : A}

/-- Left route of Mac Lane's pentagon, realized as two `Step.trans_assoc` moves. -/
theorem pentagon_left_steps (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Rw (tensorPath (tensorPath (tensorPath p q) r) s)
       (tensorPath p (tensorPath q (tensorPath r s))) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_assoc (tensorPath p q) r s)
  · exact Step.trans_assoc p q (tensorPath r s)

/-- Right route of Mac Lane's pentagon, using congruence + associators. -/
theorem pentagon_right_steps (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Rw (tensorPath (tensorPath (tensorPath p q) r) s)
       (tensorPath p (tensorPath q (tensorPath r s))) := by
  apply Rw.tail
  · apply Rw.tail
    · apply Rw.tail
      · exact Rw.refl _
      · exact Step.trans_congr_left s (Step.trans_assoc p q r)
    · exact Step.trans_assoc p (tensorPath q r) s
  · exact Step.trans_congr_right p (Step.trans_assoc q r s)

/-- Pentagon coherence as a genuine rewrite-equivalence witness. -/
theorem pentagon_identity (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    RwEq (tensorPath (tensorPath (tensorPath p q) r) s)
         (tensorPath p (tensorPath q (tensorPath r s))) :=
  rweq_of_rw (pentagon_left_steps p q r s)

/-- Triangle route: associator, then left unitor under right congruence. -/
theorem triangle_assoc_left_unitor (p : Path a b) (q : Path b c) :
    Rw (tensorPath (tensorPath p (unitPath b)) q)
       (tensorPath p q) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_assoc p (unitPath b) q)
  · exact Step.trans_congr_right p (Step.trans_refl_left q)

/-- Triangle route: right unitor whiskered on the right by `q`. -/
theorem triangle_right_unitor_whisker (p : Path a b) (q : Path b c) :
    Rw (tensorPath (tensorPath p (unitPath b)) q)
       (tensorPath p q) :=
  rw_of_step (Step.trans_congr_left q (Step.trans_refl_right p))

/-- Triangle coherence as a rewrite-equivalence witness. -/
theorem triangle_identity (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath p (unitPath b)) q)
         (tensorPath p q) :=
  rweq_of_rw (triangle_assoc_left_unitor p q)

/-- Associator and unitor interact coherently in the triangle identity. -/
theorem associator_unitor_interact (p : Path a b) (q : Path b c) :
    RwEq (tensorPath (tensorPath p (unitPath b)) q)
         (tensorPath p q) :=
  triangle_identity p q

end Monoidal
end ComputationalPaths
