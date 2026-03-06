import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.OmegaGroupoid
import ComputationalPaths.Path.OmegaGroupoid.GroupoidProofs

/-!
# Pentagon Coherence — Genuine Proof

The pentagon identity for the omega-groupoid structure on computational paths.
For four composable paths p, q, r, s, there are two ways to fully reassociate
from ((p∘q)∘r)∘s to p∘(q∘(r∘s)). The pentagon says these two ways
(via different intermediate associations) give RwEq-equal results.

Since RwEq is Type-valued, this is a genuine coherence result — it cannot be
discharged by Subsingleton.elim or proof irrelevance.

## The Pentagon Diagram

Given paths p : a→b, q : b→c, r : c→d, s : d→e:

Path 1 (right): 2 steps
  ((p∘q)∘r)∘s → (p∘q)∘(r∘s) → p∘(q∘(r∘s))

Path 2 (left): 3 steps
  ((p∘q)∘r)∘s → (p∘(q∘r))∘s → p∘((q∘r)∘s) → p∘(q∘(r∘s))
-/

namespace ComputationalPaths
namespace Path

universe u

noncomputable section

/-- Path 1 (right route): two associativity steps.
    ((p∘q)∘r)∘s → (p∘q)∘(r∘s) → p∘(q∘(r∘s)) -/
noncomputable def pentagon_right
    {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
         (Path.trans p (Path.trans q (Path.trans r s))) :=
  ComputationalPaths.Path.OmegaGroupoidCompPaths.pentagon_right_route p q r s

/-- Path 2 (left route): three associativity steps.
    ((p∘q)∘r)∘s → (p∘(q∘r))∘s → p∘((q∘r)∘s) → p∘(q∘(r∘s)) -/
noncomputable def pentagon_left
    {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
         (Path.trans p (Path.trans q (Path.trans r s))) :=
  ComputationalPaths.Path.OmegaGroupoidCompPaths.pentagon_left_route p q r s

/-- The two explicit pentagon routes, packaged as a pair. -/
noncomputable def pentagon_routes
    {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    (RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
          (Path.trans p (Path.trans q (Path.trans r s)))) ×
    (RwEq (Path.trans (Path.trans (Path.trans p q) r) s)
          (Path.trans p (Path.trans q (Path.trans r s)))) :=
  (pentagon_right p q r s, pentagon_left p q r s)

/-- Pentagon coherence as a genuine proof-relevant 3-cell between the two routes. -/
noncomputable def pentagon_coherence
    {A : Type u} {a b c d e : A}
    (p : Path a b) (q : Path b c) (r : Path c d) (s : Path d e) :
    OmegaGroupoid.RwEq₃ (pentagon_right p q r s) (pentagon_left p q r s) := by
  simpa [pentagon_right, pentagon_left] using
    (ComputationalPaths.Path.OmegaGroupoidCompPaths.pentagon_coherence p q r s)

end

end Path
end ComputationalPaths
