import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Operadic path coherence

This module packages operadic composition laws directly as rewrite paths.
Associativity and unit laws are provided as `Rw`/`RwEq` witnesses built from
LND_EQ-TRS rewrite rules (`Step.trans_assoc`, `Step.trans_refl_*`), not by
wrapping propositional equalities with `Path.stepChain`.
-/

namespace ComputationalPaths
namespace Operad

open Path
open Path.Step

universe u

/-- Operadic composition data where coherence is recorded as rewrite paths. -/
structure PathCoherentOperad (A : Type u) where
  compose : {a b c : A} → Path a b → Path b c → Path a c
  unit : (a : A) → Path a a
  assoc_rw : {a b c d : A} → (f : Path a b) → (g : Path b c) → (h : Path c d) →
    Rw (compose (compose f g) h) (compose f (compose g h))
  left_unit_rw : {a b : A} → (f : Path a b) → Rw (compose (unit a) f) f
  right_unit_rw : {a b : A} → (f : Path a b) → Rw (compose f (unit b)) f

namespace PathCoherentOperad

/-- Canonical operadic composition from path concatenation. -/
def canonical (A : Type u) : PathCoherentOperad A where
  compose := fun f g => Path.trans f g
  unit := Path.refl
  assoc_rw := fun f g h =>
    rw_of_step (Step.trans_assoc f g h)
  left_unit_rw := fun f =>
    rw_of_step (Step.trans_refl_left f)
  right_unit_rw := fun f =>
    rw_of_step (Step.trans_refl_right f)

variable {A : Type u}

/-- Associativity coherence as rewrite equivalence. -/
noncomputable def assoc {a b c d : A}
    (f : Path a b) (g : Path b c) (h : Path c d) :
    RwEq ((canonical A).compose ((canonical A).compose f g) h)
      ((canonical A).compose f ((canonical A).compose g h)) :=
  rweq_of_rw ((canonical A).assoc_rw f g h)

/-- Left unitality coherence as rewrite equivalence. -/
noncomputable def left_unit {a b : A} (f : Path a b) :
    RwEq ((canonical A).compose ((canonical A).unit a) f) f :=
  rweq_of_rw ((canonical A).left_unit_rw f)

/-- Right unitality coherence as rewrite equivalence. -/
noncomputable def right_unit {a b : A} (f : Path a b) :
    RwEq ((canonical A).compose f ((canonical A).unit b)) f :=
  rweq_of_rw ((canonical A).right_unit_rw f)

/-- First pentagon route: reassociate `( ((f·g)·h)·k )` in two rewrite steps. -/
theorem pentagon_left_route {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    Rw ((canonical A).compose ((canonical A).compose ((canonical A).compose f g) h) k)
      ((canonical A).compose f ((canonical A).compose g ((canonical A).compose h k))) := by
  apply Rw.tail
  · exact rw_of_step (Step.trans_assoc ((canonical A).compose f g) h k)
  · exact Step.trans_assoc f g ((canonical A).compose h k)

/-- Second pentagon route: congruence + associativity rewrites. -/
theorem pentagon_right_route {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    Rw ((canonical A).compose ((canonical A).compose ((canonical A).compose f g) h) k)
      ((canonical A).compose f ((canonical A).compose g ((canonical A).compose h k))) := by
  apply Rw.tail
  · apply Rw.tail
    · apply Rw.tail
      · exact Rw.refl _
      · exact Step.trans_congr_left k (Step.trans_assoc f g h)
    · exact Step.trans_assoc f ((canonical A).compose g h) k
  · exact Step.trans_congr_right f (Step.trans_assoc g h k)

/-- Pentagon coherence as a genuine rewrite equivalence witness. -/
noncomputable def pentagon {a b c d e : A}
    (f : Path a b) (g : Path b c) (h : Path c d) (k : Path d e) :
    RwEq ((canonical A).compose ((canonical A).compose ((canonical A).compose f g) h) k)
      ((canonical A).compose f ((canonical A).compose g ((canonical A).compose h k))) :=
  rweq_of_rw (pentagon_left_route f g h k)

end PathCoherentOperad
end Operad
end ComputationalPaths
