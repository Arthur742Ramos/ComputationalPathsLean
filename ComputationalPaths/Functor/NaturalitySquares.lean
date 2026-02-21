/-
# Naturality Squares via Computational Paths

This module records naturality squares for path-category natural transformations
as explicit computational paths (`Path`), including composed-edge squares built
from `Path.trans`.
-/

import ComputationalPaths.Path.YonedaLemma
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Functor
namespace NaturalitySquares

open Path

universe u v

section PathNaturality

variable {A : Type u}
variable {F G : PathFunctor (A := A)}
variable (η : PathNatTrans F G)

/-- Top-then-right route in the naturality square at `x`. -/
abbrev topThenRight {a b : A} (p : Path a b) (x : F.obj a) : G.obj b :=
  G.map p (η.app a x)

/-- Left-then-bottom route in the naturality square at `x`. -/
abbrev leftThenBottom {a b : A} (p : Path a b) (x : F.obj a) : G.obj b :=
  η.app b (F.map p x)

/-- Naturality gives an explicit path witness that the square commutes. -/
private def naturalityCore {a b : A} (p : Path a b) (x : F.obj a) :
    Path (topThenRight (η := η) p x) (leftThenBottom (η := η) p x) :=
  Path.stepChain (η.naturality (p := p) (x := x))

/-- Naturality square witness with an explicit Step-normalizable chain. -/
def naturalityWitness {a b : A} (p : Path a b) (x : F.obj a) :
    Path (topThenRight (η := η) p x) (leftThenBottom (η := η) p x) :=
  Path.trans
    (Path.trans (Path.refl _) (naturalityCore (η := η) p x))
    (Path.refl _)

noncomputable def naturalityWitness_rweq_core {a b : A} (p : Path a b) (x : F.obj a) :
    RwEq (naturalityWitness (η := η) p x) (naturalityCore (η := η) p x) := by
  apply rweq_trans
  · exact rweq_of_step
      (Path.Step.trans_assoc (Path.refl _)
        (naturalityCore (η := η) p x) (Path.refl _))
  · apply rweq_trans
    · exact rweq_trans_congr_right (Path.refl _)
        (rweq_of_step (Path.Step.trans_refl_right (naturalityCore (η := η) p x)))
    · exact rweq_of_step (Path.Step.trans_refl_left (naturalityCore (η := η) p x))

/-- Composed naturality square witness via path composition of two squares. -/
def naturalityWitness_comp {a b c : A}
    (p : Path a b) (q : Path b c) (x : F.obj a) :
    Path (G.map q (G.map p (η.app a x))) (η.app c (F.map q (F.map p x))) :=
  Path.trans
    (Path.congrArg (G.map q) (naturalityWitness (η := η) p x))
    (naturalityWitness (η := η) q (F.map p x))

/-- The same composed square, rewritten through functoriality of `map_comp`. -/
def naturalityWitness_comp_via_mapComp {a b c : A}
    (p : Path a b) (q : Path b c) (x : F.obj a) :
    Path (G.map q (G.map p (η.app a x))) (η.app c (F.map q (F.map p x))) :=
  Path.trans
    (Path.symm (G.map_comp (p := p) (q := q) (x := η.app a x)))
    (Path.trans
      (naturalityWitness (η := η) (Path.trans p q) x)
      (Path.congrArg (η.app c) (F.map_comp (p := p) (q := q) (x := x))))

/-- Natural transformations induce commutative diagrams by explicit path data. -/
def induced_commutative_diagram {a b : A} (p : Path a b) (x : F.obj a) :
    Path (topThenRight (η := η) p x) (leftThenBottom (η := η) p x) :=
  naturalityWitness (η := η) p x

end PathNaturality

end NaturalitySquares
end Functor
end ComputationalPaths
