/-
# Computational-path adjunction triangles

This module provides lightweight infrastructure for encoding adjunction
unit/counit triangles directly as computational paths. The zigzag identities
are proved as `RwEq` derivations by explicit rewriting and cancellation.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Adjunction

open Path

universe u v

/-- Unit/counit data for an adjunction in computational-path form. -/
structure AdjunctionData (C : Type u) (D : Type v)
    (F : C → D) (G : D → C) where
  unit : ∀ x : C, Path x (G (F x))
  counit : ∀ y : D, Path (F (G y)) y

namespace AdjunctionData

variable {C : Type u} {D : Type v}
variable {F : C → D} {G : D → C}

/-- Left triangle `ε_{F x} ∘ Fηₓ`. -/
def leftTriangle (adj : AdjunctionData C D F G) (x : C) : Path (F x) (F x) :=
  Path.trans (Path.congrArg F (adj.unit x)) (adj.counit (F x))

/-- Right triangle `Gεᵧ ∘ η_{G y}`. -/
def rightTriangle (adj : AdjunctionData C D F G) (y : D) : Path (G y) (G y) :=
  Path.trans (adj.unit (G y)) (Path.congrArg G (adj.counit y))

/-- Counit components rewrite to inverses of `F`-mapped unit components. -/
def LeftCounitInverse (adj : AdjunctionData C D F G) : Prop :=
  ∀ x : C, RwEq (adj.counit (F x)) (Path.symm (Path.congrArg F (adj.unit x)))

/-- Unit components rewrite to inverses of `G`-mapped counit components. -/
def RightUnitInverse (adj : AdjunctionData C D F G) : Prop :=
  ∀ y : D, RwEq (adj.unit (G y)) (Path.symm (Path.congrArg G (adj.counit y)))

/-- Triangle (zigzag) identities packaged together. -/
structure Zigzag (adj : AdjunctionData C D F G) : Prop where
  left : ∀ x : C, RwEq (adj.leftTriangle x) (Path.refl (F x))
  right : ∀ y : D, RwEq (adj.rightTriangle y) (Path.refl (G y))

/-- Left zigzag by explicit rewriting and inverse cancellation. -/
theorem left_zigzag_of_inverse
    (adj : AdjunctionData C D F G)
    (hε : LeftCounitInverse adj) :
    ∀ x : C, RwEq (adj.leftTriangle x) (Path.refl (F x)) := by
  intro x
  change
    RwEq
      (Path.trans (Path.congrArg F (adj.unit x)) (adj.counit (F x)))
      (Path.refl (F x))
  have hrewrite :
      RwEq
        (Path.trans (Path.congrArg F (adj.unit x)) (adj.counit (F x)))
        (Path.trans (Path.congrArg F (adj.unit x))
          (Path.symm (Path.congrArg F (adj.unit x)))) :=
    rweq_trans_congr_right (Path.congrArg F (adj.unit x)) (hε x)
  exact rweq_trans hrewrite (rweq_cmpA_inv_right (Path.congrArg F (adj.unit x)))

/-- Right zigzag by explicit rewriting and inverse cancellation. -/
theorem right_zigzag_of_inverse
    (adj : AdjunctionData C D F G)
    (hη : RightUnitInverse adj) :
    ∀ y : D, RwEq (adj.rightTriangle y) (Path.refl (G y)) := by
  intro y
  change
    RwEq
      (Path.trans (adj.unit (G y)) (Path.congrArg G (adj.counit y)))
      (Path.refl (G y))
  have hrewrite :
      RwEq
        (Path.trans (adj.unit (G y)) (Path.congrArg G (adj.counit y)))
        (Path.trans
          (Path.symm (Path.congrArg G (adj.counit y)))
          (Path.congrArg G (adj.counit y))) :=
    rweq_trans_congr_left (Path.congrArg G (adj.counit y)) (hη y)
  exact rweq_trans hrewrite (rweq_cmpA_inv_left (Path.congrArg G (adj.counit y)))

/-- Build both zigzag identities from inverse-style unit/counit rewrites. -/
def zigzag_of_inverse
    (adj : AdjunctionData C D F G)
    (hε : LeftCounitInverse adj)
    (hη : RightUnitInverse adj) :
    Zigzag adj where
  left := left_zigzag_of_inverse (adj := adj) hε
  right := right_zigzag_of_inverse (adj := adj) hη

end AdjunctionData

end Adjunction
end ComputationalPaths
