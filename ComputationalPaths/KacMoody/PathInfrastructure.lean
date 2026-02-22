import ComputationalPaths.KacMoody.KacMoodyAlgebraPaths
import ComputationalPaths.KacMoody.WeylGroupPaths

/-!
# Kac-Moody path infrastructure

This module couples Kac-Moody Lie-algebra path data with Weyl-group path data.
It exposes path-preserving Weyl actions and derived `RwEq` normalization lemmas.
-/

namespace ComputationalPaths
namespace KacMoody

open Path

universe u v w

/-- Compatibility package between Kac-Moody Lie and Weyl path models. -/
structure PathPreservingKacMoodyData (L : Type u) (W : Type v) (I : Type w) where
  algebra : KacMoodyAlgebraPathData L I
  weyl : WeylGroupPathData W I
  act : W → L → L
  actPath :
    {w₁ w₂ : W} → {x₁ x₂ : L} →
      Path w₁ w₂ → Path x₁ x₂ →
      Path (act w₁ x₁) (act w₂ x₂)
  /-- Path-level Weyl action of a simple reflection on its simple root. -/
  simpleActionPath :
    ∀ i : I, Path (act (weyl.simpleRef i) (algebra.simpleRoot i)) (algebra.coroot i)
  /-- Primitive right-unit normalization witness for simple actions. -/
  simpleActionStep :
    ∀ i : I,
      Path.Step
        (Path.trans (simpleActionPath i) (Path.refl (algebra.coroot i)))
        (simpleActionPath i)

namespace PathPreservingKacMoodyData

variable {L : Type u} {W : Type v} {I : Type w}
variable (K : PathPreservingKacMoodyData L W I)

noncomputable def simpleAction_rweq (i : I) :
    RwEq
      (Path.trans (K.simpleActionPath i) (Path.refl (K.algebra.coroot i)))
      (K.simpleActionPath i) :=
  rweq_of_step (K.simpleActionStep i)

noncomputable def simpleAction_cancel_rweq (i : I) :
    RwEq
      (Path.trans (Path.symm (K.simpleActionPath i)) (K.simpleActionPath i))
      (Path.refl (K.algebra.coroot i)) :=
  rweq_cmpA_inv_left (K.simpleActionPath i)

/-- Transport the Serre relation along a simple Weyl action. -/
noncomputable def transportedSerrePath (i j : I) :
    Path
      (K.act (K.weyl.simpleRef i)
        (K.algebra.adPower 2 (K.algebra.simpleRoot i) (K.algebra.simpleRoot j)))
      (K.act (K.weyl.simpleRef i) K.algebra.zero) :=
  K.actPath (Path.refl (K.weyl.simpleRef i)) (K.algebra.serrePath i j)

/-- Primitive normalization step for transported Serre relations. -/
noncomputable def transportedSerreStep (i j : I) :
    Path.Step
      (Path.trans
        (transportedSerrePath K i j)
        (Path.refl (K.act (K.weyl.simpleRef i) K.algebra.zero)))
      (transportedSerrePath K i j) :=
  Path.Step.trans_refl_right (transportedSerrePath K i j)

noncomputable def transportedSerre_rweq (i j : I) :
    RwEq
      (Path.trans
        (transportedSerrePath K i j)
        (Path.refl (K.act (K.weyl.simpleRef i) K.algebra.zero)))
      (transportedSerrePath K i j) :=
  rweq_of_step (transportedSerreStep K i j)

/-- Involutivity transported to the Lie action on a simple root. -/
noncomputable def reflectionSquarePath (i : I) :
    Path
      (K.act
        (K.weyl.mul (K.weyl.simpleRef i) (K.weyl.simpleRef i))
        (K.algebra.simpleRoot i))
      (K.act K.weyl.one (K.algebra.simpleRoot i)) :=
  K.actPath (K.weyl.involutivePath i) (Path.refl (K.algebra.simpleRoot i))

/-- Primitive normalization step for reflection-square transport. -/
noncomputable def reflectionSquareStep (i : I) :
    Path.Step
      (Path.trans
        (reflectionSquarePath K i)
        (Path.refl (K.act K.weyl.one (K.algebra.simpleRoot i))))
      (reflectionSquarePath K i) :=
  Path.Step.trans_refl_right (reflectionSquarePath K i)

noncomputable def reflectionSquare_rweq (i : I) :
    RwEq
      (Path.trans
        (reflectionSquarePath K i)
        (Path.refl (K.act K.weyl.one (K.algebra.simpleRoot i))))
      (reflectionSquarePath K i) :=
  rweq_of_step (reflectionSquareStep K i)

end PathPreservingKacMoodyData
end KacMoody
end ComputationalPaths
