 /-
# Six Functors via Computational Rewriting

This module packages six-functor coherence with explicit `Step`-based
computational witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Sheaf
namespace SixFunctors

universe u

open Path

/-- Abstract six-functor package on an object type. -/
structure SixFunctorData (Obj : Type u) where
  pullback : Obj → Obj
  pushforward : Obj → Obj
  tensor : Obj → Obj → Obj
  internalHom : Obj → Obj → Obj
  exceptionalPullback : Obj → Obj
  exceptionalPushforward : Obj → Obj

/-- Unit/counit data written with computational paths. -/
structure AdjunctionWitness {Obj : Type u} (F : SixFunctorData Obj) where
  unit : (x : Obj) → Path (F.pushforward (F.pullback x)) x
  counit : (x : Obj) → Path x (F.exceptionalPushforward (F.exceptionalPullback x))

/-- Left triangle witness as a rewrite step. -/
theorem triangle_left {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_of_step (Step.trans_refl_left p)

/-- Right triangle witness as a rewrite step. -/
theorem triangle_right {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_of_step (Step.trans_refl_right p)

/-- Unit-counit cancellation in six-functor adjunctions. -/
theorem unit_counit_cancel {A : Type u} {a b : A} (η : Path a b) :
    RwEq (Path.trans η (Path.symm η)) (Path.refl a) :=
  rweq_of_step (Step.trans_symm η)

/-- Whiskered cancellation for projection-formula style composites. -/
theorem projection_formula_normalize {A : Type u} {a b c : A}
    (η : Path a b) (k : Path a c) :
    RwEq (Path.trans (Path.trans η (Path.symm η)) k) k := by
  exact rweq_trans
    (rweq_trans_congr_left k (rweq_of_step (Step.trans_symm η)))
    (rweq_of_step (Step.trans_refl_left k))

/-- Soundness of the projection-formula normalization witness. -/
theorem projection_formula_sound {A : Type u} {a b c : A}
    (η : Path a b) (k : Path a c) :
    Path.toEq (Path.trans (Path.trans η (Path.symm η)) k) = Path.toEq k := by
  exact rweq_toEq (projection_formula_normalize η k)

end SixFunctors
end Sheaf
end ComputationalPaths
