/- 
# Quasi-category path infrastructure

This module exposes object-level quasi-category composition in the
computational-path setting, with explicit `Path.Step` witnesses for
left/right units and associativity.
-/

import ComputationalPaths.Path.Homotopy.QuasiCategory
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace InfinityCategory
namespace QuasiCategoryPaths

open Path
open Path.Homotopy

universe u

/-- Step-based composition package for path-valued quasi-category morphisms. -/
structure QuasiPathComposition (Obj : Type u) where
  compose : {x y z : Obj} → Path x y → Path y z → Path x z
  left_id_step :
    ∀ {x y : Obj} (p : Path x y),
      Path.Step (compose (Path.refl x) p) p
  right_id_step :
    ∀ {x y : Obj} (p : Path x y),
      Path.Step (compose p (Path.refl y)) p
  assoc_step :
    ∀ {w x y z : Obj}
      (p : Path w x) (q : Path x y) (r : Path y z),
      Path.Step (compose (compose p q) r) (compose p (compose q r))

namespace QuasiPathComposition

variable {Obj : Type u} (Q : QuasiPathComposition Obj)

noncomputable def left_id_rweq {x y : Obj} (p : Path x y) :
    RwEq (Q.compose (Path.refl x) p) p :=
  rweq_of_step (Q.left_id_step p)

noncomputable def right_id_rweq {x y : Obj} (p : Path x y) :
    RwEq (Q.compose p (Path.refl y)) p :=
  rweq_of_step (Q.right_id_step p)

noncomputable def assoc_rweq {w x y z : Obj}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    RwEq (Q.compose (Q.compose p q) r) (Q.compose p (Q.compose q r)) :=
  rweq_of_step (Q.assoc_step p q r)

end QuasiPathComposition

/-- Canonical quasi-category composition on paths is `Path.trans`. -/
def canonical (Obj : Type u) : QuasiPathComposition Obj where
  compose := fun p q => Path.trans p q
  left_id_step := fun p => Path.Step.trans_refl_left p
  right_id_step := fun p => Path.Step.trans_refl_right p
  assoc_step := fun p q r => Path.Step.trans_assoc p q r

/-- Every quasi-category inherits canonical composition on object paths. -/
abbrev onObjects (C : Homotopy.QuasiCategory) : QuasiPathComposition C.obj :=
  canonical C.obj

/-- Object-level composition in a quasi-category, tracked by computational paths. -/
abbrev composeObjPaths (C : Homotopy.QuasiCategory)
    {x y z : C.obj} (p : Path x y) (q : Path y z) : Path x z :=
  (onObjects C).compose p q

noncomputable def composeObjPaths_assoc (C : Homotopy.QuasiCategory)
    {w x y z : C.obj} (p : Path w x) (q : Path x y) (r : Path y z) :
    RwEq (composeObjPaths C (composeObjPaths C p q) r)
      (composeObjPaths C p (composeObjPaths C q r)) :=
  QuasiPathComposition.assoc_rweq (Q := onObjects C) p q r

end QuasiCategoryPaths
end InfinityCategory
end ComputationalPaths
