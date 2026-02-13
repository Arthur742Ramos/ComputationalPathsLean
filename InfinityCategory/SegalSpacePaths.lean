/- 
# Segal space path infrastructure

This module packages Segal-style composition for 1-simplices together with
explicit `Path.Step` witnesses for binary Segal composition and associativity.
-/

import InfinityCategory.QuasiCategoryPaths
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace InfinityCategory
namespace SegalSpacePaths

open Path

universe u

/-- Minimal Segal-space edge data valued in computational paths. -/
structure SegalPathSpace where
  Obj : Type u
  OneSimplex : Obj → Obj → Type u
  toPath : {x y : Obj} → OneSimplex x y → Path x y

namespace SegalPathSpace

/-- Canonical Segal path space with `Path` as 1-simplices. -/
def pathSpace (Obj : Type u) : SegalPathSpace where
  Obj := Obj
  OneSimplex := Path
  toPath := fun e => e

end SegalPathSpace

/-- Segal composition with explicit primitive rewrite witnesses. -/
structure SegalComposition (S : SegalPathSpace.{u}) where
  compose :
    {x y z : S.Obj} → S.OneSimplex x y → S.OneSimplex y z → S.OneSimplex x z
  binary_step :
    ∀ {x y z : S.Obj} (f : S.OneSimplex x y) (g : S.OneSimplex y z),
      Path.Step
        (Path.trans (Path.refl x) (Path.trans (S.toPath f) (S.toPath g)))
        (S.toPath (compose f g))
  assoc_step :
    ∀ {w x y z : S.Obj}
      (f : S.OneSimplex w x) (g : S.OneSimplex x y) (h : S.OneSimplex y z),
      Path.Step
        (Path.trans (S.toPath (compose f g)) (S.toPath h))
        (Path.trans (S.toPath f) (S.toPath (compose g h)))

namespace SegalComposition

variable {S : SegalPathSpace.{u}} (C : SegalComposition S)

@[simp] theorem binary_rweq {x y z : S.Obj}
    (f : S.OneSimplex x y) (g : S.OneSimplex y z) :
    RwEq
      (Path.trans (Path.refl x) (Path.trans (S.toPath f) (S.toPath g)))
      (S.toPath (C.compose f g)) :=
  rweq_of_step (C.binary_step f g)

@[simp] theorem assoc_rweq {w x y z : S.Obj}
    (f : S.OneSimplex w x) (g : S.OneSimplex x y) (h : S.OneSimplex y z) :
    RwEq
      (Path.trans (S.toPath (C.compose f g)) (S.toPath h))
      (Path.trans (S.toPath f) (S.toPath (C.compose g h))) :=
  rweq_of_step (C.assoc_step f g h)

end SegalComposition

/-- Segal composition induced from canonical quasi-category path composition. -/
def fromQuasi (Obj : Type u) :
    SegalComposition (SegalPathSpace.pathSpace Obj) where
  compose := (QuasiCategoryPaths.canonical Obj).compose
  binary_step := by
    intro x y z f g
    simpa using (QuasiCategoryPaths.canonical Obj).left_id_step (Path.trans f g)
  assoc_step := by
    intro w x y z f g h
    simpa using (QuasiCategoryPaths.canonical Obj).assoc_step f g h

/-- Canonical Segal composition on computational paths. -/
abbrev canonical (Obj : Type u) :
    SegalComposition (SegalPathSpace.pathSpace Obj) :=
  fromQuasi Obj

/-- Right-associated triple Segal composition in path form. -/
abbrev compose3 {S : SegalPathSpace.{u}} (C : SegalComposition S)
    {w x y z : S.Obj}
    (f : S.OneSimplex w x) (g : S.OneSimplex x y) (h : S.OneSimplex y z) :
    Path w z :=
  Path.trans (S.toPath f) (S.toPath (C.compose g h))

@[simp] theorem compose3_assoc_rweq (Obj : Type u)
    {w x y z : Obj} (f : Path w x) (g : Path x y) (h : Path y z) :
    RwEq
      (Path.trans (Path.trans f g) h)
      (compose3 (C := canonical Obj) f g h) :=
  rweq_of_step (Path.Step.trans_assoc f g h)

end SegalSpacePaths
end InfinityCategory
end ComputationalPaths
