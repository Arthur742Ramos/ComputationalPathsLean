/- 
# Subobject Classifier Coherence via Computational Paths

This module encodes subobject classifier coherence in a lightweight topos model
where all categorical laws and classification data are carried by explicit
`Path` witnesses and normalized through `RwEq`.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Topos
namespace SubobjectClassifierPaths

open Path

universe u v

/-- A category whose structural laws are given by computational paths. -/
structure ToposCategory where
  Obj : Type u
  Hom : Obj → Obj → Type v
  id : (X : Obj) → Hom X X
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z
  id_left : ∀ {X Y : Obj} (f : Hom X Y), Path (comp (id X) f) f
  id_right : ∀ {X Y : Obj} (f : Hom X Y), Path (comp f (id Y)) f
  assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    Path (comp (comp f g) h) (comp f (comp g h))

/-- Terminal object with uniqueness represented by computational paths. -/
structure TerminalObject (C : ToposCategory) where
  one : C.Obj
  toOne : (X : C.Obj) → C.Hom X one
  uniq : ∀ {X : C.Obj} (f g : C.Hom X one), Path f g

/-- Subobject classifier data with explicit classifying-square path coherence. -/
structure SubobjectClassifier (C : ToposCategory) (T : TerminalObject C) where
  Omega : C.Obj
  truth : C.Hom T.one Omega
  classify : {A B : C.Obj} → C.Hom A B → C.Hom B Omega
  classify_comm :
    ∀ {A B : C.Obj} (m : C.Hom A B),
      Path (C.comp m (classify m)) (C.comp (T.toOne A) truth)
  classify_unique :
    ∀ {A B : C.Obj} (m : C.Hom A B) (χ : C.Hom B Omega),
      Path (C.comp m χ) (C.comp (T.toOne A) truth) →
      Path χ (classify m)

namespace SubobjectClassifier

variable {C : ToposCategory} {T : TerminalObject C} (sc : SubobjectClassifier C T)

/-- The canonical classifying square witness for a monomorphism candidate. -/
abbrev classifyingPath {A B : C.Obj} (m : C.Hom A B) :
    Path (C.comp m (sc.classify m)) (C.comp (T.toOne A) sc.truth) :=
  sc.classify_comm m

/-- Left-unit insertion on a classifying path is rewrite-equivalent. -/
noncomputable def classifyingPath_unit_left {A B : C.Obj} (m : C.Hom A B) :
    RwEq
      (Path.trans
        (Path.refl (C.comp m (sc.classify m)))
        (sc.classifyingPath m))
      (sc.classifyingPath m) :=
  rweq_cmpA_refl_left (sc.classifyingPath m)

/-- Right-unit insertion on a classifying path is rewrite-equivalent. -/
noncomputable def classifyingPath_unit_right {A B : C.Obj} (m : C.Hom A B) :
    RwEq
      (Path.trans
        (sc.classifyingPath m)
        (Path.refl (C.comp (T.toOne A) sc.truth)))
      (sc.classifyingPath m) :=
  rweq_cmpA_refl_right (sc.classifyingPath m)

/-- A classifying path composed with its inverse contracts to reflexivity. -/
noncomputable def classifyingPath_cancel {A B : C.Obj} (m : C.Hom A B) :
    RwEq
      (Path.trans (sc.classifyingPath m) (Path.symm (sc.classifyingPath m)))
      (Path.refl (C.comp m (sc.classify m))) :=
  rweq_cmpA_inv_right (sc.classifyingPath m)

/-- Uniqueness of classifying maps is itself coherent under inverse cancellation. -/
noncomputable def classify_uniqueness_coherent {A B : C.Obj}
    (m : C.Hom A B) (χ : C.Hom B sc.Omega)
    (hχ : Path (C.comp m χ) (C.comp (T.toOne A) sc.truth)) :
    RwEq
      (Path.trans
        (sc.classify_unique m χ hχ)
        (Path.symm (sc.classify_unique m χ hχ)))
      (Path.refl χ) :=
  rweq_cmpA_inv_right (sc.classify_unique m χ hχ)

end SubobjectClassifier

end SubobjectClassifierPaths
end Topos
end ComputationalPaths
