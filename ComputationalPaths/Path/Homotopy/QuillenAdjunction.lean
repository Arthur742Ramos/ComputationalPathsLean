/-
# Quillen Adjunctions for Path Model Categories

This module defines Quillen adjunction data for model categories built from
computational paths. The adjunction is expressed using `Path`-valued hom
equivalences, and the Quillen conditions are recorded as preservation of
cofibrations and fibrations.

## Key Results

- `PathSimpleEquiv`: path-valued equivalence data.
- `ModelFunctor`: path-level functors between model categories.
- `ModelAdjunction`: adjunction data for model functors.
- `LeftQuillen`, `RightQuillen`, `QuillenAdjunction`.
- `identityQuillenAdjunction`: identity Quillen adjunction.

## References

- Quillen, "Homotopical Algebra"
- Hovey, "Model Categories"
-/

import ComputationalPaths.Path.ModelCategory

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace QuillenAdjunction

universe u v

/-! ## Path-based equivalences -/

/-- Path-based equivalence structure. -/
structure PathSimpleEquiv (α : Type u) (β : Type v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse after forward map, witnessed by a path. -/
  left_inv : ∀ x : α, Path (invFun (toFun x)) x
  /-- Forward after inverse map, witnessed by a path. -/
  right_inv : ∀ y : β, Path (toFun (invFun y)) y

/-- Identity path equivalence. -/
def pathSimpleEquivRefl (α : Type u) : PathSimpleEquiv α α :=
  { toFun := _root_.id
    invFun := _root_.id
    left_inv := fun x => Path.refl x
    right_inv := fun x => Path.refl x }

/-! ## Model-category functors -/

section ModelFunctor

variable {A : Type u} {B : Type v}

/-- A path-level functor between model categories. -/
structure ModelFunctor (M : ModelCategory A) (N : ModelCategory B) where
  /-- Action on objects. -/
  obj : A → B
  /-- Action on paths. -/
  map : {a b : A} → Path a b → Path (obj a) (obj b)
  /-- Preservation of reflexive paths. -/
  map_refl : ∀ a, Path (map (Path.refl a)) (Path.refl (obj a))
  /-- Preservation of path composition. -/
  map_trans : ∀ {a b c : A} (p : Path a b) (q : Path b c),
    Path (map (Path.trans p q)) (Path.trans (map p) (map q))

namespace ModelFunctor

/-- Identity model functor. -/
def id (M : ModelCategory A) : ModelFunctor M M :=
  { obj := _root_.id
    map := fun p => p
    map_refl := fun a => Path.refl (Path.refl a)
    map_trans := fun p q => Path.refl (Path.trans p q) }

end ModelFunctor

end ModelFunctor

/-! ## Adjunction data -/

section ModelAdjunction

variable {A : Type u} {B : Type v}
variable {M : ModelCategory A} {N : ModelCategory B}
variable {F : ModelFunctor M N} {G : ModelFunctor N M}

/-- Adjunction data for model functors, expressed with path equivalences. -/
structure ModelAdjunction (M : ModelCategory A) (N : ModelCategory B)
    (F : ModelFunctor M N) (G : ModelFunctor N M) where
  /-- Path equivalence between hom types. -/
  homEquiv :
    ∀ a b, PathSimpleEquiv (Path (F.obj a) b) (Path a (G.obj b))

namespace ModelAdjunction

/-- Unit of a model adjunction. -/
def unit (adj : ModelAdjunction M N F G) (a : A) :
    Path a (G.obj (F.obj a)) :=
  (adj.homEquiv a (F.obj a)).toFun (Path.refl (F.obj a))

/-- Counit of a model adjunction. -/
def counit (adj : ModelAdjunction M N F G) (b : B) :
    Path (F.obj (G.obj b)) b :=
  (adj.homEquiv (G.obj b) b).invFun (Path.refl (G.obj b))

end ModelAdjunction

end ModelAdjunction

/-! ## Quillen conditions -/

section QuillenConditions

variable {A : Type u} {B : Type v}

/-- Left Quillen condition: preserves cofibrations and trivial cofibrations. -/
def LeftQuillen (M : ModelCategory A) (N : ModelCategory B)
    (F : ModelFunctor M N) : Prop :=
  (∀ {a b : A} (p : Path a b), M.cof p → N.cof (F.map p)) ∧
  (∀ {a b : A} (p : Path a b),
    ModelCategory.trivialCofibration M p →
      ModelCategory.trivialCofibration N (F.map p))

/-- Right Quillen condition: preserves fibrations and trivial fibrations. -/
def RightQuillen (M : ModelCategory A) (N : ModelCategory B)
    (F : ModelFunctor M N) : Prop :=
  (∀ {a b : A} (p : Path a b), M.fib p → N.fib (F.map p)) ∧
  (∀ {a b : A} (p : Path a b),
    ModelCategory.trivialFibration M p →
      ModelCategory.trivialFibration N (F.map p))

end QuillenConditions

/-! ## Quillen adjunctions -/

section QuillenAdjunction

variable {A : Type u} {B : Type v}

/-- Quillen adjunction between model categories. -/
structure QuillenAdjunction (M : ModelCategory A) (N : ModelCategory B) where
  /-- Left adjoint functor. -/
  left : ModelFunctor M N
  /-- Right adjoint functor. -/
  right : ModelFunctor N M
  /-- Path-based adjunction data. -/
  adj : ModelAdjunction M N left right
  /-- Left adjoint preserves cofibrations and trivial cofibrations. -/
  left_quillen : LeftQuillen M N left
  /-- Right adjoint preserves fibrations and trivial fibrations. -/
  right_quillen : RightQuillen N M right

/-- Identity adjunction for a model category. -/
def identityAdjunction (M : ModelCategory A) :
    ModelAdjunction M M (ModelFunctor.id M) (ModelFunctor.id M) :=
  { homEquiv := fun a b => pathSimpleEquivRefl (Path a b) }

/-- Identity Quillen adjunction on a model category. -/
def identityQuillenAdjunction (M : ModelCategory A) : QuillenAdjunction M M :=
  { left := ModelFunctor.id M
    right := ModelFunctor.id M
    adj := identityAdjunction (M := M)
    left_quillen := by
      refine And.intro ?_ ?_
      · intro a b p h
        simpa using h
      · intro a b p h
        simpa using h
    right_quillen := by
      refine And.intro ?_ ?_
      · intro a b p h
        simpa using h
      · intro a b p h
        simpa using h }

/-- Identity Quillen adjunction for the path model structure. -/
def pathModelQuillenAdjunction (A : Type u) :
    QuillenAdjunction (pathModelCategory A) (pathModelCategory A) :=
  identityQuillenAdjunction (M := pathModelCategory A)

end QuillenAdjunction

/-! ## Summary -/

end QuillenAdjunction
end Homotopy
end Path
end ComputationalPaths
