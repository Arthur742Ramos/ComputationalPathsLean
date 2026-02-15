/-
# Closed Monoidal Structure on Computational Paths

This module develops the closed monoidal structure on computational paths:
internal hom of paths, currying/uncurrying for path maps, evaluation,
exponential transpose, and cartesian closed structure.

## Key Results

- `PathEndoMap`: internal hom of paths (endomorphism space)
- `pathCurry` / `pathUncurry`: currying and uncurrying
- `pathEval`: evaluation map
- `pathExpTranspose`: exponential transpose
- Cartesian closed coherence laws

## References

- Lambek & Scott, "Introduction to Higher Order Categorical Logic"
- de Queiroz et al., "Propositional equality, identity types, and direct computational paths"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Category
namespace ClosedPaths

universe u v

variable {A : Type u}
variable {a b c d : A}

/-! ## Internal hom of paths -/

/-- An endomorphism in the path category: a self-map on paths. -/
structure PathEndoMap (A : Type u) (a : A) where
  mapPath : Path a a → Path a a
  map_refl : mapPath (Path.refl a) = Path.refl a

/-- Simple path map: a function that transforms paths. -/
def SimplePathMap (A : Type u) (a b : A) (c d : A) :=
  Path a b → Path c d

/-- Evaluation map: apply a path map to a path. -/
@[simp] def pathEval (f : SimplePathMap A a b c d) (p : Path a b) : Path c d :=
  f p

/-- Curry: given a function on pairs of paths, produce a function from
the first path to a function on the second path. -/
@[simp] def pathCurry {e f' : A}
    (g : Path a b → Path c d → Path e f') :
    Path a b → (Path c d → Path e f') :=
  g

/-- Uncurry: given a curried function, produce a function on pairs. -/
@[simp] def pathUncurry {e f' : A}
    (g : Path a b → (Path c d → Path e f')) :
    Path a b → Path c d → Path e f' :=
  g

/-- Curry-uncurry roundtrip is identity. -/
theorem curry_uncurry {e f' : A}
    (g : Path a b → Path c d → Path e f') :
    pathUncurry (pathCurry g) = g := rfl

/-- Uncurry-curry roundtrip is identity. -/
theorem uncurry_curry {e f' : A}
    (g : Path a b → (Path c d → Path e f')) :
    pathCurry (pathUncurry g) = g := rfl

/-! ## Exponential transpose -/

/-- Exponential transpose: given `h : P × Q → R`, produce `h' : P → (Q → R)`. -/
@[simp] def pathExpTranspose {B C : Type u} (h : A × B → C) : A → B → C :=
  fun a b => h (a, b)

/-- Inverse exponential transpose. -/
@[simp] def pathExpTransposeInv {B C : Type u} (h : A → B → C) : A × B → C :=
  fun ⟨a, b⟩ => h a b

/-- Transpose roundtrip. -/
theorem exp_transpose_roundtrip {B C : Type u} (h : A × B → C) :
    pathExpTransposeInv (pathExpTranspose h) = h := by
  funext ⟨a, b⟩; rfl

/-- Inverse transpose roundtrip. -/
theorem exp_transpose_inv_roundtrip {B C : Type u} (h : A → B → C) :
    pathExpTranspose (pathExpTransposeInv h) = h := by
  funext a b; rfl

/-! ## Path function space operations -/

/-- Identity path map: maps paths to themselves. -/
@[simp] def pathMapId : SimplePathMap A a b a b :=
  fun p => p

/-- Composition of path maps. -/
@[simp] def pathMapComp {e f' : A}
    (g : SimplePathMap A c d e f') (f : SimplePathMap A a b c d) :
    SimplePathMap A a b e f' :=
  fun p => g (f p)

/-- Identity path map is left unit. -/
theorem pathMapComp_id_left (f : SimplePathMap A a b c d) :
    pathMapComp pathMapId f = f := rfl

/-- Identity path map is right unit. -/
theorem pathMapComp_id_right (f : SimplePathMap A a b c d) :
    pathMapComp f pathMapId = f := rfl

/-- Composition of path maps is associative. -/
theorem pathMapComp_assoc {e f' g h : A}
    (k : SimplePathMap A e f' g h)
    (g' : SimplePathMap A c d e f')
    (f : SimplePathMap A a b c d) :
    pathMapComp k (pathMapComp g' f) = pathMapComp (pathMapComp k g') f := rfl

/-! ## Cartesian structure -/

/-- Product of paths as a path in the product type. -/
@[simp] def pathProd {B : Type u} {b1 b2 : B}
    (p : Path a b) (q : Path b1 b2) : Path (a, b1) (b, b2) :=
  Path.mk (p.steps.map (Step.map (·, b1)) ++ q.steps.map (Step.map (b, ·)))
    (by cases p with
        | mk _ proof_p => cases q with
          | mk _ proof_q => cases proof_p; cases proof_q; rfl)

/-- Projection from product path (first component). -/
@[simp] def pathFst {B : Type u} {b1 b2 : B}
    (p : Path (a, b1) (b, b2)) : Path a b :=
  Path.congrArg Prod.fst p

/-- Projection from product path (second component). -/
@[simp] def pathSnd {B : Type u} {b1 b2 : B}
    (p : Path (a, b1) (b, b2)) : Path b1 b2 :=
  Path.congrArg Prod.snd p

/-- First projection of product path recovers component equality. -/
theorem pathFst_pathProd {B : Type u} {b1 b2 : B}
    (p : Path a b) (q : Path b1 b2) :
    (pathFst (pathProd p q)).toEq = p.toEq := by
  cases p with
  | mk _ proof_p => cases q with
    | mk _ proof_q => cases proof_p; cases proof_q; rfl

/-- Second projection of product path recovers component equality. -/
theorem pathSnd_pathProd {B : Type u} {b1 b2 : B}
    (p : Path a b) (q : Path b1 b2) :
    (pathSnd (pathProd p q)).toEq = q.toEq := by
  cases p with
  | mk _ proof_p => cases q with
    | mk _ proof_q => cases proof_p; cases proof_q; rfl

/-! ## Closed structure coherence -/

/-- Evaluation respects identity. -/
theorem pathEval_id (p : Path a b) :
    pathEval pathMapId p = p := rfl

/-- Evaluation respects composition. -/
theorem pathEval_comp {e f' : A}
    (g : SimplePathMap A c d e f') (f : SimplePathMap A a b c d) (p : Path a b) :
    pathEval (pathMapComp g f) p = pathEval g (pathEval f p) := rfl

/-- Constant path map: sends everything to the identity path. -/
@[simp] def pathMapConst (c : A) : SimplePathMap A a b c c :=
  fun _ => Path.refl c

/-- Constant map always yields identity path. -/
theorem pathMapConst_val (c : A) (p : Path a b) :
    pathMapConst c p = Path.refl c := rfl

/-- Path map from congrArg. -/
def pathMapOfFun {B : Type u} (f : A → B) (a b : A) :
    Path a b → Path (f a) (f b) :=
  fun p => Path.congrArg f p

/-- congrArg map preserves identity. -/
theorem pathMapOfFun_refl {B : Type u} (f : A → B) (a : A) :
    pathMapOfFun f a a (Path.refl a) = Path.refl (f a) :=
  rfl

/-- congrArg map preserves composition. -/
theorem pathMapOfFun_trans {B : Type u} (f : A → B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    pathMapOfFun f a c (Path.trans p q) =
    Path.trans (pathMapOfFun f a b p) (pathMapOfFun f b c q) :=
  Path.congrArg_trans f p q

/-! ## Transport as internal hom -/

/-- Transport can be viewed as a map in the internal hom. -/
@[simp] def transportAsMap {D : A → Sort v} {a b : A} (p : Path a b) :
    D a → D b :=
  Path.transport p

/-- Transport map on identity path is identity. -/
theorem transportAsMap_refl {D : A → Sort v} (a : A) :
    transportAsMap (D := D) (Path.refl a) = id := by
  funext x; rfl

/-- Transport map composes. -/
theorem transportAsMap_trans {D : A → Sort v} {a b c : A}
    (p : Path a b) (q : Path b c) :
    transportAsMap (D := D) (Path.trans p q) =
    transportAsMap q ∘ transportAsMap p := by
  funext x; exact Path.transport_trans p q x

/-! ## PathEndoMap coherence -/

/-- The identity endomorphism. -/
def PathEndoMap.id (a : A) : PathEndoMap A a where
  mapPath := fun p => p
  map_refl := rfl

/-- Composition of path endomorphisms. -/
def PathEndoMap.comp (f g : PathEndoMap A a) : PathEndoMap A a where
  mapPath := fun p => f.mapPath (g.mapPath p)
  map_refl := by rw [g.map_refl, f.map_refl]

/-- Identity is left unit for endomorphism composition. -/
theorem PathEndoMap.comp_id (f : PathEndoMap A a) :
    PathEndoMap.comp (PathEndoMap.id a) f = f := by
  cases f; rfl

/-- Identity is right unit for endomorphism composition. -/
theorem PathEndoMap.id_comp (f : PathEndoMap A a) :
    PathEndoMap.comp f (PathEndoMap.id a) = f := by
  cases f; rfl

/-- Endomorphism composition is associative. -/
theorem PathEndoMap.comp_assoc (f g h : PathEndoMap A a) :
    PathEndoMap.comp (PathEndoMap.comp f g) h =
    PathEndoMap.comp f (PathEndoMap.comp g h) := by
  cases f; cases g; cases h; rfl

end ClosedPaths
end Category
end Path
end ComputationalPaths
