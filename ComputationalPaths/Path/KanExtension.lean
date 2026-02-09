/-
# Kan Extensions for Path Functors

This module defines left and right Kan extensions for path functors over the
fundamental groupoid. We record precomposition along a functor, the Kan
extension data with universal property packaged as `SimpleEquiv`, and simple
pointwise formulas for left and right Kan extensions.

## Key Results

- `PathFunctor.precompose`: precomposition of a path functor.
- `LeftKanExtension`, `RightKanExtension`: Kan extension data and universal property.
- `pointwiseLeftKan`, `pointwiseRightKan`: pointwise Kan extensions via sigma/pi formulas.

## References

- Mac Lane, *Categories for the Working Mathematician*
- Riehl, *Category Theory in Context*
-/

import ComputationalPaths.Path.YonedaLemma
import ComputationalPaths.Path.Homotopy.FundamentalGroupoidFunctor

namespace ComputationalPaths
namespace Path

universe u v

/-! ## Precomposition of path functors -/

namespace PathFunctor

variable {A B : Type u}

/-- Precompose a path functor along a fundamental groupoid functor. -/
def precompose (F : FundamentalGroupoidFunctor A B)
    (G : PathFunctor.{u, v} (A := B)) : PathFunctor.{u, v} (A := A) where
  obj := fun a => G.obj (F.obj a)
  map := fun {a b} p x => G.map (F.map p) x
  map_id := by
    intro a x
    have h := F.map_id a
    simpa [h] using (G.map_id (F.obj a) x)
  map_comp := by
    intro a b c p q x
    have h := F.map_comp (p := p) (q := q)
    simpa [h] using (G.map_comp (p := F.map p) (q := F.map q) (x := x))

end PathFunctor

/-! ## Kan extension data -/

section KanExtensions

variable {A B : Type u}

/-- Data for a left Kan extension of a path functor. -/
structure LeftKanExtension (F : FundamentalGroupoidFunctor A B)
    (G : PathFunctor.{u, v} (A := A)) where
  /-- The left Kan extension functor. -/
  lan : PathFunctor.{u, v} (A := B)
  /-- The unit natural transformation. -/
  unit : PathNatTrans G (PathFunctor.precompose F lan)
  /-- Universal property as an equivalence of natural transformation spaces. -/
  universal :
    ∀ (M : PathFunctor.{u, v} (A := B)),
      SimpleEquiv (PathNatTrans lan M)
        (PathNatTrans G (PathFunctor.precompose F M))

/-- Data for a right Kan extension of a path functor. -/
structure RightKanExtension (F : FundamentalGroupoidFunctor A B)
    (G : PathFunctor.{u, v} (A := A)) where
  /-- The right Kan extension functor. -/
  ran : PathFunctor.{u, v} (A := B)
  /-- The counit natural transformation. -/
  counit : PathNatTrans (PathFunctor.precompose F ran) G
  /-- Universal property as an equivalence of natural transformation spaces. -/
  universal :
    ∀ (M : PathFunctor.{u, v} (A := B)),
      SimpleEquiv (PathNatTrans M ran)
        (PathNatTrans (PathFunctor.precompose F M) G)

end KanExtensions

/-! ## Pointwise Kan extensions -/

section Pointwise

variable {A B : Type u}
variable (F : FundamentalGroupoidFunctor A B) (G : PathFunctor.{u, v} (A := A))

/-- Pointwise object for the left Kan extension. -/
def pointwiseLeftKanObj (b : B) : Type (max u v) :=
  Sigma fun a : A =>
    Sigma fun _ : FundamentalGroupoid.Hom B (F.obj a) b =>
      G.obj a

/-- Action on morphisms for the pointwise left Kan extension. -/
def pointwiseLeftKanMap {b b' : B} (q : FundamentalGroupoid.Hom B b b') :
    pointwiseLeftKanObj F G b → pointwiseLeftKanObj F G b'
  | ⟨a, ⟨p, x⟩⟩ => ⟨a, ⟨FundamentalGroupoid.comp' B p q, x⟩⟩

/-- Pointwise left Kan extension as a path functor. -/
def pointwiseLeftKan : PathFunctor.{u, max u v} (A := B) where
  obj := pointwiseLeftKanObj F G
  map := fun {b b'} q x => pointwiseLeftKanMap (F := F) (G := G) (b := b) (b' := b') q x
  map_id := by
    intro b x
    cases x with
    | mk a px =>
      cases px with
      | mk p y =>
        simp [pointwiseLeftKanMap, FundamentalGroupoid.comp_id']
  map_comp := by
    intro b c d q r x
    cases x with
    | mk a px =>
      cases px with
      | mk p y =>
        simp [pointwiseLeftKanMap, FundamentalGroupoid.comp_assoc']

/-- Pointwise object for the right Kan extension. -/
def pointwiseRightKanObj (b : B) : Type (max u v) :=
  ∀ a : A, FundamentalGroupoid.Hom B b (F.obj a) → G.obj a

/-- Action on morphisms for the pointwise right Kan extension. -/
def pointwiseRightKanMap {b b' : B} (q : FundamentalGroupoid.Hom B b b') :
    pointwiseRightKanObj F G b → pointwiseRightKanObj F G b'
  | h => fun a p => h a (FundamentalGroupoid.comp' B q p)

/-- Pointwise right Kan extension as a path functor. -/
def pointwiseRightKan : PathFunctor.{u, max u v} (A := B) where
  obj := pointwiseRightKanObj F G
  map := fun {b b'} q h => pointwiseRightKanMap (F := F) (G := G) (b := b) (b' := b') q h
  map_id := by
    intro b h
    funext a p
    simp [pointwiseRightKanMap, FundamentalGroupoid.id_comp']
  map_comp := by
    intro b c d q r h
    funext a p
    simp [pointwiseRightKanMap, FundamentalGroupoid.comp_assoc']

end Pointwise

/-! ## Summary -/

/-!
We defined precomposition for path functors, packaged left and right Kan
extension data with a universal property encoded as `SimpleEquiv`, and provided
simple pointwise formulas for left and right Kan extensions.
-/

end Path
end ComputationalPaths
