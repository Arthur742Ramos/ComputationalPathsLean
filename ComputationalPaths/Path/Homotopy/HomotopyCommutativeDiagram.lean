/-
# Homotopy Commutative Diagrams in the Path Category

This module formalizes homotopy commutative squares in the path category. A
diagram is an arrow between types (a path algebra homomorphism), and a morphism
between diagrams is a square that commutes up to a computational homotopy. We
show that these squares compose to form a category and record the standard
lifting operations for homotopies.

## Key Results

- `Diagram`: arrows in the path category.
- `HomotopyCommSquare`: homotopy commutative squares between diagrams.
- `homotopy_precompose` / `homotopy_postcompose`: lift homotopies by whiskering.
- `homotopyCommDiagramCategory`: category structure on homotopy commutative diagrams.

## References

- HoTT Book, Chapter 2
- Mac Lane, "Categories for the Working Mathematician"
-/

import ComputationalPaths.Path.PathAlgebraHomomorphism
import ComputationalPaths.Path.Homotopy.HoTT

namespace ComputationalPaths
namespace Path
namespace HomotopyCommutativeDiagram

open HoTT

universe u

/-! ## Diagrams in the path category -/

/-- A diagram in the path category: a single arrow between types. -/
structure Diagram : Type (u + 1) where
  /-- Source object. -/
  source : Type u
  /-- Target object. -/
  target : Type u
  /-- The morphism in the path category. -/
  map : PathAlgebraHom source target

namespace Diagram

variable {A B : Type u}

/-- Precompose a diagram with a path algebra homomorphism. -/
noncomputable def precompose (F : Diagram) (f : PathAlgebraHom A F.source) : Diagram where
  source := A
  target := F.target
  map := PathAlgebraHom.comp f F.map

/-- Postcompose a diagram with a path algebra homomorphism. -/
noncomputable def postcompose (F : Diagram) (g : PathAlgebraHom F.target B) : Diagram where
  source := F.source
  target := B
  map := PathAlgebraHom.comp F.map g

end Diagram

/-! ## Homotopy commutative squares -/

/-- A homotopy commutative square between diagrams `F` and `G`. -/
structure HomotopyCommSquare (F G : Diagram.{u}) : Type (u + 1) where
  /-- Left map between sources. -/
  left : PathAlgebraHom F.source G.source
  /-- Right map between targets. -/
  right : PathAlgebraHom F.target G.target
  /-- Homotopy witnessing commutativity of the square. -/
  comm :
    FunHomotopy (PathAlgebraHom.comp F.map right)
      (PathAlgebraHom.comp left G.map)

/-! ## Homotopy lifting operations -/

/-- Precomposition lifts homotopies in the path category. -/
noncomputable def homotopy_precompose {A B C : Type u} (f : PathAlgebraHom A B)
    {g h : PathAlgebraHom B C} (H : FunHomotopy g h) :
    FunHomotopy (PathAlgebraHom.comp f g) (PathAlgebraHom.comp f h) :=
  fun x => H (f x)

/-- Postcomposition lifts homotopies in the path category. -/
noncomputable def homotopy_postcompose {A B C : Type u} (f : PathAlgebraHom B C)
    {g h : PathAlgebraHom A B} (H : FunHomotopy g h) :
    FunHomotopy (PathAlgebraHom.comp g f) (PathAlgebraHom.comp h f) :=
  fun x => PathAlgebraHom.map f (H x)

namespace HomotopyCommSquare

variable {F G H K : Diagram.{u}}

/-- Equality implies heterogeneous equality. -/
theorem heq_of_eq {α : Sort u} {a b : α} (h : a = b) : HEq a b := by
  cases h
  rfl

/-- Extensionality for homotopy commutative squares. -/
@[ext (iff := false)] theorem ext {eta theta : HomotopyCommSquare F G}
    (h_left : eta.left = theta.left)
    (h_right : eta.right = theta.right)
    (h_comm : HEq eta.comm theta.comm) : eta = theta := by
  cases eta with
  | mk leftEta rightEta commEta =>
    cases theta with
    | mk leftTheta rightTheta commTheta =>
      cases h_left
      cases h_right
      cases h_comm
      rfl

/-- Identity homotopy commutative square on a diagram. -/
noncomputable def id (F : Diagram.{u}) : HomotopyCommSquare F F where
  left := PathAlgebraHom.id F.source
  right := PathAlgebraHom.id F.target
  comm := fun x => Path.refl (F.map x)

/-- Vertical composition of homotopy commutative squares. -/
noncomputable def comp (eta : HomotopyCommSquare F G) (theta : HomotopyCommSquare G H) :
    HomotopyCommSquare F H where
  left := PathAlgebraHom.comp eta.left theta.left
  right := PathAlgebraHom.comp eta.right theta.right
  comm := fun x =>
    Path.trans (PathAlgebraHom.map theta.right (eta.comm x)) (theta.comm (eta.left x))

/-- Composition of squares is associative. -/
@[simp] theorem comp_assoc (eta : HomotopyCommSquare F G)
    (theta : HomotopyCommSquare G H) (kappa : HomotopyCommSquare H K) :
    comp (comp eta theta) kappa = comp eta (comp theta kappa) := by
  refine ext (h_left := rfl) (h_right := rfl) ?_
  apply heq_of_eq
  funext x
  simp [comp]

/-- Left identity for square composition. -/
@[simp] theorem id_comp (eta : HomotopyCommSquare F G) :
    comp (id F) eta = eta := by
  refine ext (h_left := rfl) (h_right := rfl) ?_
  apply heq_of_eq
  funext x
  simp [comp, id]
  cases eta.comm x
  rfl

/-- Right identity for square composition. -/
@[simp] theorem comp_id (eta : HomotopyCommSquare F G) :
    comp eta (id G) = eta := by
  refine ext (h_left := rfl) (h_right := rfl) ?_
  apply heq_of_eq
  funext x
  simp [comp, id]
  cases eta.comm x
  rfl

/-- Lift a square by precomposing its top edge. -/
noncomputable def precompose (square : HomotopyCommSquare F G) {A : Type u}
    (f : PathAlgebraHom A F.source) :
    HomotopyCommSquare (Diagram.precompose F f)
      (Diagram.precompose G (PathAlgebraHom.comp f square.left)) where
  left := PathAlgebraHom.id A
  right := square.right
  comm := homotopy_precompose f square.comm

/-- Lift a square by postcomposing its bottom edge. -/
noncomputable def postcompose (square : HomotopyCommSquare F G) {B : Type u}
    (g : PathAlgebraHom G.target B) :
    HomotopyCommSquare (Diagram.postcompose F (PathAlgebraHom.comp square.right g))
      (Diagram.postcompose G g) where
  left := square.left
  right := PathAlgebraHom.id B
  comm := homotopy_postcompose g square.comm

end HomotopyCommSquare

/-! ## Category structure -/

/-- Category structure on homotopy commutative diagrams. -/
structure HomotopyCommDiagramCategory : Type (u + 2) where
  /-- Identity square. -/
  id : ∀ F : Diagram.{u}, HomotopyCommSquare F F
  /-- Composition of squares. -/
  comp :
    ∀ {F G H : Diagram.{u}},
      HomotopyCommSquare F G → HomotopyCommSquare G H → HomotopyCommSquare F H
  /-- Associativity of composition. -/
  comp_assoc :
    ∀ {F G H K : Diagram.{u}} (eta : HomotopyCommSquare F G)
      (theta : HomotopyCommSquare G H) (kappa : HomotopyCommSquare H K),
      comp (comp eta theta) kappa = comp eta (comp theta kappa)
  /-- Left identity law. -/
  id_comp :
    ∀ {F G : Diagram.{u}} (eta : HomotopyCommSquare F G),
      comp (id F) eta = eta
  /-- Right identity law. -/
  comp_id :
    ∀ {F G : Diagram.{u}} (eta : HomotopyCommSquare F G),
      comp eta (id G) = eta

/-- The canonical category of homotopy commutative diagrams. -/
noncomputable def homotopyCommDiagramCategory : HomotopyCommDiagramCategory where
  id := HomotopyCommSquare.id
  comp := HomotopyCommSquare.comp
  comp_assoc := by
    intro F G H K eta theta kappa
    exact HomotopyCommSquare.comp_assoc (eta := eta) (theta := theta) (kappa := kappa)
  id_comp := by
    intro F G eta
    exact HomotopyCommSquare.id_comp (eta := eta)
  comp_id := by
    intro F G eta
    exact HomotopyCommSquare.comp_id (eta := eta)

/-! ## Summary -/

/-!
We packaged arrows in the path category as diagrams, defined homotopy commutative
squares between them, proved that these squares compose to form a category, and
recorded the standard homotopy lifting operations by pre- and postcomposition.
-/

end HomotopyCommutativeDiagram
end Path
end ComputationalPaths
