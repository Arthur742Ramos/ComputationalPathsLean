/-
# Path 2-Category Structure

This module packages the 2-category structure of computational paths by
combining the bicategorical primitives with the double-groupoid interchange law.
We make the 0/1/2-cells explicit and record the vertical/horizontal unit laws.

## Key Results

- `Path1Cell`/`Path2Cell`: explicit `Path`-based 1/2-cells for the path 2-category.
- `TwoCategory`: a 2-category interface extending `WeakBicategory`.
- `pathTwoCategory`: the computational-path 2-category.
- `pathTwoCategory_to_weakBicategory`: compatibility with `weakBicategory`.

## References

- Leinster, "Higher Operads, Higher Categories"
- HoTT Book, Chapter 2
-/

import ComputationalPaths.Path.BicategoryDerived
import ComputationalPaths.Path.DoubleGroupoid

namespace ComputationalPaths
namespace Path

/-! ## Two-category interface -/

universe u v w

/-- A locally strict 2-category: a weak bicategory equipped with strict vertical
composition laws, horizontal unit laws, and the interchange law. -/
structure TwoCategory (Obj : Type u) extends WeakBicategory (Obj := Obj) where
  /-- Vertical composition is associative. -/
  vcomp_assoc :
    ∀ {a b : Obj} {f g h i : Hom a b}
      (η : TwoCell f g) (θ : TwoCell g h) (ι : TwoCell h i),
      vcomp (vcomp η θ) ι = vcomp η (vcomp θ ι)
  /-- Left identity for vertical composition. -/
  vcomp_left_id :
    ∀ {a b : Obj} {f g : Hom a b} (η : TwoCell f g),
      vcomp (id₂ f) η = η
  /-- Right identity for vertical composition. -/
  vcomp_right_id :
    ∀ {a b : Obj} {f g : Hom a b} (η : TwoCell f g),
      vcomp η (id₂ g) = η
  /-- Horizontal composition with a right identity 2-cell. -/
  hcomp_id_left :
    ∀ {a b c : Obj} {f g : Hom a b} {h : Hom b c}
      (η : TwoCell f g),
      hcomp η (id₂ h) = whiskerRight h η
  /-- Horizontal composition with a left identity 2-cell. -/
  hcomp_id_right :
    ∀ {a b c : Obj} {f : Hom a b} {g h : Hom b c}
      (η : TwoCell g h),
      hcomp (id₂ f) η = whiskerLeft f η
  /-- Interchange law between vertical and horizontal composition. -/
  interchange :
    ∀ {a b c : Obj} {f₀ f₁ f₂ : Hom a b} {g₀ g₁ g₂ : Hom b c}
      (η₁ : TwoCell f₀ f₁) (η₂ : TwoCell f₁ f₂)
      (θ₁ : TwoCell g₀ g₁) (θ₂ : TwoCell g₁ g₂),
      vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂) =
        hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂)
  /-- Pentagon coherence witnessed by an explicit computational-path 3-cell
  between the two standard composites of associators. -/
  pentagon_path :
    ∀ {a b c d e : Obj}
      (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e),
      CellPath
        (vcomp
          (vcomp (whiskerRight k (assoc f g h))
                 (assoc f (comp g h) k))
          (whiskerLeft f (assoc g h k)))
        (vcomp (assoc (comp f g) h k) (assoc f g (comp h k)))
  /-- Triangle coherence witnessed by an explicit computational-path 3-cell
  between the two standard composites built from associator and unitors. -/
  triangle_path :
    ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
      CellPath
        (vcomp
          (assoc f (id₁ b) g)
          (whiskerLeft f (leftUnitor g)))
        (whiskerRight g (rightUnitor f))

namespace TwoCategory

variable {Obj : Type u}

/-- Left route of Mac Lane's pentagon in a `TwoCategory`. -/
def pentagonLeftRoute (C : TwoCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) (k : C.Hom d e) :
    C.TwoCell (C.comp (C.comp (C.comp f g) h) k)
      (C.comp f (C.comp g (C.comp h k))) :=
  C.vcomp
    (C.vcomp (C.whiskerRight k (C.assoc f g h))
      (C.assoc f (C.comp g h) k))
    (C.whiskerLeft f (C.assoc g h k))

/-- Right route of Mac Lane's pentagon in a `TwoCategory`. -/
def pentagonRightRoute (C : TwoCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) (k : C.Hom d e) :
    C.TwoCell (C.comp (C.comp (C.comp f g) h) k)
      (C.comp f (C.comp g (C.comp h k))) :=
  C.vcomp (C.assoc (C.comp f g) h k) (C.assoc f g (C.comp h k))

/-- Left route of Mac Lane's triangle in a `TwoCategory`. -/
def triangleLeftRoute (C : TwoCategory (Obj := Obj))
    {a b c : Obj} (f : C.Hom a b) (g : C.Hom b c) :
    C.TwoCell (C.comp (C.comp f (C.id₁ b)) g) (C.comp f g) :=
  C.vcomp
    (C.assoc f (C.id₁ b) g)
    (C.whiskerLeft f (C.leftUnitor g))

/-- Right route of Mac Lane's triangle in a `TwoCategory`. -/
def triangleRightRoute (C : TwoCategory (Obj := Obj))
    {a b c : Obj} (f : C.Hom a b) (g : C.Hom b c) :
    C.TwoCell (C.comp (C.comp f (C.id₁ b)) g) (C.comp f g) :=
  C.whiskerRight g (C.rightUnitor f)

/-- Explicit computational-path witness for the pentagon identity. -/
def pentagonPath (C : TwoCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) (k : C.Hom d e) :
    CellPath (pentagonLeftRoute C f g h k) (pentagonRightRoute C f g h k) :=
  C.pentagon_path f g h k

/-- Explicit computational-path witness for the triangle identity. -/
def trianglePath (C : TwoCategory (Obj := Obj))
    {a b c : Obj} (f : C.Hom a b) (g : C.Hom b c) :
    CellPath (triangleLeftRoute C f g) (triangleRightRoute C f g) :=
  C.triangle_path f g

/-- Unfolded form of `pentagonLeftRoute`. -/
theorem pentagonLeftRoute_def (C : TwoCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) (k : C.Hom d e) :
    pentagonLeftRoute C f g h k =
      C.vcomp
        (C.vcomp (C.whiskerRight k (C.assoc f g h))
          (C.assoc f (C.comp g h) k))
        (C.whiskerLeft f (C.assoc g h k)) := by
  rfl

/-- Unfolded form of `pentagonRightRoute`. -/
theorem pentagonRightRoute_def (C : TwoCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) (k : C.Hom d e) :
    pentagonRightRoute C f g h k =
      C.vcomp (C.assoc (C.comp f g) h k) (C.assoc f g (C.comp h k)) := by
  rfl

/-- Unfolded form of `triangleLeftRoute`. -/
theorem triangleLeftRoute_def (C : TwoCategory (Obj := Obj))
    {a b c : Obj} (f : C.Hom a b) (g : C.Hom b c) :
    triangleLeftRoute C f g =
      C.vcomp
        (C.assoc f (C.id₁ b) g)
        (C.whiskerLeft f (C.leftUnitor g)) := by
  rfl

/-- Unfolded form of `triangleRightRoute`. -/
theorem triangleRightRoute_def (C : TwoCategory (Obj := Obj))
    {a b c : Obj} (f : C.Hom a b) (g : C.Hom b c) :
    triangleRightRoute C f g = C.whiskerRight g (C.rightUnitor f) := by
  rfl

/-- `pentagonPath` is the packaged pentagon coherence witness. -/
theorem pentagonPath_eq_pentagon_path (C : TwoCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : C.Hom a b) (g : C.Hom b c) (h : C.Hom c d) (k : C.Hom d e) :
    pentagonPath C f g h k = C.pentagon_path f g h k := by
  rfl

/-- `trianglePath` is the packaged triangle coherence witness. -/
theorem trianglePath_eq_triangle_path (C : TwoCategory (Obj := Obj))
    {a b c : Obj} (f : C.Hom a b) (g : C.Hom b c) :
    trianglePath C f g = C.triangle_path f g := by
  rfl

/-- Vertical composition is associative in any `TwoCategory`. -/
theorem vcomp_assoc_apply (C : TwoCategory (Obj := Obj))
    {a b : Obj} {f g h i : C.Hom a b}
    (η : C.TwoCell f g) (θ : C.TwoCell g h) (ι : C.TwoCell h i) :
    C.vcomp (C.vcomp η θ) ι = C.vcomp η (C.vcomp θ ι) :=
  C.vcomp_assoc η θ ι

/-- Left identity for vertical composition in any `TwoCategory`. -/
theorem vcomp_left_id_apply (C : TwoCategory (Obj := Obj))
    {a b : Obj} {f g : C.Hom a b} (η : C.TwoCell f g) :
    C.vcomp (C.id₂ f) η = η :=
  C.vcomp_left_id η

/-- Right identity for vertical composition in any `TwoCategory`. -/
theorem vcomp_right_id_apply (C : TwoCategory (Obj := Obj))
    {a b : Obj} {f g : C.Hom a b} (η : C.TwoCell f g) :
    C.vcomp η (C.id₂ g) = η :=
  C.vcomp_right_id η

/-- Horizontal-right unit compatibility in any `TwoCategory`. -/
theorem hcomp_id_left_apply (C : TwoCategory (Obj := Obj))
    {a b c : Obj} {f g : C.Hom a b} {h : C.Hom b c}
    (η : C.TwoCell f g) :
    C.hcomp η (C.id₂ h) = C.whiskerRight h η :=
  C.hcomp_id_left η

/-- Horizontal-left unit compatibility in any `TwoCategory`. -/
theorem hcomp_id_right_apply (C : TwoCategory (Obj := Obj))
    {a b c : Obj} {f : C.Hom a b} {g h : C.Hom b c}
    (η : C.TwoCell g h) :
    C.hcomp (C.id₂ f) η = C.whiskerLeft f η :=
  C.hcomp_id_right η

/-- Interchange law between horizontal and vertical composition. -/
theorem interchange_apply (C : TwoCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : C.Hom a b} {g₀ g₁ g₂ : C.Hom b c}
    (η₁ : C.TwoCell f₀ f₁) (η₂ : C.TwoCell f₁ f₂)
    (θ₁ : C.TwoCell g₀ g₁) (θ₂ : C.TwoCell g₁ g₂) :
    C.vcomp (C.hcomp η₁ θ₁) (C.hcomp η₂ θ₂) =
      C.hcomp (C.vcomp η₁ η₂) (C.vcomp θ₁ θ₂) :=
  C.interchange η₁ η₂ θ₁ θ₂

end TwoCategory

/-! ## Path 2-category -/

/-- 0-cells in the path 2-category are points of the underlying type. -/
abbrev Path0Cell (A : Type u) : Type u :=
  A

/-- 1-cells in the path 2-category are computational paths. -/
abbrev Path1Cell {A : Type u} (a b : A) : Type u :=
  Path a b

/-- 2-cells in the path 2-category are rewrite equalities (propositional). -/
abbrev Path2Cell {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  Nonempty (RwEq (A := A) (a := a) (b := b) p q)

/-- The 2-category carried by computational paths. -/
def pathTwoCategory (A : Type u) : TwoCategory (Obj := A) where
  toWeakBicategory := weakBicategory A
  vcomp_assoc := by
    intro a b f g h i η θ ι
    apply Subsingleton.elim
  vcomp_left_id := by
    intro a b f g η
    apply Subsingleton.elim
  vcomp_right_id := by
    intro a b f g η
    apply Subsingleton.elim
  hcomp_id_left := by
    intro a b c f g h η
    exact
      (BicategoryDerived.hcomp_id_left' (A := A) (a := a) (b := b) (c := c)
        (f := f) (g := g) (h := h) η)
  hcomp_id_right := by
    intro a b c f g h η
    exact
      (BicategoryDerived.hcomp_id_right' (A := A) (a := a) (b := b) (c := c)
        (f := f) (g := g) (h := h) η)
  interchange := by
    intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
    exact
      (DoubleGroupoid.pathDoubleGroupoid (A := A)).interchange
        (a := a) (b := b) (c := c)
        (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
        (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
        (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)
  pentagon_path := by
    intro a b c d e f g h k
    exact
      TwoCell.pentagonCoherence (A := A)
        (a := a) (b := b) (c := c) (d := d) (e := e) f g h k
  triangle_path := by
    intro a b c f g
    exact
      TwoCell.triangleCoherence (A := A)
        (a := a) (b := b) (c := c) f g

/-- The underlying bicategory of the path 2-category is the standard path bicategory. -/
@[simp] theorem pathTwoCategory_to_weakBicategory (A : Type u) :
    (pathTwoCategory A).toWeakBicategory = weakBicategory A := by
  rfl

/-! ## Summary -/

/-!
We introduced a strict 2-category interface, instantiated it for computational
paths, and connected the resulting structure to the existing path bicategory.
-/

end Path
end ComputationalPaths
