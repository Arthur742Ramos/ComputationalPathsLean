/-
# Gray-category structure for computational paths

This module extends the path `TwoCategory` interface with an explicit
computational-path witness for interchange, yielding a lightweight Gray-category
layer with pentagon/triangle coherence inherited as 3-cells.
-/

import ComputationalPaths.Path.TwoCategory

namespace ComputationalPaths
namespace Path

universe u

/-- A semistrict Gray-category: a `TwoCategory` equipped with an explicit
computational-path 3-cell for interchange coherence. -/
structure GrayCategory (Obj : Type u) extends TwoCategory (Obj := Obj) where
  interchange_path :
    ∀ {a b c : Obj} {f₀ f₁ f₂ : Hom a b} {g₀ g₁ g₂ : Hom b c}
      (η₁ : TwoCell f₀ f₁) (η₂ : TwoCell f₁ f₂)
      (θ₁ : TwoCell g₀ g₁) (θ₂ : TwoCell g₁ g₂),
      CellPath
        (vcomp (hcomp η₁ θ₁) (hcomp η₂ θ₂))
        (hcomp (vcomp η₁ η₂) (vcomp θ₁ θ₂))

namespace GrayCategory

variable {Obj : Type u}

/-- Pentagon coherence as a computational-path 3-cell. -/
def pentagonPath (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    CellPath
      (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
      (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k) :=
  TwoCategory.pentagonPath G.toTwoCategory f g h k

/-- Triangle coherence as a computational-path 3-cell. -/
def trianglePath (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    CellPath
      (TwoCategory.triangleLeftRoute G.toTwoCategory f g)
      (TwoCategory.triangleRightRoute G.toTwoCategory f g) :=
  TwoCategory.trianglePath G.toTwoCategory f g

/-- Interchange coherence as a computational-path 3-cell. -/
def interchangePath (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    CellPath
      (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
      (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) :=
  G.interchange_path η₁ η₂ θ₁ θ₂

/-- The interchange 3-cell in `CellPath` implies the interchange equation. -/
theorem gray_interchange_from_path (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂) =
      G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂) := by
  simpa using _root_.congrArg PLift.down
    (Path.toEq (G.interchangePath η₁ η₂ θ₁ θ₂))

/-- The interchange equation induces a canonical `CellPath` witness. -/
def gray_interchange_path_from_interchange (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    CellPath
      (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
      (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) :=
  Path.mk
    [Step.mk _ _ (_root_.congrArg PLift.up (G.interchange η₁ η₂ θ₁ θ₂))]
    (_root_.congrArg PLift.up (G.interchange η₁ η₂ θ₁ θ₂))

/-- Interchange with identity 2-cells collapses to the original tensor. -/
theorem gray_interchange_unit (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ : G.Hom a b} {g₀ g₁ : G.Hom b c}
    (η : G.TwoCell f₀ f₁) (θ : G.TwoCell g₀ g₁) :
    G.vcomp (G.hcomp η (G.id₂ g₀)) (G.hcomp (G.id₂ f₁) θ) =
      G.hcomp η θ := by
  calc
    G.vcomp (G.hcomp η (G.id₂ g₀)) (G.hcomp (G.id₂ f₁) θ)
        = G.hcomp (G.vcomp η (G.id₂ f₁)) (G.vcomp (G.id₂ g₀) θ) := by
            exact G.interchange (η₁ := η) (η₂ := G.id₂ f₁)
              (θ₁ := G.id₂ g₀) (θ₂ := θ)
    _ = G.hcomp η θ := by
          rw [G.vcomp_right_id, G.vcomp_left_id]

/-- Interchange composes associatively across triples of composable 2-cells. -/
theorem gray_interchange_assoc (G : GrayCategory (Obj := Obj))
    {a b c : Obj}
    {f₀ f₁ f₂ f₃ : G.Hom a b} {g₀ g₁ g₂ g₃ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂) (η₃ : G.TwoCell f₂ f₃)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) (θ₃ : G.TwoCell g₂ g₃) :
    G.vcomp (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂)) (G.hcomp η₃ θ₃) =
      G.hcomp (G.vcomp η₁ (G.vcomp η₂ η₃))
        (G.vcomp θ₁ (G.vcomp θ₂ θ₃)) := by
  calc
    G.vcomp (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂)) (G.hcomp η₃ θ₃)
        = G.vcomp (G.hcomp η₁ θ₁)
            (G.vcomp (G.hcomp η₂ θ₂) (G.hcomp η₃ θ₃)) := by
              exact G.vcomp_assoc (η := G.hcomp η₁ θ₁)
                (θ := G.hcomp η₂ θ₂) (ι := G.hcomp η₃ θ₃)
    _ = G.vcomp (G.hcomp η₁ θ₁)
          (G.hcomp (G.vcomp η₂ η₃) (G.vcomp θ₂ θ₃)) := by
            rw [G.interchange (η₁ := η₂) (η₂ := η₃) (θ₁ := θ₂) (θ₂ := θ₃)]
    _ = G.hcomp (G.vcomp η₁ (G.vcomp η₂ η₃))
          (G.vcomp θ₁ (G.vcomp θ₂ θ₃)) := by
            rw [G.interchange (η₁ := η₁) (η₂ := G.vcomp η₂ η₃)
              (θ₁ := θ₁) (θ₂ := G.vcomp θ₂ θ₃)]

/-- A tensor-associative form of interchange for three composable factors. -/
theorem gray_tensor_assoc (G : GrayCategory (Obj := Obj))
    {a b c : Obj}
    {f₀ f₁ f₂ f₃ : G.Hom a b} {g₀ g₁ g₂ g₃ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂) (η₃ : G.TwoCell f₂ f₃)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) (θ₃ : G.TwoCell g₂ g₃) :
    G.vcomp (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) (G.hcomp η₃ θ₃) =
      G.hcomp (G.vcomp η₁ (G.vcomp η₂ η₃))
        (G.vcomp θ₁ (G.vcomp θ₂ θ₃)) := by
  calc
    G.vcomp (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) (G.hcomp η₃ θ₃)
        = G.vcomp (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
            (G.hcomp η₃ θ₃) := by
              rw [(G.interchange (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)).symm]
    _ = G.hcomp (G.vcomp η₁ (G.vcomp η₂ η₃))
          (G.vcomp θ₁ (G.vcomp θ₂ θ₃)) :=
        gray_interchange_assoc (G := G) η₁ η₂ η₃ θ₁ θ₂ θ₃

/-- Associativity of the Gray tensor product in equation form. -/
theorem gray_tensor_product_associative (G : GrayCategory (Obj := Obj))
    {a b c : Obj}
    {f₀ f₁ f₂ f₃ : G.Hom a b} {g₀ g₁ g₂ g₃ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂) (η₃ : G.TwoCell f₂ f₃)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) (θ₃ : G.TwoCell g₂ g₃) :
    G.vcomp (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) (G.hcomp η₃ θ₃) =
      G.hcomp (G.vcomp η₁ (G.vcomp η₂ η₃))
        (G.vcomp θ₁ (G.vcomp θ₂ θ₃)) :=
  gray_tensor_assoc (G := G) η₁ η₂ η₃ θ₁ θ₂ θ₃

/-- The tensor-product associativity equation yields explicit 3-cell coherence data. -/
theorem gray_tensor_product_associative_nonempty (G : GrayCategory (Obj := Obj))
    {a b c : Obj}
    {f₀ f₁ f₂ f₃ : G.Hom a b} {g₀ g₁ g₂ g₃ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂) (η₃ : G.TwoCell f₂ f₃)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) (θ₃ : G.TwoCell g₂ g₃) :
    Nonempty (CellPath
      (G.vcomp (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂)) (G.hcomp η₃ θ₃))
      (G.hcomp (G.vcomp η₁ (G.vcomp η₂ η₃))
        (G.vcomp θ₁ (G.vcomp θ₂ θ₃)))) :=
  ⟨Path.mk
    [Step.mk _ _
      (_root_.congrArg PLift.up
        (gray_tensor_product_associative (G := G) η₁ η₂ η₃ θ₁ θ₂ θ₃))]
    (_root_.congrArg PLift.up
      (gray_tensor_product_associative (G := G) η₁ η₂ η₃ θ₁ θ₂ θ₃))⟩

/-- Gray tensor (horizontal composition) is functorial: interchange swaps
the direction of the 3-cell. -/
theorem gray_tensor_functorial (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂) =
      G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂) := by
  exact (G.interchange (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)).symm

/-- The interchange 3-cell source and target are related by the interchange
equation. -/
theorem gray_interchange_eq (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂) =
      G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂) :=
  G.interchange η₁ η₂ θ₁ θ₂

/-- Symmetric form of Gray interchange. -/
theorem gray_interchange_eq_symm (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂) =
      G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂) :=
  (G.interchange η₁ η₂ θ₁ θ₂).symm

/-- Interchange always gives explicit 3-cell coherence data. -/
theorem gray_interchange_nonempty (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂)
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    Nonempty (CellPath
      (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
      (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂))) :=
  ⟨G.interchangePath η₁ η₂ θ₁ θ₂⟩

/-- Gray-categories inherit pentagon coherence from their underlying 2-category. -/
def gray_pentagon_from_interchange (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    CellPath
      (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
      (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k) :=
  G.pentagonPath f g h k

/-- A Gray-category carries pentagon 3-cell data. -/
def gray_to_tricategory_coherence_pentagon (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    CellPath
      (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
      (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k) :=
  G.pentagonPath f g h k

/-- A Gray-category carries triangle 3-cell data. -/
def gray_to_tricategory_coherence_triangle (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    CellPath
      (TwoCategory.triangleLeftRoute G.toTwoCategory f g)
      (TwoCategory.triangleRightRoute G.toTwoCategory f g) :=
  G.trianglePath f g

/-- Gray interchange with left identity is whiskerLeft. -/
theorem gray_interchange_id_left (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f : G.Hom a b} {g₀ g₁ g₂ : G.Hom b c}
    (θ₁ : G.TwoCell g₀ g₁) (θ₂ : G.TwoCell g₁ g₂) :
    G.vcomp (G.hcomp (G.id₂ f) θ₁) (G.hcomp (G.id₂ f) θ₂) =
      G.hcomp (G.id₂ f) (G.vcomp θ₁ θ₂) := by
  rw [G.interchange (η₁ := G.id₂ f) (η₂ := G.id₂ f) (θ₁ := θ₁) (θ₂ := θ₂)]
  rw [G.vcomp_left_id]

/-- Gray interchange with right identity is whiskerRight. -/
theorem gray_interchange_id_right (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : G.Hom a b} {g : G.Hom b c}
    (η₁ : G.TwoCell f₀ f₁) (η₂ : G.TwoCell f₁ f₂) :
    G.vcomp (G.hcomp η₁ (G.id₂ g)) (G.hcomp η₂ (G.id₂ g)) =
      G.hcomp (G.vcomp η₁ η₂) (G.id₂ g) := by
  rw [G.interchange (η₁ := η₁) (η₂ := η₂) (θ₁ := G.id₂ g) (θ₂ := G.id₂ g)]
  rw [G.vcomp_left_id]

/-- Gray interchange preserves units on both sides. -/
theorem gray_interchange_units (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    G.vcomp (G.hcomp (G.id₂ f) (G.id₂ g))
        (G.hcomp (G.id₂ f) (G.id₂ g)) =
      G.hcomp (G.id₂ f) (G.id₂ g) := by
  have h := G.interchange (η₁ := G.id₂ f) (η₂ := G.id₂ f)
    (θ₁ := G.id₂ g) (θ₂ := G.id₂ g)
  rw [h, G.vcomp_left_id, G.vcomp_left_id]

/-- Tensor naturality: hcomp is natural in both variables. -/
theorem gray_tensor_naturality (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ : G.Hom a b} {g₀ g₁ : G.Hom b c}
    (η : G.TwoCell f₀ f₁) (θ : G.TwoCell g₀ g₁) :
    G.vcomp (G.whiskerRight g₀ η) (G.whiskerLeft f₁ θ) =
      G.hcomp η θ := by
  calc G.vcomp (G.whiskerRight g₀ η) (G.whiskerLeft f₁ θ)
      = G.vcomp (G.hcomp η (G.id₂ g₀)) (G.hcomp (G.id₂ f₁) θ) := by
          rw [G.hcomp_id_left, G.hcomp_id_right]
    _ = G.hcomp η θ := gray_interchange_unit G η θ

/-- Tensor naturality (other direction): whiskerLeft then whiskerRight. -/
theorem gray_tensor_naturality' (G : GrayCategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ : G.Hom a b} {g₀ g₁ : G.Hom b c}
    (η : G.TwoCell f₀ f₁) (θ : G.TwoCell g₀ g₁) :
    G.vcomp (G.whiskerLeft f₀ θ) (G.whiskerRight g₁ η) =
      G.hcomp η θ := by
  calc G.vcomp (G.whiskerLeft f₀ θ) (G.whiskerRight g₁ η)
      = G.vcomp (G.hcomp (G.id₂ f₀) θ) (G.hcomp η (G.id₂ g₁)) := by
          rw [G.hcomp_id_right, G.hcomp_id_left]
    _ = G.hcomp (G.vcomp (G.id₂ f₀) η) (G.vcomp θ (G.id₂ g₁)) := by
          rw [G.interchange]
    _ = G.hcomp η θ := by
          rw [G.vcomp_left_id, G.vcomp_right_id]

/-- Gray pentagon data matches the tricategory-facing packaging. -/
@[simp] theorem gray_to_tricategory_coherence_pentagon_eq
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    gray_to_tricategory_coherence_pentagon G f g h k = G.pentagonPath f g h k := by
  rfl

/-- Gray triangle data matches the tricategory-facing packaging. -/
@[simp] theorem gray_to_tricategory_coherence_triangle_eq
    (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    gray_to_tricategory_coherence_triangle G f g = G.trianglePath f g := by
  rfl

/-- A Gray-category provides the pair of coherence cells required for a tricategory interface. -/
theorem gray_to_tricategory_coherence_data
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e)
    {a' b' c' : Obj} (f' : G.Hom a' b') (g' : G.Hom b' c') :
    Nonempty (CellPath
      (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
      (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k))
    ∧
    Nonempty (CellPath
      (TwoCategory.triangleLeftRoute G.toTwoCategory f' g')
      (TwoCategory.triangleRightRoute G.toTwoCategory f' g')) := by
  exact
    ⟨⟨gray_to_tricategory_coherence_pentagon G f g h k⟩,
      ⟨gray_to_tricategory_coherence_triangle G f' g'⟩⟩

/-- Gray pentagon coherence supplies tricategory pentagonator data. -/
theorem gray_to_tricategory_pentagon_nonempty
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    Nonempty (CellPath
      (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
      (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k)) :=
  ⟨gray_to_tricategory_coherence_pentagon G f g h k⟩

/-- Gray triangle coherence supplies tricategory triangulator data. -/
theorem gray_to_tricategory_triangle_nonempty
    (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    Nonempty (CellPath
      (TwoCategory.triangleLeftRoute G.toTwoCategory f g)
      (TwoCategory.triangleRightRoute G.toTwoCategory f g)) :=
  ⟨gray_to_tricategory_coherence_triangle G f g⟩

/-- Gray interchange supplies the tricategorical interchange coherence cell. -/
theorem gray_to_tricategory_interchange_nonempty
    (G : GrayCategory (Obj := Obj))
    {x y z : Obj} {u₀ u₁ u₂ : G.Hom x y} {v₀ v₁ v₂ : G.Hom y z}
    (η₁ : G.TwoCell u₀ u₁) (η₂ : G.TwoCell u₁ u₂)
    (θ₁ : G.TwoCell v₀ v₁) (θ₂ : G.TwoCell v₁ v₂) :
    Nonempty (CellPath
      (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
      (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂))) :=
  ⟨G.interchangePath η₁ η₂ θ₁ θ₂⟩

/-- A Gray-category provides all coherence cells needed for a tricategory interface. -/
theorem gray_to_tricategory_full_coherence_data
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e)
    {a' b' c' : Obj} (f' : G.Hom a' b') (g' : G.Hom b' c')
    {x y z : Obj} {u₀ u₁ u₂ : G.Hom x y} {v₀ v₁ v₂ : G.Hom y z}
    (η₁ : G.TwoCell u₀ u₁) (η₂ : G.TwoCell u₁ u₂)
    (θ₁ : G.TwoCell v₀ v₁) (θ₂ : G.TwoCell v₁ v₂) :
    Nonempty (CellPath
      (TwoCategory.pentagonLeftRoute G.toTwoCategory f g h k)
      (TwoCategory.pentagonRightRoute G.toTwoCategory f g h k))
    ∧ Nonempty (CellPath
      (TwoCategory.triangleLeftRoute G.toTwoCategory f' g')
      (TwoCategory.triangleRightRoute G.toTwoCategory f' g'))
    ∧ Nonempty (CellPath
      (G.vcomp (G.hcomp η₁ θ₁) (G.hcomp η₂ θ₂))
      (G.hcomp (G.vcomp η₁ η₂) (G.vcomp θ₁ θ₂))) := by
  refine ⟨gray_to_tricategory_pentagon_nonempty (G := G) f g h k, ?_⟩
  refine ⟨gray_to_tricategory_triangle_nonempty (G := G) f' g', ?_⟩
  exact gray_to_tricategory_interchange_nonempty (G := G) η₁ η₂ θ₁ θ₂

end GrayCategory

/-- Computational paths carry a canonical Gray-category structure. -/
def pathGrayCategory (A : Type u) : GrayCategory (Obj := A) where
  toTwoCategory := pathTwoCategory A
  interchange_path := by
    intro a b c f₀ f₁ f₂ g₀ g₁ g₂ η₁ η₂ θ₁ θ₂
    exact
      Path.mk
        [Step.mk _ _
          (_root_.congrArg PLift.up
            ((pathTwoCategory A).interchange
              (a := a) (b := b) (c := c)
              (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
              (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
              (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)))]
        (_root_.congrArg PLift.up
          ((pathTwoCategory A).interchange
            (a := a) (b := b) (c := c)
            (f₀ := f₀) (f₁ := f₁) (f₂ := f₂)
            (g₀ := g₀) (g₁ := g₁) (g₂ := g₂)
            (η₁ := η₁) (η₂ := η₂) (θ₁ := θ₁) (θ₂ := θ₂)))

/-- For `pathGrayCategory`, the stored interchange 3-cell recovers interchange by extraction. -/
theorem pathGrayCategory_interchange_from_path (A : Type u)
    {a b c : A} {f₀ f₁ f₂ : Path a b} {g₀ g₁ g₂ : Path b c}
    (η₁ : (pathGrayCategory A).TwoCell f₀ f₁) (η₂ : (pathGrayCategory A).TwoCell f₁ f₂)
    (θ₁ : (pathGrayCategory A).TwoCell g₀ g₁) (θ₂ : (pathGrayCategory A).TwoCell g₁ g₂) :
    (pathGrayCategory A).vcomp ((pathGrayCategory A).hcomp η₁ θ₁) ((pathGrayCategory A).hcomp η₂ θ₂) =
      (pathGrayCategory A).hcomp ((pathGrayCategory A).vcomp η₁ η₂) ((pathGrayCategory A).vcomp θ₁ θ₂) := by
  exact GrayCategory.gray_interchange_from_path (G := pathGrayCategory A) η₁ η₂ θ₁ θ₂

/-- Tensor product in the path Gray-category is associative up to the associator 2-cells. -/
theorem pathGrayCategory_tensor_assoc (A : Type u)
    {a b c d : A}
    {f₀ f₁ : Path a b} {g₀ g₁ : Path b c} {h₀ h₁ : Path c d}
    (η : (pathGrayCategory A).TwoCell f₀ f₁)
    (θ : (pathGrayCategory A).TwoCell g₀ g₁)
    (ι : (pathGrayCategory A).TwoCell h₀ h₁) :
    (pathGrayCategory A).vcomp
      ((pathGrayCategory A).hcomp ((pathGrayCategory A).hcomp η θ) ι)
      ((pathGrayCategory A).assoc f₁ g₁ h₁) =
    (pathGrayCategory A).vcomp
      ((pathGrayCategory A).assoc f₀ g₀ h₀)
      ((pathGrayCategory A).hcomp η ((pathGrayCategory A).hcomp θ ι)) := by
  apply Subsingleton.elim

/-- The path Gray-category tensor associativity equality can be lifted to a 3-cell witness. -/
def pathGrayCategory_tensor_assoc_path (A : Type u)
    {a b c d : A}
    {f₀ f₁ : Path a b} {g₀ g₁ : Path b c} {h₀ h₁ : Path c d}
    (η : (pathGrayCategory A).TwoCell f₀ f₁)
    (θ : (pathGrayCategory A).TwoCell g₀ g₁)
    (ι : (pathGrayCategory A).TwoCell h₀ h₁) :
    CellPath
      ((pathGrayCategory A).vcomp
        ((pathGrayCategory A).hcomp ((pathGrayCategory A).hcomp η θ) ι)
        ((pathGrayCategory A).assoc f₁ g₁ h₁))
      ((pathGrayCategory A).vcomp
        ((pathGrayCategory A).assoc f₀ g₀ h₀)
        ((pathGrayCategory A).hcomp η ((pathGrayCategory A).hcomp θ ι))) :=
  Path.mk
    [Step.mk _ _
      (_root_.congrArg PLift.up (pathGrayCategory_tensor_assoc (A := A) η θ ι))]
    (_root_.congrArg PLift.up (pathGrayCategory_tensor_assoc (A := A) η θ ι))

/-- Forgetting 3-cell data recovers the path 2-category. -/
@[simp] theorem pathGrayCategory_to_twoCategory (A : Type u) :
    (pathGrayCategory A).toTwoCategory = pathTwoCategory A := by
  rfl

end Path
end ComputationalPaths
