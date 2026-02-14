 /-
 # Tricategory layer for computational paths
 
 This module adds a lightweight tricategory interface over `GrayCategory`, with
 explicit 4-cell witnesses (`CellPath` between 3-cells) for pentagon and
 triangle coherence.
 -/
 
 import ComputationalPaths.Path.GrayCategory
 
 namespace ComputationalPaths
 namespace Path
 
 universe u
 
 /-- A minimal tricategory interface extending `GrayCategory` with 4-cell
 coherence witnesses comparing pentagon and triangle 3-cells. -/
 structure Tricategory (Obj : Type u) extends GrayCategory (Obj := Obj) where
   pentagonator :
     ∀ {a b c d e : Obj}
       (f : Hom a b) (g : Hom b c) (h : Hom c d) (k : Hom d e),
       CellPath
         (TwoCategory.pentagonPath toGrayCategory.toTwoCategory f g h k)
         (GrayCategory.pentagonPath toGrayCategory f g h k)
   triangulator :
     ∀ {a b c : Obj} (f : Hom a b) (g : Hom b c),
       CellPath
         (TwoCategory.trianglePath toGrayCategory.toTwoCategory f g)
         (GrayCategory.trianglePath toGrayCategory f g)
 
namespace Tricategory

variable {Obj : Type u}

/-- Build a single explicit rewrite `Step` in the lifted 4-cell universe. -/
@[simp] def coherenceStep {α : Sort u} {x y : α} (h : x = y) :
    ComputationalPaths.Step (PLift α) :=
  ComputationalPaths.Step.mk (PLift.up x) (PLift.up y) (congrArg PLift.up h)

/-- Build a 4-cell as a one-step computational path. -/
@[simp] def coherencePath {α : Sort u} {x y : α} (h : x = y) :
    CellPath x y :=
  Path.mk [coherenceStep h] (congrArg PLift.up h)

/-- One-step coherence paths have unit step count. -/
@[simp] theorem coherencePath_stepCount {α : Sort u} {x y : α} (h : x = y) :
    Path.stepCount (coherencePath h) = 1 := rfl

/-- Underlying pentagon 3-cells agree definitionally. -/
@[simp] theorem pentagonator_eq
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    TwoCategory.pentagonPath G.toTwoCategory f g h k =
      GrayCategory.pentagonPath G f g h k := rfl

/-- Underlying triangle 3-cells agree definitionally. -/
@[simp] theorem triangulator_eq
    (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    TwoCategory.trianglePath G.toTwoCategory f g =
      GrayCategory.trianglePath G f g := rfl

/-- Canonical pentagonator 4-cell built from one explicit step. -/
@[simp] def pentagonatorStepData
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    CellPath
      (TwoCategory.pentagonPath G.toTwoCategory f g h k)
      (GrayCategory.pentagonPath G f g h k) :=
  coherencePath (pentagonator_eq G f g h k)

/-- Canonical triangulator 4-cell built from one explicit step. -/
@[simp] def triangulatorStepData
    (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    CellPath
      (TwoCategory.trianglePath G.toTwoCategory f g)
      (GrayCategory.trianglePath G f g) :=
  coherencePath (triangulator_eq G f g)

/-- Canonical pentagonator data is a single-step path. -/
@[simp] theorem pentagonatorStepData_stepCount
    (G : GrayCategory (Obj := Obj))
    {a b c d e : Obj}
    (f : G.Hom a b) (g : G.Hom b c) (h : G.Hom c d) (k : G.Hom d e) :
    Path.stepCount (pentagonatorStepData G f g h k) = 1 :=
  coherencePath_stepCount (pentagonator_eq G f g h k)

/-- Canonical triangulator data is a single-step path. -/
@[simp] theorem triangulatorStepData_stepCount
    (G : GrayCategory (Obj := Obj))
    {a b c : Obj} (f : G.Hom a b) (g : G.Hom b c) :
    Path.stepCount (triangulatorStepData G f g) = 1 :=
  coherencePath_stepCount (triangulator_eq G f g)

/-- Pentagon coherence 4-cell in a tricategory. -/
def pentagonatorPath (T : Tricategory (Obj := Obj))
    {a b c d e : Obj}
    (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e) :
     CellPath
       (TwoCategory.pentagonPath T.toGrayCategory.toTwoCategory f g h k)
       (GrayCategory.pentagonPath T.toGrayCategory f g h k) :=
   T.pentagonator f g h k
 
 /-- Triangle coherence 4-cell in a tricategory. -/
 def triangulatorPath (T : Tricategory (Obj := Obj))
     {a b c : Obj} (f : T.Hom a b) (g : T.Hom b c) :
     CellPath
       (TwoCategory.trianglePath T.toGrayCategory.toTwoCategory f g)
       (GrayCategory.trianglePath T.toGrayCategory f g) :=
   T.triangulator f g
 
 end Tricategory
 
/-- Computational paths carry a canonical tricategory structure. -/
def pathTricategory (A : Type u) : Tricategory (Obj := A) where
  toGrayCategory := pathGrayCategory A
  pentagonator := by
    intro a b c d e f g h k
    exact Tricategory.pentagonatorStepData (pathGrayCategory A) f g h k
  triangulator := by
    intro a b c f g
    exact Tricategory.triangulatorStepData (pathGrayCategory A) f g

 /-- Forgetting 4-cell data recovers the path Gray-category. -/
@[simp] theorem pathTricategory_to_grayCategory (A : Type u) :
    (pathTricategory A).toGrayCategory = pathGrayCategory A := by
  rfl

/-- Path tricategory pentagonator is carried by one explicit Step. -/
@[simp] theorem pathTricategory_pentagonator_stepCount
    (A : Type u)
    {a b c d e : A}
    (f : (pathTricategory A).Hom a b) (g : (pathTricategory A).Hom b c)
    (h : (pathTricategory A).Hom c d) (k : (pathTricategory A).Hom d e) :
    Path.stepCount (Tricategory.pentagonatorPath (pathTricategory A) f g h k) = 1 := by
  rfl

/-- Path tricategory triangulator is carried by one explicit Step. -/
@[simp] theorem pathTricategory_triangulator_stepCount
    (A : Type u)
    {a b c : A}
    (f : (pathTricategory A).Hom a b) (g : (pathTricategory A).Hom b c) :
    Path.stepCount (Tricategory.triangulatorPath (pathTricategory A) f g) = 1 := by
  rfl

/-- Tricategories inherit the Gray interchange equation. -/
@[simp] theorem tricategory_gray_interchange_eq
    (T : Tricategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : T.Hom a b} {g₀ g₁ g₂ : T.Hom b c}
    (η₁ : T.TwoCell f₀ f₁) (η₂ : T.TwoCell f₁ f₂)
    (θ₁ : T.TwoCell g₀ g₁) (θ₂ : T.TwoCell g₁ g₂) :
    T.vcomp (T.hcomp η₁ θ₁) (T.hcomp η₂ θ₂) =
      T.hcomp (T.vcomp η₁ η₂) (T.vcomp θ₁ θ₂) :=
  GrayCategory.gray_interchange_eq T.toGrayCategory η₁ η₂ θ₁ θ₂

/-- Tricategories inherit Gray interchange with units. -/
@[simp] theorem tricategory_gray_interchange_unit
    (T : Tricategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ : T.Hom a b} {g₀ g₁ : T.Hom b c}
    (η : T.TwoCell f₀ f₁) (θ : T.TwoCell g₀ g₁) :
    T.vcomp (T.hcomp η (T.id₂ g₀)) (T.hcomp (T.id₂ f₁) θ) =
      T.hcomp η θ :=
  GrayCategory.gray_interchange_unit T.toGrayCategory η θ

/-- Tricategories inherit Gray interchange associativity. -/
@[simp] theorem tricategory_gray_interchange_assoc
    (T : Tricategory (Obj := Obj))
    {a b c : Obj}
    {f₀ f₁ f₂ f₃ : T.Hom a b} {g₀ g₁ g₂ g₃ : T.Hom b c}
    (η₁ : T.TwoCell f₀ f₁) (η₂ : T.TwoCell f₁ f₂) (η₃ : T.TwoCell f₂ f₃)
    (θ₁ : T.TwoCell g₀ g₁) (θ₂ : T.TwoCell g₁ g₂) (θ₃ : T.TwoCell g₂ g₃) :
    T.vcomp (T.vcomp (T.hcomp η₁ θ₁) (T.hcomp η₂ θ₂)) (T.hcomp η₃ θ₃) =
      T.hcomp (T.vcomp η₁ (T.vcomp η₂ η₃))
        (T.vcomp θ₁ (T.vcomp θ₂ θ₃)) :=
  GrayCategory.gray_interchange_assoc T.toGrayCategory η₁ η₂ η₃ θ₁ θ₂ θ₃

/-- Tricategories inherit Gray tensor functoriality. -/
@[simp] theorem tricategory_gray_tensor_functorial
    (T : Tricategory (Obj := Obj))
    {a b c : Obj} {f₀ f₁ f₂ : T.Hom a b} {g₀ g₁ g₂ : T.Hom b c}
    (η₁ : T.TwoCell f₀ f₁) (η₂ : T.TwoCell f₁ f₂)
    (θ₁ : T.TwoCell g₀ g₁) (θ₂ : T.TwoCell g₁ g₂) :
    T.hcomp (T.vcomp η₁ η₂) (T.vcomp θ₁ θ₂) =
      T.vcomp (T.hcomp η₁ θ₁) (T.hcomp η₂ θ₂) :=
  GrayCategory.gray_tensor_functorial T.toGrayCategory η₁ η₂ θ₁ θ₂

/-- Global tricategorical coherence: pentagonator, triangulator, and interchange. -/
theorem tricategory_coherence_theorem
    (T : Tricategory (Obj := Obj))
    {a b c d e : Obj}
    (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e)
    {a' b' c' : Obj} (f' : T.Hom a' b') (g' : T.Hom b' c')
    {x y z : Obj} {u₀ u₁ u₂ : T.Hom x y} {v₀ v₁ v₂ : T.Hom y z}
    (η₁ : T.TwoCell u₀ u₁) (η₂ : T.TwoCell u₁ u₂)
    (θ₁ : T.TwoCell v₀ v₁) (θ₂ : T.TwoCell v₁ v₂) :
    CellPath
      (TwoCategory.pentagonPath T.toGrayCategory.toTwoCategory f g h k)
      (GrayCategory.pentagonPath T.toGrayCategory f g h k)
    ∧ CellPath
      (TwoCategory.trianglePath T.toGrayCategory.toTwoCategory f' g')
      (GrayCategory.trianglePath T.toGrayCategory f' g')
    ∧ T.vcomp (T.hcomp η₁ θ₁) (T.hcomp η₂ θ₂) =
      T.hcomp (T.vcomp η₁ η₂) (T.vcomp θ₁ θ₂) := by
  refine ⟨Tricategory.pentagonatorPath T f g h k, Tricategory.triangulatorPath T f' g', ?_⟩
  exact tricategory_gray_interchange_eq T η₁ η₂ θ₁ θ₂

/-- Pentagonator naturality with respect to right unit composition. -/
@[simp] theorem tricategory_pentagon_naturality
    (T : Tricategory (Obj := Obj))
    {a b c d e : Obj}
    (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e) :
    CellPath
      (CellPath.comp
        (Tricategory.pentagonatorPath T f g h k)
        (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k)))
      (Tricategory.pentagonatorPath T f g h k) := by
  exact Path.stepChain (by simp [CellPath.comp, CellPath.refl])

/-- Triangulator naturality with respect to right unit composition. -/
@[simp] theorem tricategory_triangle_naturality
    (T : Tricategory (Obj := Obj))
    {a b c : Obj} (f : T.Hom a b) (g : T.Hom b c) :
    CellPath
      (CellPath.comp
        (Tricategory.triangulatorPath T f g)
        (CellPath.refl (GrayCategory.trianglePath T.toGrayCategory f g)))
      (Tricategory.triangulatorPath T f g) := by
  exact Path.stepChain (by simp [CellPath.comp, CellPath.refl])

/-- Pentagonator and triangulator compositions are coherent under reassociation. -/
@[simp] theorem tricategory_coherence
    (T : Tricategory (Obj := Obj))
    {a b c d e : Obj}
    (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e)
    {a' b' c' : Obj} (f' : T.Hom a' b') (g' : T.Hom b' c') :
    (CellPath
      (CellPath.comp
        (CellPath.comp
          (Tricategory.pentagonatorPath T f g h k)
          (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k)))
        (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k)))
      (CellPath.comp
        (Tricategory.pentagonatorPath T f g h k)
        (CellPath.comp
          (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k))
          (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k)))))
    ∧
    (CellPath
      (CellPath.comp
        (CellPath.comp
          (Tricategory.triangulatorPath T f' g')
          (CellPath.refl (GrayCategory.trianglePath T.toGrayCategory f' g')))
        (CellPath.refl (GrayCategory.trianglePath T.toGrayCategory f' g')))
      (CellPath.comp
        (Tricategory.triangulatorPath T f' g')
        (CellPath.comp
          (CellPath.refl (GrayCategory.trianglePath T.toGrayCategory f' g'))
          (CellPath.refl (GrayCategory.trianglePath T.toGrayCategory f' g'))))) := by
  constructor <;>
    exact Path.stepChain (by simp [CellPath.comp, CellPath.refl, Path.trans_assoc])

/-- Forgetting tricategorical 4-cells preserves pentagon and triangle coherence data. -/
@[simp] theorem forgetful_to_grayCategory_preserves_coherence
    (T : Tricategory (Obj := Obj))
    {a b c d e : Obj}
    (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e)
    {a' b' c' : Obj} (f' : T.Hom a' b') (g' : T.Hom b' c') :
    (GrayCategory.pentagonPath T.toGrayCategory f g h k =
      TwoCategory.pentagonPath T.toGrayCategory.toTwoCategory f g h k) ∧
    (GrayCategory.trianglePath T.toGrayCategory f' g' =
      TwoCategory.trianglePath T.toGrayCategory.toTwoCategory f' g') := by
  constructor <;> rfl

/-- Pentagonator with identity 1-cells has trivial right-unit composition. -/
@[simp] theorem tricategory_unit_coherence
    (T : Tricategory (Obj := Obj)) (a : Obj) :
    CellPath
      (CellPath.comp
        (Tricategory.pentagonatorPath T (T.id₁ a) (T.id₁ a) (T.id₁ a) (T.id₁ a))
        (CellPath.refl
          (GrayCategory.pentagonPath T.toGrayCategory
            (T.id₁ a) (T.id₁ a) (T.id₁ a) (T.id₁ a))))
      (Tricategory.pentagonatorPath T (T.id₁ a) (T.id₁ a) (T.id₁ a) (T.id₁ a)) := by
  exact Path.stepChain (by simp [CellPath.comp, CellPath.refl])

/-- Associativity coherence for composing the pentagonator with unit 4-cells. -/
@[simp] theorem tricategory_associator_coherence
    (T : Tricategory (Obj := Obj))
    {a b c d e : Obj}
    (f : T.Hom a b) (g : T.Hom b c) (h : T.Hom c d) (k : T.Hom d e) :
    CellPath
      (CellPath.comp
        (CellPath.comp
          (CellPath.refl
            (TwoCategory.pentagonPath T.toGrayCategory.toTwoCategory f g h k))
          (Tricategory.pentagonatorPath T f g h k))
        (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k)))
      (CellPath.comp
        (CellPath.refl
          (TwoCategory.pentagonPath T.toGrayCategory.toTwoCategory f g h k))
        (CellPath.comp
          (Tricategory.pentagonatorPath T f g h k)
          (CellPath.refl (GrayCategory.pentagonPath T.toGrayCategory f g h k)))) := by
  exact Path.stepChain (by simp [CellPath.comp, CellPath.refl, Path.trans_assoc])

end Path
end ComputationalPaths
