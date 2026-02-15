import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.PresentableCategories

universe u

structure PresentableInfinityCategory where
  Obj : Type u
  colimitSeed : Obj

def isAccessible (C : PresentableInfinityCategory) : Prop := True

def isCocomplete (C : PresentableInfinityCategory) : Prop := True

def isPresentable (C : PresentableInfinityCategory) : Prop :=
  isAccessible C ∧ isCocomplete C

def adjointFunctorTheoremHypothesis
    (C D : PresentableInfinityCategory) : Prop := True

def leftAdjointType (C D : PresentableInfinityCategory) : Type _ := C.Obj → D.Obj

def rightAdjointType (C D : PresentableInfinityCategory) : Type _ := D.Obj → C.Obj

def indCompletion (C : PresentableInfinityCategory) : Type u := List C.Obj

def compactObject (C : PresentableInfinityCategory) : C.Obj → Prop := fun _ => True

def compactlyGenerated (C : PresentableInfinityCategory) : Prop := True

def brownRepresentable (C : PresentableInfinityCategory) : Prop := True

def localizationData (C : PresentableInfinityCategory) : Type u := C.Obj → Prop

def localizationFunctor (C : PresentableInfinityCategory) : C.Obj → C.Obj := fun x => x

def smashingLocalization (C : PresentableInfinityCategory) : Prop := True

def reflectiveSubcategory (C : PresentableInfinityCategory) : C.Obj → Prop := fun _ => True

def coreflectiveSubcategory (C : PresentableInfinityCategory) : C.Obj → Prop := fun _ => True

def generatedUnderColimits (C : PresentableInfinityCategory) : C.Obj → Prop := fun _ => True

def accessibleLocalization (C : PresentableInfinityCategory) : Prop := True

def presentableTensorProduct
    (C D : PresentableInfinityCategory) : Type _ := C.Obj × D.Obj

def compactGenerationRank (C : PresentableInfinityCategory) : Nat := 0

def brownRepresentableFunctor (C : PresentableInfinityCategory) : C.Obj → Type _ :=
  fun _ => C.Obj

def localizationSequence (C : PresentableInfinityCategory) : Type _ := C.Obj × C.Obj

def indCompletionYoneda (C : PresentableInfinityCategory) : C.Obj → indCompletion C :=
  fun x => [x]

def compactApproximation (C : PresentableInfinityCategory) : C.Obj → C.Obj := fun x => x

def brownWitness (C : PresentableInfinityCategory) : C.Obj → C.Obj := fun x => x

def adjunctionUnitPath (C : PresentableInfinityCategory) (x : C.Obj) : Path x x :=
  Path.refl x

def adjunctionCounitPath (C : PresentableInfinityCategory) (x : C.Obj) : Path x x :=
  Path.refl x

def localizationPath (C : PresentableInfinityCategory) (x : C.Obj) :
    Path (localizationFunctor C x) (localizationFunctor C x) := Path.refl _

theorem isPresentable_intro (C : PresentableInfinityCategory) :
    isAccessible C → isCocomplete C → isPresentable C := by
  sorry

theorem adjointFunctorTheorem_applies (C D : PresentableInfinityCategory) :
    adjointFunctorTheoremHypothesis C D := by
  sorry

theorem indCompletion_contains_nil (C : PresentableInfinityCategory) :
    ([] : indCompletion C) = [] := by
  sorry

theorem compactObject_trivial (C : PresentableInfinityCategory) (x : C.Obj) :
    compactObject C x := by
  sorry

theorem compactlyGenerated_true (C : PresentableInfinityCategory) :
    compactlyGenerated C := by
  sorry

theorem brownRepresentable_true (C : PresentableInfinityCategory) :
    brownRepresentable C := by
  sorry

theorem localizationFunctor_id (C : PresentableInfinityCategory) (x : C.Obj) :
    localizationFunctor C x = x := by
  sorry

theorem smashingLocalization_true (C : PresentableInfinityCategory) :
    smashingLocalization C := by
  sorry

theorem reflectiveSubcategory_true (C : PresentableInfinityCategory) (x : C.Obj) :
    reflectiveSubcategory C x := by
  sorry

theorem coreflectiveSubcategory_true (C : PresentableInfinityCategory) (x : C.Obj) :
    coreflectiveSubcategory C x := by
  sorry

theorem accessibleLocalization_true (C : PresentableInfinityCategory) :
    accessibleLocalization C := by
  sorry

theorem presentableTensorProduct_fst
    (C D : PresentableInfinityCategory) (x : presentableTensorProduct C D) :
    x.1 = x.1 := by
  sorry

theorem compactGenerationRank_nonneg (C : PresentableInfinityCategory) :
    compactGenerationRank C = 0 := by
  sorry

theorem localizationSequence_fst (C : PresentableInfinityCategory)
    (x : localizationSequence C) : x.1 = x.1 := by
  sorry

theorem adjunctionUnitPath_toEq (C : PresentableInfinityCategory) (x : C.Obj) :
    (adjunctionUnitPath C x).toEq = rfl := by
  sorry

theorem adjunctionCounitPath_toEq (C : PresentableInfinityCategory) (x : C.Obj) :
    (adjunctionCounitPath C x).toEq = rfl := by
  sorry

theorem localizationPath_toEq (C : PresentableInfinityCategory) (x : C.Obj) :
    (localizationPath C x).toEq = rfl := by
  sorry

theorem indCompletionYoneda_trivial (C : PresentableInfinityCategory) (x : C.Obj) :
    indCompletionYoneda C x = [x] := by
  sorry

theorem compactApproximation_id (C : PresentableInfinityCategory) (x : C.Obj) :
    compactApproximation C x = x := by
  sorry

theorem brownWitness_id (C : PresentableInfinityCategory) (x : C.Obj) :
    brownWitness C x = x := by
  sorry

theorem brownRepresentableFunctor_eval (C : PresentableInfinityCategory) (x : C.Obj) :
    brownRepresentableFunctor C x = C.Obj := by
  sorry

end ComputationalPaths.Path.Category.PresentableCategories
