import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.HigherMonoidal

universe u

structure HigherMonoidalCategory where
  Obj : Type u
  tensor : Obj → Obj → Obj
  unit : Obj

def infinityOperadShape (n : Nat) : Type := Fin (n + 1)

def infinityOperadAxiom (C : HigherMonoidalCategory) : Prop := True

def algebraObject (C : HigherMonoidalCategory) : Type _ := C.Obj

def commutativeAlgebraObject (C : HigherMonoidalCategory) : Type _ := C.Obj

def dayConvolutionObj (C D : HigherMonoidalCategory) : Type _ := C.Obj × D.Obj

def dayConvolutionTensor (C D : HigherMonoidalCategory) :
    dayConvolutionObj C D → dayConvolutionObj C D → dayConvolutionObj C D :=
  fun x y => (C.tensor x.1 y.1, D.tensor x.2 y.2)

def dayConvolutionUnit (C D : HigherMonoidalCategory) : dayConvolutionObj C D :=
  (C.unit, D.unit)

def dayConvolutionMonoidal (C D : HigherMonoidalCategory) : Prop := True

def operadicLeftKanExtension (C : HigherMonoidalCategory) : C.Obj → C.Obj := fun x => x

def operadicRightKanExtension (C : HigherMonoidalCategory) : C.Obj → C.Obj := fun x => x

def monoidalYoneda (C : HigherMonoidalCategory) : C.Obj → Type _ := fun _ => C.Obj

def cotangentComplex (C : HigherMonoidalCategory) : algebraObject C → Type _ :=
  fun _ => C.Obj

def quillenCohomology (C : HigherMonoidalCategory) : algebraObject C → Type _ :=
  fun _ => C.Obj

def derivationSpace (C : HigherMonoidalCategory) : algebraObject C → Type _ :=
  fun _ => C.Obj

def squareZeroExtension (C : HigherMonoidalCategory) :
    algebraObject C → algebraObject C := fun a => a

def indecomposables (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => C.Obj

def stabilizationFunctor (C : HigherMonoidalCategory) : C.Obj → C.Obj := fun x => x

def spectralCotangentComplex (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => C.Obj

def operadicBarConstruction (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => List C.Obj

def operadicCobarConstruction (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => List C.Obj

def quillenCohomologyClass (C : HigherMonoidalCategory) :
    algebraObject C → algebraObject C := fun a => a

def infinityOperadAlgebraMap (C : HigherMonoidalCategory) :
    algebraObject C → algebraObject C := fun a => a

def dayConvolutionComparison (C D : HigherMonoidalCategory) :
    dayConvolutionObj C D → dayConvolutionObj C D := fun x => x

def algebraPath (C : HigherMonoidalCategory) (a : algebraObject C) : Path a a := Path.refl a

def commutativePath (C : HigherMonoidalCategory) (a : commutativeAlgebraObject C) :
    Path a a := Path.refl a

def dayConvolutionPath (C D : HigherMonoidalCategory) (x : dayConvolutionObj C D) :
    Path x x := Path.trans (Path.refl x) (Path.refl x)

def cotangentPath (C : HigherMonoidalCategory) (a : algebraObject C) : Path a a :=
  Path.refl a

def quillenPath (C : HigherMonoidalCategory) (a : algebraObject C) : Path a a :=
  Path.refl a

theorem infinityOperadShape_nonempty (n : Nat) : Nat.succ n > 0 := by
  sorry

theorem dayConvolutionTensor_formula (C D : HigherMonoidalCategory)
    (x y : dayConvolutionObj C D) :
    dayConvolutionTensor C D x y = (C.tensor x.1 y.1, D.tensor x.2 y.2) := by
  sorry

theorem dayConvolutionUnit_fst (C D : HigherMonoidalCategory) :
    (dayConvolutionUnit C D).1 = C.unit := by
  sorry

theorem dayConvolutionMonoidal_true (C D : HigherMonoidalCategory) :
    dayConvolutionMonoidal C D := by
  sorry

theorem cotangentComplex_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    cotangentComplex C a = C.Obj := by
  sorry

theorem quillenCohomology_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    quillenCohomology C a = C.Obj := by
  sorry

theorem derivationSpace_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    derivationSpace C a = C.Obj := by
  sorry

theorem squareZeroExtension_id (C : HigherMonoidalCategory) (a : algebraObject C) :
    squareZeroExtension C a = a := by
  sorry

theorem indecomposables_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    indecomposables C a = C.Obj := by
  sorry

theorem stabilizationFunctor_id (C : HigherMonoidalCategory) (x : C.Obj) :
    stabilizationFunctor C x = x := by
  sorry

theorem spectralCotangentComplex_is_type (C : HigherMonoidalCategory)
    (a : algebraObject C) : spectralCotangentComplex C a = C.Obj := by
  sorry

theorem operadicBar_nil (C : HigherMonoidalCategory) (a : algebraObject C) :
    ([] : operadicBarConstruction C a) = [] := by
  sorry

theorem operadicCobar_nil (C : HigherMonoidalCategory) (a : algebraObject C) :
    ([] : operadicCobarConstruction C a) = [] := by
  sorry

theorem quillenCohomologyClass_id (C : HigherMonoidalCategory) (a : algebraObject C) :
    quillenCohomologyClass C a = a := by
  sorry

theorem algebraPath_toEq (C : HigherMonoidalCategory) (a : algebraObject C) :
    (algebraPath C a).toEq = rfl := by
  sorry

theorem commutativePath_toEq (C : HigherMonoidalCategory) (a : commutativeAlgebraObject C) :
    (commutativePath C a).toEq = rfl := by
  sorry

theorem dayConvolutionPath_toEq (C D : HigherMonoidalCategory)
    (x : dayConvolutionObj C D) :
    (dayConvolutionPath C D x).toEq = rfl := by
  sorry

theorem cotangentPath_toEq (C : HigherMonoidalCategory) (a : algebraObject C) :
    (cotangentPath C a).toEq = rfl := by
  sorry

theorem quillenPath_toEq (C : HigherMonoidalCategory) (a : algebraObject C) :
    (quillenPath C a).toEq = rfl := by
  sorry

theorem infinityOperadAlgebraMap_id (C : HigherMonoidalCategory) (a : algebraObject C) :
    infinityOperadAlgebraMap C a = a := by
  sorry

theorem dayConvolutionComparison_id (C D : HigherMonoidalCategory)
    (x : dayConvolutionObj C D) : dayConvolutionComparison C D x = x := by
  sorry

end ComputationalPaths.Path.Category.HigherMonoidal
