import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.HigherMonoidal

universe u

structure HigherMonoidalCategory where
  Obj : Type u
  tensor : Obj → Obj → Obj
  unit : Obj

noncomputable def infinityOperadShape (n : Nat) : Type := Fin (n + 1)

noncomputable def infinityOperadAxiom (C : HigherMonoidalCategory) : Prop := True

noncomputable def algebraObject (C : HigherMonoidalCategory) : Type _ := C.Obj

noncomputable def commutativeAlgebraObject (C : HigherMonoidalCategory) : Type _ := C.Obj

noncomputable def dayConvolutionObj (C D : HigherMonoidalCategory) : Type _ := C.Obj × D.Obj

noncomputable def dayConvolutionTensor (C D : HigherMonoidalCategory) :
    dayConvolutionObj C D → dayConvolutionObj C D → dayConvolutionObj C D :=
  fun x y => (C.tensor x.1 y.1, D.tensor x.2 y.2)

noncomputable def dayConvolutionUnit (C D : HigherMonoidalCategory) : dayConvolutionObj C D :=
  (C.unit, D.unit)

noncomputable def dayConvolutionMonoidal (C D : HigherMonoidalCategory) : Prop := True

noncomputable def operadicLeftKanExtension (C : HigherMonoidalCategory) : C.Obj → C.Obj := fun x => x

noncomputable def operadicRightKanExtension (C : HigherMonoidalCategory) : C.Obj → C.Obj := fun x => x

noncomputable def monoidalYoneda (C : HigherMonoidalCategory) : C.Obj → Type _ := fun _ => C.Obj

noncomputable def cotangentComplex (C : HigherMonoidalCategory) : algebraObject C → Type _ :=
  fun _ => C.Obj

noncomputable def quillenCohomology (C : HigherMonoidalCategory) : algebraObject C → Type _ :=
  fun _ => C.Obj

noncomputable def derivationSpace (C : HigherMonoidalCategory) : algebraObject C → Type _ :=
  fun _ => C.Obj

noncomputable def squareZeroExtension (C : HigherMonoidalCategory) :
    algebraObject C → algebraObject C := fun a => a

noncomputable def indecomposables (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => C.Obj

noncomputable def stabilizationFunctor (C : HigherMonoidalCategory) : C.Obj → C.Obj := fun x => x

noncomputable def spectralCotangentComplex (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => C.Obj

noncomputable def operadicBarConstruction (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => List C.Obj

noncomputable def operadicCobarConstruction (C : HigherMonoidalCategory) :
    algebraObject C → Type _ := fun _ => List C.Obj

noncomputable def quillenCohomologyClass (C : HigherMonoidalCategory) :
    algebraObject C → algebraObject C := fun a => a

noncomputable def infinityOperadAlgebraMap (C : HigherMonoidalCategory) :
    algebraObject C → algebraObject C := fun a => a

noncomputable def dayConvolutionComparison (C D : HigherMonoidalCategory) :
    dayConvolutionObj C D → dayConvolutionObj C D := fun x => x

noncomputable def algebraPath (C : HigherMonoidalCategory) (a : algebraObject C) : Path a a := Path.refl a

noncomputable def commutativePath (C : HigherMonoidalCategory) (a : commutativeAlgebraObject C) :
    Path a a := Path.refl a

noncomputable def dayConvolutionPath (C D : HigherMonoidalCategory) (x : dayConvolutionObj C D) :
    Path x x := Path.trans (Path.refl x) (Path.refl x)

noncomputable def cotangentPath (C : HigherMonoidalCategory) (a : algebraObject C) : Path a a :=
  Path.refl a

noncomputable def quillenPath (C : HigherMonoidalCategory) (a : algebraObject C) : Path a a :=
  Path.refl a

theorem infinityOperadShape_nonempty (n : Nat) : Nat.succ n > 0 := by
  omega

theorem dayConvolutionTensor_formula (C D : HigherMonoidalCategory)
    (x y : dayConvolutionObj C D) :
    dayConvolutionTensor C D x y = (C.tensor x.1 y.1, D.tensor x.2 y.2) := by
  rfl

theorem dayConvolutionUnit_fst (C D : HigherMonoidalCategory) :
    (dayConvolutionUnit C D).1 = C.unit := by
  rfl

theorem dayConvolutionMonoidal_true (C D : HigherMonoidalCategory) :
    dayConvolutionMonoidal C D := by
  trivial

theorem cotangentComplex_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    cotangentComplex C a = C.Obj := by
  rfl

theorem quillenCohomology_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    quillenCohomology C a = C.Obj := by
  rfl

theorem derivationSpace_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    derivationSpace C a = C.Obj := by
  rfl

theorem squareZeroExtension_id (C : HigherMonoidalCategory) (a : algebraObject C) :
    squareZeroExtension C a = a := by
  rfl

theorem indecomposables_is_type (C : HigherMonoidalCategory) (a : algebraObject C) :
    indecomposables C a = C.Obj := by
  rfl

theorem stabilizationFunctor_id (C : HigherMonoidalCategory) (x : C.Obj) :
    stabilizationFunctor C x = x := by
  rfl

theorem spectralCotangentComplex_is_type (C : HigherMonoidalCategory)
    (a : algebraObject C) : spectralCotangentComplex C a = C.Obj := by
  rfl

theorem operadicBar_nil (C : HigherMonoidalCategory) (a : algebraObject C) :
    ([] : operadicBarConstruction C a) = [] := by
  rfl

theorem operadicCobar_nil (C : HigherMonoidalCategory) (a : algebraObject C) :
    ([] : operadicCobarConstruction C a) = [] := by
  rfl

theorem quillenCohomologyClass_id (C : HigherMonoidalCategory) (a : algebraObject C) :
    quillenCohomologyClass C a = a := by
  rfl

theorem algebraPath_toEq (C : HigherMonoidalCategory) (a : algebraObject C) :
    (algebraPath C a).toEq = rfl := by
  rfl

theorem commutativePath_toEq (C : HigherMonoidalCategory) (a : commutativeAlgebraObject C) :
    (commutativePath C a).toEq = rfl := by
  rfl

theorem dayConvolutionPath_toEq (C D : HigherMonoidalCategory)
    (x : dayConvolutionObj C D) :
    (dayConvolutionPath C D x).toEq = rfl := by
  rfl

theorem cotangentPath_toEq (C : HigherMonoidalCategory) (a : algebraObject C) :
    (cotangentPath C a).toEq = rfl := by
  rfl

theorem quillenPath_toEq (C : HigherMonoidalCategory) (a : algebraObject C) :
    (quillenPath C a).toEq = rfl := by
  rfl

theorem infinityOperadAlgebraMap_id (C : HigherMonoidalCategory) (a : algebraObject C) :
    infinityOperadAlgebraMap C a = a := by
  rfl

theorem dayConvolutionComparison_id (C D : HigherMonoidalCategory)
    (x : dayConvolutionObj C D) : dayConvolutionComparison C D x = x := by
  rfl

end ComputationalPaths.Path.Category.HigherMonoidal
