/-
# Model Category Examples

Examples of model category structures using computational paths.
-/

import ComputationalPaths.Path.Homotopy.ModelCategory
import ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep

namespace ComputationalPaths.Path.Homotopy.ModelCategoryExamples

open ComputationalPaths.Path

universe u

abbrev ChainComplex (C : Nat → Type u) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.ChainComplex C

abbrev ChainMap {C D : Nat → Type u}
    (cC : ChainComplex C) (cD : ChainComplex D) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.ChainMap cC cD

abbrev QuillenAdjData (A B : Type u) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.QuillenAdjData A B

abbrev CylinderObj (A : Type u) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.CylinderObj A

abbrev WFS (A B : Type u) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.WFS A B

abbrev WeakEquiv {A : Type u} (f : A → A) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.WeakEquiv f

abbrev LeftDerived (A B : Type u) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.LeftDerived A B

/-! ## Representative model-category example paths -/

@[inline] noncomputable def dMap {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y : C (n + 1)} (p : Path x y) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.dMap cx p

theorem dMap_refl {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} (x : C (n + 1)) :
    dMap cx (Path.refl x) = Path.refl (cx.d x) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.dMap_refl cx x

theorem dMap_trans {C : Nat → Type u} (cx : ChainComplex C)
    {n : Nat} {x y z : C (n + 1)} (p : Path x y) (q : Path y z) :
    dMap cx (Path.trans p q) = Path.trans (dMap cx p) (dMap cx q) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.dMap_trans cx p q

@[inline] noncomputable def chainMapPath {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y : C n} (p : Path x y) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.chainMapPath φ p

theorem chainMapPath_symm {C D : Nat → Type u}
    {cC : ChainComplex C} {cD : ChainComplex D}
    (φ : ChainMap cC cD) {n : Nat} {x y : C n} (p : Path x y) :
    chainMapPath φ (Path.symm p) = Path.symm (chainMapPath φ p) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.chainMapPath_symm φ p

@[inline] noncomputable def roundTripRL {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.roundTripRL Q p

theorem roundTripRL_refl {A B : Type u} (Q : QuillenAdjData A B) (a : A) :
    roundTripRL Q (Path.refl a) = Path.refl (Q.R (Q.L a)) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.roundTripRL_refl Q a

theorem roundTripRL_trans {A B : Type u} (Q : QuillenAdjData A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    roundTripRL Q (Path.trans p q) =
      Path.trans (roundTripRL Q p) (roundTripRL Q q) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.roundTripRL_trans Q p q

@[inline] noncomputable def cylI₀Path {A : Type u} (C : CylinderObj A)
    {a₁ a₂ : A} (p : Path a₁ a₂) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.cylI₀Path C p

theorem cylI₀Path_trans {A : Type u} (C : CylinderObj A)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    cylI₀Path C (Path.trans p q) =
      Path.trans (cylI₀Path C p) (cylI₀Path C q) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.cylI₀Path_trans C p q

@[inline] noncomputable def retractWitness {A B : Type u}
    (R : ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.RetractData A B)
    (a : A) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.retractWitness R a

@[inline] noncomputable def wfsComposite {A B : Type u} (w : WFS A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.wfsComposite w p

theorem wfsComposite_refl {A B : Type u} (w : WFS A B) (a : A) :
    wfsComposite w (Path.refl a) = Path.refl (w.rightMap (w.leftMap a)) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.wfsComposite_refl w a

theorem wfsComposite_trans {A B : Type u} (w : WFS A B)
    {a₁ a₂ a₃ : A} (p : Path a₁ a₂) (q : Path a₂ a₃) :
    wfsComposite w (Path.trans p q) =
      Path.trans (wfsComposite w p) (wfsComposite w q) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.wfsComposite_trans w p q

@[inline] noncomputable def weakEquiv_leftInv_path {A : Type u}
    {f : A → A} (w : WeakEquiv f) (a : A) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.weakEquiv_leftInv_path w a

@[inline] noncomputable def weakEquiv_rightInv_path {A : Type u}
    {f : A → A} (w : WeakEquiv f) (a : A) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.weakEquiv_rightInv_path w a

@[inline] noncomputable def leftDerivedPath {A B : Type u}
    (D : LeftDerived A B) {a₁ a₂ : A} (p : Path a₁ a₂) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.leftDerivedPath D p

theorem leftDerivedPath_refl {A B : Type u} (D : LeftDerived A B) (a : A) :
    leftDerivedPath D (Path.refl a) = Path.refl (D.F a) :=
  ComputationalPaths.Path.Homotopy.ModelCategoryExamplesDeep.leftDerivedPath_refl D a

end ComputationalPaths.Path.Homotopy.ModelCategoryExamples
