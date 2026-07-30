/-
# Topological realization of nerve edges

This module constructs the canonical functor

```
C ⥤ FundamentalGroupoid (SSet.toTop.obj (CategoryTheory.nerve C))
```

for every small category `C`. Objects are realized vertices and morphisms are
realized one-simplices. Degenerate edges prove preservation of identities, and
the convexity of the topological two-simplex gives the endpoint-fixed homotopy
that proves preservation of composition.

The construction is the explicit forward map needed by the comparison between
a groupoid and the topological fundamental groupoid of its classifying space.
Proving that it is full and faithful is the separate topological edge-path
theorem; essential surjectivity is proved below.

## References

- Gabriel--Zisman, *Calculus of Fractions and Homotopy Theory*
- May, *Simplicial Objects in Algebraic Topology*, Section 16
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.Nerve
import Mathlib.AlgebraicTopology.SingularSet

open CategoryTheory Simplicial Opposite
open CategoryTheory.Limits

namespace ComputationalPaths
namespace Path
namespace TopologicalNerve

universe u

noncomputable def realizeSimplexHom
    {X : SSet.{u}} {n : SimplexCategory}
    (σ : X.obj (op n)) :
    SimplexCategory.toTop.{u}.obj n ⟶ SSet.toTop.obj X :=
  (SSet.toTopSimplex.inv.app n ≫
    SSet.toTop.map (SSet.yonedaEquiv.symm σ))

noncomputable def realizeSimplex
    {X : SSet.{u}} {n : SimplexCategory}
    (σ : X.obj (op n)) :
    C(SimplexCategory.toTop.{u}.obj n, SSet.toTop.obj X) :=
  (realizeSimplexHom σ).hom

theorem realizeSimplexHom_naturality
    {X : SSet.{u}} {m n : SimplexCategory}
    (f : m ⟶ n) (σ : X.obj (op n)) :
    SimplexCategory.toTop.map f ≫ realizeSimplexHom σ =
      realizeSimplexHom (X.map f.op σ) := by
  rw [realizeSimplexHom,
    SSet.toTopSimplex.inv.naturality_assoc]
  rw [realizeSimplexHom]
  congr 1
  change
    SSet.toTop.map (SSet.stdSimplex.map f) ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm σ) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (X.map f.op σ))
  rw [← SSet.toTop.map_comp]
  congr 1
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map,
    Equiv.apply_symm_apply]
  rfl

noncomputable def zeroTopPoint : ⦋0⦌.toTopObj :=
  ⟨1, show ∑ _, _ = _ by simp [SimplexCategory.toType_apply]⟩

noncomputable def zeroSimplexPoint :
    SimplexCategory.toTop.{u}.obj ⦋0⦌ :=
  (TopCat.of ⦋0⦌.toTopObj).uliftFunctorObjHomeo zeroTopPoint

noncomputable def edgeParameter (t : unitInterval) :
    SimplexCategory.toTop.{u}.obj ⦋1⦌ :=
  (TopCat.of ⦋1⦌.toTopObj).uliftFunctorObjHomeo
    (SimplexCategory.toTopObjOneHomeo.symm (unitInterval.symm t))

theorem continuous_edgeParameter :
    Continuous (edgeParameter : unitInterval →
      SimplexCategory.toTop.{u}.obj ⦋1⦌) := by
  exact
    (TopCat.of ⦋1⦌.toTopObj).uliftFunctorObjHomeo.continuous.comp
      (SimplexCategory.toTopObjOneHomeo.symm.continuous.comp
        unitInterval.continuous_symm)

theorem edgeParameter_zero :
    edgeParameter (0 : unitInterval) =
      SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (1 : Fin 2)) zeroSimplexPoint := by
  rw [edgeParameter, zeroSimplexPoint]
  change
    ULift.up
        (SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm (0 : unitInterval))) =
      ULift.up
        (SimplexCategory.toTopMap
          (SimplexCategory.δ (1 : Fin 2)) zeroTopPoint)
  apply ULift.ext
  have hδ (x : ToType ⦋0⦌) :
      (ConcreteCategory.hom
        (SimplexCategory.δ (1 : Fin 2))) x = 0 := by
    fin_cases x
    rfl
  apply SimplexCategory.toTopObj.ext
  funext i
  fin_cases i
  · rw [SimplexCategory.coe_toTopMap]
    have hfilter :
        Finset.univ.filter
            (fun x : ToType ⦋0⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.δ (1 : Fin 2))) x =
                  (0 : ToType ⦋1⦌)) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro x _
      exact hδ x
    change
      (SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm (0 : unitInterval))) (0 : Fin 2) =
        ∑ j ∈ Finset.univ.filter
          (fun x : ToType ⦋0⦌ =>
            (ConcreteCategory.hom
              (SimplexCategory.δ (1 : Fin 2))) x =
                (0 : ToType ⦋1⦌)), zeroTopPoint j
    rw [hfilter]
    simp [zeroTopPoint, SimplexCategory.toTopObjOneHomeo]
    rfl
  · rw [SimplexCategory.coe_toTopMap]
    have hfilter :
        Finset.univ.filter
            (fun x : ToType ⦋0⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.δ (1 : Fin 2))) x =
                  (1 : ToType ⦋1⦌)) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      rw [hδ x]
      decide
    change
      (SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm (0 : unitInterval))) (1 : Fin 2) =
        ∑ j ∈ Finset.univ.filter
          (fun x : ToType ⦋0⦌ =>
            (ConcreteCategory.hom
              (SimplexCategory.δ (1 : Fin 2))) x =
                (1 : ToType ⦋1⦌)), zeroTopPoint j
    rw [hfilter]
    simp [SimplexCategory.toTopObjOneHomeo]
    rfl

theorem edgeParameter_one :
    edgeParameter (1 : unitInterval) =
      SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (0 : Fin 2)) zeroSimplexPoint := by
  rw [edgeParameter, zeroSimplexPoint]
  change
    ULift.up
        (SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm (1 : unitInterval))) =
      ULift.up
        (SimplexCategory.toTopMap
          (SimplexCategory.δ (0 : Fin 2)) zeroTopPoint)
  apply ULift.ext
  have hδ (x : ToType ⦋0⦌) :
      (ConcreteCategory.hom
        (SimplexCategory.δ (0 : Fin 2))) x = 1 := by
    fin_cases x
    rfl
  apply SimplexCategory.toTopObj.ext
  funext i
  fin_cases i
  · rw [SimplexCategory.coe_toTopMap]
    have hfilter :
        Finset.univ.filter
            (fun x : ToType ⦋0⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.δ (0 : Fin 2))) x =
                  (0 : ToType ⦋1⦌)) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      rw [hδ x]
      decide
    change
      (SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm (1 : unitInterval))) (0 : Fin 2) =
        ∑ j ∈ Finset.univ.filter
          (fun x : ToType ⦋0⦌ =>
            (ConcreteCategory.hom
              (SimplexCategory.δ (0 : Fin 2))) x =
                (0 : ToType ⦋1⦌)), zeroTopPoint j
    rw [hfilter]
    simp [SimplexCategory.toTopObjOneHomeo]
    rfl
  · rw [SimplexCategory.coe_toTopMap]
    have hfilter :
        Finset.univ.filter
            (fun x : ToType ⦋0⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.δ (0 : Fin 2))) x =
                  (1 : ToType ⦋1⦌)) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro x _
      exact hδ x
    change
      (SimplexCategory.toTopObjOneHomeo.symm
          (unitInterval.symm (1 : unitInterval))) (1 : Fin 2) =
        ∑ j ∈ Finset.univ.filter
          (fun x : ToType ⦋0⦌ =>
            (ConcreteCategory.hom
              (SimplexCategory.δ (0 : Fin 2))) x =
                (1 : ToType ⦋1⦌)), zeroTopPoint j
    rw [hfilter]
    simp [zeroTopPoint, SimplexCategory.toTopObjOneHomeo]
    rfl

noncomputable def edgeParameterPath :
    _root_.Path
      (SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (1 : Fin 2)) zeroSimplexPoint)
      (SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (0 : Fin 2)) zeroSimplexPoint) where
  toFun := edgeParameter
  continuous_toFun := continuous_edgeParameter
  source' := edgeParameter_zero
  target' := edgeParameter_one

noncomputable def simplexVertexPoint
    {n : SimplexCategory} (i : ToType n) :
    SimplexCategory.toTop.{u}.obj n :=
  SimplexCategory.toTop.{u}.map
    (SimplexCategory.const ⦋0⦌ n i) zeroSimplexPoint

theorem simplexEdge_source
    {n : SimplexCategory} (f : ⦋1⦌ ⟶ n) :
    SimplexCategory.toTop.{u}.map f
        (SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (1 : Fin 2)) zeroSimplexPoint) =
      simplexVertexPoint (f.toOrderHom 0) := by
  have hf :
      SimplexCategory.δ (1 : Fin 2) ≫ f =
        SimplexCategory.const ⦋0⦌ n (f.toOrderHom 0) := by
    apply SimplexCategory.Hom.ext_zero_left
    rfl
  change
    (SimplexCategory.toTop.{u}.map f)
        ((SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (1 : Fin 2))) zeroSimplexPoint) =
      (SimplexCategory.toTop.{u}.map
        (SimplexCategory.const ⦋0⦌ n (f.toOrderHom 0)))
          zeroSimplexPoint
  rw [← ConcreteCategory.comp_apply, ← SimplexCategory.toTop.map_comp, hf]

theorem simplexEdge_target
    {n : SimplexCategory} (f : ⦋1⦌ ⟶ n) :
    SimplexCategory.toTop.{u}.map f
        (SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (0 : Fin 2)) zeroSimplexPoint) =
      simplexVertexPoint (f.toOrderHom 1) := by
  have hf :
      SimplexCategory.δ (0 : Fin 2) ≫ f =
        SimplexCategory.const ⦋0⦌ n (f.toOrderHom 1) := by
    apply SimplexCategory.Hom.ext_zero_left
    rfl
  change
    (SimplexCategory.toTop.{u}.map f)
        ((SimplexCategory.toTop.{u}.map
          (SimplexCategory.δ (0 : Fin 2))) zeroSimplexPoint) =
      (SimplexCategory.toTop.{u}.map
        (SimplexCategory.const ⦋0⦌ n (f.toOrderHom 1)))
          zeroSimplexPoint
  rw [← ConcreteCategory.comp_apply, ← SimplexCategory.toTop.map_comp, hf]

noncomputable def simplexEdgePath
    {n : SimplexCategory} (f : ⦋1⦌ ⟶ n) :
    _root_.Path
      (simplexVertexPoint (f.toOrderHom 0))
      (simplexVertexPoint (f.toOrderHom 1)) :=
  (edgeParameterPath.map
    (SimplexCategory.toTop.{u}.map f).hom.continuous).cast
      (simplexEdge_source f).symm
      (simplexEdge_target f).symm

noncomputable def simplexTriangleEdge01 :
    _root_.Path
      (simplexVertexPoint (n := ⦋2⦌) 0)
      (simplexVertexPoint (n := ⦋2⦌) 1) :=
  simplexEdgePath (SimplexCategory.mkOfLe
    (0 : Fin 3) (1 : Fin 3) (by decide))

noncomputable def simplexTriangleEdge12 :
    _root_.Path
      (simplexVertexPoint (n := ⦋2⦌) 1)
      (simplexVertexPoint (n := ⦋2⦌) 2) :=
  simplexEdgePath (SimplexCategory.mkOfLe
    (1 : Fin 3) (2 : Fin 3) (by decide))

noncomputable def simplexTriangleEdge02 :
    _root_.Path
      (simplexVertexPoint (n := ⦋2⦌) 0)
      (simplexVertexPoint (n := ⦋2⦌) 2) :=
  simplexEdgePath (SimplexCategory.mkOfLe
    (0 : Fin 3) (2 : Fin 3) (by decide))

noncomputable def topSimplexPathHomotopy
    {n : SimplexCategory}
    {x y : SimplexCategory.toTop.{u}.obj n}
    (p q : _root_.Path x y) :
    p.Homotopy q where
  toFun st :=
    ULift.up
      ⟨unitInterval.toNNReal (unitInterval.symm st.1) •
            (p st.2).down.1 +
          unitInterval.toNNReal st.1 • (q st.2).down.1,
        by
          change
            ∑ i,
                (unitInterval.toNNReal (unitInterval.symm st.1) •
                    (p st.2).down.1 +
                  unitInterval.toNNReal st.1 •
                    (q st.2).down.1) i =
              1
          simp only [Pi.add_apply, Pi.smul_apply]
          rw [Finset.sum_add_distrib, ← Finset.smul_sum,
            ← Finset.smul_sum, (p st.2).down.2, (q st.2).down.2]
          apply NNReal.eq
          simp [unitInterval.toNNReal]⟩
  continuous_toFun := by
    fun_prop
  map_zero_left t := by
    apply ULift.ext
    apply SimplexCategory.toTopObj.ext
    funext i
    apply NNReal.eq
    simp [unitInterval.toNNReal]
  map_one_left t := by
    apply ULift.ext
    apply SimplexCategory.toTopObj.ext
    funext i
    apply NNReal.eq
    simp [unitInterval.toNNReal]
  prop' s t ht := by
    rcases ht with ht | ht
    · subst t
      change
        ULift.up
            ⟨unitInterval.toNNReal (unitInterval.symm s) •
                  (p (0 : unitInterval)).down.1 +
                unitInterval.toNNReal s •
                  (q (0 : unitInterval)).down.1,
              _⟩ =
          p (0 : unitInterval)
      rw [p.source, q.source]
      apply ULift.ext
      apply SimplexCategory.toTopObj.ext
      funext i
      apply NNReal.eq
      simp [unitInterval.toNNReal]
      ring
    · subst t
      change
        ULift.up
            ⟨unitInterval.toNNReal (unitInterval.symm s) •
                  (p (1 : unitInterval)).down.1 +
                unitInterval.toNNReal s •
                  (q (1 : unitInterval)).down.1,
              _⟩ =
          p (1 : unitInterval)
      rw [p.target, q.target]
      apply ULift.ext
      apply SimplexCategory.toTopObj.ext
      funext i
      apply NNReal.eq
      simp [unitInterval.toNNReal]
      ring

noncomputable def simplexTriangleCompositionHomotopy :
    (simplexTriangleEdge01.trans simplexTriangleEdge12).Homotopy
      simplexTriangleEdge02 :=
  topSimplexPathHomotopy _ _

noncomputable def realizedVertex
    {X : SSet.{u}} (x : X _⦋0⦌) :
    SSet.toTop.obj X :=
  realizeSimplex x zeroSimplexPoint

noncomputable def realizedEdge
    {X : SSet.{u}} (e : X _⦋1⦌) :
    _root_.Path
      (realizedVertex (X.δ (1 : Fin 2) e))
      (realizedVertex (X.δ (0 : Fin 2) e)) where
  toFun t := realizeSimplex e (edgeParameter t)
  continuous_toFun :=
    (realizeSimplex e).continuous.comp continuous_edgeParameter
  source' := by
    rw [edgeParameter_zero]
    have h := _root_.congrArg
      (fun k :
          SimplexCategory.toTop.{u}.obj ⦋0⦌ ⟶
            SSet.toTop.obj X =>
        k zeroSimplexPoint)
      (realizeSimplexHom_naturality
        (SimplexCategory.δ (1 : Fin 2)) e)
    simpa [realizedVertex, realizeSimplex] using h
  target' := by
    rw [edgeParameter_one]
    have h := _root_.congrArg
      (fun k :
          SimplexCategory.toTop.{u}.obj ⦋0⦌ ⟶
            SSet.toTop.obj X =>
        k zeroSimplexPoint)
      (realizeSimplexHom_naturality
        (SimplexCategory.δ (0 : Fin 2)) e)
    simpa [realizedVertex, realizeSimplex] using h

section Nerve

variable {C : Type u} [Category.{u} C]

theorem nerve_mk₁_source
    {x y : C} (f : x ⟶ y) :
    (CategoryTheory.nerve C).δ (1 : Fin 2)
        (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₀ x :=
  ComposableArrows.ext₀ rfl

theorem nerve_mk₁_target
    {x y : C} (f : x ⟶ y) :
    (CategoryTheory.nerve C).δ (0 : Fin 2)
        (ComposableArrows.mk₁ f) =
      ComposableArrows.mk₀ y :=
  ComposableArrows.ext₀ rfl

noncomputable def nerveVertex (x : C) :
    SSet.toTop.obj (CategoryTheory.nerve C) :=
  realizedVertex (ComposableArrows.mk₀ x)

noncomputable def nerveEdge
    {x y : C} (f : x ⟶ y) :
    _root_.Path (nerveVertex x) (nerveVertex y) :=
  (realizedEdge (ComposableArrows.mk₁ f)).cast
    (by
      change
        realizedVertex (ComposableArrows.mk₀ x) =
          realizedVertex
            ((CategoryTheory.nerve C).δ (1 : Fin 2)
              (ComposableArrows.mk₁ f))
      rw [nerve_mk₁_source])
    (by
      change
        realizedVertex (ComposableArrows.mk₀ y) =
          realizedVertex
            ((CategoryTheory.nerve C).δ (0 : Fin 2)
              (ComposableArrows.mk₁ f))
      rw [nerve_mk₁_target])

theorem simplexDegeneracyParameter
    (t : unitInterval) :
    SimplexCategory.toTop.{u}.map
        (SimplexCategory.σ (0 : Fin 1)) (edgeParameter t) =
      zeroSimplexPoint :=
  by
    apply ULift.ext
    change _ = zeroTopPoint
    exact Subsingleton.elim _ _

theorem nerveEdge_id (x : C) :
    nerveEdge (𝟙 x) = _root_.Path.refl (nerveVertex x) := by
  ext t
  change
    realizeSimplex (X := CategoryTheory.nerve C) (n := ⦋1⦌)
        (ComposableArrows.mk₁ (𝟙 x)) (edgeParameter t) =
      realizeSimplex (X := CategoryTheory.nerve C) (n := ⦋0⦌)
        (ComposableArrows.mk₀ x) zeroSimplexPoint
  rw [← CategoryTheory.nerve.σ₀_mk₀_eq]
  have h := _root_.congrArg
    (fun k :
        SimplexCategory.toTop.{u}.obj ⦋1⦌ ⟶
          SSet.toTop.obj (CategoryTheory.nerve C) =>
      k (edgeParameter t))
    (realizeSimplexHom_naturality
      (X := CategoryTheory.nerve C)
      (SimplexCategory.σ (0 : Fin 1))
      (ComposableArrows.mk₀ x))
  change
    realizeSimplex (X := CategoryTheory.nerve C) (n := ⦋0⦌)
        (ComposableArrows.mk₀ x)
        (SimplexCategory.toTop.{u}.map
          (SimplexCategory.σ (0 : Fin 1)) (edgeParameter t)) =
      realizeSimplex (X := CategoryTheory.nerve C) (n := ⦋1⦌)
        ((CategoryTheory.nerve C).σ (0 : Fin 1)
          (ComposableArrows.mk₀ x)) (edgeParameter t) at h
  rw [simplexDegeneracyParameter] at h
  simpa [realizeSimplex] using h.symm

theorem mkOfLe_zero_one_eq_delta_two :
    SimplexCategory.mkOfLe
        (0 : Fin 3) (1 : Fin 3) (by decide) =
      SimplexCategory.δ (2 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

theorem mkOfLe_one_two_eq_delta_zero :
    SimplexCategory.mkOfLe
        (1 : Fin 3) (2 : Fin 3) (by decide) =
      SimplexCategory.δ (0 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

theorem mkOfLe_zero_two_eq_delta_one :
    SimplexCategory.mkOfLe
        (0 : Fin 3) (2 : Fin 3) (by decide) =
      SimplexCategory.δ (1 : Fin 3) := by
  ext i
  fin_cases i <;> rfl

theorem nerve_mk₂_edge01
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (CategoryTheory.nerve C).map
        (SimplexCategory.mkOfLe
          (0 : Fin 3) (1 : Fin 3) (by decide)).op
        (ComposableArrows.mk₂ f g) =
      ComposableArrows.mk₁ f := by
  rw [mkOfLe_zero_one_eq_delta_two]
  exact CategoryTheory.nerve.δ₂_mk₂_eq f g

theorem nerve_mk₂_edge12
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (CategoryTheory.nerve C).map
        (SimplexCategory.mkOfLe
          (1 : Fin 3) (2 : Fin 3) (by decide)).op
        (ComposableArrows.mk₂ f g) =
      ComposableArrows.mk₁ g := by
  rw [mkOfLe_one_two_eq_delta_zero]
  exact CategoryTheory.nerve.δ₀_mk₂_eq f g

theorem nerve_mk₂_edge02
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (CategoryTheory.nerve C).map
        (SimplexCategory.mkOfLe
          (0 : Fin 3) (2 : Fin 3) (by decide)).op
        (ComposableArrows.mk₂ f g) =
      ComposableArrows.mk₁ (f ≫ g) := by
  rw [mkOfLe_zero_two_eq_delta_one]
  exact CategoryTheory.nerve.δ₁_mk₂_eq f g

theorem map_simplexTriangleEdge01_apply
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
    (t : unitInterval) :
    (simplexTriangleEdge01.map
        (realizeSimplex
          (X := CategoryTheory.nerve C)
          (n := ⦋2⦌)
          (ComposableArrows.mk₂ f g)).continuous) t =
      nerveEdge f t := by
  change
    realizeSimplex (X := CategoryTheory.nerve C)
        (n := ⦋2⦌)
        (ComposableArrows.mk₂ f g)
        (SimplexCategory.toTop.{u}.map
          (SimplexCategory.mkOfLe
            (0 : Fin 3) (1 : Fin 3) (by decide))
          (edgeParameter t)) =
      realizeSimplex (X := CategoryTheory.nerve C)
        (n := ⦋1⦌)
        (ComposableArrows.mk₁ f) (edgeParameter t)
  have h := _root_.congrArg
    (fun k :
        SimplexCategory.toTop.{u}.obj ⦋1⦌ ⟶
          SSet.toTop.obj (CategoryTheory.nerve C) =>
      k (edgeParameter t))
    (realizeSimplexHom_naturality
      (X := CategoryTheory.nerve C)
      (SimplexCategory.mkOfLe
        (0 : Fin 3) (1 : Fin 3) (by decide))
      (ComposableArrows.mk₂ f g))
  rw [nerve_mk₂_edge01] at h
  simpa [realizeSimplex] using h

theorem map_simplexTriangleEdge12_apply
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
    (t : unitInterval) :
    (simplexTriangleEdge12.map
        (realizeSimplex
          (X := CategoryTheory.nerve C)
          (n := ⦋2⦌)
          (ComposableArrows.mk₂ f g)).continuous) t =
      nerveEdge g t := by
  change
    realizeSimplex (X := CategoryTheory.nerve C)
        (n := ⦋2⦌)
        (ComposableArrows.mk₂ f g)
        (SimplexCategory.toTop.{u}.map
          (SimplexCategory.mkOfLe
            (1 : Fin 3) (2 : Fin 3) (by decide))
          (edgeParameter t)) =
      realizeSimplex (X := CategoryTheory.nerve C)
        (n := ⦋1⦌)
        (ComposableArrows.mk₁ g) (edgeParameter t)
  have h := _root_.congrArg
    (fun k :
        SimplexCategory.toTop.{u}.obj ⦋1⦌ ⟶
          SSet.toTop.obj (CategoryTheory.nerve C) =>
      k (edgeParameter t))
    (realizeSimplexHom_naturality
      (X := CategoryTheory.nerve C)
      (SimplexCategory.mkOfLe
        (1 : Fin 3) (2 : Fin 3) (by decide))
      (ComposableArrows.mk₂ f g))
  rw [nerve_mk₂_edge12] at h
  simpa [realizeSimplex] using h

theorem map_simplexTriangleEdge02_apply
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z)
    (t : unitInterval) :
    (simplexTriangleEdge02.map
        (realizeSimplex
          (X := CategoryTheory.nerve C)
          (n := ⦋2⦌)
          (ComposableArrows.mk₂ f g)).continuous) t =
      nerveEdge (f ≫ g) t := by
  change
    realizeSimplex (X := CategoryTheory.nerve C)
        (n := ⦋2⦌)
        (ComposableArrows.mk₂ f g)
        (SimplexCategory.toTop.{u}.map
          (SimplexCategory.mkOfLe
            (0 : Fin 3) (2 : Fin 3) (by decide))
          (edgeParameter t)) =
      realizeSimplex (X := CategoryTheory.nerve C)
        (n := ⦋1⦌)
        (ComposableArrows.mk₁ (f ≫ g)) (edgeParameter t)
  have h := _root_.congrArg
    (fun k :
        SimplexCategory.toTop.{u}.obj ⦋1⦌ ⟶
          SSet.toTop.obj (CategoryTheory.nerve C) =>
      k (edgeParameter t))
    (realizeSimplexHom_naturality
      (X := CategoryTheory.nerve C)
      (SimplexCategory.mkOfLe
        (0 : Fin 3) (2 : Fin 3) (by decide))
      (ComposableArrows.mk₂ f g))
  rw [nerve_mk₂_edge02] at h
  simpa [realizeSimplex] using h

noncomputable def nerveEdge_comp_homotopy
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    (nerveEdge f).trans (nerveEdge g) |>.Homotopy
      (nerveEdge (f ≫ g)) := by
  let r :=
    realizeSimplex
      (X := CategoryTheory.nerve C)
      (n := ⦋2⦌)
      (ComposableArrows.mk₂ f g)
  have h := _root_.Path.Homotopy.map
    simplexTriangleCompositionHomotopy r
  let p01 := simplexTriangleEdge01.map r.continuous
  let p12 := simplexTriangleEdge12.map r.continuous
  let p02 := simplexTriangleEdge02.map r.continuous
  have h01 (t : unitInterval) : p01 t = nerveEdge f t :=
    map_simplexTriangleEdge01_apply f g t
  have h12 (t : unitInterval) : p12 t = nerveEdge g t :=
    map_simplexTriangleEdge12_apply f g t
  have h02 (t : unitInterval) : p02 t = nerveEdge (f ≫ g) t :=
    map_simplexTriangleEdge02_apply f g t
  refine
    { toFun := h
      continuous_toFun := h.continuous
      map_zero_left := ?_
      map_one_left := ?_
      prop' := ?_ }
  · intro t
    calc
      h (0, t) = p01.trans p12 t := by
        simp [p01, p12]
      _ = (nerveEdge f).trans (nerveEdge g) t := by
        rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
        split_ifs
        · exact h01 _
        · exact h12 _
  · intro t
    calc
      h (1, t) = p02 t := by
        simp [p02]
      _ = nerveEdge (f ≫ g) t := h02 t
  · intro s t ht
    calc
      h (s, t) = p01.trans p12 t := by
        simpa [p01, p12] using h.eq_fst s ht
      _ = (nerveEdge f).trans (nerveEdge g) t := by
        rw [_root_.Path.trans_apply, _root_.Path.trans_apply]
        split_ifs
        · exact h01 _
        · exact h12 _

attribute [local instance] _root_.Path.Homotopic.setoid

noncomputable def nerveRealizationFunctor :
    C ⥤ FundamentalGroupoid
      (SSet.toTop.obj (CategoryTheory.nerve C)) where
  obj x := ⟨nerveVertex x⟩
  map f := Quotient.mk' (nerveEdge f)
  map_id x := by
    rw [nerveEdge_id, FundamentalGroupoid.id_eq_path_refl]
    rfl
  map_comp f g := by
    exact Quotient.sound ⟨(nerveEdge_comp_homotopy f g).symm⟩

end Nerve

/-- Every point of a geometric realization is represented by a point of one
of its topological simplices. -/
theorem realization_point_representation
    (X : SSet.{u}) (x : SSet.toTop.obj X) :
    ∃ (n : SimplexCategory) (σ : X.obj (op n))
      (p : SimplexCategory.toTop.{u}.obj n),
      realizeSimplex σ p = x := by
  let E := Functor.LeftExtension.mk SSet.toTop SSet.toTopSimplex.inv
  let h : IsColimit (E.coconeAt X) :=
    Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      SSet.toTop SSet.toTopSimplex.inv X
  let h' := isColimitOfPreserves (forget TopCat) h
  obtain ⟨g, p, hp⟩ :=
    Types.jointly_surjective_of_isColimit h' x
  refine ⟨g.left, SSet.yonedaEquiv g.hom, p, ?_⟩
  simpa [E, Functor.LeftExtension.coconeAt, realizeSimplex,
    realizeSimplexHom] using hp

/-- Chosen simplex representative of a point in a geometric realization. -/
structure RealizationPointRepresentation
    (X : SSet.{u}) (x : SSet.toTop.obj X) where
  /-- Dimension category of the representing simplex. -/
  n : SimplexCategory
  /-- The simplex containing the point. -/
  simplex : X.obj (op n)
  /-- Barycentric point of that simplex. -/
  point : SimplexCategory.toTop.{u}.obj n
  /-- The simplex point realizes to the original point. -/
  realize_eq : realizeSimplex simplex point = x

/-- Choose a simplex representative using the colimit presentation of
geometric realization. -/
noncomputable def realizationPointRepresentation
    (X : SSet.{u}) (x : SSet.toTop.obj X) :
    RealizationPointRepresentation X x :=
  Classical.choice (by
    rcases realization_point_representation X x with ⟨n, σ, p, hp⟩
    exact ⟨⟨n, σ, p, hp⟩⟩)

/-- Zeroth vertex in a topological simplex. -/
noncomputable def simplexZeroVertex (n : SimplexCategory) :
    SimplexCategory.toTop.{u}.obj n :=
  simplexVertexPoint (0 : ToType n)

/-- Every point of a topological simplex is joined to its zeroth vertex. -/
noncomputable def pathToSimplexZeroVertex
    {n : SimplexCategory}
    (p : SimplexCategory.toTop.{u}.obj n) :
    _root_.Path p (simplexZeroVertex n) := by
  let γ := @PathConnectedSpace.somePath n.toTopObj _
    (inferInstance : PathConnectedSpace n.toTopObj)
    p.down (simplexZeroVertex n).down
  exact (γ.map continuous_uliftUp).cast
    (ULift.up_down p).symm
    (ULift.up_down (simplexZeroVertex n)).symm

theorem nerve_simplex_zero_vertex
    {C : Type u} [Category.{u} C]
    {n : SimplexCategory}
    (σ : (CategoryTheory.nerve C).obj (op n)) :
    (CategoryTheory.nerve C).map
        (SimplexCategory.const ⦋0⦌ n 0).op σ =
      ComposableArrows.mk₀ (σ.obj 0) :=
  ComposableArrows.ext₀ rfl

theorem realize_nerve_simplex_zero_vertex
    {C : Type u} [Category.{u} C]
    {n : SimplexCategory}
    (σ : (CategoryTheory.nerve C).obj (op n)) :
    realizeSimplex σ (simplexZeroVertex n) =
      nerveVertex (σ.obj 0) := by
  have h := _root_.congrArg
    (fun k :
        SimplexCategory.toTop.{u}.obj ⦋0⦌ ⟶
          SSet.toTop.obj (CategoryTheory.nerve C) =>
      k zeroSimplexPoint)
    (realizeSimplexHom_naturality
      (X := CategoryTheory.nerve C)
      (SimplexCategory.const ⦋0⦌ n 0) σ)
  rw [nerve_simplex_zero_vertex] at h
  simpa [simplexZeroVertex, simplexVertexPoint, realizeSimplex,
    nerveVertex, realizedVertex] using h

/-- Every point of the realized nerve is joined to a realized object. -/
noncomputable def realizationPathToVertex
    {C : Type u} [Category.{u} C]
    (x : SSet.toTop.obj (CategoryTheory.nerve C)) :
    Σ c : C, _root_.Path x (nerveVertex c) := by
  let rep :=
    realizationPointRepresentation (CategoryTheory.nerve C) x
  refine ⟨rep.simplex.obj 0, ?_⟩
  exact
    ((pathToSimplexZeroVertex rep.point).map
      (realizeSimplex rep.simplex).continuous).cast
        rep.realize_eq.symm
        (realize_nerve_simplex_zero_vertex rep.simplex).symm

attribute [local instance] _root_.Path.Homotopic.setoid

/-- The canonical nerve-realization functor is essentially surjective: every
point of the realization lies in the path component of a realized vertex. -/
noncomputable instance nerveRealizationFunctor_essSurj
    {C : Type u} [Category.{u} C] :
    (nerveRealizationFunctor (C := C)).EssSurj where
  mem_essImage x := by
    let ⟨c, p⟩ := realizationPathToVertex x.as
    exact ⟨c, ⟨asIso (Quotient.mk' p.symm)⟩⟩

/-- Computational-path certificate for the composition law carried by the
canonical realization functor. -/
noncomputable def nerveRealizationCompositionPath
    {C : Type u} [Category.{u} C]
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    Path
      (Quotient.mk' ((nerveEdge f).trans (nerveEdge g)))
      (Quotient.mk' (nerveEdge (f ≫ g))) :=
  Path.stepChain
    (Quotient.sound ⟨nerveEdge_comp_homotopy f g⟩)

/-- The composition certificate is stable under a trailing reflexive
topological comparison step. -/
noncomputable def nerveRealizationCompositionCoherence
    {C : Type u} [Category.{u} C]
    {x y z : C} (f : x ⟶ y) (g : y ⟶ z) :
    RwEq
      (Path.trans (nerveRealizationCompositionPath f g)
        (Path.refl (Quotient.mk' (nerveEdge (f ≫ g)))))
      (nerveRealizationCompositionPath f g) :=
  rweq_cmpA_refl_right (nerveRealizationCompositionPath f g)

end TopologicalNerve
end Path
end ComputationalPaths
