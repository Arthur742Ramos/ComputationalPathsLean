/-
# Realization atlases and contractions of categorical nerves

This module supplies two pieces of point-set topology used by the topological
edge-path comparison.

* `realizationAtlas` presents Mathlib's genuine geometric realization as a
  quotient of the disjoint union of its topological simplices.
* `contractibleSpace_nerve_of_isInitial` constructs an explicit contraction of
  the realization of the nerve of a category with an initial object.

The contraction is obtained by prepending the initial object to every
composable chain and assigning it barycentric weight `t`.  Its joint continuity
is proved through the left-Kan-extension colimit defining `SSet.toTop`; no
synthetic realization or additional axiom is used.

## References

* May, *Simplicial Objects in Algebraic Topology*, Section 16.
* Goerss--Jardine, *Simplicial Homotopy Theory*, I.5.
-/

import ComputationalPaths.Path.Homotopy.TopologicalNerve
import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Maps.Basic

open CategoryTheory Simplicial Opposite
open CategoryTheory.Limits

namespace ComputationalPaths
namespace Path
namespace TopologicalNerve

universe u

/-! ## The quotient atlas of geometric realization -/

/-- The left extension whose value at a simplicial set is its geometric
realization. -/
noncomputable def realizationExtension :
    SSet.stdSimplex.{u}.LeftExtension SimplexCategory.toTop.{u} :=
  Functor.LeftExtension.mk SSet.toTop SSet.toTopSimplex.inv

/-- The category of simplices indexing the realization of `X`. -/
abbrev RealizationIndex (X : SSet.{u}) :=
  CostructuredArrow SSet.stdSimplex X

/-- Disjoint union of all topological simplices mapping to `X`. -/
abbrev RealizationAtlas (X : SSet.{u}) :=
  Σ j : RealizationIndex X, SimplexCategory.toTop.{u}.obj j.left

/-- The canonical cocone exhibiting the realization as the colimit of its
topological simplices. -/
noncomputable def realizationCocone (X : SSet.{u}) :
    Cocone (CostructuredArrow.proj SSet.stdSimplex X ⋙
      SimplexCategory.toTop.{u}) :=
  realizationExtension.coconeAt X

/-- The canonical realization cocone is colimiting. -/
noncomputable def realizationCoconeIsColimit (X : SSet.{u}) :
    IsColimit (realizationCocone X) :=
  Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
    SSet.toTop SSet.toTopSimplex.inv X

/-- Aggregate map from the disjoint union of topological simplices to the
geometric realization. -/
noncomputable def realizationAtlas (X : SSet.{u}) :
    RealizationAtlas X → SSet.toTop.obj X :=
  fun p => (realizationCocone X).ι.app p.1 p.2

theorem realizationAtlas_surjective (X : SSet.{u}) :
    Function.Surjective (realizationAtlas X) := by
  intro x
  let h := isColimitOfPreserves (forget TopCat)
    (realizationCoconeIsColimit X)
  obtain ⟨j, p, hp⟩ := Types.jointly_surjective_of_isColimit h x
  exact ⟨⟨j, p⟩, hp⟩

/-- The aggregate simplex map carries precisely the final topology of
geometric realization. -/
theorem realizationAtlas_isQuotientMap (X : SSet.{u}) :
    Topology.IsQuotientMap (realizationAtlas X) := by
  rw [Topology.isQuotientMap_iff]
  refine ⟨realizationAtlas_surjective X, ?_⟩
  intro U
  rw [TopCat.isOpen_iff_of_isColimit
    (realizationCocone X) (realizationCoconeIsColimit X)]
  rw [isOpen_sigma_iff]
  rfl

theorem realizationAtlas_apply
    {X : SSet.{u}} (j : RealizationIndex X)
    (p : SimplexCategory.toTop.{u}.obj j.left) :
    realizationAtlas X ⟨j, p⟩ =
      realizeSimplex (SSet.yonedaEquiv j.hom) p := by
  simp [realizationAtlas, realizationCocone, realizationExtension,
    Functor.LeftExtension.coconeAt, realizeSimplex, realizeSimplexHom]

/-! ## Categorical and barycentric cone operations -/

variable {D : Type u} [Category.{u} D]

/-- Prepend an initial object to a composable chain. -/
noncomputable def prependSimplex
    {d₀ : D} (h : IsInitial d₀) {n : ℕ}
    (s : ComposableArrows D n) :
    ComposableArrows D (n + 1) :=
  s.precomp (h.to s.left)

/-- Extend a simplex-category map by a new initial vertex. -/
def prependMap {a b : SimplexCategory} (f : a ⟶ b) :
    ⦋a.len + 1⦌ ⟶ ⦋b.len + 1⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i =>
        Fin.cases (0 : Fin (b.len + 2))
          (fun j => (f.toOrderHom j).succ) i
      monotone' := by
        rintro ⟨_ | i, hi⟩ ⟨_ | j, hj⟩ hij
        · exact le_rfl
        · exact Fin.zero_le _
        · simp only [Fin.mk_le_mk] at hij
          omega
        · simp only [Fin.mk_le_mk] at hij ⊢
          have hi' : i < a.len + 1 := by simpa using hi
          have hj' : j < a.len + 1 := by simpa using hj
          change
            (f.toOrderHom ⟨i, hi'⟩).succ ≤
              (f.toOrderHom ⟨j, hj'⟩).succ
          exact Fin.succ_le_succ_iff.mpr
            (f.toOrderHom.monotone
              (show (⟨i, hi'⟩ : Fin (a.len + 1)) ≤
                  ⟨j, hj'⟩ by
                simpa only [Fin.mk_le_mk] using
                  (show i ≤ j by omega))) }

@[simp] theorem prependMap_zero
    {a b : SimplexCategory} (f : a ⟶ b) :
    (prependMap f).toOrderHom 0 = 0 := rfl

@[simp] theorem prependMap_succ
    {a b : SimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len + 1)) :
    (prependMap f).toOrderHom i.succ =
      (f.toOrderHom i).succ := rfl

@[simp] theorem coe_prependMap_zero
    {a b : SimplexCategory} (f : a ⟶ b) :
    (ConcreteCategory.hom (prependMap f)) 0 = 0 := rfl

@[simp] theorem coe_prependMap_succ
    {a b : SimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len + 1)) :
    (ConcreteCategory.hom (prependMap f)) i.succ =
      (ConcreteCategory.hom f i).succ := rfl

theorem coe_prependMap
    {a b : SimplexCategory} (f : a ⟶ b)
    (i : Fin (a.len + 2)) :
    (ConcreteCategory.hom (prependMap f)) i =
      Fin.cases (0 : Fin (b.len + 2))
        (fun j => (ConcreteCategory.hom f j).succ) i := rfl

theorem prependSimplex_naturality
    {d₀ : D} (h : IsInitial d₀)
    {a b : SimplexCategory} (f : a ⟶ b)
    (s : ComposableArrows D b.len) :
    prependSimplex h ((CategoryTheory.nerve D).map f.op s) =
      (prependSimplex h s).whiskerLeft
        (SimplexCategory.toCat.map (prependMap f)) := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro i
    rcases i with ⟨_ | i, hi⟩
    · rfl
    · rfl
  · intro i hi
    cases i with
    | zero =>
        dsimp [prependSimplex]
        simp only [Category.id_comp, Category.comp_id]
        apply h.hom_ext
    | succ i =>
        dsimp [prependSimplex, prependMap]
        simp only [Category.id_comp, Category.comp_id]
        change s.map _ = s.map _
        congr 1

/-- Add a barycentric coordinate of weight `t` at the new initial vertex. -/
noncomputable def coneTopPoint {a : SimplexCategory}
    (t : unitInterval) (p : a.toTopObj) :
    ⦋a.len + 1⦌.toTopObj :=
  ⟨Fin.cases (unitInterval.toNNReal t)
      (fun i => unitInterval.toNNReal (unitInterval.symm t) * p i),
    by
      show ∑ i : Fin (a.len + 2), Fin.cases
        (unitInterval.toNNReal t)
        (fun i => unitInterval.toNNReal (unitInterval.symm t) * p i) i =
          (1 : NNReal)
      rw [Fin.sum_univ_succ]
      simp only [Fin.cases_zero, Fin.cases_succ]
      rw [← Finset.mul_sum]
      have hp : ∑ i : Fin (a.len + 1), p i = 1 := by
        change ∑ i : ToType a, p i = 1
        exact p.2
      rw [hp]
      apply NNReal.eq
      simp [unitInterval.toNNReal]⟩

/-- Universe-lifted barycentric cone map. -/
noncomputable def coneParameter {a : SimplexCategory}
    (t : unitInterval)
    (p : SimplexCategory.toTop.{u}.obj a) :
    SimplexCategory.toTop.{u}.obj ⦋a.len + 1⦌ :=
  ULift.up (coneTopPoint t p.down)

theorem continuous_coneParameter {a : SimplexCategory} :
    Continuous (fun tp :
      unitInterval × SimplexCategory.toTop.{u}.obj a =>
        coneParameter tp.1 tp.2) := by
  unfold coneParameter coneTopPoint
  apply continuous_uliftUp.comp
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (unitInterval.toNNReal_continuous).comp continuous_fst
  · exact
      ((unitInterval.toNNReal_continuous).comp
        (unitInterval.continuous_symm.comp continuous_fst)).mul
        (show Continuous
          (fun tp : unitInterval ×
            SimplexCategory.toTop.{u}.obj a =>
              (tp.2.down : a.toTopObj).val j) from
          (continuous_apply j).comp
            (continuous_subtype_val.comp
              (continuous_uliftDown.comp continuous_snd)))

theorem coneParameter_zero {n : ℕ}
    (p : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    coneParameter (0 : unitInterval) p =
      SimplexCategory.toTop.{u}.map
        (SimplexCategory.δ (0 : Fin (n + 2))) p := by
  apply ULift.ext
  change coneTopPoint (0 : unitInterval) p.down =
    SimplexCategory.toTopMap
      (SimplexCategory.δ (0 : Fin (n + 2))) p.down
  apply SimplexCategory.toTopObj.ext
  funext i
  have hδ (x : ToType ⦋n⦌) :
      (ConcreteCategory.hom
        (SimplexCategory.δ (0 : Fin (n + 2)))) x = x.succ := by
    rfl
  rcases i with ⟨_ | i, hi⟩
  · rw [SimplexCategory.coe_toTopMap]
    have hf :
        Finset.univ.filter
            (fun x : ToType ⦋n⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.δ (0 : Fin (n + 2)))) x =
                  (0 : ToType ⦋n + 1⦌)) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      rw [hδ x]
      exact Fin.succ_ne_zero x
    change _ =
      ∑ j ∈ Finset.univ.filter
        (fun x : ToType ⦋n⦌ =>
          (ConcreteCategory.hom
            (SimplexCategory.δ (0 : Fin (n + 2)))) x =
              (0 : ToType ⦋n + 1⦌)), p.down.val j
    rw [hf]
    simp [coneTopPoint, unitInterval.toNNReal]
  · rw [SimplexCategory.coe_toTopMap]
    change i + 1 < n + 2 at hi
    let j : Fin (n + 1) := ⟨i, by omega⟩
    have ht :
        (⟨i + 1, hi⟩ : ToType ⦋n + 1⦌) = j.succ := by
      rfl
    have hf :
        Finset.univ.filter
            (fun x : ToType ⦋n⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.δ (0 : Fin (n + 2)))) x =
                  (⟨i + 1, hi⟩ : ToType ⦋n + 1⦌)) =
          {j} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      rw [hδ x, ht]
      exact (Fin.succ_injective _).eq_iff
    rw [hf]
    simp [coneTopPoint, unitInterval.toNNReal, j]

theorem coneParameter_one {n : ℕ}
    (p : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    coneParameter (1 : unitInterval) p =
      simplexVertexPoint
        (n := ⦋n + 1⦌) (0 : Fin (n + 2)) := by
  apply ULift.ext
  change coneTopPoint (1 : unitInterval) p.down =
    SimplexCategory.toTopMap
      (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌ (0 : Fin (n + 2)))
      zeroTopPoint
  apply SimplexCategory.toTopObj.ext
  funext i
  have hc (x : ToType ⦋0⦌) :
      (ConcreteCategory.hom
        (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌
          (0 : Fin (n + 2)))) x = 0 := by
    fin_cases x
    rfl
  rcases i with ⟨_ | i, hi⟩
  · rw [SimplexCategory.coe_toTopMap]
    have hf :
        Finset.univ.filter
            (fun x : ToType ⦋0⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌
                  (0 : Fin (n + 2)))) x =
                    (0 : ToType ⦋n + 1⦌)) =
          Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro x _
      exact hc x
    change _ =
      ∑ j ∈ Finset.univ.filter
        (fun x : ToType ⦋0⦌ =>
          (ConcreteCategory.hom
            (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌
              (0 : Fin (n + 2)))) x =
                (0 : ToType ⦋n + 1⦌)), zeroTopPoint j
    rw [hf]
    simp [coneTopPoint, unitInterval.toNNReal, zeroTopPoint]
  · rw [SimplexCategory.coe_toTopMap]
    have hf :
        Finset.univ.filter
            (fun x : ToType ⦋0⦌ =>
              (ConcreteCategory.hom
                (SimplexCategory.const ⦋0⦌ ⦋n + 1⦌
                  (0 : Fin (n + 2)))) x =
                    (⟨i + 1, hi⟩ : ToType ⦋n + 1⦌)) =
          ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro x _
      rw [hc x]
      intro h
      have h' := _root_.congrArg Fin.val h
      simp at h'
    rw [hf]
    simp [coneTopPoint, unitInterval.toNNReal]

/-- The face opposite the newly adjoined initial vertex. -/
def prependFace (a : SimplexCategory) :
    a ⟶ ⦋a.len + 1⦌ :=
  eqToHom (SimplexCategory.mk_len a).symm ≫
    SimplexCategory.δ (0 : Fin (a.len + 2))

theorem coneParameter_zero_general
    {a : SimplexCategory}
    (p : SimplexCategory.toTop.{u}.obj a) :
    coneParameter (0 : unitInterval) p =
      SimplexCategory.toTop.{u}.map (prependFace a) p := by
  induction a using SimplexCategory.rec with
  | _ n =>
      simpa [prependFace] using (coneParameter_zero (n := n) p)

theorem coneParameter_one_general
    {a : SimplexCategory}
    (p : SimplexCategory.toTop.{u}.obj a) :
    coneParameter (1 : unitInterval) p =
      simplexVertexPoint
        (n := ⦋a.len + 1⦌) (0 : Fin (a.len + 2)) := by
  induction a using SimplexCategory.rec with
  | _ n =>
      simpa using (coneParameter_one (n := n) p)

theorem coneParameter_naturality
    {a b : SimplexCategory} (f : a ⟶ b)
    (t : unitInterval)
    (p : SimplexCategory.toTop.{u}.obj a) :
    SimplexCategory.toTop.{u}.map (prependMap f)
        (coneParameter t p) =
      coneParameter t (SimplexCategory.toTop.{u}.map f p) := by
  apply ULift.ext
  change
    SimplexCategory.toTopMap (prependMap f) (coneTopPoint t p.down) =
      coneTopPoint t (SimplexCategory.toTopMap f p.down)
  apply SimplexCategory.toTopObj.ext
  funext i
  rcases i with ⟨_ | i, hi⟩
  · rw [SimplexCategory.coe_toTopMap]
    rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    change
      (if (0 : Fin (b.len + 2)) = 0 then
          unitInterval.toNNReal t else 0) +
          (∑ x : Fin (a.len + 1),
            if (ConcreteCategory.hom f x).succ = 0 then
              unitInterval.toNNReal (unitInterval.symm t) * p.down.val x
            else 0) =
        unitInterval.toNNReal t
    simp
  · rw [SimplexCategory.coe_toTopMap]
    change i + 1 < b.len + 2 at hi
    let k : Fin (b.len + 1) := ⟨i, by omega⟩
    have ht :
        (⟨i + 1, hi⟩ : Fin (b.len + 2)) = k.succ := by
      rfl
    rw [ht]
    rw [Finset.sum_filter]
    rw [Fin.sum_univ_succ]
    simp only [coe_prependMap, Fin.cases_zero, Fin.cases_succ,
      Ne.symm (Fin.succ_ne_zero k), ↓reduceIte, zero_add,
      Fin.succ_inj]
    simp only [coneTopPoint, Fin.cases_succ]
    rw [SimplexCategory.coe_toTopMap]
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ConcreteCategory.hom f x = k <;> simp [hx]

/-! ## Descent of the contraction through geometric realization -/

theorem costructured_simplex_naturality
    {X : SSet.{u}}
    {A B : CostructuredArrow SSet.stdSimplex X}
    (f : A ⟶ B) :
    SSet.yonedaEquiv A.hom =
      X.map f.left.op (SSet.yonedaEquiv B.hom) := by
  rw [← CostructuredArrow.w f]
  rw [SSet.yonedaEquiv_comp, SSet.stdSimplex.yonedaEquiv_map]
  have hn := congr_fun (B.hom.naturality f.left.op)
    (SSet.stdSimplex.objEquiv.symm (𝟙 B.left))
  simpa [SSet.stdSimplex.map_apply] using hn

/-- The contraction path associated to a point in a single simplex. -/
noncomputable def contractionPath
    {d₀ : D} (h : IsInitial d₀)
    {a : SimplexCategory}
    (s : (CategoryTheory.nerve D).obj (op a))
    (p : SimplexCategory.toTop.{u}.obj a) :
    C(unitInterval, SSet.toTop.obj (CategoryTheory.nerve D)) where
  toFun t :=
    realizeSimplex
      (X := CategoryTheory.nerve D) (n := ⦋a.len + 1⦌)
      (prependSimplex h s) (coneParameter t p)
  continuous_toFun :=
    (realizeSimplex
      (X := CategoryTheory.nerve D) (n := ⦋a.len + 1⦌)
      (prependSimplex h s)).continuous.comp
      (continuous_coneParameter.comp
        (continuous_id.prodMk continuous_const))

theorem continuous_contractionPath
    {d₀ : D} (h : IsInitial d₀)
    {a : SimplexCategory}
    (s : (CategoryTheory.nerve D).obj (op a)) :
    Continuous (contractionPath h s) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact
    (realizeSimplex
      (X := CategoryTheory.nerve D) (n := ⦋a.len + 1⦌)
      (prependSimplex h s)).continuous.comp
      (continuous_coneParameter.comp
        (continuous_snd.prodMk continuous_fst))

/-- The simplexwise contractions form a cocone valued in the compact-open path
space. -/
noncomputable def contractionCocone
    {d₀ : D} (h : IsInitial d₀) :
    Cocone
      (CostructuredArrow.proj SSet.stdSimplex
        (CategoryTheory.nerve D) ⋙
          SimplexCategory.toTop.{u}) where
  pt := TopCat.of
    C(unitInterval, SSet.toTop.obj (CategoryTheory.nerve D))
  ι :=
    { app := fun j =>
        TopCat.ofHom
          ⟨fun p =>
              contractionPath h (a := j.left)
                (SSet.yonedaEquiv j.hom) p,
            continuous_contractionPath h _⟩
      naturality := by
        intro A B f
        ext p
        apply ContinuousMap.ext
        intro t
        let sB : (CategoryTheory.nerve D).obj (op B.left) :=
          SSet.yonedaEquiv B.hom
        change
          contractionPath h sB
              (SimplexCategory.toTop.{u}.map f.left p) t =
            contractionPath h (SSet.yonedaEquiv A.hom) p t
        have hs :
            SSet.yonedaEquiv A.hom =
              (CategoryTheory.nerve D).map f.left.op sB :=
          costructured_simplex_naturality f
        have hcone :
            (CategoryTheory.nerve D).map
                (prependMap f.left).op (prependSimplex h sB) =
              prependSimplex h (SSet.yonedaEquiv A.hom) := by
          rw [hs]
          exact (prependSimplex_naturality h f.left sB).symm
        change
          realizeSimplex
              (X := CategoryTheory.nerve D)
              (n := ⦋B.left.len + 1⦌)
              (prependSimplex h sB)
              (coneParameter t
                (SimplexCategory.toTop.{u}.map f.left p)) =
            realizeSimplex
              (X := CategoryTheory.nerve D)
              (n := ⦋A.left.len + 1⦌)
              (prependSimplex h (SSet.yonedaEquiv A.hom))
              (coneParameter t p)
        rw [← coneParameter_naturality]
        have hr := _root_.congrArg
          (fun k :
              SimplexCategory.toTop.{u}.obj
                  ⦋A.left.len + 1⦌ ⟶
                SSet.toTop.obj (CategoryTheory.nerve D) =>
            k (coneParameter t p))
          (realizeSimplexHom_naturality
            (X := CategoryTheory.nerve D)
            (prependMap f.left) (prependSimplex h sB))
        change
          realizeSimplex (prependSimplex h sB)
              (SimplexCategory.toTop.{u}.map
                (prependMap f.left) (coneParameter t p)) =
            realizeSimplex
              ((CategoryTheory.nerve D).map
                (prependMap f.left).op (prependSimplex h sB))
              (coneParameter t p) at hr
        rw [← hcone]
        simpa [contractionPath] using hr }

/-- The contraction, curried as a continuous map into the compact-open path
space. -/
noncomputable def contractionCurried
    {d₀ : D} (h : IsInitial d₀) :
    SSet.toTop.obj (CategoryTheory.nerve D) ⟶
      TopCat.of
        C(unitInterval,
          SSet.toTop.obj (CategoryTheory.nerve D)) :=
  (realizationCoconeIsColimit
    (CategoryTheory.nerve D)).desc (contractionCocone h)

theorem contractionCurried_realizeSimplex
    {d₀ : D} (h : IsInitial d₀)
    (j : RealizationIndex (CategoryTheory.nerve D))
    (p : SimplexCategory.toTop.{u}.obj j.left) :
    contractionCurried h
        (realizeSimplex (SSet.yonedaEquiv j.hom) p) =
      contractionPath h (SSet.yonedaEquiv j.hom) p := by
  have hf :=
    (realizationCoconeIsColimit
      (CategoryTheory.nerve D)).fac (contractionCocone h) j
  have hp := _root_.congrArg (fun k => k p) hf
  simpa [contractionCurried, contractionCocone,
    realizationCocone, realizationExtension,
    Functor.LeftExtension.coconeAt, realizeSimplex,
    realizeSimplexHom] using hp

theorem prependSimplex_face_zero
    {d₀ : D} (h : IsInitial d₀)
    {a : SimplexCategory}
    (s : (CategoryTheory.nerve D).obj (op a)) :
    (CategoryTheory.nerve D).map
        (SimplexCategory.δ
          (0 : Fin (a.len + 2))).op
        (prependSimplex h s) =
      s := by
  exact ComposableArrows.precomp_δ₀ _ _

theorem prependSimplex_prependFace
    {d₀ : D} (h : IsInitial d₀)
    {a : SimplexCategory}
    (s : (CategoryTheory.nerve D).obj (op a)) :
    (CategoryTheory.nerve D).map
        (prependFace a).op (prependSimplex h s) = s := by
  induction a using SimplexCategory.rec with
  | _ n =>
      simpa [prependFace] using
        (prependSimplex_face_zero h s)

theorem contractionPath_zero
    {d₀ : D} (h : IsInitial d₀)
    {a : SimplexCategory}
    (s : (CategoryTheory.nerve D).obj (op a))
    (p : SimplexCategory.toTop.{u}.obj a) :
    contractionPath h s p (0 : unitInterval) =
      realizeSimplex s p := by
  change
    realizeSimplex (prependSimplex h s)
        (coneParameter (0 : unitInterval) p) =
      realizeSimplex s p
  rw [coneParameter_zero_general]
  have hr := _root_.congrArg
    (fun k :
        SimplexCategory.toTop.{u}.obj a ⟶
          SSet.toTop.obj (CategoryTheory.nerve D) => k p)
    (realizeSimplexHom_naturality
      (X := CategoryTheory.nerve D)
      (prependFace a) (prependSimplex h s))
  change
    realizeSimplex (prependSimplex h s)
        (SimplexCategory.toTop.{u}.map (prependFace a) p) =
      realizeSimplex
        ((CategoryTheory.nerve D).map
          (prependFace a).op (prependSimplex h s)) p at hr
  rw [prependSimplex_prependFace h s] at hr
  exact hr

theorem contractionPath_one
    {d₀ : D} (h : IsInitial d₀)
    {a : SimplexCategory}
    (s : (CategoryTheory.nerve D).obj (op a))
    (p : SimplexCategory.toTop.{u}.obj a) :
    contractionPath h s p (1 : unitInterval) =
      nerveVertex d₀ := by
  change
    realizeSimplex (prependSimplex h s)
        (coneParameter (1 : unitInterval) p) =
      nerveVertex d₀
  rw [coneParameter_one_general]
  simpa [prependSimplex] using
    (realize_nerve_simplex_zero_vertex
      (C := D) (n := ⦋a.len + 1⦌)
      (prependSimplex h s))

theorem contractionCurried_zero
    {d₀ : D} (h : IsInitial d₀)
    (x : SSet.toTop.obj (CategoryTheory.nerve D)) :
    contractionCurried h x (0 : unitInterval) = x := by
  obtain ⟨⟨j, p⟩, hp⟩ :=
    realizationAtlas_surjective (CategoryTheory.nerve D) x
  rw [realizationAtlas_apply] at hp
  rw [← hp, contractionCurried_realizeSimplex, contractionPath_zero]
  rfl

theorem contractionCurried_one
    {d₀ : D} (h : IsInitial d₀)
    (x : SSet.toTop.obj (CategoryTheory.nerve D)) :
    contractionCurried h x (1 : unitInterval) =
      nerveVertex d₀ := by
  obtain ⟨⟨j, p⟩, hp⟩ :=
    realizationAtlas_surjective (CategoryTheory.nerve D) x
  rw [realizationAtlas_apply] at hp
  rw [← hp, contractionCurried_realizeSimplex, contractionPath_one]

/-- Explicit topological contraction of the realized nerve. -/
noncomputable def contractionHomotopy
    {d₀ : D} (h : IsInitial d₀) :
    ContinuousMap.Homotopy
      (ContinuousMap.id
        (SSet.toTop.obj (CategoryTheory.nerve D)))
      (ContinuousMap.const
        (SSet.toTop.obj (CategoryTheory.nerve D))
        (nerveVertex d₀)) where
  toFun tx := contractionCurried h tx.2 tx.1
  continuous_toFun :=
    (ContinuousMap.continuous_uncurry_of_continuous
      (contractionCurried h).hom).comp
        (continuous_snd.prodMk continuous_fst)
  map_zero_left := contractionCurried_zero h
  map_one_left := contractionCurried_one h

/-- The realization of the nerve of a category with an initial object is
contractible. -/
theorem contractibleSpace_nerve_of_isInitial
    {d₀ : D} (h : IsInitial d₀) :
    ContractibleSpace
      (SSet.toTop.obj (CategoryTheory.nerve D)) := by
  rw [contractible_iff_id_nullhomotopic]
  exact ⟨nerveVertex d₀, ⟨contractionHomotopy h⟩⟩

/-! ## Computational-path certificate -/

/-- Path-valued certificate recording the contraction's initial endpoint. -/
noncomputable def contractionEndpointPath
    {d₀ : D} (h : IsInitial d₀)
    (x : SSet.toTop.obj (CategoryTheory.nerve D)) :
    Path (contractionCurried h x (0 : unitInterval)) x :=
  Path.stepChain (contractionCurried_zero h x)

/-- The endpoint certificate is coherent with a trailing reflexive step. -/
noncomputable def contractionEndpointCoherence
    {d₀ : D} (h : IsInitial d₀)
    (x : SSet.toTop.obj (CategoryTheory.nerve D)) :
    RwEq
      (Path.trans (contractionEndpointPath h x) (Path.refl x))
      (contractionEndpointPath h x) :=
  rweq_cmpA_refl_right (contractionEndpointPath h x)

end TopologicalNerve
end Path
end ComputationalPaths
