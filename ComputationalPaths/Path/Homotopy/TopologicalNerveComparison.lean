/-
# Fundamental groupoid of a realized groupoid nerve

The realized under-category projection is a covering map with contractible
total space.  Path and homotopy lifting therefore identify arrows of a
groupoid with homotopy classes of paths between its realized vertices.
-/

import ComputationalPaths.Path.Homotopy.TopologicalNerveCover
import Mathlib.Topology.Homotopy.Lifting

open CategoryTheory Simplicial Opposite
open unitInterval

namespace ComputationalPaths
namespace Path
namespace TopologicalNerve

universe u

variable {K : Type u} [Groupoid.{u} K]

/-! ## Vertex stars and their fibers -/

noncomputable def nerveVertexCore
    {D : Type u} [Category.{u} D] (y : D) :
    (CategoryTheory.nerve D) _⦋0⦌ :=
  ComposableArrows.mk₀ y

theorem nerveVertexCore_nonDegenerate
    {D : Type u} [Category.{u} D] (y : D) :
    nerveVertexCore y ∈
      (CategoryTheory.nerve D).nonDegenerate 0 := by
  simp [nerveVertexCore]

/-- A zero-simplex point lies in the descended star of that simplex. -/
theorem zeroSimplexPoint_mem_realizationStar
    (X : SSet.{u}) (c : X _⦋0⦌)
    (hc : c ∈ X.nonDegenerate 0) :
    realizeSimplex c zeroSimplexPoint ∈
      SimplexCoreFace.realizationStar
        X c hc := by
  apply (SimplexCoreFace.realizeSimplex_mem_realizationStar_iff
    (n := ⦋0⦌) X c hc c zeroSimplexPoint).2
  let p : ⦋0⦌.toTopObj := zeroSimplexPoint.down
  change p ∈ SimplexCoreFace.simplexStar
    X c c
  rw [SimplexCoreFace.simplexStar, Set.mem_iUnion]
  let h := SimplexCoreFace.identity (X := X) c
  refine ⟨h, ?_⟩
  intro i
  fin_cases i
  have hout : h.totalOutsideMass p = 0 := by
    simp [h, SimplexCoreFace.totalOutsideMass,
      SimplexCoreFace.identity]
  have hp0 : p 0 = 1 :=
    SimplexCategory.toTopObj_zero_apply_zero p
  have hcore : h.coreMass p 0 = 1 := by
    unfold SimplexCoreFace.coreMass
    change ∑ j : Fin 1 with j = 0, p j = 1
    have hf :
        Finset.univ.filter (fun j : Fin 1 => j = 0) = {0} := by
      ext j
      simp
    rw [hf]
    simp [hp0]
  have hpos : h.totalOutsideMass p < h.coreMass p 0 := by
    rw [hout, hcore]
    exact zero_lt_one
  simpa using hpos

/-- A realized vertex lies in the descended star of its zero-simplex. -/
theorem nerveVertex_mem_realizationStar
    {D : Type u} [Category.{u} D] (y : D) :
    nerveVertex y ∈
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve D) (nerveVertexCore y)
        (nerveVertexCore_nonDegenerate y) :=
  zeroSimplexPoint_mem_realizationStar
    (CategoryTheory.nerve D) (nerveVertexCore y)
      (nerveVertexCore_nonDegenerate y)

theorem liftCoreSimplex_nerveVertexCore (x y : K)
    (e : NerveCoreFiber x (nerveVertexCore y)) :
    liftCoreSimplex x (nerveVertexCore y) e =
      ComposableArrows.mk₀ e.1 := by
  apply ComposableArrows.ext₀
  exact liftCoreSimplex_vertex x (nerveVertexCore y) e

theorem nerveVertex_mem_nerveCoreSheet (x y : K)
    (e : NerveCoreFiber x (nerveVertexCore y)) :
    nerveVertex e.1 ∈
      nerveCoreSheet x (nerveVertexCore y)
        (nerveVertexCore_nonDegenerate y) e := by
  rw [nerveCoreSheet]
  have hpoint :
      nerveVertex e.1 =
        realizeSimplex
          (liftCoreSimplex x (nerveVertexCore y) e)
          zeroSimplexPoint := by
    exact _root_.congrArg
      (fun s :
        (CategoryTheory.nerve (Under x)) _⦋0⦌ =>
          realizeSimplex s zeroSimplexPoint)
      (liftCoreSimplex_nerveVertexCore x y e).symm
  rw [hpoint]
  exact zeroSimplexPoint_mem_realizationStar
    (CategoryTheory.nerve (Under x))
    (liftCoreSimplex x (nerveVertexCore y) e)
    (liftCoreSimplex_nonDegenerate x (nerveVertexCore y)
      (nerveVertexCore_nonDegenerate y) e)

/-- Object of `Under x` labelling a point over the realized vertex `y`. -/
noncomputable def nerveCoverFiberObject (x y : K)
    (z : SSet.toTop.obj (CategoryTheory.nerve (Under x)))
    (hz : nerveCoverMap x z = nerveVertex y) :
    Under x := by
  let z' : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) (nerveVertexCore y)
        (nerveVertexCore_nonDegenerate y) :=
    ⟨z, by
      change nerveCoverMap x z ∈
        SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) (nerveVertexCore y)
          (nerveVertexCore_nonDegenerate y)
      rw [hz]
      exact nerveVertex_mem_realizationStar y⟩
  exact (nerveCoreSheetLabel x (nerveVertexCore y)
    (nerveVertexCore_nonDegenerate y) z').1

theorem nerveCoverFiberObject_right (x y : K)
    (z : SSet.toTop.obj (CategoryTheory.nerve (Under x)))
    (hz : nerveCoverMap x z = nerveVertex y) :
    (nerveCoverFiberObject x y z hz).right = y := by
  unfold nerveCoverFiberObject
  exact (nerveCoreSheetLabel x (nerveVertexCore y)
    (nerveVertexCore_nonDegenerate y) _).2

/-- A point over a realized vertex is itself the corresponding realized
under-category vertex. -/
theorem eq_nerveVertex_nerveCoverFiberObject (x y : K)
    (z : SSet.toTop.obj (CategoryTheory.nerve (Under x)))
    (hz : nerveCoverMap x z = nerveVertex y) :
    z = nerveVertex (nerveCoverFiberObject x y z hz) := by
  let z' : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) (nerveVertexCore y)
        (nerveVertexCore_nonDegenerate y) :=
    ⟨z, by
      change nerveCoverMap x z ∈
        SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) (nerveVertexCore y)
          (nerveVertexCore_nonDegenerate y)
      rw [hz]
      exact nerveVertex_mem_realizationStar y⟩
  let e : NerveCoreFiber x (nerveVertexCore y) :=
    nerveCoreSheetLabel x (nerveVertexCore y)
      (nerveVertexCore_nonDegenerate y) z'
  have hzSheet :
      z ∈ nerveCoreSheet x (nerveVertexCore y)
        (nerveVertexCore_nonDegenerate y) e :=
    nerveCoreSheetLabel_mem x (nerveVertexCore y)
      (nerveVertexCore_nonDegenerate y) z'
  have heSheet :
      nerveVertex e.1 ∈ nerveCoreSheet x (nerveVertexCore y)
        (nerveVertexCore_nonDegenerate y) e :=
    nerveVertex_mem_nerveCoreSheet x y e
  have eright : e.1.right = y := by
    simpa [nerveVertexCore] using e.2
  apply nerveCoreSheet_injOn x (nerveVertexCore y)
    (nerveVertexCore_nonDegenerate y) e hzSheet heSheet
  calc
    nerveCoverMap x z = nerveVertex y := hz
    _ = nerveVertex e.1.right := by rw [eright]
    _ = nerveCoverMap x (nerveVertex e.1) :=
      (nerveCoverMap_vertex x e.1).symm

/-- Arrow represented by a point in the fiber over a realized vertex. -/
noncomputable def nerveCoverFiberArrow (x y : K)
    (z : SSet.toTop.obj (CategoryTheory.nerve (Under x)))
    (hz : nerveCoverMap x z = nerveVertex y) :
    x ⟶ y :=
  (nerveCoverFiberObject x y z hz).hom ≫
    eqToHom (nerveCoverFiberObject_right x y z hz)

theorem nerveCoverFiberObject_eq_mk (x y : K)
    (z : SSet.toTop.obj (CategoryTheory.nerve (Under x)))
    (hz : nerveCoverMap x z = nerveVertex y) :
    nerveCoverFiberObject x y z hz =
      Under.mk (nerveCoverFiberArrow x y z hz) := by
  apply underObjectExt
    (nerveCoverFiberObject_right x y z hz)
  rfl

theorem nerveCoverFiberObject_nerveVertex (x : K)
    (e : Under x) :
    nerveCoverFiberObject x e.right (nerveVertex e)
      (nerveCoverMap_vertex x e) = e := by
  have hzstar :
      nerveCoverMap x (nerveVertex e) ∈
        SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) (nerveVertexCore e.right)
          (nerveVertexCore_nonDegenerate e.right) := by
    rw [nerveCoverMap_vertex]
    exact nerveVertex_mem_realizationStar e.right
  let z' : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) (nerveVertexCore e.right)
        (nerveVertexCore_nonDegenerate e.right) :=
    ⟨nerveVertex e, hzstar⟩
  change (nerveCoreSheetLabel x (nerveVertexCore e.right)
    (nerveVertexCore_nonDegenerate e.right) z').1 = e
  exact _root_.congrArg Subtype.val
    (nerveCoreSheetLabel_eq_of_mem x
      (nerveVertexCore e.right)
      (nerveVertexCore_nonDegenerate e.right) z' ⟨e, rfl⟩
      (nerveVertex_mem_nerveCoreSheet x e.right ⟨e, rfl⟩))

theorem under_hom_comp_eqToHom_of_eq (x : K)
    {U V : Under x} (h : U = V) :
    U.hom ≫ eqToHom (_root_.congrArg
      (fun q : Under x => q.right) h) = V.hom := by
  subst V
  simp

theorem nerveCoverFiberArrow_nerveVertex (x : K)
    (e : Under x) :
    nerveCoverFiberArrow x e.right (nerveVertex e)
      (nerveCoverMap_vertex x e) = e.hom := by
  let o := nerveCoverFiberObject x e.right (nerveVertex e)
    (nerveCoverMap_vertex x e)
  have ho : o = e := nerveCoverFiberObject_nerveVertex x e
  change o.hom ≫ eqToHom _ = e.hom
  simpa using under_hom_comp_eqToHom_of_eq x ho

theorem nerveCoverFiberArrow_eq_of_eq (x y : K)
    {z z' : SSet.toTop.obj (CategoryTheory.nerve (Under x))}
    (hz : nerveCoverMap x z = nerveVertex y)
    (hz' : nerveCoverMap x z' = nerveVertex y)
    (h : z = z') :
    nerveCoverFiberArrow x y z hz =
      nerveCoverFiberArrow x y z' hz' := by
  subst z'
  rfl

/-! ## Projection of realized edges -/

theorem nerveCoverMap_nerveEdge (x : K)
    {e₀ e₁ : Under x} (f : e₀ ⟶ e₁) :
    ((nerveEdge f).map (continuous_nerveCoverMap x)).cast
        (nerveCoverMap_vertex x e₀).symm
        (nerveCoverMap_vertex x e₁).symm =
      nerveEdge f.right := by
  ext t
  change nerveCoverMap x
      (realizeSimplex (ComposableArrows.mk₁ f) (edgeParameter t)) =
    realizeSimplex (ComposableArrows.mk₁ f.right) (edgeParameter t)
  rw [nerveCoverMap, map_realizeSimplex]
  congr 2
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro j
    fin_cases j <;> rfl
  · intro j hj
    change j < 1 at hj
    have : j = 0 := by omega
    subst j
    simp [nerveCoverSSetMap, nerveCoverFunctor]

/-! ## Path lifting and the hom-set inverse -/

noncomputable def nervePathLift (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    C(I, SSet.toTop.obj (CategoryTheory.nerve (Under a))) :=
  (isCoveringMap_nerveCoverMap a).liftPath γ
    (nerveCoverBaseVertex a)
    (γ.source.trans (nerveCoverMap_baseVertex a).symm)

theorem nervePathLift_lifts (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    nerveCoverMap a ∘ nervePathLift a b γ = γ :=
  (isCoveringMap_nerveCoverMap a).liftPath_lifts γ
    (nerveCoverBaseVertex a)
    (γ.source.trans (nerveCoverMap_baseVertex a).symm)

theorem nervePathLift_zero (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    nervePathLift a b γ 0 = nerveCoverBaseVertex a :=
  (isCoveringMap_nerveCoverMap a).liftPath_zero γ
    (nerveCoverBaseVertex a)
    (γ.source.trans (nerveCoverMap_baseVertex a).symm)

theorem nervePathLift_one_projects (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    nerveCoverMap a (nervePathLift a b γ 1) =
      nerveVertex b := by
  exact (congrFun (nervePathLift_lifts a b γ) 1).trans γ.target

/-- Decode a topological path by lifting it to the contractible realized
under-category and reading off its endpoint sheet. -/
noncomputable def nervePathArrow (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    a ⟶ b :=
  nerveCoverFiberArrow a b (nervePathLift a b γ 1)
    (nervePathLift_one_projects a b γ)

theorem nervePathArrow_homotopic (a b : K)
    {γ δ : _root_.Path (nerveVertex a) (nerveVertex b)}
    (h : γ.Homotopic δ) :
    nervePathArrow a b γ = nervePathArrow a b δ := by
  have hend :=
    (isCoveringMap_nerveCoverMap a).liftPath_apply_one_eq_of_homotopicRel
      h (nerveCoverBaseVertex a)
      (γ.source.trans (nerveCoverMap_baseVertex a).symm)
      (δ.source.trans (nerveCoverMap_baseVertex a).symm)
  exact nerveCoverFiberArrow_eq_of_eq a b
    (nervePathLift_one_projects a b γ)
    (nervePathLift_one_projects a b δ) hend

/-- Decode a morphism in the topological fundamental groupoid to the original
groupoid. -/
noncomputable def nerveRealizationHomInv (a b : K) :
    (FundamentalGroupoid.mk (nerveVertex a) ⟶
      FundamentalGroupoid.mk (nerveVertex b)) →
      (a ⟶ b) :=
  Quotient.lift (nervePathArrow a b)
    (fun _ _ h => nervePathArrow_homotopic a b h)

noncomputable def nerveCoverInitialMorphism (a : K)
    (e : Under a) :
    Under.mk (𝟙 a) ⟶ e :=
  (nerveCoverInitial a).to e

theorem nerveCoverInitialMorphism_right (a : K)
    (e : Under a) :
    (nerveCoverInitialMorphism a e).right = e.hom := by
  simpa [nerveCoverInitialMorphism] using
    Under.w (nerveCoverInitialMorphism a e)

theorem nerveCoverInitialEdge_lifts
    {a b : K} (f : a ⟶ b) :
    nerveCoverMap a ∘
        nerveEdge (nerveCoverInitialMorphism a (Under.mk f)) =
      nerveEdge f := by
  funext t
  change nerveCoverMap a
      (realizeSimplex
        (ComposableArrows.mk₁
          (nerveCoverInitialMorphism a (Under.mk f)))
        (edgeParameter t)) =
    realizeSimplex (ComposableArrows.mk₁ f) (edgeParameter t)
  rw [nerveCoverMap, map_realizeSimplex]
  congr 2
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro j
    fin_cases j <;> rfl
  · intro j hj
    change j < 1 at hj
    have : j = 0 := by omega
    subst j
    simp [nerveCoverSSetMap, nerveCoverFunctor,
      nerveCoverInitialMorphism_right]

theorem nerveCoverInitialEdge_zero
    {a b : K} (f : a ⟶ b) :
    nerveEdge (nerveCoverInitialMorphism a (Under.mk f)) 0 =
      nerveCoverBaseVertex a := by
  change nerveEdge (nerveCoverInitialMorphism a (Under.mk f)) 0 =
    nerveVertex (Under.mk (𝟙 a))
  exact (nerveEdge
    (nerveCoverInitialMorphism a (Under.mk f))).source

theorem nervePathLift_nerveEdge
    {a b : K} (f : a ⟶ b) :
    (nerveEdge
      (nerveCoverInitialMorphism a (Under.mk f))).toContinuousMap =
        nervePathLift a b (nerveEdge f) := by
  apply ((isCoveringMap_nerveCoverMap a).eq_liftPath_iff'
    (γ := nerveEdge f)
    (e := nerveCoverBaseVertex a)
    (γ_0 := (nerveEdge f).source.trans
      (nerveCoverMap_baseVertex a).symm)).2
  exact ⟨nerveCoverInitialEdge_lifts f,
    nerveCoverInitialEdge_zero f⟩

theorem nervePathArrow_nerveEdge
    {a b : K} (f : a ⟶ b) :
    nervePathArrow a b (nerveEdge f) = f := by
  let ef : Under a := Under.mk f
  have hend :
      nervePathLift a b (nerveEdge f) 1 =
        nerveVertex ef := by
    rw [← nervePathLift_nerveEdge f]
    exact (nerveEdge
      (nerveCoverInitialMorphism a (Under.mk f))).target
  calc
    nervePathArrow a b (nerveEdge f) =
        nerveCoverFiberArrow a b (nerveVertex ef)
          (nerveCoverMap_vertex a ef) :=
      nerveCoverFiberArrow_eq_of_eq a b
        (nervePathLift_one_projects a b (nerveEdge f))
        (nerveCoverMap_vertex a ef) hend
    _ = f := nerveCoverFiberArrow_nerveVertex a ef

theorem nerveRealizationHomInv_map
    {a b : K} (f : a ⟶ b) :
    nerveRealizationHomInv a b
      ((nerveRealizationFunctor (C := K)).map f) = f := by
  exact nervePathArrow_nerveEdge f

theorem nervePathLift_one_eq_nerveVertex_arrow
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    nervePathLift a b γ 1 =
      nerveVertex (Under.mk (nervePathArrow a b γ)) := by
  let z := nervePathLift a b γ 1
  let hz := nervePathLift_one_projects a b γ
  calc
    z = nerveVertex (nerveCoverFiberObject a b z hz) :=
      eq_nerveVertex_nerveCoverFiberObject a b z hz
    _ = nerveVertex (Under.mk (nervePathArrow a b γ)) :=
      _root_.congrArg nerveVertex
        (nerveCoverFiberObject_eq_mk a b z hz)

noncomputable def nervePathLiftPath
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    _root_.Path (nerveCoverBaseVertex a)
      (nervePathLift a b γ 1) where
  toFun := nervePathLift a b γ
  continuous_toFun := (nervePathLift a b γ).continuous
  source' := nervePathLift_zero a b γ
  target' := rfl

noncomputable def nervePathLiftPathToArrow
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    _root_.Path (nerveCoverBaseVertex a)
      (nerveVertex (Under.mk (nervePathArrow a b γ))) :=
  (nervePathLiftPath a b γ).cast rfl
    (nervePathLift_one_eq_nerveVertex_arrow a b γ).symm

noncomputable def projectedNervePathLift
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    _root_.Path (nerveVertex a) (nerveVertex b) :=
  ((nervePathLiftPathToArrow a b γ).map
    (continuous_nerveCoverMap a)).cast
      (nerveCoverMap_baseVertex a).symm
      (nerveCoverMap_vertex a
        (Under.mk (nervePathArrow a b γ))).symm

theorem projectedNervePathLift_eq
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    projectedNervePathLift a b γ = γ := by
  ext t
  change nerveCoverMap a (nervePathLift a b γ t) = γ t
  exact congrFun (nervePathLift_lifts a b γ) t

noncomputable def projectedInitialEdge
    {a b : K} (f : a ⟶ b) :
    _root_.Path (nerveVertex a) (nerveVertex b) :=
  ((nerveEdge
      (nerveCoverInitialMorphism a (Under.mk f))).map
        (continuous_nerveCoverMap a)).cast
    (nerveCoverMap_vertex a (Under.mk (𝟙 a))).symm
    (nerveCoverMap_vertex a (Under.mk f)).symm

theorem projectedInitialEdge_eq
    {a b : K} (f : a ⟶ b) :
    projectedInitialEdge f = nerveEdge f := by
  simpa [projectedInitialEdge, nerveCoverInitialMorphism_right] using
    nerveCoverMap_nerveEdge a
      (nerveCoverInitialMorphism a (Under.mk f))

theorem nervePathLiftPath_homotopic_initialEdge
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    (nervePathLiftPathToArrow a b γ).Homotopic
      (nerveEdge
        (nerveCoverInitialMorphism a
          (Under.mk (nervePathArrow a b γ)))) := by
  letI : ContractibleSpace
      (SSet.toTop.obj (CategoryTheory.nerve (Under a))) :=
    contractibleSpace_nerveCover a
  exact SimplyConnectedSpace.paths_homotopic _ _

theorem projectedNervePathLift_homotopic_initialEdge
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    (projectedNervePathLift a b γ).Homotopic
      (projectedInitialEdge (nervePathArrow a b γ)) := by
  obtain ⟨H⟩ :=
    nervePathLiftPath_homotopic_initialEdge a b γ
  refine ⟨?_⟩
  exact (H.compContinuousMap
    ⟨nerveCoverMap a, continuous_nerveCoverMap a⟩).cast rfl rfl

theorem nerveEdge_nervePathArrow_homotopic
    (a b : K)
    (γ : _root_.Path (nerveVertex a) (nerveVertex b)) :
    γ.Homotopic (nerveEdge (nervePathArrow a b γ)) := by
  obtain ⟨H⟩ :=
    projectedNervePathLift_homotopic_initialEdge a b γ
  exact ⟨H.cast
    (projectedNervePathLift_eq a b γ)
    (projectedInitialEdge_eq (nervePathArrow a b γ))⟩

theorem nerveRealizationMap_homInv
    {a b : K}
    (q : FundamentalGroupoid.mk (nerveVertex a) ⟶
      FundamentalGroupoid.mk (nerveVertex b)) :
    (nerveRealizationFunctor (C := K)).map
        (nerveRealizationHomInv a b q) = q := by
  refine Quotient.inductionOn q fun γ => ?_
  exact Quotient.sound
    (nerveEdge_nervePathArrow_homotopic a b γ).symm

/-- Explicit hom-set equivalence between a groupoid and the fundamental
groupoid of its realized nerve. -/
noncomputable def nerveRealizationHomEquiv (a b : K) :
    (a ⟶ b) ≃
      (FundamentalGroupoid.mk (nerveVertex a) ⟶
        FundamentalGroupoid.mk (nerveVertex b)) where
  toFun := (nerveRealizationFunctor (C := K)).map
  invFun := nerveRealizationHomInv a b
  left_inv := nerveRealizationHomInv_map
  right_inv := nerveRealizationMap_homInv

noncomputable instance nerveRealizationFunctor_full :
    (nerveRealizationFunctor (C := K)).Full where
  map_surjective {a b} q :=
    ⟨nerveRealizationHomInv a b q,
      nerveRealizationMap_homInv q⟩

noncomputable instance nerveRealizationFunctor_faithful :
    (nerveRealizationFunctor (C := K)).Faithful where
  map_injective {a b} f g h := by
    rw [← nerveRealizationHomInv_map f,
      ← nerveRealizationHomInv_map g, h]

noncomputable instance nerveRealizationFunctor_isEquivalence :
    (nerveRealizationFunctor (C := K)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := inferInstance

/-- Public edge-path equivalence for every Mathlib groupoid. -/
noncomputable def nerveFundamentalGroupoidEquivalence :
    K ≌ FundamentalGroupoid
      (SSet.toTop.obj (CategoryTheory.nerve K)) :=
  (nerveRealizationFunctor (C := K)).asEquivalence

/-! ## Computational-path certificate -/

noncomputable def coveringBaseVertexPath (x : K) :
    Path (nerveCoverMap x (nerveCoverBaseVertex x)) (nerveVertex x) :=
  nerveCoverBaseVertexPath x

noncomputable def coveringBaseVertexCoherence (x : K) :
    RwEq
      (Path.trans (coveringBaseVertexPath x)
        (Path.refl (nerveVertex x)))
      (coveringBaseVertexPath x) :=
  rweq_cmpA_refl_right (coveringBaseVertexPath x)

end TopologicalNerve
end Path
end ComputationalPaths
