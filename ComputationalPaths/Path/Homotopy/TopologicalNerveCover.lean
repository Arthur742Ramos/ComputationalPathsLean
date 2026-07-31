/-
# Universal categorical cover of a realized groupoid nerve

For an object `x` in a groupoid `C`, the under-category `Under x` is the
categorical universal cover of `C`: it has the initial object `𝟙 x`, and the
forgetful functor records the endpoint of an arrow out of `x`.

This module constructs the induced map on Mathlib geometric realizations and
proves that its total space is contractible.  The remaining point-set theorem
needed by the edge-path comparison is that this realized discrete
Grothendieck fibration is a covering map; the definitions here isolate that
map without replacing the genuine realization.
-/

import ComputationalPaths.Path.Homotopy.TopologicalNerveContractible
import Mathlib.CategoryTheory.Comma.Over.Basic

open CategoryTheory Simplicial Opposite
open CategoryTheory.Limits

namespace ComputationalPaths
namespace Path
namespace TopologicalNerve

universe u

variable {C : Type u} [Category.{u} C]

/-- The categorical universal-cover total category based at `x`. -/
abbrev NerveCover (x : C) := Under x

/-- Projection of the categorical universal cover to the original category. -/
def nerveCoverFunctor (x : C) : NerveCover x ⥤ C :=
  Under.forget x

/-- Simplicial map induced by the categorical universal-cover projection. -/
def nerveCoverSSetMap (x : C) :
    CategoryTheory.nerve (NerveCover x) ⟶ CategoryTheory.nerve C :=
  CategoryTheory.nerveMap (nerveCoverFunctor x)

/-- Map on genuine Mathlib geometric realizations induced by the categorical
universal cover. -/
noncomputable def nerveCoverMap (x : C) :
    SSet.toTop.obj (CategoryTheory.nerve (NerveCover x)) →
      SSet.toTop.obj (CategoryTheory.nerve C) :=
  (SSet.toTop.map (nerveCoverSSetMap x)).hom

theorem continuous_nerveCoverMap (x : C) :
    Continuous (nerveCoverMap x) :=
  (SSet.toTop.map (nerveCoverSSetMap x)).hom.continuous

/-- Initial object of the categorical universal cover. -/
noncomputable def nerveCoverInitial (x : C) :
    IsInitial (Under.mk (𝟙 x)) :=
  Under.mkIdInitial

/-- The total realization of the categorical universal cover is
contractible. -/
theorem contractibleSpace_nerveCover (x : C) :
    ContractibleSpace
      (SSet.toTop.obj (CategoryTheory.nerve (NerveCover x))) :=
  contractibleSpace_nerve_of_isInitial (nerveCoverInitial x)

/-- The canonical base vertex in the total space. -/
noncomputable def nerveCoverBaseVertex (x : C) :
    SSet.toTop.obj (CategoryTheory.nerve (NerveCover x)) :=
  nerveVertex (Under.mk (𝟙 x))

theorem nerveCoverSSetMap_vertex
    (x : C) (e : NerveCover x) :
    (nerveCoverSSetMap x).app (op ⦋0⦌)
        (ComposableArrows.mk₀ e) =
      ComposableArrows.mk₀ e.right :=
  ComposableArrows.ext₀ rfl

theorem map_realizeSimplex
    {X Y : SSet.{u}} (f : X ⟶ Y)
    {n : SimplexCategory} (s : X.obj (op n))
    (p : SimplexCategory.toTop.{u}.obj n) :
    SSet.toTop.map f (realizeSimplex s p) =
      realizeSimplex (f.app _ s) p := by
  change
    ((SSet.toTopSimplex.inv.app n ≫
        SSet.toTop.map (SSet.yonedaEquiv.symm s)) ≫
      SSet.toTop.map f) p =
    (SSet.toTopSimplex.inv.app n ≫
      SSet.toTop.map
        (SSet.yonedaEquiv.symm (f.app _ s))) p
  have hmap :
      SSet.yonedaEquiv.symm s ≫ f =
        SSet.yonedaEquiv.symm (f.app _ s) := by
    apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  rw [Category.assoc, ← SSet.toTop.map_comp, hmap]

theorem nerveCoverMap_vertex
    (x : C) (e : NerveCover x) :
    nerveCoverMap x (nerveVertex e) =
      nerveVertex e.right := by
  change
    SSet.toTop.map (nerveCoverSSetMap x)
        (realizeSimplex (ComposableArrows.mk₀ e) zeroSimplexPoint) =
      realizeSimplex (ComposableArrows.mk₀ e.right) zeroSimplexPoint
  rw [map_realizeSimplex, nerveCoverSSetMap_vertex]

@[simp] theorem nerveCoverMap_baseVertex (x : C) :
    nerveCoverMap x (nerveCoverBaseVertex x) =
      nerveVertex x := by
  simpa [nerveCoverBaseVertex] using
    nerveCoverMap_vertex x (Under.mk (𝟙 x))

/-! ## Unique lifting of simplices -/

variable {K : Type u} [Groupoid.{u} K]

/-- Extensionality for objects of an under-category, including the necessary
transport along equality of codomains. -/
theorem underObjectExt {x : K} {U V : Under x}
    (hr : U.right = V.right)
    (hh : U.hom ≫ eqToHom hr = V.hom) :
    U = V := by
  rcases U with ⟨uLeft, uRight, uHom⟩
  rcases V with ⟨vLeft, vRight, vHom⟩
  rcases uLeft with ⟨⟨⟩⟩
  rcases vLeft with ⟨⟨⟩⟩
  dsimp at hr hh ⊢
  subst hr
  simp only [eqToHom_refl, Category.comp_id] at hh
  subst hh
  rfl

/-- Lift a composable chain after choosing one object in a vertex fiber.  The
groupoid inverse transports the chosen arrow back to the zeroth vertex, after
which the whole chain lifts functorially. -/
noncomputable def nerveCoverLiftChain (x : K)
    {n : ℕ} (s : ComposableArrows K n)
    (i : Fin (n + 1)) (e : Under x)
    (he : e.right = s.obj i) :
    ComposableArrows (Under x) n := by
  let fi : s.obj 0 ⟶ s.obj i :=
    s.map (homOfLE (Fin.zero_le i))
  let e' : Under x :=
    Under.mk (e.hom ≫ eqToHom he ≫ Groupoid.inv fi)
  let obj : Fin (n + 1) → Under x :=
    fun j => Under.mk
      (e'.hom ≫ s.map (homOfLE (Fin.zero_le j)))
  let map :
      ∀ {j k : Fin (n + 1)}, (j ⟶ k) → (obj j ⟶ obj k) :=
    fun {j k} f => Under.homMk (s.map f) (by
      dsimp [obj]
      rw [Category.assoc]
      congr 1
      rw [← s.map_comp]
      congr 1)
  exact
    { obj := obj
      map := map
      map_id := by
        intro j
        apply StructuredArrow.hom_ext
        change s.map (𝟙 j) = 𝟙 (s.obj j)
        simp
      map_comp := by
        intro j k l f g
        apply StructuredArrow.hom_ext
        change s.map (f ≫ g) = s.map f ≫ s.map g
        simp }

theorem nerveCoverLiftChain_forget (x : K)
    {n : ℕ} (s : ComposableArrows K n)
    (i : Fin (n + 1)) (e : Under x)
    (he : e.right = s.obj i) :
    (((nerveCoverFunctor x).mapComposableArrows n).obj
      (nerveCoverLiftChain x s i e he)) = s := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro j
    rfl
  · intro j hj
    simp [nerveCoverLiftChain, nerveCoverFunctor]

theorem nerveCoverLiftChain_vertex (x : K)
    {n : ℕ} (s : ComposableArrows K n)
    (i : Fin (n + 1)) (e : Under x)
    (he : e.right = s.obj i) :
    (nerveCoverLiftChain x s i e he).obj i = e := by
  rcases e with ⟨left, right, hom⟩
  rcases left with ⟨⟨⟩⟩
  dsimp at he ⊢
  subst he
  change Under.mk _ = _
  congr
  simp [Category.assoc]

/-- The lifted chain is uniquely determined by its projection and any one of
its vertices. -/
theorem nerveCoverLiftChain_unique (x : K)
    {n : ℕ} (s : ComposableArrows K n)
    (i : Fin (n + 1)) (e : Under x)
    (he : e.right = s.obj i)
    (t : ComposableArrows (Under x) n)
    (ht : (((nerveCoverFunctor x).mapComposableArrows n).obj t) = s)
    (hvertex : t.obj i = e) :
    t = nerveCoverLiftChain x s i e he := by
  subst s
  subst e
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro j
    refine underObjectExt
      (U := t.obj j)
      (V := (nerveCoverLiftChain x
        (((nerveCoverFunctor x).mapComposableArrows n).obj t)
        i (t.obj i) he).obj j)
      rfl ?_
    let a0i : t.obj 0 ⟶ t.obj i :=
      t.map (homOfLE (Fin.zero_le i))
    let a0j : t.obj 0 ⟶ t.obj j :=
      t.map (homOfLE (Fin.zero_le j))
    dsimp [nerveCoverLiftChain]
    simp only [nerveCoverFunctor, Under.forget_map,
      Category.comp_id, Category.id_comp]
    change
      (t.obj j).hom =
        ((t.obj i).hom ≫ Groupoid.inv a0i.right) ≫ a0j.right
    calc
      (t.obj j).hom =
          (t.obj 0).hom ≫ a0j.right := (Under.w a0j).symm
      _ = (((t.obj 0).hom ≫ a0i.right) ≫
          Groupoid.inv a0i.right) ≫ a0j.right := by
            conv_rhs =>
              rw [Category.assoc (t.obj 0).hom a0i.right
                (Groupoid.inv a0i.right)]
              rw [Groupoid.comp_inv, Category.comp_id]
      _ = ((t.obj i).hom ≫
          Groupoid.inv a0i.right) ≫ a0j.right := by
            rw [Under.w a0i]
  · intro j hj
    apply Under.UnderMorphism.ext
    simp [nerveCoverLiftChain, nerveCoverFunctor]

/-- Bundled unique-simplex-lifting certificate for an under-category
projection. -/
structure NerveCoverCertificate (x : K) : Type u where
  lift :
    ∀ {n : ℕ} (s : ComposableArrows K n)
      (i : Fin (n + 1)) (e : Under x),
      e.right = s.obj i → ComposableArrows (Under x) n
  project :
    ∀ {n : ℕ} (s : ComposableArrows K n)
      (i : Fin (n + 1)) (e : Under x) (he),
      (((nerveCoverFunctor x).mapComposableArrows n).obj
        (lift s i e he)) = s
  vertex :
    ∀ {n : ℕ} (s : ComposableArrows K n)
      (i : Fin (n + 1)) (e : Under x) (he),
      (lift s i e he).obj i = e
  unique :
    ∀ {n : ℕ} (s : ComposableArrows K n)
      (i : Fin (n + 1)) (e : Under x) (he)
      (t : ComposableArrows (Under x) n),
      (((nerveCoverFunctor x).mapComposableArrows n).obj t) = s →
      t.obj i = e → t = lift s i e he

/-- The categorical universal cover has unique simplex lifting from any
chosen vertex. -/
noncomputable def nerveCoverCertificate (x : K) :
    NerveCoverCertificate x where
  lift s i e he := nerveCoverLiftChain x s i e he
  project := nerveCoverLiftChain_forget x
  vertex := nerveCoverLiftChain_vertex x
  unique := nerveCoverLiftChain_unique x

/-! ## Computational-path certificate -/

/-- Path certificate for the image of the universal-cover base vertex. -/
noncomputable def nerveCoverBaseVertexPath (x : C) :
    Path (nerveCoverMap x (nerveCoverBaseVertex x)) (nerveVertex x) :=
  Path.stepChain (nerveCoverMap_baseVertex x)

/-- Coherence of the base-vertex certificate. -/
noncomputable def nerveCoverBaseVertexCoherence (x : C) :
    RwEq
      (Path.trans (nerveCoverBaseVertexPath x)
        (Path.refl (nerveVertex x)))
      (nerveCoverBaseVertexPath x) :=
  rweq_cmpA_refl_right (nerveCoverBaseVertexPath x)

end TopologicalNerve
end Path
end ComputationalPaths
