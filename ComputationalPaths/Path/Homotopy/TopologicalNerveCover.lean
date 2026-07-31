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

import ComputationalPaths.Path.Homotopy.TopologicalSimplexStar
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

/-! ## Core-face stars and their lifted sheets -/

noncomputable def coreFaceIndex
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t) :
    Fin (h.dim + 1) :=
  Classical.choose (h.collapse_surjective (0 : Fin (k + 1)))

theorem coreFaceIndex_collapse
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t) :
    h.collapse.toOrderHom (coreFaceIndex h) = 0 :=
  Classical.choose_spec
    (h.collapse_surjective (0 : Fin (k + 1)))

theorem coreFace_vertex_eq
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t) :
    t.obj (h.face.toOrderHom (coreFaceIndex h)) = c.obj 0 := by
  have hv := _root_.congrArg
    (fun s : (CategoryTheory.nerve K) _⦋h.dim⦌ =>
      s.obj (coreFaceIndex h)) h.face_eq
  change
    t.obj (h.face.toOrderHom (coreFaceIndex h)) =
      c.obj (h.collapse.toOrderHom (coreFaceIndex h)) at hv
  rw [coreFaceIndex_collapse h] at hv
  exact hv

/-- Fiber used to label a sheet over a core simplex. -/
abbrev NerveCoreFiber (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌) :=
  {e : Under x // e.right = c.obj 0}

/-- Lift the core simplex from its zeroth vertex. -/
noncomputable def liftCoreSimplex (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (e : NerveCoreFiber x c) :
    ComposableArrows (Under x) k :=
  nerveCoverLiftChain x c 0 e.1 e.2

/-- Lift an ambient simplex using a selected core-face sheet. -/
noncomputable def liftSimplexAtCoreFace (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c) :
    ComposableArrows (Under x) n :=
  nerveCoverLiftChain x t
    (h.face.toOrderHom (coreFaceIndex h)) e.1
    (e.2.trans (coreFace_vertex_eq h).symm)

theorem nerveCover_project_map
    (x : K) {m n : ℕ}
    (f : ⦋m⦌ ⟶ ⦋n⦌)
    (s : ComposableArrows (Under x) n) :
    (((nerveCoverFunctor x).mapComposableArrows m).obj
      ((CategoryTheory.nerve (Under x)).map f.op s)) =
    (CategoryTheory.nerve K).map f.op
      (((nerveCoverFunctor x).mapComposableArrows n).obj s) := by
  refine ComposableArrows.ext (h := ?_) (w := ?_)
  · intro j
    rfl
  · intro j hj
    simp [nerveCoverFunctor]

/-- A base core face and a core-fiber element determine a core face in the
corresponding lifted simplex. -/
noncomputable def liftCoreFace (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c) :
    SimplexCoreFace (CategoryTheory.nerve (Under x))
      (liftCoreSimplex x c e) (liftSimplexAtCoreFace x h e) where
  dim := h.dim
  face := h.face
  face_injective := h.face_injective
  collapse := h.collapse
  collapse_surjective := h.collapse_surjective
  face_eq := by
    let lhs :=
      (CategoryTheory.nerve (Under x)).map h.face.op
        (liftSimplexAtCoreFace x h e)
    let rhs :=
      (CategoryTheory.nerve (Under x)).map h.collapse.op
        (liftCoreSimplex x c e)
    let base :=
      (CategoryTheory.nerve K).map h.face.op t
    have hlproj :
        (((nerveCoverFunctor x).mapComposableArrows h.dim).obj lhs) =
          base := by
      rw [show lhs =
        (CategoryTheory.nerve (Under x)).map h.face.op
          (liftSimplexAtCoreFace x h e) by rfl]
      rw [nerveCover_project_map]
      change
        (CategoryTheory.nerve K).map h.face.op
          (((nerveCoverFunctor x).mapComposableArrows n).obj
            (nerveCoverLiftChain x t
              (h.face.toOrderHom (coreFaceIndex h)) e.1
              (e.2.trans (coreFace_vertex_eq h).symm))) =
          base
      rw [nerveCoverLiftChain_forget]
    have hrproj :
        (((nerveCoverFunctor x).mapComposableArrows h.dim).obj rhs) =
          base := by
      rw [show rhs =
        (CategoryTheory.nerve (Under x)).map h.collapse.op
          (liftCoreSimplex x c e) by rfl]
      rw [nerveCover_project_map]
      change
        (CategoryTheory.nerve K).map h.collapse.op
          (((nerveCoverFunctor x).mapComposableArrows k).obj
            (nerveCoverLiftChain x c 0 e.1 e.2)) =
          base
      rw [nerveCoverLiftChain_forget]
      exact h.face_eq.symm
    have hlvertex :
        lhs.obj (coreFaceIndex h) = e.1 := by
      change
        (liftSimplexAtCoreFace x h e).obj
          (h.face.toOrderHom (coreFaceIndex h)) = e.1
      exact nerveCoverLiftChain_vertex _ _ _ _ _
    have hrvertex :
        rhs.obj (coreFaceIndex h) = e.1 := by
      change
        (liftCoreSimplex x c e).obj
          (h.collapse.toOrderHom (coreFaceIndex h)) = e.1
      rw [coreFaceIndex_collapse h]
      exact nerveCoverLiftChain_vertex _ _ _ _ _
    have hl :=
      nerveCoverLiftChain_unique x base (coreFaceIndex h) e.1
        (by
          have hv := _root_.congrArg
            (fun s : ComposableArrows K h.dim =>
              s.obj (coreFaceIndex h)) hlproj
          change
            (lhs.obj (coreFaceIndex h)).right =
              base.obj (coreFaceIndex h) at hv
          rw [hlvertex] at hv
          exact hv)
        lhs hlproj hlvertex
    have hr :=
      nerveCoverLiftChain_unique x base (coreFaceIndex h) e.1
        (by
          have hv := _root_.congrArg
            (fun s : ComposableArrows K h.dim =>
              s.obj (coreFaceIndex h)) hrproj
          change
            (rhs.obj (coreFaceIndex h)).right =
              base.obj (coreFaceIndex h) at hv
          rw [hrvertex] at hv
          exact hv)
        rhs hrproj hrvertex
    exact hl.trans hr.symm

theorem liftCoreFace_starSet_iff (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c) (p : ⦋n⦌.toTopObj) :
    p ∈ (liftCoreFace x h e).starSet ↔ p ∈ h.starSet :=
  Iff.rfl

/-- The open chart in a topological simplex determined by a core face. -/
abbrev CoreFaceOpen
    {X : SSet.{u}} {k n : ℕ}
    {c : X _⦋k⦌} {t : X _⦋n⦌}
    (h : SimplexCoreFace X c t) :=
  {p : SimplexCategory.toTop.{u}.obj ⦋n⦌ //
    p.down ∈ h.starSet}

/-- On every simplex chart, a chosen core-fiber element identifies the lifted
open sheet homeomorphically with the base core-face star. -/
noncomputable def coreFaceSheetHomeomorph (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c) :
    CoreFaceOpen (liftCoreFace x h e) ≃ₜ CoreFaceOpen h :=
  Homeomorph.refl _

theorem nerveCoverMap_liftSimplexAtCoreFace (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c)
    (p : SimplexCategory.toTop.{u}.obj ⦋n⦌) :
    nerveCoverMap x
        (realizeSimplex (liftSimplexAtCoreFace x h e) p) =
      realizeSimplex t p := by
  rw [nerveCoverMap]
  rw [map_realizeSimplex]
  change
    realizeSimplex
        (((nerveCoverFunctor x).mapComposableArrows n).obj
          (liftSimplexAtCoreFace x h e)) p =
      realizeSimplex t p
  have hp :
      (((nerveCoverFunctor x).mapComposableArrows n).obj
        (liftSimplexAtCoreFace x h e)) = t := by
    change
      (((nerveCoverFunctor x).mapComposableArrows n).obj
        (nerveCoverLiftChain x t
          (h.face.toOrderHom (coreFaceIndex h)) e.1
          (e.2.trans (coreFace_vertex_eq h).symm))) = t
    exact nerveCoverLiftChain_forget _ _ _ _ _
  rw [hp]

theorem coreFaceSheetHomeomorph_realize (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c)
    (p : CoreFaceOpen (liftCoreFace x h e)) :
    nerveCoverMap x
        (realizeSimplex (liftSimplexAtCoreFace x h e) p.1) =
      realizeSimplex t (coreFaceSheetHomeomorph x h e p).1 :=
  nerveCoverMap_liftSimplexAtCoreFace x h e p.1

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
