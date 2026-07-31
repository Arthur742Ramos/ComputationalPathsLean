/-
# Universal categorical cover of a realized groupoid nerve

For an object `x` in a groupoid `C`, the under-category `Under x` is the
categorical universal cover of `C`: it has the initial object `𝟙 x`, and the
forgetful functor records the endpoint of an arrow out of `x`.

This module constructs the induced map on Mathlib geometric realizations,
proves that its total space is contractible, and builds quotient-saturated
open-star trivializations proving that the realized discrete Grothendieck
fibration is a Mathlib covering map.
-/

import ComputationalPaths.Path.Homotopy.TopologicalSimplexStar
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Topology.Covering

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

/-- Simplex-category-indexed form of `nerveCoverLiftChain`. -/
noncomputable def nerveCoverLiftSimplex (x : K)
    {n : SimplexCategory}
    (s : (CategoryTheory.nerve K).obj (op n))
    (i : ToType n) (e : Under x)
    (he : e.right = s.obj i) :
    (CategoryTheory.nerve (Under x)).obj (op n) := by
  induction n using SimplexCategory.rec with
  | _ n => exact nerveCoverLiftChain x s i e he

theorem nerveCoverLiftSimplex_forget (x : K)
    {n : SimplexCategory}
    (s : (CategoryTheory.nerve K).obj (op n))
    (i : ToType n) (e : Under x)
    (he : e.right = s.obj i) :
    (nerveCoverSSetMap x).app (op n)
        (nerveCoverLiftSimplex x s i e he) = s := by
  induction n using SimplexCategory.rec with
  | _ n => exact nerveCoverLiftChain_forget x s i e he

theorem nerveCoverLiftSimplex_vertex (x : K)
    {n : SimplexCategory}
    (s : (CategoryTheory.nerve K).obj (op n))
    (i : ToType n) (e : Under x)
    (he : e.right = s.obj i) :
    (nerveCoverLiftSimplex x s i e he).obj i = e := by
  induction n using SimplexCategory.rec with
  | _ n => exact nerveCoverLiftChain_vertex x s i e he

theorem nerveCoverLiftSimplex_unique (x : K)
    {n : SimplexCategory}
    (s : (CategoryTheory.nerve K).obj (op n))
    (i : ToType n) (e : Under x)
    (he : e.right = s.obj i)
    (t : (CategoryTheory.nerve (Under x)).obj (op n))
    (ht : (nerveCoverSSetMap x).app (op n) t = s)
    (hvertex : t.obj i = e) :
    t = nerveCoverLiftSimplex x s i e he := by
  induction n using SimplexCategory.rec with
  | _ n => exact nerveCoverLiftChain_unique x s i e he t ht hvertex

theorem nerveCoverLiftSimplex_eq_of_project_eq_vertex_eq (x : K)
    {n : SimplexCategory}
    (s₁ s₂ : (CategoryTheory.nerve (Under x)).obj (op n))
    (hproject :
      (nerveCoverSSetMap x).app (op n) s₁ =
        (nerveCoverSSetMap x).app (op n) s₂)
    (i : ToType n) (hvertex : s₁.obj i = s₂.obj i) :
    s₁ = s₂ := by
  let t := (nerveCoverSSetMap x).app (op n) s₁
  let e := s₁.obj i
  have he : e.right = t.obj i := rfl
  have h₁ :=
    nerveCoverLiftSimplex_unique x t i e he s₁ rfl rfl
  have h₂ :=
    nerveCoverLiftSimplex_unique x t i e he s₂
      (hproject ▸ rfl) hvertex.symm
  exact h₁.trans h₂.symm

/-! ## Core-face stars and their lifted sheets -/

noncomputable def coreFaceIndex
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t) :
    Fin (h.dim + 1) :=
  Classical.choose (h.collapse_surjective (0 : Fin (k + 1)))

theorem coreFace_vertex_eq_at
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (j : Fin (h.dim + 1)) :
    t.obj (h.face.toOrderHom j) =
      c.obj (h.collapse.toOrderHom j) := by
  have hv := _root_.congrArg
    (fun s : (CategoryTheory.nerve K) _⦋h.dim⦌ => s.obj j)
    h.face_eq
  exact hv

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

noncomputable instance nerveCoreFiberTopologicalSpace (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌) :
    TopologicalSpace (NerveCoreFiber x c) :=
  ⊥

instance nerveCoreFiberDiscreteTopology (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌) :
    DiscreteTopology (NerveCoreFiber x c) :=
  ⟨rfl⟩

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

/-- Two lifted chains with the same projection and one common vertex are
equal. -/
theorem nerveCoverLiftChain_eq_of_project_eq_vertex_eq (x : K)
    {n : ℕ} (s₁ s₂ : ComposableArrows (Under x) n)
    (hproject :
      (((nerveCoverFunctor x).mapComposableArrows n).obj s₁) =
        (((nerveCoverFunctor x).mapComposableArrows n).obj s₂))
    (i : Fin (n + 1)) (hvertex : s₁.obj i = s₂.obj i) :
    s₁ = s₂ := by
  let t :=
    ((nerveCoverFunctor x).mapComposableArrows n).obj s₁
  let e := s₁.obj i
  have he : e.right = t.obj i := rfl
  have h₁ :=
    nerveCoverLiftChain_unique x t i e he s₁ rfl rfl
  have h₂ :=
    nerveCoverLiftChain_unique x t i e he s₂
      (hproject ▸ rfl) hvertex.symm
  exact h₁.trans h₂.symm

theorem liftCoreSimplex_forget (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (e : NerveCoreFiber x c) :
    (((nerveCoverFunctor x).mapComposableArrows k).obj
      (liftCoreSimplex x c e)) = c :=
  nerveCoverLiftChain_forget x c 0 e.1 e.2

theorem liftCoreSimplex_vertex (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (e : NerveCoreFiber x c) :
    (liftCoreSimplex x c e).obj 0 = e.1 :=
  nerveCoverLiftChain_vertex x c 0 e.1 e.2

/-- A lift of a nondegenerate simplex is nondegenerate. -/
theorem liftCoreSimplex_nonDegenerate (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    liftCoreSimplex x c e ∈
      (CategoryTheory.nerve (Under x)).nonDegenerate k := by
  rw [SSet.mem_nonDegenerate_iff_notMem_degenerate] at hc ⊢
  intro hdeg
  apply hc
  rw [SSet.mem_degenerate_iff] at hdeg ⊢
  obtain ⟨m, hm, f, hf, s, hs⟩ := hdeg
  refine ⟨m, hm, f, hf, ?_⟩
  refine ⟨(((nerveCoverFunctor x).mapComposableArrows m).obj s), ?_⟩
  calc
    (CategoryTheory.nerve K).map f.op
          (((nerveCoverFunctor x).mapComposableArrows m).obj s) =
        (((nerveCoverFunctor x).mapComposableArrows k).obj
          ((CategoryTheory.nerve (Under x)).map f.op s)) :=
      (nerveCover_project_map x f s).symm
    _ =
        (((nerveCoverFunctor x).mapComposableArrows k).obj
          (liftCoreSimplex x c e)) := by
      rw [hs]
    _ = c := liftCoreSimplex_forget x c e

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

/-- Project a core face whose core is a chosen lift of `c`. -/
noncomputable def projectLiftedCoreFace (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {s : (CategoryTheory.nerve (Under x)) _⦋n⦌}
    (e : NerveCoreFiber x c)
    (H : SimplexCoreFace (CategoryTheory.nerve (Under x))
      (liftCoreSimplex x c e) s) :
    SimplexCoreFace (CategoryTheory.nerve K) c
      (((nerveCoverFunctor x).mapComposableArrows n).obj s) where
  dim := H.dim
  face := H.face
  face_injective := H.face_injective
  collapse := H.collapse
  collapse_surjective := H.collapse_surjective
  face_eq := by
    calc
      (CategoryTheory.nerve K).map H.face.op
          (((nerveCoverFunctor x).mapComposableArrows n).obj s) =
        (((nerveCoverFunctor x).mapComposableArrows H.dim).obj
          ((CategoryTheory.nerve (Under x)).map H.face.op s)) :=
        (nerveCover_project_map x H.face s).symm
      _ =
        (((nerveCoverFunctor x).mapComposableArrows H.dim).obj
          ((CategoryTheory.nerve (Under x)).map H.collapse.op
            (liftCoreSimplex x c e))) := by
        rw [H.face_eq]
      _ =
        (CategoryTheory.nerve K).map H.collapse.op
          (((nerveCoverFunctor x).mapComposableArrows k).obj
            (liftCoreSimplex x c e)) :=
        nerveCover_project_map x H.collapse (liftCoreSimplex x c e)
      _ = (CategoryTheory.nerve K).map H.collapse.op c := by
        rw [liftCoreSimplex_forget]

theorem liftCoreFace_starSet_iff (x : K)
    {k n : ℕ} {c : (CategoryTheory.nerve K) _⦋k⦌}
    {t : (CategoryTheory.nerve K) _⦋n⦌}
    (h : SimplexCoreFace (CategoryTheory.nerve K) c t)
    (e : NerveCoreFiber x c) (p : ⦋n⦌.toTopObj) :
    p ∈ (liftCoreFace x h e).starSet ↔ p ∈ h.starSet :=
  Iff.rfl

/-! ## Global descended sheets -/

/-- The quotient-saturated lifted sheet indexed by a lift of the core
simplex's zeroth vertex. -/
noncomputable def nerveCoreSheet (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    Set (SSet.toTop.obj (CategoryTheory.nerve (Under x))) :=
  SimplexCoreFace.realizationStar (CategoryTheory.nerve (Under x))
    (liftCoreSimplex x c e)
    (liftCoreSimplex_nonDegenerate x c hc e)

theorem isOpen_nerveCoreSheet (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    IsOpen (nerveCoreSheet x c hc e) :=
  SimplexCoreFace.isOpen_realizationStar _ _ _

theorem liftCoreSimplex_injective (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌) :
    Function.Injective (liftCoreSimplex x c) := by
  intro e₁ e₂ h
  apply Subtype.ext
  have hv := _root_.congrArg
    (fun s : ComposableArrows (Under x) k => s.obj 0) h
  change
    (liftCoreSimplex x c e₁).obj 0 =
      (liftCoreSimplex x c e₂).obj 0 at hv
  rw [liftCoreSimplex_vertex x c e₁,
    liftCoreSimplex_vertex x c e₂] at hv
  exact hv

/-- Different core-fiber labels give disjoint global sheets. -/
theorem disjoint_nerveCoreSheet (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    {e₁ e₂ : NerveCoreFiber x c} (hne : e₁ ≠ e₂) :
    Disjoint (nerveCoreSheet x c hc e₁)
      (nerveCoreSheet x c hc e₂) := by
  exact SimplexCoreFace.disjoint_realizationStar
    (CategoryTheory.nerve (Under x))
    (liftCoreSimplex_nonDegenerate x c hc e₁)
    (liftCoreSimplex_nonDegenerate x c hc e₂)
    (fun h => hne (liftCoreSimplex_injective x c h))

theorem pairwiseDisjoint_nerveCoreSheet (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    Set.PairwiseDisjoint Set.univ (nerveCoreSheet x c hc) := by
  intro e₁ _ e₂ _ hne
  exact disjoint_nerveCoreSheet x c hc hne

/-- Every lifted sheet maps into its base realization star. -/
theorem nerveCoreSheet_mapsTo (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    Set.MapsTo (nerveCoverMap x)
      (nerveCoreSheet x c hc e)
      (SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc) := by
  intro z hz
  obtain ⟨n, s, p, rfl⟩ :=
    realization_point_representation
      (CategoryTheory.nerve (Under x)) z
  induction n using SimplexCategory.rec with
  | _ n =>
      rw [nerveCoreSheet,
        SimplexCoreFace.realizeSimplex_mem_realizationStar_iff] at hz
      rw [nerveCoverMap, map_realizeSimplex]
      rw [SimplexCoreFace.realizeSimplex_mem_realizationStar_iff]
      change p.down ∈ SimplexCoreFace.simplexStar
        (CategoryTheory.nerve K) c
        (((nerveCoverFunctor x).mapComposableArrows n).obj s)
      change p.down ∈ SimplexCoreFace.simplexStar
        (CategoryTheory.nerve (Under x))
        (liftCoreSimplex x c e) s at hz
      rw [SimplexCoreFace.simplexStar, Set.mem_iUnion] at hz ⊢
      obtain ⟨H, hH⟩ := hz
      exact ⟨projectLiftedCoreFace x e H, hH⟩

/-- Over one fixed simplex coordinate, a sheet contains at most one lift. -/
theorem eq_of_mem_nerveCoreSheet_simplex (x : K)
    {k n : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c)
    (s₁ s₂ : (CategoryTheory.nerve (Under x)) _⦋n⦌)
    (hproject :
      (((nerveCoverFunctor x).mapComposableArrows n).obj s₁) =
        (((nerveCoverFunctor x).mapComposableArrows n).obj s₂))
    (p : ⦋n⦌.toTopObj)
    (h₁ : p ∈ SimplexCoreFace.simplexStar
      (CategoryTheory.nerve (Under x))
      (liftCoreSimplex x c e) s₁)
    (h₂ : p ∈ SimplexCoreFace.simplexStar
      (CategoryTheory.nerve (Under x))
      (liftCoreSimplex x c e) s₂) :
    s₁ = s₂ := by
  rw [SimplexCoreFace.simplexStar, Set.mem_iUnion] at h₁ h₂
  obtain ⟨H₁, hp₁⟩ := h₁
  obtain ⟨H₂, hp₂⟩ := h₂
  let B₁ := projectLiftedCoreFace x e H₁
  let B₂raw := projectLiftedCoreFace x e H₂
  let B₂ : SimplexCoreFace (CategoryTheory.nerve K) c
      (((nerveCoverFunctor x).mapComposableArrows n).obj s₁) :=
    { dim := H₂.dim
      face := H₂.face
      face_injective := H₂.face_injective
      collapse := H₂.collapse
      collapse_surjective := H₂.collapse_surjective
      face_eq := by
        rw [hproject]
        exact B₂raw.face_eq }
  have hpB₁ : p ∈ B₁.naturalStarSet := by
    exact hp₁
  have hpB₂ : p ∈ B₂.naturalStarSet := by
    exact hp₂
  obtain ⟨_, a, b, hab', ha', hb'⟩ :=
    SimplexCoreFace.eq_and_exists_commonZero_of_mem_naturalStarSet
      (CategoryTheory.nerve K) hc hc
      B₁ B₂ p hpB₁ hpB₂
  have hab :
      H₁.face.toOrderHom a = H₂.face.toOrderHom b := by
    exact hab'
  have ha : H₁.collapse.toOrderHom a = 0 := by
    simpa [B₁] using ha'
  have hb : H₂.collapse.toOrderHom b = 0 := by
    exact hb'
  let i : Fin (n + 1) := H₁.face.toOrderHom a
  have hv₁ :
      s₁.obj i = e.1 := by
    change s₁.obj (H₁.face.toOrderHom a) = e.1
    have hface :=
      _root_.congrArg
        (fun q :
          (CategoryTheory.nerve (Under x)) _⦋H₁.dim⦌ =>
            q.obj a) H₁.face_eq
    calc
      s₁.obj (H₁.face.toOrderHom a) =
          (liftCoreSimplex x c e).obj
            (H₁.collapse.toOrderHom a) :=
        hface
      _ = (liftCoreSimplex x c e).obj 0 := by rw [ha]
      _ = e.1 := liftCoreSimplex_vertex x c e
  have hv₂ :
      s₂.obj i = e.1 := by
    change s₂.obj (H₁.face.toOrderHom a) = e.1
    rw [hab]
    have hface :=
      _root_.congrArg
        (fun q :
          (CategoryTheory.nerve (Under x)) _⦋H₂.dim⦌ =>
            q.obj b) H₂.face_eq
    calc
      s₂.obj (H₂.face.toOrderHom b) =
          (liftCoreSimplex x c e).obj
            (H₂.collapse.toOrderHom b) :=
        hface
      _ = (liftCoreSimplex x c e).obj 0 := by rw [hb]
      _ = e.1 := liftCoreSimplex_vertex x c e
  exact nerveCoverLiftChain_eq_of_project_eq_vertex_eq
    x s₁ s₂ hproject i (hv₁.trans hv₂.symm)

theorem eq_of_mem_nerveCoreSheet_simplexObj (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c)
    {n : SimplexCategory}
    (s₁ s₂ : (CategoryTheory.nerve (Under x)).obj (op n))
    (hproject :
      (nerveCoverSSetMap x).app (op n) s₁ =
        (nerveCoverSSetMap x).app (op n) s₂)
    (p : SimplexCategory.toTop.{u}.obj n)
    (h₁ : p ∈ SimplexCoreFace.simplexStarObj
      (CategoryTheory.nerve (Under x))
      (liftCoreSimplex x c e) n s₁)
    (h₂ : p ∈ SimplexCoreFace.simplexStarObj
      (CategoryTheory.nerve (Under x))
      (liftCoreSimplex x c e) n s₂) :
    s₁ = s₂ := by
  induction n using SimplexCategory.rec with
  | _ n =>
      exact eq_of_mem_nerveCoreSheet_simplex
        x c hc e s₁ s₂ hproject p.down h₁ h₂

/-- Each lifted sheet maps onto the entire base star. -/
theorem nerveCoreSheet_surjOn (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    Set.SurjOn (nerveCoverMap x)
      (nerveCoreSheet x c hc e)
      (SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc) := by
  intro z hz
  obtain ⟨n, t, p, rfl⟩ :=
    realization_point_representation (CategoryTheory.nerve K) z
  induction n using SimplexCategory.rec with
  | _ n =>
      rw [SimplexCoreFace.realizeSimplex_mem_realizationStar_iff] at hz
      change p.down ∈ SimplexCoreFace.simplexStar
        (CategoryTheory.nerve K) c t at hz
      rw [SimplexCoreFace.simplexStar, Set.mem_iUnion] at hz
      obtain ⟨h, hp⟩ := hz
      refine ⟨realizeSimplex (liftSimplexAtCoreFace x h e) p, ?_, ?_⟩
      · rw [nerveCoreSheet,
          SimplexCoreFace.realizeSimplex_mem_realizationStar_iff]
        change p.down ∈ SimplexCoreFace.simplexStar
          (CategoryTheory.nerve (Under x))
          (liftCoreSimplex x c e) (liftSimplexAtCoreFace x h e)
        rw [SimplexCoreFace.simplexStar, Set.mem_iUnion]
        exact ⟨liftCoreFace x h e, hp⟩
      · rw [nerveCoverMap, map_realizeSimplex]
        change
          realizeSimplex
              (((nerveCoverFunctor x).mapComposableArrows n).obj
                (liftSimplexAtCoreFace x h e)) p =
            realizeSimplex t p
        rw [show
          (((nerveCoverFunctor x).mapComposableArrows n).obj
            (liftSimplexAtCoreFace x h e)) = t by
          exact nerveCoverLiftChain_forget _ _ _ _ _]

/-! ## Descent of sheet representatives -/

/-- A lift, in one realization chart, of a base atlas point that lies in a
fixed global sheet. -/
structure NerveCoreSheetRepresentative (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c)
    (a : RealizationAtlas (CategoryTheory.nerve K)) where
  simplex :
    (CategoryTheory.nerve (Under x)).obj (op a.1.left)
  project :
    (nerveCoverSSetMap x).app (op a.1.left) simplex =
      SSet.yonedaEquiv a.1.hom
  mem_sheet :
    realizeSimplex simplex a.2 ∈ nerveCoreSheet x c hc e

namespace NerveCoreSheetRepresentative

noncomputable def realized
    {x : K} {k : ℕ}
    {c : (CategoryTheory.nerve K) _⦋k⦌}
    {hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k}
    {e : NerveCoreFiber x c}
    {a : RealizationAtlas (CategoryTheory.nerve K)}
    (r : NerveCoreSheetRepresentative x c hc e a) :
    SSet.toTop.obj (CategoryTheory.nerve (Under x)) :=
  realizeSimplex r.simplex a.2

/-- Lift one generating realization identification in its forward
direction. -/
theorem forward
    {x : K} {k : ℕ}
    {c : (CategoryTheory.nerve K) _⦋k⦌}
    {hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k}
    {e : NerveCoreFiber x c}
    {a b : RealizationAtlas (CategoryTheory.nerve K)}
    (hab :
      (RealizationTypeDiagram
        (CategoryTheory.nerve K)).ColimitTypeRel a b)
    (r : NerveCoreSheetRepresentative x c hc e a) :
    ∃ r' : NerveCoreSheetRepresentative x c hc e b,
      r'.realized = r.realized := by
  rcases a with ⟨a, p⟩
  rcases b with ⟨b, q⟩
  obtain ⟨f, hq⟩ := hab
  let ta := SSet.yonedaEquiv a.hom
  let tb := SSet.yonedaEquiv b.hom
  have hta :
      ta = (CategoryTheory.nerve K).map f.left.op tb :=
    realizationIndex_simplex_naturality f
  let i : ToType b.left := f.left.toOrderHom (0 : ToType a.left)
  have he :
      (r.simplex.obj (0 : ToType a.left)).right = tb.obj i := by
    have hv := _root_.congrArg
      (fun s => s.obj (0 : ToType a.left)) r.project
    change (r.simplex.obj (0 : ToType a.left)).right =
      ta.obj 0 at hv
    have htav := _root_.congrArg
      (fun s => s.obj (0 : ToType a.left)) hta
    change ta.obj 0 = tb.obj i at htav
    exact hv.trans htav
  let s :=
    nerveCoverLiftSimplex x tb i
      (r.simplex.obj (0 : ToType a.left)) he
  have hsproject :
      (nerveCoverSSetMap x).app (op b.left) s = tb :=
    nerveCoverLiftSimplex_forget _ _ _ _ _
  have hrestrict :
      (CategoryTheory.nerve (Under x)).map f.left.op s =
        r.simplex := by
    apply nerveCoverLiftSimplex_eq_of_project_eq_vertex_eq x
    · have hnat := congrFun
        ((nerveCoverSSetMap x).naturality f.left.op) s
      calc
        (nerveCoverSSetMap x).app (op a.left)
            ((CategoryTheory.nerve (Under x)).map f.left.op s) =
            (CategoryTheory.nerve K).map f.left.op
              ((nerveCoverSSetMap x).app (op b.left) s) := hnat
        _ = (CategoryTheory.nerve K).map f.left.op tb := by
          rw [hsproject]
        _ = ta := hta.symm
        _ = (nerveCoverSSetMap x).app (op a.left)
              r.simplex := r.project.symm
    · change s.obj i = r.simplex.obj 0
      exact nerveCoverLiftSimplex_vertex _ _ _ _ _
  have hq' :
      q = SimplexCategory.toTop.map f.left p := hq
  have hnat :
      realizeSimplex s (SimplexCategory.toTop.map f.left p) =
        realizeSimplex
          ((CategoryTheory.nerve (Under x)).map f.left.op s) p := by
    change
      (SimplexCategory.toTop.map f.left ≫ realizeSimplexHom s) p =
        realizeSimplexHom
          ((CategoryTheory.nerve (Under x)).map f.left.op s) p
    rw [realizeSimplexHom_naturality]
  have hpoint :
      realizeSimplex s q = realizeSimplex r.simplex p := by
    rw [hq', hnat, hrestrict]
  exact
    ⟨{ simplex := s
       project := hsproject
       mem_sheet := hpoint ▸ r.mem_sheet },
     hpoint⟩

/-- Lift one generating realization identification in its reverse
direction. -/
theorem backward
    {x : K} {k : ℕ}
    {c : (CategoryTheory.nerve K) _⦋k⦌}
    {hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k}
    {e : NerveCoreFiber x c}
    {a b : RealizationAtlas (CategoryTheory.nerve K)}
    (hab :
      (RealizationTypeDiagram
        (CategoryTheory.nerve K)).ColimitTypeRel a b)
    (r : NerveCoreSheetRepresentative x c hc e b) :
    ∃ r' : NerveCoreSheetRepresentative x c hc e a,
      r'.realized = r.realized := by
  rcases a with ⟨a, p⟩
  rcases b with ⟨b, q⟩
  obtain ⟨f, hq⟩ := hab
  let ta := SSet.yonedaEquiv a.hom
  let tb := SSet.yonedaEquiv b.hom
  have hta :
      ta = (CategoryTheory.nerve K).map f.left.op tb :=
    realizationIndex_simplex_naturality f
  let s :=
    (CategoryTheory.nerve (Under x)).map f.left.op r.simplex
  have hsproject :
      (nerveCoverSSetMap x).app (op a.left) s = ta := by
    have hnat := congrFun
      ((nerveCoverSSetMap x).naturality f.left.op) r.simplex
    calc
      (nerveCoverSSetMap x).app (op a.left) s =
          (CategoryTheory.nerve K).map f.left.op
            ((nerveCoverSSetMap x).app (op b.left) r.simplex) :=
        hnat
      _ = (CategoryTheory.nerve K).map f.left.op tb := by
        rw [r.project]
      _ = ta := hta.symm
  have hq' :
      q = SimplexCategory.toTop.map f.left p := hq
  have hnat :
      realizeSimplex r.simplex
          (SimplexCategory.toTop.map f.left p) =
        realizeSimplex s p := by
    change
      (SimplexCategory.toTop.map f.left ≫
        realizeSimplexHom r.simplex) p =
        realizeSimplexHom s p
    rw [realizeSimplexHom_naturality]
  have hpoint :
      realizeSimplex s p = realizeSimplex r.simplex q := by
    calc
      realizeSimplex s p =
          realizeSimplex r.simplex
            (SimplexCategory.toTop.map f.left p) := hnat.symm
      _ = realizeSimplex r.simplex q :=
        _root_.congrArg (realizeSimplex r.simplex) hq'.symm
  exact
    ⟨{ simplex := s
       project := hsproject
       mem_sheet := hpoint ▸ r.mem_sheet },
     hpoint⟩

/-- Sheet representatives descend across the full equivalence relation
generating geometric realization. -/
theorem transport
    {x : K} {k : ℕ}
    {c : (CategoryTheory.nerve K) _⦋k⦌}
    {hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k}
    {e : NerveCoreFiber x c}
    {a b : RealizationAtlas (CategoryTheory.nerve K)}
    (h : Relation.EqvGen
      (RealizationTypeDiagram
        (CategoryTheory.nerve K)).ColimitTypeRel a b) :
    (∀ r : NerveCoreSheetRepresentative x c hc e a,
        ∃ r' : NerveCoreSheetRepresentative x c hc e b,
          r'.realized = r.realized) ∧
      (∀ r : NerveCoreSheetRepresentative x c hc e b,
        ∃ r' : NerveCoreSheetRepresentative x c hc e a,
          r'.realized = r.realized) := by
  induction h with
  | rel a b hab =>
      exact ⟨fun r => forward hab r, fun r => backward hab r⟩
  | refl a =>
      exact ⟨fun r => ⟨r, rfl⟩, fun r => ⟨r, rfl⟩⟩
  | symm a b hab ih =>
      exact ⟨ih.2, ih.1⟩
  | trans a b d hab hbd ihab ihbd =>
      constructor
      · intro r
        obtain ⟨r', hr'⟩ := ihab.1 r
        obtain ⟨r'', hr''⟩ := ihbd.1 r'
        exact ⟨r'', hr''.trans hr'⟩
      · intro r
        obtain ⟨r', hr'⟩ := ihbd.2 r
        obtain ⟨r'', hr''⟩ := ihab.2 r'
        exact ⟨r'', hr''.trans hr'⟩

end NerveCoreSheetRepresentative

/-- The realized covering projection is injective on each descended sheet. -/
theorem nerveCoreSheet_injOn (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    Set.InjOn (nerveCoverMap x) (nerveCoreSheet x c hc e) := by
  intro z₁ hz₁ z₂ hz₂ hmap
  let q₁ := realizationPointRepresentation
    (CategoryTheory.nerve (Under x)) z₁
  let q₂ := realizationPointRepresentation
    (CategoryTheory.nerve (Under x)) z₂
  let t₁ :=
    (nerveCoverSSetMap x).app (op q₁.n) q₁.simplex
  let t₂ :=
    (nerveCoverSSetMap x).app (op q₂.n) q₂.simplex
  let a₁ : RealizationAtlas (CategoryTheory.nerve K) :=
    ⟨realizationIndexOfSimplex t₁, q₁.point⟩
  let a₂ : RealizationAtlas (CategoryTheory.nerve K) :=
    ⟨realizationIndexOfSimplex t₂, q₂.point⟩
  let r₁ : NerveCoreSheetRepresentative x c hc e a₁ :=
    { simplex := q₁.simplex
      project := by
        change t₁ =
          SSet.yonedaEquiv (SSet.yonedaEquiv.symm t₁)
        exact (SSet.yonedaEquiv.apply_symm_apply t₁).symm
      mem_sheet := by
        change realizeSimplex q₁.simplex q₁.point ∈
          nerveCoreSheet x c hc e
        rw [q₁.realize_eq]
        exact hz₁ }
  let r₂ : NerveCoreSheetRepresentative x c hc e a₂ :=
    { simplex := q₂.simplex
      project := by
        change t₂ =
          SSet.yonedaEquiv (SSet.yonedaEquiv.symm t₂)
        exact (SSet.yonedaEquiv.apply_symm_apply t₂).symm
      mem_sheet := by
        change realizeSimplex q₂.simplex q₂.point ∈
          nerveCoreSheet x c hc e
        rw [q₂.realize_eq]
        exact hz₂ }
  have ha₁ :
      realizationAtlas (CategoryTheory.nerve K) a₁ =
        nerveCoverMap x z₁ := by
    calc
      realizationAtlas (CategoryTheory.nerve K) a₁ =
          realizeSimplex t₁ q₁.point := by
        exact realizationAtlas_indexOfSimplex t₁ q₁.point
      _ = nerveCoverMap x
          (realizeSimplex q₁.simplex q₁.point) := by
        rw [nerveCoverMap, map_realizeSimplex]
      _ = nerveCoverMap x z₁ :=
        _root_.congrArg (nerveCoverMap x) q₁.realize_eq
  have ha₂ :
      realizationAtlas (CategoryTheory.nerve K) a₂ =
        nerveCoverMap x z₂ := by
    calc
      realizationAtlas (CategoryTheory.nerve K) a₂ =
          realizeSimplex t₂ q₂.point := by
        exact realizationAtlas_indexOfSimplex t₂ q₂.point
      _ = nerveCoverMap x
          (realizeSimplex q₂.simplex q₂.point) := by
        rw [nerveCoverMap, map_realizeSimplex]
      _ = nerveCoverMap x z₂ :=
        _root_.congrArg (nerveCoverMap x) q₂.realize_eq
  have hrel :
      Relation.EqvGen
        (RealizationTypeDiagram
          (CategoryTheory.nerve K)).ColimitTypeRel a₁ a₂ :=
    realizationAtlas_eqvGen (ha₁.trans (hmap.trans ha₂.symm))
  obtain ⟨r₁', hr₁'⟩ :=
    (NerveCoreSheetRepresentative.transport
      (c := c) (hc := hc) (e := e) hrel).1 r₁
  have hm₁ := r₁'.mem_sheet
  have hm₂ := r₂.mem_sheet
  rw [nerveCoreSheet,
    SimplexCoreFace.realizeSimplex_mem_realizationStar_iff] at hm₁ hm₂
  have hs : r₁'.simplex = r₂.simplex := by
    apply eq_of_mem_nerveCoreSheet_simplexObj
      x c hc e r₁'.simplex r₂.simplex
        (r₁'.project.trans r₂.project.symm) a₂.2 hm₁ hm₂
  calc
    z₁ = r₁.realized := q₁.realize_eq.symm
    _ = r₁'.realized := hr₁'.symm
    _ = r₂.realized := by
      change realizeSimplex r₁'.simplex a₂.2 =
        realizeSimplex r₂.simplex a₂.2
      rw [hs]
    _ = z₂ := q₂.realize_eq

/-- Images of open subsets contained in one sheet are open.  The proof
descends the coordinatewise identity maps through the realization relation. -/
theorem isOpen_image_of_subset_nerveCoreSheet (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c)
    (U : Set (SSet.toTop.obj
      (CategoryTheory.nerve (Under x))))
    (hU : IsOpen U) (hUS : U ⊆ nerveCoreSheet x c hc e) :
    IsOpen (nerveCoverMap x '' U) := by
  rw [← (realizationAtlas_isQuotientMap
    (CategoryTheory.nerve K)).isOpen_preimage]
  rw [isOpen_sigma_iff]
  intro j
  let t := SSet.yonedaEquiv j.hom
  have hset :
      Sigma.mk j ⁻¹'
          (realizationAtlas (CategoryTheory.nerve K) ⁻¹'
            (nerveCoverMap x '' U)) =
        ⋃ s : (CategoryTheory.nerve (Under x)).obj (op j.left),
          ⋃ _hs : (nerveCoverSSetMap x).app (op j.left) s = t,
            realizeSimplex s ⁻¹' U := by
    ext p
    constructor
    · intro hp
      change realizationAtlas (CategoryTheory.nerve K) ⟨j, p⟩ ∈
        nerveCoverMap x '' U at hp
      obtain ⟨z, hzU, hfz⟩ := hp
      have hzS := hUS hzU
      let q := realizationPointRepresentation
        (CategoryTheory.nerve (Under x)) z
      let tq :=
        (nerveCoverSSetMap x).app (op q.n) q.simplex
      let a : RealizationAtlas (CategoryTheory.nerve K) :=
        ⟨realizationIndexOfSimplex tq, q.point⟩
      let r : NerveCoreSheetRepresentative x c hc e a :=
        { simplex := q.simplex
          project := by
            change tq =
              SSet.yonedaEquiv (SSet.yonedaEquiv.symm tq)
            exact (SSet.yonedaEquiv.apply_symm_apply tq).symm
          mem_sheet := by
            change realizeSimplex q.simplex q.point ∈
              nerveCoreSheet x c hc e
            rw [q.realize_eq]
            exact hzS }
      have ha :
          realizationAtlas (CategoryTheory.nerve K) a =
            nerveCoverMap x z := by
        calc
          realizationAtlas (CategoryTheory.nerve K) a =
              realizeSimplex tq q.point :=
            realizationAtlas_indexOfSimplex tq q.point
          _ = nerveCoverMap x
              (realizeSimplex q.simplex q.point) := by
            rw [nerveCoverMap, map_realizeSimplex]
          _ = nerveCoverMap x z :=
            _root_.congrArg (nerveCoverMap x) q.realize_eq
      have hj :
          realizationAtlas (CategoryTheory.nerve K) ⟨j, p⟩ =
            nerveCoverMap x z := hfz.symm
      have hrel :
          Relation.EqvGen
            (RealizationTypeDiagram
              (CategoryTheory.nerve K)).ColimitTypeRel a ⟨j, p⟩ :=
        realizationAtlas_eqvGen (ha.trans hj.symm)
      obtain ⟨r', hr'⟩ :=
        (NerveCoreSheetRepresentative.transport
          (c := c) (hc := hc) (e := e) hrel).1 r
      rw [Set.mem_iUnion]
      refine ⟨r'.simplex, ?_⟩
      rw [Set.mem_iUnion]
      refine ⟨r'.project, ?_⟩
      change realizeSimplex r'.simplex p ∈ U
      have hrz : r'.realized = z :=
        hr'.trans q.realize_eq
      change realizeSimplex r'.simplex p = z at hrz
      rw [hrz]
      exact hzU
    · intro hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨s, hp⟩ := hp
      rw [Set.mem_iUnion] at hp
      obtain ⟨hs, hsU⟩ := hp
      change realizeSimplex s p ∈ U at hsU
      change realizationAtlas (CategoryTheory.nerve K) ⟨j, p⟩ ∈
        nerveCoverMap x '' U
      refine ⟨realizeSimplex s p, hsU, ?_⟩
      calc
        nerveCoverMap x (realizeSimplex s p) =
            realizeSimplex
              ((nerveCoverSSetMap x).app (op j.left) s) p := by
          rw [nerveCoverMap, map_realizeSimplex]
        _ = realizeSimplex t p :=
          _root_.congrArg (fun q => realizeSimplex q p) hs
        _ = realizationAtlas (CategoryTheory.nerve K) ⟨j, p⟩ := by
          exact (realizationAtlas_apply j p).symm
  rw [hset]
  apply isOpen_iUnion
  intro s
  apply isOpen_iUnion
  intro hs
  exact hU.preimage (realizeSimplex s).continuous

/-- Restriction of the realized projection to one global sheet. -/
noncomputable def nerveCoreSheetMap (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    nerveCoreSheet x c hc e →
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc :=
  fun z => ⟨nerveCoverMap x z.1,
    nerveCoreSheet_mapsTo x c hc e z.2⟩

theorem continuous_nerveCoreSheetMap (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    Continuous (nerveCoreSheetMap x c hc e) :=
  Continuous.subtype_mk
    ((continuous_nerveCoverMap x).comp continuous_subtype_val) _

theorem bijective_nerveCoreSheetMap (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    Function.Bijective (nerveCoreSheetMap x c hc e) := by
  constructor
  · intro z₁ z₂ h
    apply Subtype.ext
    apply nerveCoreSheet_injOn x c hc e z₁.2 z₂.2
    exact _root_.congrArg Subtype.val h
  · intro z
    obtain ⟨y, hy, hfy⟩ :=
      nerveCoreSheet_surjOn x c hc e z.2
    exact ⟨⟨y, hy⟩, Subtype.ext hfy⟩

/-- The set-level equivalence underlying a sheet chart. -/
noncomputable def nerveCoreSheetEquiv (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    nerveCoreSheet x c hc e ≃
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc :=
  Equiv.ofBijective (nerveCoreSheetMap x c hc e)
    (bijective_nerveCoreSheetMap x c hc e)

theorem isOpenMap_nerveCoreSheetMap (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    IsOpenMap (nerveCoreSheetMap x c hc e) := by
  intro V hV
  let U : Set (SSet.toTop.obj
      (CategoryTheory.nerve (Under x))) :=
    Subtype.val '' V
  have hU : IsOpen U :=
    (isOpen_nerveCoreSheet x c hc e).isOpenMap_subtype_val V hV
  have hUS : U ⊆ nerveCoreSheet x c hc e := by
    rintro _ ⟨z, _, rfl⟩
    exact z.2
  have hImage :=
    isOpen_image_of_subset_nerveCoreSheet x c hc e U hU hUS
  have hpre := hImage.preimage
    (continuous_subtype_val :
      Continuous
        (fun z :
          SimplexCoreFace.realizationStar
            (CategoryTheory.nerve K) c hc => z.1))
  convert hpre using 1
  ext z
  simp only [Set.mem_image, Set.mem_preimage, U,
    nerveCoreSheetMap]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨y.1, ⟨y, hy, rfl⟩, ?_⟩
    exact _root_.congrArg Subtype.val h
  · rintro ⟨y, ⟨z', hz', hzy⟩, hy⟩
    subst y
    refine ⟨z', hz', ?_⟩
    apply Subtype.ext
    exact hy

/-- Each descended lifted sheet is homeomorphic to the descended base star. -/
noncomputable def nerveCoreSheetHomeomorph (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (e : NerveCoreFiber x c) :
    nerveCoreSheet x c hc e ≃ₜ
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc :=
  Equiv.toHomeomorphOfContinuousOpen
    (nerveCoreSheetEquiv x c hc e)
    (continuous_nerveCoreSheetMap x c hc e)
    (isOpenMap_nerveCoreSheetMap x c hc e)

/-- The inverse image of a descended base star is exactly the union of its
lifted descended sheets. -/
theorem preimage_realizationStar_eq_iUnion_nerveCoreSheet (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    nerveCoverMap x ⁻¹'
        SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) c hc =
      ⋃ e : NerveCoreFiber x c, nerveCoreSheet x c hc e := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, s, p, rfl⟩ :=
      realization_point_representation
        (CategoryTheory.nerve (Under x)) z
    induction n using SimplexCategory.rec with
    | _ n =>
        change nerveCoverMap x (realizeSimplex s p) ∈
          SimplexCoreFace.realizationStar
            (CategoryTheory.nerve K) c hc at hz
        rw [nerveCoverMap, map_realizeSimplex,
          SimplexCoreFace.realizeSimplex_mem_realizationStar_iff] at hz
        change p.down ∈ SimplexCoreFace.simplexStar
          (CategoryTheory.nerve K) c
          (((nerveCoverFunctor x).mapComposableArrows n).obj s) at hz
        rw [SimplexCoreFace.simplexStar, Set.mem_iUnion] at hz
        obtain ⟨h, hp⟩ := hz
        let i : Fin (n + 1) :=
          h.face.toOrderHom (coreFaceIndex h)
        have he :
            (s.obj i).right = c.obj 0 := by
          simpa [i] using coreFace_vertex_eq h
        let e : NerveCoreFiber x c := ⟨s.obj i, he⟩
        have hs : s = liftSimplexAtCoreFace x h e := by
          apply nerveCoverLiftChain_unique x
            (((nerveCoverFunctor x).mapComposableArrows n).obj s)
            i e.1
            (e.2.trans (coreFace_vertex_eq h).symm)
          · rfl
          · rfl
        rw [Set.mem_iUnion]
        refine ⟨e, ?_⟩
        rw [nerveCoreSheet,
          SimplexCoreFace.realizeSimplex_mem_realizationStar_iff]
        change p.down ∈ SimplexCoreFace.simplexStar
          (CategoryTheory.nerve (Under x))
          (liftCoreSimplex x c e) s
        rw [hs, SimplexCoreFace.simplexStar, Set.mem_iUnion]
        exact ⟨liftCoreFace x h e, hp⟩
  · intro hz
    rw [Set.mem_iUnion] at hz
    obtain ⟨e, he⟩ := hz
    exact nerveCoreSheet_mapsTo x c hc e he

/-! ## Even covering trivializations -/

/-- Every point over a base star belongs to one of its lifted sheets. -/
theorem exists_nerveCoreSheet_of_mem_preimage (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (z : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc) :
    ∃ e : NerveCoreFiber x c,
      z.1 ∈ nerveCoreSheet x c hc e := by
  have hz :
      z.1 ∈ ⋃ e : NerveCoreFiber x c,
        nerveCoreSheet x c hc e := by
    rw [← preimage_realizationStar_eq_iUnion_nerveCoreSheet x c hc]
    exact z.2
  exact Set.mem_iUnion.mp hz

/-- The unique sheet label of a point over a base star. -/
noncomputable def nerveCoreSheetLabel (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (z : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc) :
    NerveCoreFiber x c :=
  Classical.choose (exists_nerveCoreSheet_of_mem_preimage x c hc z)

theorem nerveCoreSheetLabel_mem (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (z : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc) :
    z.1 ∈ nerveCoreSheet x c hc
      (nerveCoreSheetLabel x c hc z) := by
  exact Classical.choose_spec
    (exists_nerveCoreSheet_of_mem_preimage x c hc z)

theorem nerveCoreSheetLabel_eq_of_mem (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (z : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc)
    (e : NerveCoreFiber x c)
    (hz : z.1 ∈ nerveCoreSheet x c hc e) :
    nerveCoreSheetLabel x c hc z = e := by
  by_contra hne
  have hd := disjoint_nerveCoreSheet x c hc hne
  exact Set.disjoint_left.mp hd
    (nerveCoreSheetLabel_mem x c hc z) hz

theorem continuous_nerveCoreSheetLabel (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    Continuous (nerveCoreSheetLabel x c hc) := by
  rw [continuous_def]
  intro V hV
  have hpre :
      nerveCoreSheetLabel x c hc ⁻¹' V =
        ⋃ e : V,
          Subtype.val ⁻¹' nerveCoreSheet x c hc e.1 := by
    ext z
    constructor
    · intro hz
      rw [Set.mem_iUnion]
      refine ⟨⟨nerveCoreSheetLabel x c hc z, hz⟩, ?_⟩
      exact nerveCoreSheetLabel_mem x c hc z
    · intro hz
      rw [Set.mem_iUnion] at hz
      obtain ⟨e, he⟩ := hz
      change z.1 ∈ nerveCoreSheet x c hc e.1 at he
      change nerveCoreSheetLabel x c hc z ∈ V
      rw [nerveCoreSheetLabel_eq_of_mem x c hc z e.1 he]
      exact e.2
  rw [hpre]
  apply isOpen_iUnion
  intro e
  exact (isOpen_nerveCoreSheet x c hc e.1).preimage
    continuous_subtype_val

/-- Product chart associated to the partition of the star preimage into
global sheets. -/
noncomputable def nerveCoreStarTrivializationEquiv (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    (nerveCoverMap x ⁻¹'
        SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) c hc) ≃
      (SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) c hc) ×
        NerveCoreFiber x c where
  toFun z :=
    (⟨nerveCoverMap x z.1, z.2⟩,
      nerveCoreSheetLabel x c hc z)
  invFun ze := by
    let w :=
      (nerveCoreSheetHomeomorph x c hc ze.2).symm ze.1
    refine ⟨w.1, ?_⟩
    exact nerveCoreSheet_mapsTo x c hc ze.2 w.2
  left_inv := by
    intro z
    apply Subtype.ext
    let e := nerveCoreSheetLabel x c hc z
    let w :=
      (nerveCoreSheetHomeomorph x c hc e).symm
        ⟨nerveCoverMap x z.1, z.2⟩
    have hwmap :
        nerveCoverMap x w.1 = nerveCoverMap x z.1 := by
      have h :=
        (nerveCoreSheetHomeomorph x c hc e).apply_symm_apply
          ⟨nerveCoverMap x z.1, z.2⟩
      exact _root_.congrArg Subtype.val h
    exact nerveCoreSheet_injOn x c hc e w.2
      (nerveCoreSheetLabel_mem x c hc z) hwmap
  right_inv := by
    intro ze
    let w :=
      (nerveCoreSheetHomeomorph x c hc ze.2).symm ze.1
    apply Prod.ext
    · have h :=
        (nerveCoreSheetHomeomorph x c hc ze.2).apply_symm_apply ze.1
      exact h
    · apply nerveCoreSheetLabel_eq_of_mem x c hc
        ⟨w.1, nerveCoreSheet_mapsTo x c hc ze.2 w.2⟩
        ze.2
      exact w.2

theorem continuous_nerveCoreStarTrivializationEquiv (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    Continuous (nerveCoreStarTrivializationEquiv x c hc) := by
  apply Continuous.prodMk
  · exact Continuous.subtype_mk
      ((continuous_nerveCoverMap x).comp continuous_subtype_val) _
  · exact continuous_nerveCoreSheetLabel x c hc

theorem continuous_nerveCoreStarTrivializationEquiv_symm (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    Continuous (nerveCoreStarTrivializationEquiv x c hc).symm := by
  apply Continuous.subtype_mk
  apply continuous_prod_of_discrete_right.mpr
  intro e
  exact continuous_subtype_val.comp
    (nerveCoreSheetHomeomorph x c hc e).symm.continuous

/-- The exact global trivialization over one descended realization star. -/
noncomputable def nerveCoreStarTrivialization (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k) :
    (nerveCoverMap x ⁻¹'
        SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) c hc) ≃ₜ
      (SimplexCoreFace.realizationStar
          (CategoryTheory.nerve K) c hc) ×
        NerveCoreFiber x c where
  toEquiv := nerveCoreStarTrivializationEquiv x c hc
  continuous_toFun :=
    continuous_nerveCoreStarTrivializationEquiv x c hc
  continuous_invFun :=
    continuous_nerveCoreStarTrivializationEquiv_symm x c hc

theorem nerveCoreStarTrivialization_fst (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    (z : nerveCoverMap x ⁻¹'
      SimplexCoreFace.realizationStar
        (CategoryTheory.nerve K) c hc) :
    ((nerveCoreStarTrivialization x c hc z).1).1 =
      nerveCoverMap x z.1 :=
  rfl

/-- Every point of a descended star is evenly covered, with the core fiber as
the discrete sheet type. -/
theorem isEvenlyCovered_nerveCoverMap_of_mem_realizationStar (x : K)
    {k : ℕ} (c : (CategoryTheory.nerve K) _⦋k⦌)
    (hc : c ∈ (CategoryTheory.nerve K).nonDegenerate k)
    {z : SSet.toTop.obj (CategoryTheory.nerve K)}
    (hz : z ∈ SimplexCoreFace.realizationStar
      (CategoryTheory.nerve K) c hc) :
    IsEvenlyCovered (nerveCoverMap x) z (NerveCoreFiber x c) := by
  refine ⟨inferInstance,
    SimplexCoreFace.realizationStar
      (CategoryTheory.nerve K) c hc,
    hz,
    SimplexCoreFace.isOpen_realizationStar
      (CategoryTheory.nerve K) c hc,
    ?_,
    nerveCoreStarTrivialization x c hc,
    ?_⟩
  · exact (SimplexCoreFace.isOpen_realizationStar
      (CategoryTheory.nerve K) c hc).preimage
      (continuous_nerveCoverMap x)
  · intro y
    exact nerveCoreStarTrivialization_fst x c hc y

/-- The realized under-category projection of every groupoid is a Mathlib
covering map. -/
theorem isCoveringMap_nerveCoverMap (x : K) :
    IsCoveringMap (nerveCoverMap x) := by
  intro z
  obtain ⟨k, c, hc, hz⟩ :=
    SimplexCoreFace.exists_mem_realizationStar
      (CategoryTheory.nerve K) z
  exact
    (isEvenlyCovered_nerveCoverMap_of_mem_realizationStar
      x c hc hz).to_isEvenlyCovered_preimage

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
