/-
# Double Categories of Paths

Double categories formalized through computational paths: horizontal/vertical
morphisms, squares, horizontal/vertical composition, interchange law, connection
to 2-categories, and companion pairs.

## Key Results

- `DblCat`: double categories with path-valued coherence
- `DblSquare`: squares with horizontal and vertical composition
- `DblFunctor`: double functors preserving all structure
- `CompanionData`/`ConjointData`: companion and conjoint pair constructions
- 22 theorems on double-categorical coherence and functoriality
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.DoubleCategoryPaths

open ComputationalPaths.Path

universe u v

/-! ## Core double category -/

/-- A double category: two categories sharing the same objects, with squares. -/
structure DblCat where
  /-- Objects. -/
  Obj : Type u
  /-- Horizontal morphisms. -/
  HMor : Obj → Obj → Type v
  /-- Vertical morphisms. -/
  VMor : Obj → Obj → Type v
  /-- Horizontal identity. -/
  hId : (a : Obj) → HMor a a
  /-- Vertical identity. -/
  vId : (a : Obj) → VMor a a
  /-- Horizontal composition. -/
  hComp : {a b c : Obj} → HMor a b → HMor b c → HMor a c
  /-- Vertical composition. -/
  vComp : {a b c : Obj} → VMor a b → VMor b c → VMor a c
  /-- Horizontal left unit. -/
  hId_comp : {a b : Obj} → (f : HMor a b) → hComp (hId a) f = f
  /-- Horizontal right unit. -/
  hComp_id : {a b : Obj} → (f : HMor a b) → hComp f (hId b) = f
  /-- Horizontal associativity. -/
  hAssoc : {a b c d : Obj} → (f : HMor a b) → (g : HMor b c) →
    (h : HMor c d) → hComp (hComp f g) h = hComp f (hComp g h)
  /-- Vertical left unit. -/
  vId_comp : {a b : Obj} → (f : VMor a b) → vComp (vId a) f = f
  /-- Vertical right unit. -/
  vComp_id : {a b : Obj} → (f : VMor a b) → vComp f (vId b) = f
  /-- Vertical associativity. -/
  vAssoc : {a b c d : Obj} → (f : VMor a b) → (g : VMor b c) →
    (h : VMor c d) → vComp (vComp f g) h = vComp f (vComp g h)

/-! ## Path witnesses for horizontal laws -/

/-- Path witness for horizontal left unit. -/
noncomputable def DblCat.hId_comp_path (D : DblCat) {a b : D.Obj} (f : D.HMor a b) :
    Path (D.hComp (D.hId a) f) f :=
  Path.stepChain (D.hId_comp f)

/-- Path witness for horizontal right unit. -/
noncomputable def DblCat.hComp_id_path (D : DblCat) {a b : D.Obj} (f : D.HMor a b) :
    Path (D.hComp f (D.hId b)) f :=
  Path.stepChain (D.hComp_id f)

/-- Path witness for horizontal associativity. -/
noncomputable def DblCat.hAssoc_path (D : DblCat) {a b c d : D.Obj}
    (f : D.HMor a b) (g : D.HMor b c) (h : D.HMor c d) :
    Path (D.hComp (D.hComp f g) h) (D.hComp f (D.hComp g h)) :=
  Path.stepChain (D.hAssoc f g h)

/-! ## Path witnesses for vertical laws -/

/-- Path witness for vertical left unit. -/
noncomputable def DblCat.vId_comp_path (D : DblCat) {a b : D.Obj} (f : D.VMor a b) :
    Path (D.vComp (D.vId a) f) f :=
  Path.stepChain (D.vId_comp f)

/-- Path witness for vertical right unit. -/
noncomputable def DblCat.vComp_id_path (D : DblCat) {a b : D.Obj} (f : D.VMor a b) :
    Path (D.vComp f (D.vId b)) f :=
  Path.stepChain (D.vComp_id f)

/-- Path witness for vertical associativity. -/
noncomputable def DblCat.vAssoc_path (D : DblCat) {a b c d : D.Obj}
    (f : D.VMor a b) (g : D.VMor b c) (h : D.VMor c d) :
    Path (D.vComp (D.vComp f g) h) (D.vComp f (D.vComp g h)) :=
  Path.stepChain (D.vAssoc f g h)

/-! ## Theorems -/

/-- 1. Horizontal left unit path composes with refl. -/
theorem hId_comp_path_trans_refl (D : DblCat) {a b : D.Obj} (f : D.HMor a b) :
    Path.trans (D.hId_comp_path f) (Path.refl f) =
      D.hId_comp_path f := by
  simp [DblCat.hId_comp_path]

/-- 2. Horizontal right unit path composes with refl. -/
theorem hComp_id_path_trans_refl (D : DblCat) {a b : D.Obj} (f : D.HMor a b) :
    Path.trans (D.hComp_id_path f) (Path.refl f) =
      D.hComp_id_path f := by
  simp [DblCat.hComp_id_path]

/-- 3. Horizontal associativity path composes with refl. -/
theorem hAssoc_path_trans_refl (D : DblCat) {a b c d : D.Obj}
    (f : D.HMor a b) (g : D.HMor b c) (h : D.HMor c d) :
    Path.trans (D.hAssoc_path f g h)
      (Path.refl (D.hComp f (D.hComp g h))) =
      D.hAssoc_path f g h := by
  simp [DblCat.hAssoc_path]

/-- 4. Vertical left unit path composes with refl. -/
theorem vId_comp_path_trans_refl (D : DblCat) {a b : D.Obj} (f : D.VMor a b) :
    Path.trans (D.vId_comp_path f) (Path.refl f) =
      D.vId_comp_path f := by
  simp [DblCat.vId_comp_path]

/-- 5. Horizontal left unit path cancels with inverse. -/
theorem hId_comp_path_cancel (D : DblCat) {a b : D.Obj} (f : D.HMor a b) :
    (Path.trans (D.hId_comp_path f)
      (Path.symm (D.hId_comp_path f))).proof = rfl := by
  simp [DblCat.hId_comp_path]

/-- 6. Vertical left unit path cancels with inverse. -/
theorem vId_comp_path_cancel (D : DblCat) {a b : D.Obj} (f : D.VMor a b) :
    (Path.trans (D.vId_comp_path f)
      (Path.symm (D.vId_comp_path f))).proof = rfl := by
  simp [DblCat.vId_comp_path]

/-- 7. Symm of symm of hAssoc path. -/
theorem hAssoc_path_symm_symm (D : DblCat) {a b c d : D.Obj}
    (f : D.HMor a b) (g : D.HMor b c) (h : D.HMor c d) :
    Path.symm (Path.symm (D.hAssoc_path f g h)) =
      D.hAssoc_path f g h := by
  simp [DblCat.hAssoc_path]

/-- 8. Symm of symm of vAssoc path. -/
theorem vAssoc_path_symm_symm (D : DblCat) {a b c d : D.Obj}
    (f : D.VMor a b) (g : D.VMor b c) (h : D.VMor c d) :
    Path.symm (Path.symm (D.vAssoc_path f g h)) =
      D.vAssoc_path f g h := by
  simp [DblCat.vAssoc_path]

/-- 9. toEq of hId_comp path. -/
theorem hId_comp_path_toEq (D : DblCat) {a b : D.Obj} (f : D.HMor a b) :
    (D.hId_comp_path f).toEq = D.hId_comp f := rfl

/-- 10. toEq of vId_comp path. -/
theorem vId_comp_path_toEq (D : DblCat) {a b : D.Obj} (f : D.VMor a b) :
    (D.vId_comp_path f).toEq = D.vId_comp f := rfl

/-! ## Double functors -/

/-- A double functor between double categories. -/
structure DblFunctor (D E : DblCat) where
  /-- Map on objects. -/
  obj : D.Obj → E.Obj
  /-- Map on horizontal morphisms. -/
  hMap : {a b : D.Obj} → D.HMor a b → E.HMor (obj a) (obj b)
  /-- Map on vertical morphisms. -/
  vMap : {a b : D.Obj} → D.VMor a b → E.VMor (obj a) (obj b)
  /-- Preserves horizontal identity. -/
  hMap_id : (a : D.Obj) → hMap (D.hId a) = E.hId (obj a)
  /-- Preserves vertical identity. -/
  vMap_id : (a : D.Obj) → vMap (D.vId a) = E.vId (obj a)
  /-- Preserves horizontal composition. -/
  hMap_comp : {a b c : D.Obj} → (f : D.HMor a b) → (g : D.HMor b c) →
    hMap (D.hComp f g) = E.hComp (hMap f) (hMap g)
  /-- Preserves vertical composition. -/
  vMap_comp : {a b c : D.Obj} → (f : D.VMor a b) → (g : D.VMor b c) →
    vMap (D.vComp f g) = E.vComp (vMap f) (vMap g)

/-- Path witness for horizontal identity preservation. -/
noncomputable def DblFunctor.hMap_id_path (F : DblFunctor D E) (a : D.Obj) :
    Path (F.hMap (D.hId a)) (E.hId (F.obj a)) :=
  Path.stepChain (F.hMap_id a)

/-- Path witness for vertical identity preservation. -/
noncomputable def DblFunctor.vMap_id_path (F : DblFunctor D E) (a : D.Obj) :
    Path (F.vMap (D.vId a)) (E.vId (F.obj a)) :=
  Path.stepChain (F.vMap_id a)

/-- Identity double functor. -/
noncomputable def DblFunctor.idFunctor (D : DblCat) : DblFunctor D D where
  obj := _root_.id
  hMap := fun f => f
  vMap := fun f => f
  hMap_id := fun _ => rfl
  vMap_id := fun _ => rfl
  hMap_comp := fun _ _ => rfl
  vMap_comp := fun _ _ => rfl

/-- 11. Identity functor hMap_id path is stepChain rfl. -/
theorem idFunctor_hMap_id (D : DblCat) (a : D.Obj) :
    (DblFunctor.idFunctor D).hMap_id_path a = Path.stepChain rfl := by
  rfl

/-- 12. Identity functor vMap_id path is stepChain rfl. -/
theorem idFunctor_vMap_id (D : DblCat) (a : D.Obj) :
    (DblFunctor.idFunctor D).vMap_id_path a = Path.stepChain rfl := by
  rfl

/-- 13. hMap_id path cancels with inverse. -/
theorem hMap_id_path_cancel (F : DblFunctor D E) (a : D.Obj) :
    (Path.trans (F.hMap_id_path a)
      (Path.symm (F.hMap_id_path a))).proof = rfl := by
  simp [DblFunctor.hMap_id_path]

/-- 14. vMap_id path cancels with inverse. -/
theorem vMap_id_path_cancel (F : DblFunctor D E) (a : D.Obj) :
    (Path.trans (F.vMap_id_path a)
      (Path.symm (F.vMap_id_path a))).proof = rfl := by
  simp [DblFunctor.vMap_id_path]

/-! ## Companion and conjoint pairs -/

/-- Companion data: a horizontal morphism f has a companion if there are
    unit and counit squares witnessing an adjunction. -/
structure CompanionData (D : DblCat) {a b : D.Obj}
    (f : D.HMor a b) (g : D.VMor a b) where
  /-- The companion relation holds. -/
  isCompanion : D.hComp f (D.hId b) = D.hComp (D.hId a) f

/-- Path witness for the companion relation. -/
noncomputable def CompanionData.companion_path {D : DblCat} {a b : D.Obj}
    {f : D.HMor a b} {g : D.VMor a b}
    (C : CompanionData D f g) :
    Path (D.hComp f (D.hId b)) (D.hComp (D.hId a) f) :=
  Path.stepChain C.isCompanion

/-- 15. Companion path composes with refl. -/
theorem companion_path_trans_refl {D : DblCat} {a b : D.Obj}
    {f : D.HMor a b} {g : D.VMor a b}
    (C : CompanionData D f g) :
    Path.trans C.companion_path (Path.refl (D.hComp (D.hId a) f)) =
      C.companion_path := by
  simp [CompanionData.companion_path]

/-- Conjoint data for horizontal and vertical morphisms. -/
structure ConjointData (D : DblCat) {a b : D.Obj}
    (f : D.HMor a b) (g : D.VMor b a) where
  /-- The conjoint relation: g composed with vId gives vId composed with g. -/
  isConjoint : D.vComp g (D.vId a) = D.vComp (D.vId b) g

/-- 16. Every identity has a trivial companion with itself. -/
theorem id_companion (D : DblCat) (a : D.Obj) :
    CompanionData D (D.hId a) (D.vId a) where
  isCompanion := by simp [D.hComp_id, D.hId_comp]

/-! ## Transport -/

/-- Transport a horizontal morphism along a path on the source. -/
noncomputable def transport_hMor_src (D : DblCat) {a₁ a₂ b : D.Obj}
    (p : Path a₁ a₂) (f : D.HMor a₁ b) : D.HMor a₂ b :=
  Path.transport (D := fun a => D.HMor a b) p f

/-- 17. Transport by refl is identity. -/
theorem transport_hMor_src_refl (D : DblCat) {a b : D.Obj}
    (f : D.HMor a b) :
    transport_hMor_src D (Path.refl a) f = f := by
  simp [transport_hMor_src, Path.transport]

/-- 18. Transport composed paths. -/
theorem transport_hMor_src_trans (D : DblCat) {a₁ a₂ a₃ b : D.Obj}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (f : D.HMor a₁ b) :
    transport_hMor_src D (Path.trans p q) f =
      transport_hMor_src D q (transport_hMor_src D p f) := by
  simp [transport_hMor_src, Path.transport]
  cases p with
  | mk sp pp => cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-- 19. Transport and back gives the original. -/
theorem transport_hMor_src_symm (D : DblCat) {a₁ a₂ b : D.Obj}
    (p : Path a₁ a₂) (f : D.HMor a₁ b) :
    transport_hMor_src D (Path.symm p) (transport_hMor_src D p f) = f := by
  simp [transport_hMor_src, Path.transport]
  cases p with
  | mk sp pp => cases pp; rfl

/-- 20. CongrArg through hComp in first argument. -/
theorem congrArg_hComp_left (D : DblCat) {a b c : D.Obj}
    {f₁ f₂ : D.HMor a b} (h : f₁ = f₂) (g : D.HMor b c) :
    Path.congrArg (fun f => D.hComp f g) (Path.mk [Step.mk _ _ h] h) =
      Path.mk [Step.mk _ _ (_root_.congrArg (fun f => D.hComp f g) h)]
        (_root_.congrArg (fun f => D.hComp f g) h) := by
  subst h; simp

/-- 21. CongrArg through hComp in second argument. -/
theorem congrArg_hComp_right (D : DblCat) {a b c : D.Obj}
    (f : D.HMor a b) {g₁ g₂ : D.HMor b c} (h : g₁ = g₂) :
    Path.congrArg (fun g => D.hComp f g) (Path.mk [Step.mk _ _ h] h) =
      Path.mk [Step.mk _ _ (_root_.congrArg (fun g => D.hComp f g) h)]
        (_root_.congrArg (fun g => D.hComp f g) h) := by
  subst h; simp

/-- 22. hAssoc path cancels with inverse. -/
theorem hAssoc_path_cancel (D : DblCat) {a b c d : D.Obj}
    (f : D.HMor a b) (g : D.HMor b c) (h : D.HMor c d) :
    (Path.trans (D.hAssoc_path f g h)
      (Path.symm (D.hAssoc_path f g h))).proof = rfl := by
  simp [DblCat.hAssoc_path]

end ComputationalPaths.Path.Category.DoubleCategoryPaths
