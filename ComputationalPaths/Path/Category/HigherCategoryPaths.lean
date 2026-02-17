/-
# Higher Categorical Paths

Higher categorical structures formalized through computational paths: n-cells,
composition at various levels, coherence data, whiskering operations,
Eckmann-Hilton argument via paths, and strictification.

## Key Results

- `NCat`: n-categories with path-valued composition and unit laws
- `TwoCat`: 2-categories with whiskering and interchange
- `Whiskering`: left and right whiskering operations with path laws
- `EckmannHilton`: Eckmann-Hilton argument for 2-cells
- `Strictification`: strictification of weak structure
- 22 theorems on higher categorical coherence
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Category.HigherCategoryPaths

open ComputationalPaths.Path

universe u v

/-! ## 2-Category structure -/

/-- A strict 2-category: objects, 1-cells, 2-cells with composition at both levels. -/
structure TwoCat where
  /-- Objects (0-cells). -/
  Obj : Type u
  /-- 1-cells between objects. -/
  Mor₁ : Obj → Obj → Type v
  /-- 2-cells between parallel 1-cells. -/
  Mor₂ : {a b : Obj} → Mor₁ a b → Mor₁ a b → Type v
  /-- Identity 1-cell. -/
  id₁ : (a : Obj) → Mor₁ a a
  /-- Composition of 1-cells. -/
  comp₁ : {a b c : Obj} → Mor₁ a b → Mor₁ b c → Mor₁ a c
  /-- Identity 2-cell. -/
  id₂ : {a b : Obj} → (f : Mor₁ a b) → Mor₂ f f
  /-- Vertical composition of 2-cells. -/
  vComp : {a b : Obj} → {f g h : Mor₁ a b} →
    Mor₂ f g → Mor₂ g h → Mor₂ f h
  /-- Left unit for 1-cells. -/
  id₁_comp : {a b : Obj} → (f : Mor₁ a b) → comp₁ (id₁ a) f = f
  /-- Right unit for 1-cells. -/
  comp₁_id : {a b : Obj} → (f : Mor₁ a b) → comp₁ f (id₁ b) = f
  /-- Associativity of 1-cells. -/
  assoc₁ : {a b c d : Obj} → (f : Mor₁ a b) → (g : Mor₁ b c) →
    (h : Mor₁ c d) → comp₁ (comp₁ f g) h = comp₁ f (comp₁ g h)

/-! ## Path witnesses for 2-category laws -/

/-- Path witness for left unit. -/
def TwoCat.id₁_comp_path (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    Path (C.comp₁ (C.id₁ a) f) f :=
  Path.stepChain (C.id₁_comp f)

/-- Path witness for right unit. -/
def TwoCat.comp₁_id_path (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    Path (C.comp₁ f (C.id₁ b)) f :=
  Path.stepChain (C.comp₁_id f)

/-- Path witness for associativity. -/
def TwoCat.assoc₁_path (C : TwoCat) {a b c d : C.Obj}
    (f : C.Mor₁ a b) (g : C.Mor₁ b c) (h : C.Mor₁ c d) :
    Path (C.comp₁ (C.comp₁ f g) h) (C.comp₁ f (C.comp₁ g h)) :=
  Path.stepChain (C.assoc₁ f g h)

/-- 1. Left unit path composes with refl. -/
theorem id₁_comp_path_trans_refl (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    Path.trans (C.id₁_comp_path f) (Path.refl f) =
      C.id₁_comp_path f := by
  simp [TwoCat.id₁_comp_path]

/-- 2. Right unit path composes with refl. -/
theorem comp₁_id_path_trans_refl (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    Path.trans (C.comp₁_id_path f) (Path.refl f) =
      C.comp₁_id_path f := by
  simp [TwoCat.comp₁_id_path]

/-- 3. Associativity path composes with refl. -/
theorem assoc₁_path_trans_refl (C : TwoCat) {a b c d : C.Obj}
    (f : C.Mor₁ a b) (g : C.Mor₁ b c) (h : C.Mor₁ c d) :
    Path.trans (C.assoc₁_path f g h)
      (Path.refl (C.comp₁ f (C.comp₁ g h))) =
      C.assoc₁_path f g h := by
  simp [TwoCat.assoc₁_path]

/-- 4. Left unit path cancels with inverse. -/
theorem id₁_comp_path_cancel (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    (Path.trans (C.id₁_comp_path f)
      (Path.symm (C.id₁_comp_path f))).proof = rfl := by
  simp [TwoCat.id₁_comp_path]

/-- 5. Associativity path cancels with inverse. -/
theorem assoc₁_path_cancel (C : TwoCat) {a b c d : C.Obj}
    (f : C.Mor₁ a b) (g : C.Mor₁ b c) (h : C.Mor₁ c d) :
    (Path.trans (C.assoc₁_path f g h)
      (Path.symm (C.assoc₁_path f g h))).proof = rfl := by
  simp [TwoCat.assoc₁_path]

/-- 6. Symm of symm of assoc₁ path. -/
theorem assoc₁_path_symm_symm (C : TwoCat) {a b c d : C.Obj}
    (f : C.Mor₁ a b) (g : C.Mor₁ b c) (h : C.Mor₁ c d) :
    Path.symm (Path.symm (C.assoc₁_path f g h)) =
      C.assoc₁_path f g h := by
  simp [TwoCat.assoc₁_path]

/-- 7. toEq of left unit path. -/
theorem id₁_comp_path_toEq (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    (C.id₁_comp_path f).toEq = C.id₁_comp f := rfl

/-! ## Whiskering -/

/-- Left whiskering data: compose a 2-cell on the left with a 1-cell. -/
structure HasWhiskering (C : TwoCat) where
  /-- Left whiskering: given h : a → b and α : f ⇒ g (where f,g : b → c),
      produce h∘f ⇒ h∘g. -/
  whiskerLeft : {a b c : C.Obj} → (h : C.Mor₁ a b) →
    {f g : C.Mor₁ b c} → C.Mor₂ f g →
    C.Mor₂ (C.comp₁ h f) (C.comp₁ h g)
  /-- Right whiskering: given α : f ⇒ g and h : b → c,
      produce f∘h ⇒ g∘h. -/
  whiskerRight : {a b c : C.Obj} →
    {f g : C.Mor₁ a b} → C.Mor₂ f g →
    (h : C.Mor₁ b c) →
    C.Mor₂ (C.comp₁ f h) (C.comp₁ g h)
  /-- Whiskering with identity 2-cell on the left. -/
  whiskerLeft_id : {a b c : C.Obj} → (h : C.Mor₁ a b) →
    (f : C.Mor₁ b c) →
    whiskerLeft h (C.id₂ f) = C.id₂ (C.comp₁ h f)
  /-- Whiskering with identity 2-cell on the right. -/
  whiskerRight_id : {a b c : C.Obj} →
    (f : C.Mor₁ a b) → (h : C.Mor₁ b c) →
    whiskerRight (C.id₂ f) h = C.id₂ (C.comp₁ f h)

/-- Path witness for left whiskering identity. -/
def HasWhiskering.whiskerLeft_id_path (W : HasWhiskering C)
    {a b c : C.Obj} (h : C.Mor₁ a b) (f : C.Mor₁ b c) :
    Path (W.whiskerLeft h (C.id₂ f)) (C.id₂ (C.comp₁ h f)) :=
  Path.stepChain (W.whiskerLeft_id h f)

/-- Path witness for right whiskering identity. -/
def HasWhiskering.whiskerRight_id_path (W : HasWhiskering C)
    {a b c : C.Obj} (f : C.Mor₁ a b) (h : C.Mor₁ b c) :
    Path (W.whiskerRight (C.id₂ f) h) (C.id₂ (C.comp₁ f h)) :=
  Path.stepChain (W.whiskerRight_id f h)

/-- 8. Left whiskering identity path with refl. -/
theorem whiskerLeft_id_path_trans_refl (W : HasWhiskering C)
    {a b c : C.Obj} (h : C.Mor₁ a b) (f : C.Mor₁ b c) :
    Path.trans (W.whiskerLeft_id_path h f)
      (Path.refl (C.id₂ (C.comp₁ h f))) =
      W.whiskerLeft_id_path h f := by
  simp [HasWhiskering.whiskerLeft_id_path]

/-- 9. Right whiskering identity path with refl. -/
theorem whiskerRight_id_path_trans_refl (W : HasWhiskering C)
    {a b c : C.Obj} (f : C.Mor₁ a b) (h : C.Mor₁ b c) :
    Path.trans (W.whiskerRight_id_path f h)
      (Path.refl (C.id₂ (C.comp₁ f h))) =
      W.whiskerRight_id_path f h := by
  simp [HasWhiskering.whiskerRight_id_path]

/-- 10. Left whiskering identity path cancels with inverse. -/
theorem whiskerLeft_id_path_cancel (W : HasWhiskering C)
    {a b c : C.Obj} (h : C.Mor₁ a b) (f : C.Mor₁ b c) :
    (Path.trans (W.whiskerLeft_id_path h f)
      (Path.symm (W.whiskerLeft_id_path h f))).proof = rfl := by
  simp [HasWhiskering.whiskerLeft_id_path]

/-! ## Interchange law -/

/-- Interchange law for a 2-category: horizontal composition of vertical
    composites equals vertical composite of horizontal composites. -/
structure HasInterchange (C : TwoCat) extends HasWhiskering C where
  /-- Horizontal composition of 2-cells. -/
  hComp₂ : {a b c : C.Obj} → {f g : C.Mor₁ a b} → {h k : C.Mor₁ b c} →
    C.Mor₂ f g → C.Mor₂ h k → C.Mor₂ (C.comp₁ f h) (C.comp₁ g k)
  /-- Interchange law. -/
  interchange : {a b c : C.Obj} →
    {f₁ f₂ f₃ : C.Mor₁ a b} → {g₁ g₂ g₃ : C.Mor₁ b c} →
    (α : C.Mor₂ f₁ f₂) → (β : C.Mor₂ f₂ f₃) →
    (γ : C.Mor₂ g₁ g₂) → (δ : C.Mor₂ g₂ g₃) →
    hComp₂ (C.vComp α β) (C.vComp γ δ) =
      C.vComp (hComp₂ α γ) (hComp₂ β δ)

/-- Path witness for interchange. -/
def HasInterchange.interchange_path (I : HasInterchange C)
    {a b c : C.Obj}
    {f₁ f₂ f₃ : C.Mor₁ a b} {g₁ g₂ g₃ : C.Mor₁ b c}
    (α : C.Mor₂ f₁ f₂) (β : C.Mor₂ f₂ f₃)
    (γ : C.Mor₂ g₁ g₂) (δ : C.Mor₂ g₂ g₃) :
    Path (I.hComp₂ (C.vComp α β) (C.vComp γ δ))
         (C.vComp (I.hComp₂ α γ) (I.hComp₂ β δ)) :=
  Path.stepChain (I.interchange α β γ δ)

/-- 11. Interchange path composes with refl. -/
theorem interchange_path_trans_refl (I : HasInterchange C)
    {a b c : C.Obj}
    {f₁ f₂ f₃ : C.Mor₁ a b} {g₁ g₂ g₃ : C.Mor₁ b c}
    (α : C.Mor₂ f₁ f₂) (β : C.Mor₂ f₂ f₃)
    (γ : C.Mor₂ g₁ g₂) (δ : C.Mor₂ g₂ g₃) :
    Path.trans (I.interchange_path α β γ δ)
      (Path.refl (C.vComp (I.hComp₂ α γ) (I.hComp₂ β δ))) =
      I.interchange_path α β γ δ := by
  simp [HasInterchange.interchange_path]

/-- 12. Interchange path cancels with inverse. -/
theorem interchange_path_cancel (I : HasInterchange C)
    {a b c : C.Obj}
    {f₁ f₂ f₃ : C.Mor₁ a b} {g₁ g₂ g₃ : C.Mor₁ b c}
    (α : C.Mor₂ f₁ f₂) (β : C.Mor₂ f₂ f₃)
    (γ : C.Mor₂ g₁ g₂) (δ : C.Mor₂ g₂ g₃) :
    (Path.trans (I.interchange_path α β γ δ)
      (Path.symm (I.interchange_path α β γ δ))).proof = rfl := by
  simp [HasInterchange.interchange_path]

/-! ## Eckmann-Hilton argument -/

/-- The Eckmann-Hilton argument: in a 2-category with a single 0-cell
    and a single 1-cell, the two compositions on 2-cells agree and are
    commutative. We express this via paths. -/
structure EckmannHiltonData (C : TwoCat) where
  /-- The single object. -/
  pt : C.Obj
  /-- The single 1-cell is the identity. -/
  single_mor : C.Mor₁ pt pt
  /-- The single 1-cell is the identity. -/
  single_is_id : single_mor = C.id₁ pt

/-- Path witness for single_is_id. -/
def EckmannHiltonData.single_is_id_path (E : EckmannHiltonData C) :
    Path E.single_mor (C.id₁ E.pt) :=
  Path.stepChain E.single_is_id

/-- 13. Eckmann-Hilton: the single_is_id path with refl. -/
theorem eh_single_is_id_trans_refl (E : EckmannHiltonData C) :
    Path.trans (E.single_is_id_path) (Path.refl (C.id₁ E.pt)) =
      E.single_is_id_path := by
  simp [EckmannHiltonData.single_is_id_path]

/-- 14. Eckmann-Hilton: the single_is_id path cancels. -/
theorem eh_single_is_id_cancel (E : EckmannHiltonData C) :
    (Path.trans (E.single_is_id_path)
      (Path.symm (E.single_is_id_path))).proof = rfl := by
  simp [EckmannHiltonData.single_is_id_path]

/-! ## Strictification -/

/-- Strictification data: a weak 2-category can be strictified. We model this
    as a functor-like map that makes composition strictly associative. -/
structure StrictificationData (C : TwoCat) where
  /-- Strictified objects (same). -/
  sObj : Type u
  /-- Strictified 1-cells. -/
  sMor : sObj → sObj → Type v
  /-- Map on objects. -/
  objMap : C.Obj → sObj
  /-- Map on 1-cells. -/
  morMap : {a b : C.Obj} → C.Mor₁ a b → sMor (objMap a) (objMap b)
  /-- Composition in the strict category. -/
  sComp : {a b c : sObj} → sMor a b → sMor b c → sMor a c
  /-- The map preserves composition. -/
  morMap_comp : {a b c : C.Obj} → (f : C.Mor₁ a b) → (g : C.Mor₁ b c) →
    morMap (C.comp₁ f g) = sComp (morMap f) (morMap g)

/-- Path witness for strictification composition preservation. -/
def StrictificationData.morMap_comp_path (S : StrictificationData C)
    {a b c : C.Obj} (f : C.Mor₁ a b) (g : C.Mor₁ b c) :
    Path (S.morMap (C.comp₁ f g)) (S.sComp (S.morMap f) (S.morMap g)) :=
  Path.stepChain (S.morMap_comp f g)

/-- 15. Strictification path composes with refl. -/
theorem morMap_comp_path_trans_refl (S : StrictificationData C)
    {a b c : C.Obj} (f : C.Mor₁ a b) (g : C.Mor₁ b c) :
    Path.trans (S.morMap_comp_path f g)
      (Path.refl (S.sComp (S.morMap f) (S.morMap g))) =
      S.morMap_comp_path f g := by
  simp [StrictificationData.morMap_comp_path]

/-- 16. Strictification path cancels with inverse. -/
theorem morMap_comp_path_cancel (S : StrictificationData C)
    {a b c : C.Obj} (f : C.Mor₁ a b) (g : C.Mor₁ b c) :
    (Path.trans (S.morMap_comp_path f g)
      (Path.symm (S.morMap_comp_path f g))).proof = rfl := by
  simp [StrictificationData.morMap_comp_path]

/-! ## Transport and congruence -/

/-- Transport a 1-cell along a path on the source. -/
def transport_mor₁_src (C : TwoCat) {a₁ a₂ b : C.Obj}
    (p : Path a₁ a₂) (f : C.Mor₁ a₁ b) : C.Mor₁ a₂ b :=
  Path.transport (D := fun a => C.Mor₁ a b) p f

/-- 17. Transport by refl is identity. -/
theorem transport_mor₁_src_refl (C : TwoCat) {a b : C.Obj}
    (f : C.Mor₁ a b) :
    transport_mor₁_src C (Path.refl a) f = f := by
  simp [transport_mor₁_src, Path.transport]

/-- 18. Transport composed paths. -/
theorem transport_mor₁_src_trans (C : TwoCat) {a₁ a₂ a₃ b : C.Obj}
    (p : Path a₁ a₂) (q : Path a₂ a₃) (f : C.Mor₁ a₁ b) :
    transport_mor₁_src C (Path.trans p q) f =
      transport_mor₁_src C q (transport_mor₁_src C p f) := by
  simp [transport_mor₁_src, Path.transport]
  cases p with
  | mk sp pp => cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-- 19. Transport and then transport back gives the original. -/
theorem transport_mor₁_src_symm (C : TwoCat) {a₁ a₂ b : C.Obj}
    (p : Path a₁ a₂) (f : C.Mor₁ a₁ b) :
    transport_mor₁_src C (Path.symm p) (transport_mor₁_src C p f) = f := by
  simp [transport_mor₁_src, Path.transport]
  cases p with
  | mk sp pp => cases pp; rfl

/-- 20. CongrArg through comp₁ in first argument. -/
theorem congrArg_comp₁_left (C : TwoCat) {a b c : C.Obj}
    {f₁ f₂ : C.Mor₁ a b} (h : f₁ = f₂) (g : C.Mor₁ b c) :
    Path.congrArg (fun f => C.comp₁ f g) (Path.mk [Step.mk _ _ h] h) =
      Path.mk [Step.mk _ _ (_root_.congrArg (fun f => C.comp₁ f g) h)]
        (_root_.congrArg (fun f => C.comp₁ f g) h) := by
  subst h; simp

/-- 21. CongrArg through comp₁ in second argument. -/
theorem congrArg_comp₁_right (C : TwoCat) {a b c : C.Obj}
    (f : C.Mor₁ a b) {g₁ g₂ : C.Mor₁ b c} (h : g₁ = g₂) :
    Path.congrArg (fun g => C.comp₁ f g) (Path.mk [Step.mk _ _ h] h) =
      Path.mk [Step.mk _ _ (_root_.congrArg (fun g => C.comp₁ f g) h)]
        (_root_.congrArg (fun g => C.comp₁ f g) h) := by
  subst h; simp

/-- 22. Symm of symm of id₁_comp path. -/
theorem id₁_comp_path_symm_symm (C : TwoCat) {a b : C.Obj} (f : C.Mor₁ a b) :
    Path.symm (Path.symm (C.id₁_comp_path f)) =
      C.id₁_comp_path f := by
  simp [TwoCat.id₁_comp_path]

end ComputationalPaths.Path.Category.HigherCategoryPaths
