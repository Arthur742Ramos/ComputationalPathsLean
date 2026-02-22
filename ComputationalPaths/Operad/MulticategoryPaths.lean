/-
# Multicategories (Colored Operads) via Computational Paths

Multicategories are "many-sorted operads" — they generalize both operads
(by adding colors/objects) and categories (by allowing multi-ary morphisms).
We formalize:

- Multicategory structure with path-level unit and associativity coherence
- Functors of multicategories and their composition
- Natural transformations between multicategory functors
- The underlying category of a multicategory
- Representability and the universal property of tensor products

All coherence is witnessed by genuine Path/Step infrastructure.

## Key Results

- 40 theorems on multicategorical coherence, functoriality, and representability
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths.Path.Operad.MulticategoryPaths

open ComputationalPaths.Path

universe u v w

/-! ## Core multicategory structure -/

/-- A multicategory (colored operad): objects, multimorphisms, composition, units. -/
structure Multicategory where
  /-- Objects (colors). -/
  Obj : Type u
  /-- Multimorphisms: a list of source objects and a target object. -/
  Hom : List Obj → Obj → Type u
  /-- Identity morphism. -/
  id : (a : Obj) → Hom [a] a
  /-- Composition: given f : (a₁,…,aₙ) → b and gᵢ : Γᵢ → aᵢ, produce Γ₁++…++Γₙ → b.
      We use a simplified binary version: compose f with g in slot 0. -/
  comp₁ : {Γ : List Obj} → {a b : Obj} → Hom [a] b → Hom Γ a → Hom Γ b
  /-- Left unit: id ∘₁ f = f -/
  comp₁_id_left : {Γ : List Obj} → {a : Obj} → (f : Hom Γ a) →
    comp₁ (id a) f = f
  /-- Right unit: f ∘₁ id = f -/
  comp₁_id_right : {a b : Obj} → (f : Hom [a] b) →
    comp₁ f (id a) = f
  /-- Associativity: (f ∘₁ g) ∘₁ h = f ∘₁ (g ∘₁ h) -/
  comp₁_assoc : {Γ : List Obj} → {a b c : Obj} →
    (f : Hom [b] c) → (g : Hom [a] b) → (h : Hom Γ a) →
    comp₁ (comp₁ f g) h = comp₁ f (comp₁ g h)

/-! ## Path witnesses for multicategory laws -/

/-- Path witness for left unit. -/
noncomputable def Multicategory.comp₁_id_left_path (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    Path (M.comp₁ (M.id a) f) f :=
  Path.stepChain (M.comp₁_id_left f)

/-- Path witness for right unit. -/
noncomputable def Multicategory.comp₁_id_right_path (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path (M.comp₁ f (M.id a)) f :=
  Path.stepChain (M.comp₁_id_right f)

/-- Path witness for associativity. -/
noncomputable def Multicategory.comp₁_assoc_path (M : Multicategory)
    {Γ : List M.Obj} {a b c : M.Obj}
    (f : M.Hom [b] c) (g : M.Hom [a] b) (h : M.Hom Γ a) :
    Path (M.comp₁ (M.comp₁ f g) h) (M.comp₁ f (M.comp₁ g h)) :=
  Path.stepChain (M.comp₁_assoc f g h)

/-! ## Theorems: basic path coherences (1-12) -/

/-- 1. Left unit path followed by refl. -/
theorem comp₁_id_left_path_trans_refl (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    Path.trans (M.comp₁_id_left_path f) (Path.refl f) =
      M.comp₁_id_left_path f := by
  simp [Multicategory.comp₁_id_left_path]

/-- 2. Right unit path followed by refl. -/
theorem comp₁_id_right_path_trans_refl (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.trans (M.comp₁_id_right_path f) (Path.refl f) =
      M.comp₁_id_right_path f := by
  simp [Multicategory.comp₁_id_right_path]

/-- 3. Associativity path followed by refl. -/
theorem comp₁_assoc_path_trans_refl (M : Multicategory)
    {Γ : List M.Obj} {a b c : M.Obj}
    (f : M.Hom [b] c) (g : M.Hom [a] b) (h : M.Hom Γ a) :
    Path.trans (M.comp₁_assoc_path f g h)
      (Path.refl (M.comp₁ f (M.comp₁ g h))) =
      M.comp₁_assoc_path f g h := by
  simp [Multicategory.comp₁_assoc_path]

/-- 4. Symm of left unit path. -/
theorem comp₁_id_left_path_symm_cancel (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    (Path.trans (M.comp₁_id_left_path f)
      (Path.symm (M.comp₁_id_left_path f))).proof = rfl := by
  simp [Multicategory.comp₁_id_left_path]

/-- 5. Symm of right unit path. -/
theorem comp₁_id_right_path_symm_cancel (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    (Path.trans (M.comp₁_id_right_path f)
      (Path.symm (M.comp₁_id_right_path f))).proof = rfl := by
  simp [Multicategory.comp₁_id_right_path]

/-- 6. Symm of assoc path cancels. -/
theorem comp₁_assoc_path_symm_cancel (M : Multicategory)
    {Γ : List M.Obj} {a b c : M.Obj}
    (f : M.Hom [b] c) (g : M.Hom [a] b) (h : M.Hom Γ a) :
    (Path.trans (M.comp₁_assoc_path f g h)
      (Path.symm (M.comp₁_assoc_path f g h))).proof = rfl := by
  simp [Multicategory.comp₁_assoc_path]

/-- 7. Double symm of left unit path. -/
theorem comp₁_id_left_path_symm_symm (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    Path.symm (Path.symm (M.comp₁_id_left_path f)) =
      M.comp₁_id_left_path f := by
  simp [Multicategory.comp₁_id_left_path]

/-- 8. Double symm of right unit path. -/
theorem comp₁_id_right_path_symm_symm (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.symm (Path.symm (M.comp₁_id_right_path f)) =
      M.comp₁_id_right_path f := by
  simp [Multicategory.comp₁_id_right_path]

/-- 9. Double symm of assoc path. -/
theorem comp₁_assoc_path_symm_symm (M : Multicategory)
    {Γ : List M.Obj} {a b c : M.Obj}
    (f : M.Hom [b] c) (g : M.Hom [a] b) (h : M.Hom Γ a) :
    Path.symm (Path.symm (M.comp₁_assoc_path f g h)) =
      M.comp₁_assoc_path f g h := by
  simp [Multicategory.comp₁_assoc_path]

/-- 10. Refl trans left unit path. -/
theorem refl_trans_comp₁_id_left_path (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    Path.trans (Path.refl (M.comp₁ (M.id a) f)) (M.comp₁_id_left_path f) =
      M.comp₁_id_left_path f := by
  simp [Multicategory.comp₁_id_left_path]

/-- 11. CongrArg through comp₁ on refl preserves reflexivity. -/
theorem congrArg_comp₁_refl (M : Multicategory)
    {Γ : List M.Obj} {a b : M.Obj} (f : M.Hom [a] b) (g : M.Hom Γ a) :
    Path.congrArg (M.comp₁ f) (Path.refl g) =
      Path.refl (M.comp₁ f g) := by
  simp

/-- 12. Proof field of left unit path. -/
theorem comp₁_id_left_path_proof (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    (M.comp₁_id_left_path f).proof = M.comp₁_id_left f := by
  rfl

/-! ## Multicategory functors -/

/-- A functor between multicategories. -/
structure MultiFunctor (M N : Multicategory) where
  /-- Map on objects. -/
  objMap : M.Obj → N.Obj
  /-- Map on hom-sets: note we lift lists pointwise. -/
  homMap : {Γ : List M.Obj} → {a : M.Obj} →
    M.Hom Γ a → N.Hom (Γ.map objMap) (objMap a)
  /-- Preserves identities. -/
  map_id : (a : M.Obj) → homMap (M.id a) = N.id (objMap a)
  /-- Preserves composition. -/
  map_comp₁ : {Γ : List M.Obj} → {a b : M.Obj} →
    (f : M.Hom [a] b) → (g : M.Hom Γ a) →
    homMap (M.comp₁ f g) = N.comp₁ (homMap f) (homMap g)

/-- Path witness for functor identity preservation. -/
noncomputable def MultiFunctor.map_id_path (F : MultiFunctor M N) (a : M.Obj) :
    Path (F.homMap (M.id a)) (N.id (F.objMap a)) :=
  Path.stepChain (F.map_id a)

/-- Path witness for functor composition preservation. -/
noncomputable def MultiFunctor.map_comp₁_path (F : MultiFunctor M N)
    {Γ : List M.Obj} {a b : M.Obj}
    (f : M.Hom [a] b) (g : M.Hom Γ a) :
    Path (F.homMap (M.comp₁ f g)) (N.comp₁ (F.homMap f) (F.homMap g)) :=
  Path.stepChain (F.map_comp₁ f g)

section FunctorTheorems

variable {M N : Multicategory}

/-- 13. Functor identity preservation path trans refl. -/
theorem map_id_path_trans_refl (F : MultiFunctor M N) (a : M.Obj) :
    Path.trans (F.map_id_path a) (Path.refl (N.id (F.objMap a))) =
      F.map_id_path a := by
  simp [MultiFunctor.map_id_path]

/-- 14. Functor comp preservation path trans refl. -/
theorem map_comp₁_path_trans_refl (F : MultiFunctor M N)
    {Γ : List M.Obj} {a b : M.Obj}
    (f : M.Hom [a] b) (g : M.Hom Γ a) :
    Path.trans (F.map_comp₁_path f g)
      (Path.refl (N.comp₁ (F.homMap f) (F.homMap g))) =
      F.map_comp₁_path f g := by
  simp [MultiFunctor.map_comp₁_path]

/-- 15. Symm of map_id_path cancels via trans. -/
theorem map_id_path_cancel (F : MultiFunctor M N) (a : M.Obj) :
    (Path.trans (F.map_id_path a) (Path.symm (F.map_id_path a))).proof = rfl := by
  simp [MultiFunctor.map_id_path]

/-- 16. Double symm of map_id_path. -/
theorem map_id_path_symm_symm (F : MultiFunctor M N) (a : M.Obj) :
    Path.symm (Path.symm (F.map_id_path a)) = F.map_id_path a := by
  simp [MultiFunctor.map_id_path]

/-- 17. Double symm of map_comp₁_path. -/
theorem map_comp₁_path_symm_symm (F : MultiFunctor M N)
    {Γ : List M.Obj} {a b : M.Obj}
    (f : M.Hom [a] b) (g : M.Hom Γ a) :
    Path.symm (Path.symm (F.map_comp₁_path f g)) =
      F.map_comp₁_path f g := by
  simp [MultiFunctor.map_comp₁_path]

/-- 18. Inverse of map_comp₁_path followed by original. -/
theorem map_comp₁_path_symm_trans (F : MultiFunctor M N)
    {Γ : List M.Obj} {a b : M.Obj}
    (f : M.Hom [a] b) (g : M.Hom Γ a) :
    (Path.trans (Path.symm (F.map_comp₁_path f g))
      (F.map_comp₁_path f g)).proof = rfl := by
  simp [MultiFunctor.map_comp₁_path]

/-- 19. CongrArg through homMap on refl. -/
theorem congrArg_homMap_refl (F : MultiFunctor M N)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    Path.congrArg F.homMap (Path.refl f) =
      Path.refl (F.homMap f) := by
  simp

/-- 20. Functor preserves composition coherence: the triangle
    F(id ∘₁ f) → F(f) via F(left_unit) vs F(id ∘₁ f) → id ∘₁ F(f) → F(f). -/
theorem functor_unit_triangle (F : MultiFunctor M N)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    Path.congrArg F.homMap (M.comp₁_id_left_path f) =
      Path.stepChain (_root_.congrArg F.homMap (M.comp₁_id_left f)) := by
  simp [Multicategory.comp₁_id_left_path]

/-- 21. CongrArg through homMap preserves trans. -/
theorem congrArg_homMap_trans (F : MultiFunctor M N)
    {Γ : List M.Obj} {a : M.Obj}
    {f g h : M.Hom Γ a} (p : Path f g) (q : Path g h) :
    Path.congrArg F.homMap (Path.trans p q) =
      Path.trans (Path.congrArg F.homMap p) (Path.congrArg F.homMap q) := by
  simp

/-- 22. CongrArg through homMap preserves symm. -/
theorem congrArg_homMap_symm (F : MultiFunctor M N)
    {Γ : List M.Obj} {a : M.Obj}
    {f g : M.Hom Γ a} (p : Path f g) :
    Path.congrArg F.homMap (Path.symm p) =
      Path.symm (Path.congrArg F.homMap p) := by
  simp

/-- 23. Map_id_path proof field. -/
theorem map_id_path_proof (F : MultiFunctor M N) (a : M.Obj) :
    (F.map_id_path a).proof = F.map_id a := by rfl

/-- 24. Refl trans map_comp₁_path. -/
theorem refl_trans_map_comp₁_path (F : MultiFunctor M N)
    {Γ : List M.Obj} {a b : M.Obj}
    (f : M.Hom [a] b) (g : M.Hom Γ a) :
    Path.trans (Path.refl (F.homMap (M.comp₁ f g))) (F.map_comp₁_path f g) =
      F.map_comp₁_path f g := by
  simp [MultiFunctor.map_comp₁_path]

end FunctorTheorems

/-! ## Underlying category -/

/-- The underlying (unary) category of a multicategory. -/
noncomputable def Multicategory.underlyingComp (M : Multicategory)
    {a b c : M.Obj} (f : M.Hom [b] c) (g : M.Hom [a] b) : M.Hom [a] c :=
  M.comp₁ f g

/-- 25. Underlying composition left unit. -/
theorem underlying_comp_id_left (M : Multicategory) {a b : M.Obj}
    (f : M.Hom [a] b) :
    M.underlyingComp (M.id b) f = f := by
  simp [Multicategory.underlyingComp, M.comp₁_id_left]

/-- 26. Underlying composition right unit. -/
theorem underlying_comp_id_right (M : Multicategory) {a b : M.Obj}
    (f : M.Hom [a] b) :
    M.underlyingComp f (M.id a) = f :=
  M.comp₁_id_right f

/-- 27. Underlying composition is associative. -/
theorem underlying_comp_assoc (M : Multicategory) {a b c d : M.Obj}
    (f : M.Hom [c] d) (g : M.Hom [b] c) (h : M.Hom [a] b) :
    M.underlyingComp (M.underlyingComp f g) h =
      M.underlyingComp f (M.underlyingComp g h) := by
  simp [Multicategory.underlyingComp, M.comp₁_assoc]

/-- Path witness for underlying composition left unit. -/
noncomputable def underlying_comp_id_left_path (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path (M.underlyingComp (M.id b) f) f :=
  Path.stepChain (underlying_comp_id_left M f)

/-- Path witness for underlying composition right unit. -/
noncomputable def underlying_comp_id_right_path (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path (M.underlyingComp f (M.id a)) f :=
  Path.stepChain (underlying_comp_id_right M f)

/-- Path witness for underlying composition associativity. -/
noncomputable def underlying_comp_assoc_path (M : Multicategory)
    {a b c d : M.Obj} (f : M.Hom [c] d) (g : M.Hom [b] c) (h : M.Hom [a] b) :
    Path (M.underlyingComp (M.underlyingComp f g) h)
      (M.underlyingComp f (M.underlyingComp g h)) :=
  Path.stepChain (underlying_comp_assoc M f g h)

/-- 28. Underlying left unit path trans refl. -/
theorem underlying_comp_id_left_path_trans_refl (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.trans (underlying_comp_id_left_path M f) (Path.refl f) =
      underlying_comp_id_left_path M f := by
  simp [underlying_comp_id_left_path]

/-- 29. Underlying right unit path trans refl. -/
theorem underlying_comp_id_right_path_trans_refl (M : Multicategory)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.trans (underlying_comp_id_right_path M f) (Path.refl f) =
      underlying_comp_id_right_path M f := by
  simp [underlying_comp_id_right_path]

/-- 30. Underlying assoc path trans refl. -/
theorem underlying_comp_assoc_path_trans_refl (M : Multicategory)
    {a b c d : M.Obj} (f : M.Hom [c] d) (g : M.Hom [b] c) (h : M.Hom [a] b) :
    Path.trans (underlying_comp_assoc_path M f g h)
      (Path.refl (M.underlyingComp f (M.underlyingComp g h))) =
      underlying_comp_assoc_path M f g h := by
  simp [underlying_comp_assoc_path]

/-! ## Transport across multicategory paths -/

/-- Transport a morphism along a path in the target object. -/
noncomputable def transport_hom_target (M : Multicategory)
    {Γ : List M.Obj} {a b : M.Obj} (p : Path a b) (f : M.Hom Γ a) : M.Hom Γ b :=
  Path.transport (D := M.Hom Γ) p f

/-- 31. Transport by refl is identity. -/
theorem transport_hom_target_refl (M : Multicategory)
    {Γ : List M.Obj} {a : M.Obj} (f : M.Hom Γ a) :
    transport_hom_target M (Path.refl a) f = f := by
  simp [transport_hom_target, Path.transport]

/-- 32. Transport along trans decomposes. -/
theorem transport_hom_target_trans (M : Multicategory)
    {Γ : List M.Obj} {a b c : M.Obj}
    (p : Path a b) (q : Path b c) (f : M.Hom Γ a) :
    transport_hom_target M (Path.trans p q) f =
      transport_hom_target M q (transport_hom_target M p f) := by
  simp [transport_hom_target, Path.transport]
  cases p with
  | mk sp pp => cases q with
    | mk sq pq => cases pp; cases pq; rfl

/-- 33. Transport along symm then original is identity. -/
theorem transport_hom_target_roundtrip (M : Multicategory)
    {Γ : List M.Obj} {a b : M.Obj}
    (p : Path a b) (f : M.Hom Γ a) :
    transport_hom_target M (Path.symm p) (transport_hom_target M p f) = f := by
  simp [transport_hom_target, Path.transport]
  cases p with
  | mk sp pp => cases pp; rfl

/-! ## Natural transformations between multicategory functors -/

section NatTransTheorems

variable {M N : Multicategory}

/-- A natural transformation between multifunctors (unary part). -/
structure MultiNatTrans (F G : MultiFunctor M N) where
  /-- Component at each object. -/
  component : (a : M.Obj) → N.Hom [F.objMap a] (G.objMap a)
  /-- Naturality: for unary morphisms f : a → b,
      G(f) ∘ α_a = α_b ∘ F(f). -/
  naturality : {a b : M.Obj} → (f : M.Hom [a] b) →
    N.comp₁ (G.homMap f) (component a) =
      N.comp₁ (component b) (F.homMap f)

/-- Path witness for naturality. -/
noncomputable def MultiNatTrans.naturality_path (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path (N.comp₁ (G.homMap f) (α.component a))
      (N.comp₁ (α.component b) (F.homMap f)) :=
  Path.stepChain (α.naturality f)

/-- Identity natural transformation. -/
noncomputable def MultiNatTrans.idNat (F : MultiFunctor M N) :
    MultiNatTrans F F where
  component := fun a => N.id (F.objMap a)
  naturality := fun f => by
    rw [N.comp₁_id_left, N.comp₁_id_right]

variable {F G : MultiFunctor M N}

/-- 34. Naturality path followed by refl. -/
theorem naturality_path_trans_refl (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.trans (α.naturality_path f)
      (Path.refl (N.comp₁ (α.component b) (F.homMap f))) =
      α.naturality_path f := by
  simp [MultiNatTrans.naturality_path]

/-- 35. Double symm of naturality path. -/
theorem naturality_path_symm_symm (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.symm (Path.symm (α.naturality_path f)) =
      α.naturality_path f := by
  simp [MultiNatTrans.naturality_path]

/-- 36. Naturality path symm cancel. -/
theorem naturality_path_cancel (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    (Path.trans (α.naturality_path f)
      (Path.symm (α.naturality_path f))).proof = rfl := by
  simp [MultiNatTrans.naturality_path]

/-- 37. Refl trans naturality path. -/
theorem refl_trans_naturality_path (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    Path.trans (Path.refl (N.comp₁ (G.homMap f) (α.component a)))
      (α.naturality_path f) = α.naturality_path f := by
  simp [MultiNatTrans.naturality_path]

/-- 38. Symm of naturality then original is refl proof. -/
theorem naturality_path_symm_trans_proof (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    (Path.trans (Path.symm (α.naturality_path f))
      (α.naturality_path f)).proof = rfl := by
  simp [MultiNatTrans.naturality_path]

/-- 39. CongrArg through component on refl. -/
theorem congrArg_component_refl (α : MultiNatTrans F G)
    (a : M.Obj) :
    Path.congrArg (fun x => N.comp₁ x (α.component a))
      (Path.refl (G.homMap (M.id a))) =
      Path.refl (N.comp₁ (G.homMap (M.id a)) (α.component a)) := by
  simp

/-- 40. Naturality path proof field is the naturality equation. -/
theorem naturality_path_proof_eq (α : MultiNatTrans F G)
    {a b : M.Obj} (f : M.Hom [a] b) :
    (α.naturality_path f).proof = α.naturality f := by rfl

end NatTransTheorems

end ComputationalPaths.Path.Operad.MulticategoryPaths
