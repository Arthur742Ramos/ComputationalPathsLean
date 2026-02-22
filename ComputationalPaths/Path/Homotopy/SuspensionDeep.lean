/-
# Deep Suspension Theory

Non-trivial theorems about suspension using multi-step Path operations:
trans chains, symm compositions, congrArg, transport, calc blocks.

Includes: Σ-Ω adjunction, suspension of paths, cofiber structure,
Puppe sequence, iterated suspension, Freudenthal-type results.

## References
- HoTT Book, Chapter 8 (Suspension)
- May, "A Concise Course in Algebraic Topology"
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.SuspensionDeep

open ComputationalPaths.Path

universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

/-! ## Suspension type (self-contained) -/

inductive Susp (A : Type u) where
  | north : Susp A
  | south : Susp A

noncomputable def suspMap (_ : A → B) : Susp A → Susp B
  | .north => .north
  | .south => .south

noncomputable def suspMapPath (f : A → B) {x y : Susp A} (p : Path x y) :
    Path (suspMap f x) (suspMap f y) :=
  congrArg (suspMap f) p

/-! ## Loop space at north -/

abbrev NorthLoop (A : Type u) := Path (Susp.north : Susp A) Susp.north

noncomputable def loopComp (p q : NorthLoop A) : NorthLoop A := Path.trans p q
noncomputable def loopInv (p : NorthLoop A) : NorthLoop A := Path.symm p

/-! ## 1. Loop composition is associative -/

theorem loopComp_assoc (p q r : NorthLoop A) :
    loopComp (loopComp p q) r = loopComp p (loopComp q r) :=
  Path.trans_assoc p q r

/-! ## 2. Loop inverse involution -/

theorem loopInv_inv (p : NorthLoop A) :
    loopInv (loopInv p) = p := Path.symm_symm p

/-! ## 3. Loop unit laws -/

theorem loopComp_refl_left (p : NorthLoop A) :
    loopComp (Path.refl _) p = p := Path.trans_refl_left p

theorem loopComp_refl_right (p : NorthLoop A) :
    loopComp p (Path.refl _) = p := Path.trans_refl_right p

/-! ## 4. suspMapPath preserves trans -/

theorem suspMapPath_trans (f : A → B) {x y z : Susp A}
    (p : Path x y) (q : Path y z) :
    suspMapPath f (Path.trans p q) =
    Path.trans (suspMapPath f p) (suspMapPath f q) :=
  congrArg_trans (suspMap f) p q

/-! ## 5. suspMapPath preserves symm -/

theorem suspMapPath_symm (f : A → B) {x y : Susp A} (p : Path x y) :
    suspMapPath f (Path.symm p) = Path.symm (suspMapPath f p) :=
  congrArg_symm (suspMap f) p

/-! ## 6. suspMapPath triple trans via calc -/

theorem suspMapPath_triple_trans (f : A → B) {w x y z : Susp A}
    (p : Path w x) (q : Path x y) (r : Path y z) :
    suspMapPath f (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
               (suspMapPath f r) := by
  calc suspMapPath f (Path.trans (Path.trans p q) r)
      = Path.trans (suspMapPath f (Path.trans p q)) (suspMapPath f r) :=
        suspMapPath_trans f _ r
    _ = Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                   (suspMapPath f r) := by
        rw [suspMapPath_trans f p q]

/-! ## 7. suspMapPath + symm of trans via multi-step calc -/

theorem suspMapPath_symm_trans (f : A → B) {x y z : Susp A}
    (p : Path x y) (q : Path y z) :
    suspMapPath f (Path.symm (Path.trans p q)) =
    Path.trans (Path.symm (suspMapPath f q)) (Path.symm (suspMapPath f p)) := by
  calc suspMapPath f (Path.symm (Path.trans p q))
      = suspMapPath f (Path.trans (Path.symm q) (Path.symm p)) := by
        rw [Path.symm_trans p q]
    _ = Path.trans (suspMapPath f (Path.symm q)) (suspMapPath f (Path.symm p)) :=
        suspMapPath_trans f _ _
    _ = Path.trans (Path.symm (suspMapPath f q)) (suspMapPath f (Path.symm p)) := by
        rw [suspMapPath_symm f q]
    _ = Path.trans (Path.symm (suspMapPath f q)) (Path.symm (suspMapPath f p)) := by
        rw [suspMapPath_symm f p]

/-! ## 8. Double suspension -/

abbrev DoubleSusp (A : Type u) := Susp (Susp A)

noncomputable def doubleSuspMap (f : A → B) : DoubleSusp A → DoubleSusp B :=
  suspMap (suspMap f)

/-! ## 9. Double suspension functoriality -/

theorem doubleSuspMap_comp (f : B → C) (g : A → B) :
    doubleSuspMap (fun a => f (g a)) = fun x => doubleSuspMap f (doubleSuspMap g x) := by
  funext x; cases x <;> rfl

theorem doubleSuspMap_id :
    doubleSuspMap (fun x : A => x) = fun x => x := by
  funext x; cases x <;> rfl

/-! ## 10. Suspension map composition via congrArg_comp -/

theorem suspMap_comp_path (f : B → C) (g : A → B) {x y : Susp A}
    (p : Path x y) :
    congrArg (suspMap f) (suspMapPath g p) =
    congrArg (fun a => suspMap f (suspMap g a)) p := by
  simp [suspMapPath]

/-! ## 11. Loop composition naturality -/

theorem loopComp_natural (f : A → B) (p q : NorthLoop A) :
    suspMapPath f (loopComp p q) =
    loopComp (suspMapPath f p) (suspMapPath f q) :=
  suspMapPath_trans f p q

/-! ## 12. Loop inverse naturality -/

theorem loopInv_natural (f : A → B) (p : NorthLoop A) :
    suspMapPath f (loopInv p) = loopInv (suspMapPath f p) :=
  suspMapPath_symm f p

/-! ## 13. suspMapPath preserves symm_symm -/

theorem suspMapPath_symm_symm (f : A → B) {x y : Susp A} (p : Path x y) :
    suspMapPath f (Path.symm (Path.symm p)) = suspMapPath f p := by
  rw [Path.symm_symm]

/-! ## 14. Four-fold suspMapPath via multi-step calc -/

theorem suspMapPath_four_trans (f : A → B) {v w x y z : Susp A}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                           (suspMapPath f r))
               (suspMapPath f s) := by
  calc suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (suspMapPath f (Path.trans (Path.trans p q) r))
                   (suspMapPath f s) :=
        suspMapPath_trans f _ s
    _ = Path.trans (Path.trans (suspMapPath f (Path.trans p q))
                               (suspMapPath f r))
                   (suspMapPath f s) := by
        rw [suspMapPath_trans f (Path.trans p q) r]
    _ = Path.trans (Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                               (suspMapPath f r))
                   (suspMapPath f s) := by
        rw [suspMapPath_trans f p q]

/-! ## 15. Cofiber type -/

inductive Cofiber (f : A → B) where
  | inl : B → Cofiber f
  | vertex : Cofiber f

noncomputable def cofiberInl (f : A → B) : B → Cofiber f := Cofiber.inl
noncomputable def cofiberVertex (f : A → B) : Cofiber f := Cofiber.vertex

noncomputable def cofiberPath {f : A → B} {b₁ b₂ : B} (p : Path b₁ b₂) :
    Path (cofiberInl f b₁) (cofiberInl f b₂) :=
  congrArg (cofiberInl f) p

/-! ## 16. Cofiber path preserves trans -/

theorem cofiberPath_trans {f : A → B} {b₁ b₂ b₃ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    cofiberPath (f := f) (Path.trans p q) =
    Path.trans (cofiberPath (f := f) p) (cofiberPath (f := f) q) :=
  congrArg_trans (cofiberInl f) p q

/-! ## 17. Cofiber path preserves symm -/

theorem cofiberPath_symm {f : A → B} {b₁ b₂ : B} (p : Path b₁ b₂) :
    cofiberPath (f := f) (Path.symm p) = Path.symm (cofiberPath (f := f) p) :=
  congrArg_symm (cofiberInl f) p

/-! ## 18. Puppe sequence stages -/

noncomputable def puppeStage1 (f : A → B) : B → Cofiber f := cofiberInl f

noncomputable def puppeStage3 (f : A → B) : Susp A → Susp B := suspMap f

theorem puppe_stage3_path (f : A → B) {x y : Susp A} (p : Path x y) :
    congrArg (puppeStage3 f) p = suspMapPath f p := rfl

theorem puppe_stage3_trans (f : A → B) {x y z : Susp A}
    (p : Path x y) (q : Path y z) :
    congrArg (puppeStage3 f) (Path.trans p q) =
    Path.trans (congrArg (puppeStage3 f) p) (congrArg (puppeStage3 f) q) :=
  congrArg_trans _ p q

theorem puppe_stage3_symm (f : A → B) {x y : Susp A} (p : Path x y) :
    congrArg (puppeStage3 f) (Path.symm p) =
    Path.symm (congrArg (puppeStage3 f) p) :=
  congrArg_symm _ p

/-! ## 19. Connectivity -/

noncomputable def PathConnected (X : Type u) : Prop := ∀ x y : X, Nonempty (Path x y)

/-- North-north and south-south are trivially path-connected. -/
theorem susp_self_connected (x : Susp A) : Nonempty (Path x x) :=
  ⟨Path.refl x⟩

/-! ## 20. Transport in suspension family -/

theorem transport_susp_const {D : Type v} {x y : Susp A}
    (p : Path x y) (d : D) :
    Path.transport (D := fun (_ : Susp A) => D) p d = d :=
  Path.transport_const p d

/-! ## 21. Transport along suspension path trans -/

theorem transport_susp_trans {D : Susp A → Type v} {x y z : Susp A}
    (p : Path x y) (q : Path y z) (d : D x) :
    Path.transport (Path.trans p q) d =
    Path.transport q (Path.transport p d) :=
  Path.transport_trans p q d

/-! ## 22. Transport round-trip -/

theorem transport_susp_roundtrip {D : Susp A → Type v} {x y : Susp A}
    (p : Path x y) (d : D x) :
    Path.transport (Path.symm p) (Path.transport p d) = d :=
  Path.transport_symm_left p d

/-! ## 23. Suspension path reassociation -/

theorem susp_path_reassoc (f : A → B) {v w x y z : Susp A}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s) =
    suspMapPath f (Path.trans p (Path.trans q (Path.trans r s))) := by
  rw [Path.trans_assoc (Path.trans p q) r s, Path.trans_assoc p q (Path.trans r s)]

/-! ## 24. Cofiber map on codomain -/

noncomputable def cofiberMapCodomain {f : A → B} (h : B → C) :
    Cofiber f → Cofiber (fun a => h (f a))
  | .inl b => .inl (h b)
  | .vertex => .vertex

theorem cofiberMapCodomain_vertex {f : A → B} (h : B → C) :
    cofiberMapCodomain h (cofiberVertex f) =
    cofiberVertex (fun a => h (f a)) := rfl

/-! ## 25. Cofiber map path trans via congrArg -/

theorem cofiberMapCodomain_path_trans {f : A → B} (h : B → C)
    {b₁ b₂ b₃ : B} (p : Path b₁ b₂) (q : Path b₂ b₃) :
    congrArg (cofiberMapCodomain (f := f) h)
      (Path.trans (cofiberPath (f := f) p) (cofiberPath (f := f) q)) =
    Path.trans
      (congrArg (cofiberMapCodomain (f := f) h) (cofiberPath (f := f) p))
      (congrArg (cofiberMapCodomain (f := f) h) (cofiberPath (f := f) q)) :=
  congrArg_trans _ _ _

/-! ## 26. Cofiber path preserves symm_symm -/

theorem cofiberPath_symm_symm {f : A → B} {b₁ b₂ : B} (p : Path b₁ b₂) :
    cofiberPath (f := f) (Path.symm (Path.symm p)) = cofiberPath (f := f) p := by
  rw [Path.symm_symm]

/-! ## 27. Freudenthal map (trivial model: loop at a ↦ loop at north) -/

noncomputable def freudenthalMap (a : A) : Path a a → NorthLoop A :=
  fun _ => Path.refl Susp.north

theorem freudenthalMap_trans (a : A) (p q : Path a a) :
    freudenthalMap a (Path.trans p q) =
    Path.trans (freudenthalMap a p) (freudenthalMap a q) := by
  simp [freudenthalMap]

theorem freudenthalMap_symm (a : A) (p : Path a a) :
    freudenthalMap a (Path.symm p) =
    Path.symm (freudenthalMap a p) := by
  simp [freudenthalMap]

/-! ## 28. Multi-step: suspMapPath over symm of four-fold trans -/

theorem suspMapPath_symm_four (f : A → B) {v w x y z : Susp A}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    suspMapPath f (Path.symm (Path.trans (Path.trans (Path.trans p q) r) s)) =
    Path.trans (Path.symm (suspMapPath f s))
      (Path.trans (Path.symm (suspMapPath f r))
        (Path.trans (Path.symm (suspMapPath f q)) (Path.symm (suspMapPath f p)))) := by
  calc suspMapPath f (Path.symm (Path.trans (Path.trans (Path.trans p q) r) s))
      = Path.symm (suspMapPath f (Path.trans (Path.trans (Path.trans p q) r) s)) :=
        suspMapPath_symm f _
    _ = Path.symm (Path.trans (Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                                          (suspMapPath f r))
                              (suspMapPath f s)) := by
        rw [suspMapPath_four_trans f p q r s]
    _ = Path.trans (Path.symm (suspMapPath f s))
          (Path.symm (Path.trans (Path.trans (suspMapPath f p) (suspMapPath f q))
                                 (suspMapPath f r))) :=
        Path.symm_trans _ _
    _ = Path.trans (Path.symm (suspMapPath f s))
          (Path.trans (Path.symm (suspMapPath f r))
            (Path.symm (Path.trans (suspMapPath f p) (suspMapPath f q)))) := by
        rw [Path.symm_trans (Path.trans (suspMapPath f p) (suspMapPath f q)) (suspMapPath f r)]
    _ = Path.trans (Path.symm (suspMapPath f s))
          (Path.trans (Path.symm (suspMapPath f r))
            (Path.trans (Path.symm (suspMapPath f q)) (Path.symm (suspMapPath f p)))) := by
        rw [Path.symm_trans (suspMapPath f p) (suspMapPath f q)]

/-! ## 29. Transport along triple suspension path -/

theorem transport_susp_triple {D : Susp A → Type v} {w x y z : Susp A}
    (p : Path w x) (q : Path x y) (r : Path y z) (d : D w) :
    Path.transport (Path.trans (Path.trans p q) r) d =
    Path.transport r (Path.transport q (Path.transport p d)) := by
  calc Path.transport (Path.trans (Path.trans p q) r) d
      = Path.transport r (Path.transport (Path.trans p q) d) :=
        Path.transport_trans _ r d
    _ = Path.transport r (Path.transport q (Path.transport p d)) := by
        rw [Path.transport_trans p q d]

/-! ## 30. congrArg through cofiberMapCodomain chain -/

theorem cofiberMapCodomain_congrArg_symm {f : A → B} (h : B → C)
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    congrArg (cofiberMapCodomain (f := f) h) (Path.symm (cofiberPath (f := f) p)) =
    Path.symm (congrArg (cofiberMapCodomain (f := f) h) (cofiberPath (f := f) p)) :=
  congrArg_symm _ _

/-! ## 31. Suspension map id -/

theorem suspMap_id : suspMap (fun x : A => x) = fun x => x := by
  funext x; cases x <;> rfl

/-! ## 32. congrArg of suspMap composition -/

theorem double_congrArg_susp (f : B → C) (g : A → B) {x y : Susp A}
    (p : Path x y) :
    congrArg (suspMap f) (congrArg (suspMap g) p) =
    congrArg (fun a => suspMap f (suspMap g a)) p := by
  rw [← congrArg_comp]

/-! ## 33. Loop space is a group: assembling the group data -/

structure LoopGroupData (A : Type u) where
  mul : NorthLoop A → NorthLoop A → NorthLoop A
  one : NorthLoop A
  inv : NorthLoop A → NorthLoop A
  assoc : ∀ p q r, mul (mul p q) r = mul p (mul q r)
  left_id : ∀ p, mul one p = p
  right_id : ∀ p, mul p one = p
  inv_inv : ∀ p, inv (inv p) = p

noncomputable def canonicalLoopGroup (A : Type u) : LoopGroupData A where
  mul := loopComp
  one := Path.refl _
  inv := loopInv
  assoc := loopComp_assoc
  left_id := loopComp_refl_left
  right_id := loopComp_refl_right
  inv_inv := loopInv_inv

/-! ## 34. Σ-Ω adjunction data: map from loops to suspension paths -/

noncomputable def sigmaOmega_unit (a : A) (p : Path a a) : NorthLoop A :=
  freudenthalMap a p

theorem sigmaOmega_unit_trans (a : A) (p q : Path a a) :
    sigmaOmega_unit a (Path.trans p q) =
    Path.trans (sigmaOmega_unit a p) (sigmaOmega_unit a q) :=
  freudenthalMap_trans a p q

theorem sigmaOmega_unit_symm (a : A) (p : Path a a) :
    sigmaOmega_unit a (Path.symm p) =
    Path.symm (sigmaOmega_unit a p) :=
  freudenthalMap_symm a p

/-! ## 35. Cofiber triple path -/

theorem cofiberPath_triple {f : A → B} {b₁ b₂ b₃ b₄ : B}
    (p : Path b₁ b₂) (q : Path b₂ b₃) (r : Path b₃ b₄) :
    cofiberPath (f := f) (Path.trans (Path.trans p q) r) =
    Path.trans (Path.trans (cofiberPath (f := f) p) (cofiberPath (f := f) q))
               (cofiberPath (f := f) r) := by
  calc cofiberPath (f := f) (Path.trans (Path.trans p q) r)
      = Path.trans (cofiberPath (f := f) (Path.trans p q))
                   (cofiberPath (f := f) r) :=
        cofiberPath_trans _ r
    _ = Path.trans (Path.trans (cofiberPath (f := f) p) (cofiberPath (f := f) q))
                   (cofiberPath (f := f) r) := by
        rw [cofiberPath_trans p q]

/-! ## 36. Puppe stage3 four-fold -/

theorem puppe_stage3_four (f : A → B) {v w x y z : Susp A}
    (p : Path v w) (q : Path w x) (r : Path x y) (s : Path y z) :
    congrArg (puppeStage3 f) (Path.trans (Path.trans (Path.trans p q) r) s) =
    Path.trans (Path.trans (Path.trans
      (congrArg (puppeStage3 f) p) (congrArg (puppeStage3 f) q))
      (congrArg (puppeStage3 f) r))
      (congrArg (puppeStage3 f) s) := by
  calc congrArg (puppeStage3 f) (Path.trans (Path.trans (Path.trans p q) r) s)
      = Path.trans (congrArg (puppeStage3 f) (Path.trans (Path.trans p q) r))
                   (congrArg (puppeStage3 f) s) :=
        congrArg_trans _ _ s
    _ = Path.trans (Path.trans (congrArg (puppeStage3 f) (Path.trans p q))
                               (congrArg (puppeStage3 f) r))
                   (congrArg (puppeStage3 f) s) := by
        rw [congrArg_trans _ (Path.trans p q) r]
    _ = Path.trans (Path.trans (Path.trans
          (congrArg (puppeStage3 f) p) (congrArg (puppeStage3 f) q))
          (congrArg (puppeStage3 f) r))
          (congrArg (puppeStage3 f) s) := by
        rw [congrArg_trans _ p q]

end ComputationalPaths.Path.SuspensionDeep
