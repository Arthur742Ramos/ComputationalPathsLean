/-
# Derived Sigma/Product Identities

This module provides derived rewrite-equivalence lemmas for sigma types and
products, built from the core rewrite system.  We establish projection β-rules,
η-expansion identities, interactions between product/sigma operations and
path composition, and coherence witnesses.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace ProductSigmaDerived

universe u

variable {A : Type u} {B : A → Type u}

/-! ## Sigma eta -/

/-- Sigma eta: rebuilding a sigma path from its projections. -/
noncomputable def rweq_sigmaMk_sigmaFst_sigmaSnd {x y : Sigma B}
    (p : Path x y) :
    RwEq (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p :=
  rweq_sigma_eta (A := A) (B := B) (p := p)

/-! ## Sigma projection β-rules -/

/-- First projection β-rule: `sigmaFst (sigmaMk p q) ≃ ofEq p.toEq`. -/
noncomputable def rweq_sigmaFst_sigmaMk {a₁ a₂ : A}
    {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path
      (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    RwEq (Path.sigmaFst (Path.sigmaMk (A := A) (B := B) p q))
         (Path.stepChain p.toEq) :=
  rweq_sigma_fst_beta (A := A) (B := B) (p := p) (q := q)

/-- Second projection β-rule. -/
noncomputable def rweq_sigmaSnd_sigmaMk {a₁ a₂ : A}
    {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path
      (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    RwEq (Path.sigmaSnd (Path.sigmaMk (A := A) (B := B) p q))
         (Path.stepChain q.toEq) :=
  rweq_sigma_snd_beta (A := A) (B := B) (p := p) (q := q)

/-! ## Product β-rules -/

/-- First projection β-rule for products: `fst (prodMk p q) ≃ p`. -/
noncomputable def rweq_fst_prodMk {α β : Type u} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (Path.fst (Path.prodMk p q)) p :=
  rweq_prod_fst_beta p q

/-- Second projection β-rule for products: `snd (prodMk p q) ≃ q`. -/
noncomputable def rweq_snd_prodMk {α β : Type u} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (Path.snd (Path.prodMk p q)) q :=
  rweq_prod_snd_beta p q

/-! ## Product eta -/

/-- Product η: rebuilding a product path from its projections. -/
noncomputable def rweq_prodMk_fst_snd {α β : Type u} {x y : α × β}
    (p : Path x y) :
    RwEq (Path.prodMk (Path.fst p) (Path.snd p)) p :=
  rweq_prod_eta p

/-! ## Product-path coherence -/

/-- `prodMk (refl a) (refl b)` is definitionally `refl (a, b)`. -/
theorem prodMk_refl_refl_eq {α β : Type u} (a : α) (b : β) :
    Path.prodMk (Path.refl a) (Path.refl b) = Path.refl (a, b) := by
  simp

/-- The toEq of a prodMk decomposes componentwise. -/
theorem toEq_prodMk_components {α β : Type u} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Path.prodMk p q).toEq =
      show (a₁, b₁) = (a₂, b₂) from
        match p.toEq, q.toEq with
        | rfl, rfl => rfl := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-! ## Sigma path construction coherence -/

/-- `sigmaMk (refl a) (refl (transport refl b))` has `toEq = rfl`. -/
theorem sigmaMk_refl_toEq (a : A) (b : B a) :
    (Path.sigmaMk (Path.refl a)
      (Path.stepChain (show Path.transport (Path.refl a) b = b from rfl))).toEq =
        rfl := by
  simp

/-- The first projection of a reflexive path is reflexive. -/
theorem sigmaFst_refl (x : Sigma B) :
    (Path.sigmaFst (Path.refl x)).toEq = rfl := by
  simp

/-- The second projection of a reflexive path is reflexive at the equality level. -/
theorem sigmaSnd_refl_toEq (x : Sigma B) :
    (Path.sigmaSnd (Path.refl x)).toEq = rfl := by
  simp

/-! ## Product projection coherence with trans -/

/-- `fst (trans p q)` has the same toEq as composing `fst p` and `fst q`. -/
theorem fst_trans_toEq {α β : Type u} {x y z : α × β}
    (p : Path x y) (q : Path y z) :
    (Path.fst (Path.trans p q)).toEq =
      ((Path.fst p).toEq.trans (Path.fst q).toEq) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-- `snd (trans p q)` has the same toEq as composing `snd p` and `snd q`. -/
theorem snd_trans_toEq {α β : Type u} {x y z : α × β}
    (p : Path x y) (q : Path y z) :
    (Path.snd (Path.trans p q)).toEq =
      ((Path.snd p).toEq.trans (Path.snd q).toEq) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-- `fst (symm p) = symm (fst p)` at the equality level. -/
theorem fst_symm_toEq {α β : Type u} {x y : α × β}
    (p : Path x y) :
    (Path.fst (Path.symm p)).toEq = (Path.fst p).toEq.symm := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-- `snd (symm p) = symm (snd p)` at the equality level. -/
theorem snd_symm_toEq {α β : Type u} {x y : α × β}
    (p : Path x y) :
    (Path.snd (Path.symm p)).toEq = (Path.snd p).toEq.symm := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-! ## Sigma projection coherence with trans -/

/-- `sigmaFst (trans p q)` decomposes at the equality level. -/
theorem sigmaFst_trans_toEq {x y z : Sigma B}
    (p : Path x y) (q : Path y z) :
    (Path.sigmaFst (Path.trans p q)).toEq =
      ((Path.sigmaFst p).toEq.trans (Path.sigmaFst q).toEq) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-- `sigmaFst (symm p)` is the symmetric of `sigmaFst p` at the equality level. -/
theorem sigmaFst_symm_toEq {x y : Sigma B}
    (p : Path x y) :
    (Path.sigmaFst (Path.symm p)).toEq = (Path.sigmaFst p).toEq.symm := by
  cases p with
  | mk steps proof =>
    cases proof
    rfl

/-! ## Sum type coherence -/

/-- `inlCongr (refl a)` is definitionally `refl (Sum.inl a)`. -/
theorem inlCongr_refl {α β : Type u} (a : α) :
    Path.inlCongr (B := β) (Path.refl a) = Path.refl (Sum.inl a) := by
  simp [Path.inlCongr]

/-- `inrCongr (refl b)` is definitionally `refl (Sum.inr b)`. -/
theorem inrCongr_refl {α β : Type u} (b : β) :
    Path.inrCongr (A := α) (Path.refl b) = Path.refl (Sum.inr b) := by
  simp [Path.inrCongr]

/-- `inlCongr` distributes over `trans` at the equality level. -/
theorem inlCongr_trans_toEq {α β : Type u} {a₁ a₂ a₃ : α}
    (p : Path a₁ a₂) (q : Path a₂ a₃) :
    (Path.inlCongr (B := β) (Path.trans p q)).toEq =
      ((Path.inlCongr (B := β) p).toEq.trans
       (Path.inlCongr (B := β) q).toEq) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-- `inrCongr` distributes over `trans` at the equality level. -/
theorem inrCongr_trans_toEq {α β : Type u} {b₁ b₂ b₃ : β}
    (p : Path b₁ b₂) (q : Path b₂ b₃) :
    (Path.inrCongr (A := α) (Path.trans p q)).toEq =
      ((Path.inrCongr (A := α) p).toEq.trans
       (Path.inrCongr (A := α) q).toEq) := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-! ## Function type coherence -/

/-- `lamCongr` of reflexive pointwise paths is `refl`. -/
theorem lamCongr_refl_eq {α β : Type u} (f : α → β) :
    Path.lamCongr (fun x => Path.refl (f x)) = Path.refl f := by
  simp

/-- `app` of a reflexive path at any point is `refl`. -/
theorem app_refl_eq {α β : Type u} (f : α → β) (a : α) :
    Path.app (Path.refl f) a = Path.refl (f a) := by
  simp [Path.app]

/-! ## Concrete product/sigma examples -/

/-- A concrete product path. -/
noncomputable example : Path ((1, 2) : Nat × Nat) (1, 2) :=
  Path.prodMk (Path.refl 1) (Path.refl 2)

/-- A concrete sigma path (dependent pair with constant family). -/
noncomputable example : Path (⟨0, 1⟩ : @Sigma Nat (fun _ => Nat)) (⟨0, 1⟩ : @Sigma Nat (fun _ => Nat)) :=
  Path.refl (⟨0, 1⟩ : @Sigma Nat (fun _ => Nat))

/-- A concrete sum path. -/
noncomputable example : Path (Sum.inl 42 : Nat ⊕ Bool) (Sum.inl 42) :=
  Path.inlCongr (Path.refl 42)

/-- Projecting out of a concrete product path. -/
example : (Path.fst (Path.refl ((1, 2) : Nat × Nat))).toEq = rfl := by
  rfl

/-- Symmetry of a product path decomposes componentwise at toEq. -/
example {α β : Type u} {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    (Path.symm (Path.prodMk p q)).toEq =
      (Path.prodMk (Path.symm p) (Path.symm q)).toEq := by
  cases p with
  | mk steps₁ proof₁ =>
    cases proof₁
    cases q with
    | mk steps₂ proof₂ =>
      cases proof₂
      rfl

/-! ## RwEq coherence for products -/

/-- `RwEq` for `prodMk` congruence in the first component. -/
noncomputable def rweq_prodMk_congr_left {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    {p q : Path a₁ a₂} (r : Path b₁ b₂)
    (h : RwEq p q) :
    RwEq (Path.prodMk p r) (Path.prodMk q r) := by
  induction h with
  | refl => exact RwEq.refl _
  | step s =>
      exact rweq_of_step (Step.trans_congr_left
        (Path.mapRight Prod.mk a₂ r)
        (Step.context_congr ⟨fun a => (a, b₁)⟩ s))
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

/-- `RwEq` for `prodMk` congruence in the second component. -/
noncomputable def rweq_prodMk_congr_right {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) {r s : Path b₁ b₂}
    (h : RwEq r s) :
    RwEq (Path.prodMk p r) (Path.prodMk p s) := by
  induction h with
  | refl => exact RwEq.refl _
  | step st =>
      exact rweq_of_step (Step.trans_congr_right
        (Path.mapLeft Prod.mk p b₁)
        (Step.context_congr ⟨fun b => (a₂, b)⟩ st))
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

end ProductSigmaDerived
end Path
end ComputationalPaths
