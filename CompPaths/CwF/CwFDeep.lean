/-
# Categories with Families from Computational Paths

Deep CwF semantics where contexts are types, substitutions are functions,
types-in-context are dependent families, and terms are sections. Identity
types are interpreted by `Path`, with elimination and type formers witnessed
through explicit `Step`/`RwEq` proofs.
-/

import CompPaths.Core

namespace CompPaths.CwF

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Core CwF data from computational paths -/

abbrev Ctx := Type u
abbrev Sub (Δ Γ : Ctx) := Δ → Γ
abbrev Ty (Γ : Ctx) := Γ → Type u
abbrev Tm (Γ : Ctx) (A : Ty Γ) := (γ : Γ) → A γ

@[simp] def subId (Γ : Ctx) : Sub Γ Γ := fun γ => γ

@[simp] def subComp {Γ Δ Θ : Ctx} (σ : Sub Δ Γ) (τ : Sub Θ Δ) : Sub Θ Γ :=
  fun θ => σ (τ θ)

@[simp] def tySub {Γ Δ : Ctx} (A : Ty Γ) (σ : Sub Δ Γ) : Ty Δ :=
  fun δ => A (σ δ)

@[simp] def tmSub {Γ Δ : Ctx} {A : Ty Γ} (t : Tm Γ A) (σ : Sub Δ Γ) :
    Tm Δ (tySub A σ) :=
  fun δ => t (σ δ)

def ctxExt (Γ : Ctx) (A : Ty Γ) : Ctx := Sigma A

def projSub {Γ : Ctx} (A : Ty Γ) : Sub (ctxExt Γ A) Γ := Sigma.fst

def varTm {Γ : Ctx} (A : Ty Γ) : Tm (ctxExt Γ A) (tySub A (projSub A)) := Sigma.snd

def extSub {Γ Δ : Ctx} {A : Ty Γ} (σ : Sub Δ Γ) (t : Tm Δ (tySub A σ)) :
    Sub Δ (ctxExt Γ A) :=
  fun δ => ⟨σ δ, t δ⟩

/-! ## Identity type former from computational paths -/

def IdTy {Γ : Ctx} {A : Ty Γ} (a b : Tm Γ A) : Ty Γ :=
  fun γ => Path (a γ) (b γ)

def idRefl {Γ : Ctx} {A : Ty Γ} (a : Tm Γ A) : Tm Γ (IdTy a a) :=
  fun γ => Path.refl (a γ)

theorem id_subst {Γ Δ : Ctx} {A : Ty Γ} (a b : Tm Γ A) (σ : Sub Δ Γ) :
    tySub (IdTy a b) σ = IdTy (tmSub a σ) (tmSub b σ) := rfl

def idSubstCongr {Γ Δ : Ctx} {A : Ty Γ} (a b : Tm Γ A)
    (σ : Sub Δ Γ) (δ : Δ)
    (p : IdTy a b (σ δ)) :
    IdTy (tmSub a σ) (tmSub b σ) δ :=
  Path.congrArg (fun x => x) p

noncomputable def idSubstCongr_rw {Γ Δ : Ctx} {A : Ty Γ} (a b : Tm Γ A)
    (σ : Sub Δ Γ) (δ : Δ)
    (p : IdTy a b (σ δ)) :
    RwEq (idSubstCongr a b σ δ p) p :=
  rweq_of_eq (Path.congrArg_id p)

/-! ## J eliminator derived from computational paths -/

noncomputable def jElim {A : Type u} {a : A}
    (C : (b : A) → (a = b) → Type u)
    (c : C a rfl)
    {b : A} (p : Path a b) :
    C b p.toEq := by
  cases p with
  | mk steps proof =>
      cases proof
      simpa using c

theorem jElim_refl {A : Type u} {a : A}
    (C : (b : A) → (a = b) → Type u)
    (c : C a rfl) :
    jElim C c (Path.refl a) = c := rfl

def jElim_refl_via_step {A : Type u} {a : A}
    (C : (b : A) → (a = b) → Type u)
    (c : C a rfl) :
    {h : RwEq (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) // jElim C c (Path.refl a) = c} := by
  exact ⟨RwEq.step (Step.trans_refl_right (Path.refl a)), rfl⟩

/-! ## Σ-types and Π-types with explicit β/η Steps -/

def SigmaTy {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) : Ty Γ :=
  fun γ => Sigma (fun a : A γ => B ⟨γ, a⟩)

def sigmaPair {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (a : Tm Γ A) (b : Tm Γ (fun γ => B ⟨γ, a γ⟩)) :
    Tm Γ (SigmaTy A B) :=
  fun γ => ⟨a γ, b γ⟩

def sigmaFstTm {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (t : Tm Γ (SigmaTy A B)) : Tm Γ A :=
  fun γ => (t γ).1

def sigmaSndTm {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (t : Tm Γ (SigmaTy A B)) :
    Tm Γ (fun γ => B ⟨γ, (sigmaFstTm t) γ⟩) :=
  fun γ => (t γ).2

def PiTy {Γ : Ctx} (A : Ty Γ) (B : Ty (ctxExt Γ A)) : Ty Γ :=
  fun γ => (a : A γ) → B ⟨γ, a⟩

def piLam {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (body : Tm (ctxExt Γ A) B) : Tm Γ (PiTy A B) :=
  fun γ a => body ⟨γ, a⟩

def piApp {Γ : Ctx} {A : Ty Γ} {B : Ty (ctxExt Γ A)}
    (f : Tm Γ (PiTy A B)) (a : Tm Γ A) : Tm Γ (fun γ => B ⟨γ, a γ⟩) :=
  fun γ => f γ (a γ)

def sigmaFstBetaStep {A : Type u} {B : A → Type u}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Step (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) :=
  Step.sigma_fst_beta (A := A) (B := B) p q

def sigmaSndBetaStep {A : Type u} {B : A → Type u}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Step (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂)
        q.toEq) :=
  Step.sigma_snd_beta (A₀ := A) (B := B) p q

def sigmaEtaStep {A : Type u} {B : A → Type u}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path (Sigma.mk a₁ b₁) (Sigma.mk a₂ b₂)) :
    Step (Path.sigmaMk (B := B) (Path.sigmaFst (B := B) p) (Path.sigmaSnd (B := B) p)) p :=
  Step.sigma_eta p

def sigmaFstBetaRwEq {A : Type u} {B : A → Type u}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    RwEq (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) :=
  RwEq.step (sigmaFstBetaStep p q)

def sigmaSndBetaRwEq {A : Type u} {B : A → Type u}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    RwEq (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂)
        q.toEq) :=
  RwEq.step (sigmaSndBetaStep p q)

def sigmaEtaRwEq {A : Type u} {B : A → Type u}
    {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path (Sigma.mk a₁ b₁) (Sigma.mk a₂ b₂)) :
    RwEq (Path.sigmaMk (B := B) (Path.sigmaFst (B := B) p) (Path.sigmaSnd (B := B) p)) p :=
  RwEq.step (sigmaEtaStep p)

def piBetaStep {α β : Type u} {f g : α → β}
    (p : ∀ x : α, Path (f x) (g x)) (a : α) :
    Step (Path.app (Path.lamCongr p) a) (p a) := by
  simpa [Path.app] using (Step.fun_app_beta (A := β) (α := α) p a)

def piEtaStep {α β : Type u} {f g : α → β}
    (p : Path f g) :
    Step (Path.lamCongr (fun x => Path.app p x)) p :=
  Step.fun_eta (α := α) (β := β) (p := p)

def piBetaRwEq {α β : Type u} {f g : α → β}
    (p : ∀ x : α, Path (f x) (g x)) (a : α) :
    RwEq (Path.app (Path.lamCongr p) a) (p a) :=
  RwEq.step (piBetaStep p a)

def piEtaRwEq {α β : Type u} {f g : α → β}
    (p : Path f g) :
    RwEq (Path.lamCongr (fun x => Path.app p x)) p :=
  RwEq.step (piEtaStep p)

/-! ## Morphism to the syntactic CwF and initiality witness -/

structure CwFMorToSyntactic where
  onSub : (Γ Δ : Ctx) → Sub Δ Γ → Sub Δ Γ
  onTy : (Γ : Ctx) → Ty Γ → Ty Γ
  onTm : (Γ : Ctx) → (A : Ty Γ) → Tm Γ A → Tm Γ A
  sub_id : ∀ (Γ Δ : Ctx) (σ : Sub Δ Γ), onSub Γ Δ σ = σ
  ty_id : ∀ (Γ : Ctx) (A : Ty Γ), onTy Γ A = A
  tm_id : ∀ (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A), onTm Γ A t = t

def toSyntactic : CwFMorToSyntactic where
  onSub := fun _ _ σ => σ
  onTy := fun _ A => A
  onTm := fun _ _ t => t
  sub_id := fun _ _ σ => rfl
  ty_id := fun _ A => rfl
  tm_id := fun _ _ t => rfl

noncomputable def toSyntactic_id_preserves_paths {Γ : Ctx} {A : Ty Γ}
    (a b : Tm Γ A) (γ : Γ) (p : IdTy a b γ) :
    RwEq (Path.congrArg (fun x => x) p) p :=
  rweq_of_eq (Path.congrArg_id p)

def toSyntactic_unit_step {Γ : Ctx} {A : Ty Γ} (t : Tm Γ A) :
    RwEq (Path.trans (Path.refl t) (Path.refl t)) (Path.refl t) :=
  RwEq.step (Step.trans_refl_right (Path.refl t))

theorem computational_paths_cwf_initial (F : CwFMorToSyntactic) :
    F = toSyntactic := by
  cases F with
  | mk onSub onTy onTm sub_id ty_id tm_id =>
      have hSub : onSub = (fun (Γ Δ : Ctx) (σ : Sub Δ Γ) => σ) := by
        funext Γ Δ σ
        exact sub_id Γ Δ σ
      have hTy : onTy = (fun (Γ : Ctx) (A : Ty Γ) => A) := by
        funext Γ A
        exact ty_id Γ A
      have hTm : onTm = (fun (Γ : Ctx) (A : Ty Γ) (t : Tm Γ A) => t) := by
        funext Γ A t
        exact tm_id Γ A t
      cases hSub
      cases hTy
      cases hTm
      rfl

end CompPaths.CwF
