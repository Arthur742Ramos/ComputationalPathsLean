import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths.TypeFormers

open ComputationalPaths

universe u

section Pi

variable {A B : Type u}
variable {f g : A → B}

@[simp] noncomputable def piBetaStep
    (p : ∀ x : A, Path (f x) (g x)) (a : A) :
    Path.Step (Path.congrArg (fun h : A → B => h a) (Path.lamCongr p)) (p a) :=
  Path.Step.fun_app_beta (A := B) (α := A) (p := p) (a := a)

@[simp] noncomputable def piEtaStep (p : Path f g) :
    Path.Step (Path.lamCongr (fun x => Path.app p x)) p :=
  Path.Step.fun_eta p

@[simp] noncomputable def piBetaRwEq
    (p : ∀ x : A, Path (f x) (g x)) (a : A) :
    Path.RwEq (Path.congrArg (fun h : A → B => h a) (Path.lamCongr p)) (p a) :=
  Path.RwEq.step (piBetaStep p a)

@[simp] noncomputable def piEtaRwEq (p : Path f g) :
    Path.RwEq (Path.lamCongr (fun x => Path.app p x)) p :=
  Path.RwEq.step (piEtaStep p)

end Pi

section Product

variable {A B : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

@[simp] noncomputable def prodFstBetaStep
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path.Step (Path.fst (Path.prodMk p q)) p := by
  simpa [Path.fst, Path.prodMk] using
    (Path.Step.prod_fst_beta (A := A) (B := B) (p := p) (q := q))

@[simp] noncomputable def prodSndBetaStep
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path.Step (Path.snd (Path.prodMk p q)) q := by
  simpa [Path.snd, Path.prodMk] using
    (Path.Step.prod_snd_beta (A := B) (B := A) (p := p) (q := q))

@[simp] noncomputable def prodEtaStep
    (r : Path (a₁, b₁) (a₂, b₂)) :
    Path.Step (Path.prodMk (Path.fst r) (Path.snd r)) r :=
  Path.Step.prod_eta r

@[simp] noncomputable def prodFstBetaRwEq
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path.RwEq (Path.fst (Path.prodMk p q)) p :=
  Path.RwEq.step (prodFstBetaStep p q)

@[simp] noncomputable def prodSndBetaRwEq
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Path.RwEq (Path.snd (Path.prodMk p q)) q :=
  Path.RwEq.step (prodSndBetaStep p q)

@[simp] noncomputable def prodEtaRwEq
    (r : Path (a₁, b₁) (a₂, b₂)) :
    Path.RwEq (Path.prodMk (Path.fst r) (Path.snd r)) r :=
  Path.RwEq.step (prodEtaStep r)

end Product

section Sigma

variable {A : Type u} {B : A → Type u}
variable {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}

@[simp] noncomputable def sigmaFstBetaStep
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Path.Step (Path.sigmaFst (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) := by
  simpa [Path.sigmaFst] using
    (Path.Step.sigma_fst_beta (A := A) (B := B) (p := p) (q := q))

@[simp] noncomputable def sigmaSndBetaStep
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Path.Step (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂) q.toEq) :=
  Path.Step.sigma_snd_beta (A₀ := A) (B := B) (p := p) (q := q)

@[simp] noncomputable def sigmaEtaStep
    (r : Path (A := Sigma B) ⟨a₁, b₁⟩ ⟨a₂, b₂⟩) :
    Path.Step (Path.sigmaMk (Path.sigmaFst r) (Path.sigmaSnd r)) r :=
  Path.Step.sigma_eta r

@[simp] noncomputable def sigmaFstBetaRwEq
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Path.RwEq (Path.sigmaFst (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) :=
  Path.RwEq.step (sigmaFstBetaStep p q)

@[simp] noncomputable def sigmaSndBetaRwEq
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Path.RwEq (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂) q.toEq) :=
  Path.RwEq.step (sigmaSndBetaStep p q)

@[simp] noncomputable def sigmaEtaRwEq
    (r : Path (A := Sigma B) ⟨a₁, b₁⟩ ⟨a₂, b₂⟩) :
    Path.RwEq (Path.sigmaMk (Path.sigmaFst r) (Path.sigmaSnd r)) r :=
  Path.RwEq.step (sigmaEtaStep r)

end Sigma

section Sum

variable {A B C : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

@[simp] noncomputable def copair (f : A → C) (g : B → C) : Sum A B → C :=
  fun s =>
    match s with
    | Sum.inl a => f a
    | Sum.inr b => g b

@[simp] noncomputable def sumInlBetaStep
    (f : A → C) (g : B → C) (p : Path a₁ a₂) :
    Path.Step (Path.congrArg (copair f g) (Path.inlCongr p)) (Path.congrArg f p) := by
  simpa [copair] using
    (Path.Step.sum_rec_inl_beta (A := C) (α := A) (β := B) (f := f) (g := g) (p := p))

@[simp] noncomputable def sumInrBetaStep
    (f : A → C) (g : B → C) (p : Path b₁ b₂) :
    Path.Step (Path.congrArg (copair f g) (Path.inrCongr p)) (Path.congrArg g p) := by
  simpa [copair] using
    (Path.Step.sum_rec_inr_beta (A := C) (α := A) (β := B) (f := f) (g := g) (p := p))

@[simp] noncomputable def sumEtaPath (h : Sum A B → C) :
    Path h (fun s =>
      match s with
      | Sum.inl a => h (Sum.inl a)
      | Sum.inr b => h (Sum.inr b)) :=
  Path.lamCongr (fun s =>
    match s with
    | Sum.inl a => Path.refl (h (Sum.inl a))
    | Sum.inr b => Path.refl (h (Sum.inr b)))

@[simp] noncomputable def sumEtaStep (h : Sum A B → C) :
    Path.Step (Path.lamCongr (fun s => Path.app (sumEtaPath h) s)) (sumEtaPath h) :=
  Path.Step.fun_eta (sumEtaPath h)

@[simp] noncomputable def sumInlBetaRwEq
    (f : A → C) (g : B → C) (p : Path a₁ a₂) :
    Path.RwEq (Path.congrArg (copair f g) (Path.inlCongr p)) (Path.congrArg f p) :=
  Path.RwEq.step (sumInlBetaStep f g p)

@[simp] noncomputable def sumInrBetaRwEq
    (f : A → C) (g : B → C) (p : Path b₁ b₂) :
    Path.RwEq (Path.congrArg (copair f g) (Path.inrCongr p)) (Path.congrArg g p) :=
  Path.RwEq.step (sumInrBetaStep f g p)

@[simp] noncomputable def sumEtaRwEq (h : Sum A B → C) :
    Path.RwEq (Path.lamCongr (fun s => Path.app (sumEtaPath h) s)) (sumEtaPath h) :=
  Path.RwEq.step (sumEtaStep h)

end Sum

section ConfluenceAndComputation

variable {A B : Type u}
variable {f g : A → B}
variable {a : A}

noncomputable def piBetaThenEtaAt (p : Path f g) :
    Path.RwEq (Path.app (Path.lamCongr (fun x => Path.app p x)) a) (Path.app p a) :=
  Path.RwEq.step (piBetaStep (p := fun x => Path.app p x) a)

noncomputable def piEtaThenBetaAt (p : Path f g) :
    Path.RwEq (Path.app (Path.lamCongr (fun x => Path.app p x)) a) (Path.app p a) := by
  exact Path.rweq_congrArg_of_rweq (f := fun h : A → B => h a) (piEtaRwEq p)

noncomputable def piBetaEtaConfluentAt (p : Path f g) :
    Path.RwEq (Path.app p a) (Path.app p a) :=
  Path.RwEq.trans (Path.RwEq.symm (piBetaThenEtaAt (a := a) p)) (piEtaThenBetaAt (a := a) p)

variable {a₁ a₂ : A} {b₁ b₂ : B}

noncomputable def prodBetaThenEtaFst (r : Path (a₁, b₁) (a₂, b₂)) :
    Path.RwEq (Path.fst (Path.prodMk (Path.fst r) (Path.snd r))) (Path.fst r) :=
  Path.RwEq.step (prodFstBetaStep (p := Path.fst r) (q := Path.snd r))

noncomputable def prodEtaThenBetaFst (r : Path (a₁, b₁) (a₂, b₂)) :
    Path.RwEq (Path.fst (Path.prodMk (Path.fst r) (Path.snd r))) (Path.fst r) := by
  exact Path.rweq_congrArg_of_rweq (f := Prod.fst) (prodEtaRwEq r)

noncomputable def prodBetaEtaConfluentFst (r : Path (a₁, b₁) (a₂, b₂)) :
    Path.RwEq (Path.fst r) (Path.fst r) :=
  Path.RwEq.trans (Path.RwEq.symm (prodBetaThenEtaFst r)) (prodEtaThenBetaFst r)

noncomputable def lambdaApplicationComputationStep
    (body : A → B) (arg : A) :
    Path.Step (Path.app (Path.lamCongr (fun x => Path.refl (body x))) arg)
      (Path.refl (body arg)) := by
  simpa [Path.app] using
    (Path.Step.fun_app_beta (A := B) (α := A)
      (p := fun x => Path.refl (body x)) (a := arg))

noncomputable def lambdaApplicationComputationRwEq
    (body : A → B) (arg : A) :
    Path.RwEq (Path.app (Path.lamCongr (fun x => Path.refl (body x))) arg)
      (Path.refl (body arg)) :=
  Path.RwEq.step (lambdaApplicationComputationStep body arg)

theorem betaEtaNormalFormsUnique
    {X : Type u} {x y : X} {p q : Path x y}
    (h : Path.RwEq p q) :
    Path.normalizeForm (A := X) (a := x) (b := y) p =
      Path.normalizeForm (A := X) (a := x) (b := y) q :=
  Path.normalizeForm_eq_of_rweq h

end ConfluenceAndComputation

end ComputationalPaths.TypeFormers
