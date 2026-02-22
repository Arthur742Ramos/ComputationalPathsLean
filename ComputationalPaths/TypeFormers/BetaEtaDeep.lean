import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
namespace ComputationalPaths.TypeFormers

open ComputationalPaths
open ComputationalPaths.Path

universe u

section Pi

variable {A B : Type u}
variable {f g : A → B}

@[simp] def piBetaStep
    (p : ∀ x : A, Path (f x) (g x)) (a : A) :
    Step (Path.app (Path.lamCongr p) a) (p a) := by
  simpa [Path.app] using
    (Step.fun_app_beta (A := B) (α := A) (p := p) (a := a))

@[simp] def piEtaStep (p : Path f g) :
    Step (Path.lamCongr (fun x => Path.app p x)) p :=
  Step.fun_eta p

@[simp] def piBetaRwEq
    (p : ∀ x : A, Path (f x) (g x)) (a : A) :
    RwEq (Path.app (Path.lamCongr p) a) (p a) :=
  RwEq.step (piBetaStep p a)

@[simp] def piEtaRwEq (p : Path f g) :
    RwEq (Path.lamCongr (fun x => Path.app p x)) p :=
  RwEq.step (piEtaStep p)

end Pi

section Product

variable {A B : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

@[simp] def prodFstBetaStep
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Step (Path.fst (Path.prodMk p q)) p := by
  simpa [Path.fst, Path.prodMk] using
    (Step.prod_fst_beta (A := A) (B := B) (p := p) (q := q))

@[simp] def prodSndBetaStep
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Step (Path.snd (Path.prodMk p q)) q := by
  simpa [Path.snd, Path.prodMk] using
    (Step.prod_snd_beta (A := B) (B := A) (p := p) (q := q))

@[simp] def prodEtaStep
    (r : Path (a₁, b₁) (a₂, b₂)) :
    Step (Path.prodMk (Path.fst r) (Path.snd r)) r :=
  Step.prod_eta r

@[simp] def prodFstBetaRwEq
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (Path.fst (Path.prodMk p q)) p :=
  RwEq.step (prodFstBetaStep p q)

@[simp] def prodSndBetaRwEq
    (p : Path a₁ a₂) (q : Path b₁ b₂) :
    RwEq (Path.snd (Path.prodMk p q)) q :=
  RwEq.step (prodSndBetaStep p q)

@[simp] def prodEtaRwEq
    (r : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.prodMk (Path.fst r) (Path.snd r)) r :=
  RwEq.step (prodEtaStep r)

end Product

section Sigma

variable {A : Type u} {B : A → Type u}
variable {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}

@[simp] def sigmaFstBetaStep
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Step (Path.sigmaFst (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) := by
  simpa [Path.sigmaFst] using
    (Step.sigma_fst_beta (A := A) (B := B) (p := p) (q := q))

@[simp] def sigmaSndBetaStep
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    Step (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂) q.toEq) :=
  Step.sigma_snd_beta (A₀ := A) (B := B) (p := p) (q := q)

@[simp] def sigmaEtaStep
    (r : Path (A := Sigma B) ⟨a₁, b₁⟩ ⟨a₂, b₂⟩) :
    Step (Path.sigmaMk (Path.sigmaFst r) (Path.sigmaSnd r)) r :=
  Step.sigma_eta r

@[simp] def sigmaFstBetaRwEq
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    RwEq (Path.sigmaFst (Path.sigmaMk (B := B) p q))
      (Path.stepChain (A := A) p.toEq) :=
  RwEq.step (sigmaFstBetaStep p q)

@[simp] def sigmaSndBetaRwEq
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
    RwEq (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.stepChain
        (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂) q.toEq) :=
  RwEq.step (sigmaSndBetaStep p q)

@[simp] def sigmaEtaRwEq
    (r : Path (A := Sigma B) ⟨a₁, b₁⟩ ⟨a₂, b₂⟩) :
    RwEq (Path.sigmaMk (Path.sigmaFst r) (Path.sigmaSnd r)) r :=
  RwEq.step (sigmaEtaStep r)

end Sigma

section Sum

variable {A B C : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

@[simp] def copair (f : A → C) (g : B → C) : Sum A B → C :=
  fun s =>
    match s with
    | Sum.inl a => f a
    | Sum.inr b => g b

@[simp] def sumInlBetaStep
    (f : A → C) (g : B → C) (p : Path a₁ a₂) :
    Step (Path.congrArg (copair f g) (Path.inlCongr p)) (Path.congrArg f p) := by
  simpa [copair] using
    (Step.sum_rec_inl_beta (A := C) (α := A) (β := B) (f := f) (g := g) (p := p))

@[simp] def sumInrBetaStep
    (f : A → C) (g : B → C) (p : Path b₁ b₂) :
    Step (Path.congrArg (copair f g) (Path.inrCongr p)) (Path.congrArg g p) := by
  simpa [copair] using
    (Step.sum_rec_inr_beta (A := C) (α := A) (β := B) (f := f) (g := g) (p := p))

@[simp] def sumEtaPath (h : Sum A B → C) :
    Path h (fun s =>
      match s with
      | Sum.inl a => h (Sum.inl a)
      | Sum.inr b => h (Sum.inr b)) :=
  Path.lamCongr (fun s =>
    match s with
    | Sum.inl a => Path.refl (h (Sum.inl a))
    | Sum.inr b => Path.refl (h (Sum.inr b)))

@[simp] def sumEtaStep (h : Sum A B → C) :
    Step (Path.lamCongr (fun s => Path.app (sumEtaPath h) s)) (sumEtaPath h) :=
  Step.fun_eta (sumEtaPath h)

@[simp] def sumInlBetaRwEq
    (f : A → C) (g : B → C) (p : Path a₁ a₂) :
    RwEq (Path.congrArg (copair f g) (Path.inlCongr p)) (Path.congrArg f p) :=
  RwEq.step (sumInlBetaStep f g p)

@[simp] def sumInrBetaRwEq
    (f : A → C) (g : B → C) (p : Path b₁ b₂) :
    RwEq (Path.congrArg (copair f g) (Path.inrCongr p)) (Path.congrArg g p) :=
  RwEq.step (sumInrBetaStep f g p)

@[simp] def sumEtaRwEq (h : Sum A B → C) :
    RwEq (Path.lamCongr (fun s => Path.app (sumEtaPath h) s)) (sumEtaPath h) :=
  RwEq.step (sumEtaStep h)

end Sum

section ConfluenceAndComputation

variable {A B : Type u}
variable {f g : A → B}
variable {a : A}

def piBetaThenEtaAt (p : Path f g) :
    RwEq (Path.app (Path.lamCongr (fun x => Path.app p x)) a) (Path.app p a) :=
  RwEq.step (piBetaStep (p := fun x => Path.app p x) a)

noncomputable def piEtaThenBetaAt (p : Path f g) :
    RwEq (Path.app (Path.lamCongr (fun x => Path.app p x)) a) (Path.app p a) := by
  exact rweq_congrArg_of_rweq (f := fun h : A → B => h a) (piEtaRwEq p)

noncomputable def piBetaEtaConfluentAt (p : Path f g) :
    RwEq (Path.app p a) (Path.app p a) :=
  RwEq.trans (RwEq.symm (piBetaThenEtaAt (a := a) p)) (piEtaThenBetaAt (a := a) p)

variable {a₁ a₂ : A} {b₁ b₂ : B}

def prodBetaThenEtaFst (r : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.fst (Path.prodMk (Path.fst r) (Path.snd r))) (Path.fst r) :=
  RwEq.step (prodFstBetaStep (p := Path.fst r) (q := Path.snd r))

noncomputable def prodEtaThenBetaFst (r : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.fst (Path.prodMk (Path.fst r) (Path.snd r))) (Path.fst r) := by
  exact rweq_congrArg_of_rweq (f := Prod.fst) (prodEtaRwEq r)

noncomputable def prodBetaEtaConfluentFst (r : Path (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.fst r) (Path.fst r) :=
  RwEq.trans (RwEq.symm (prodBetaThenEtaFst r)) (prodEtaThenBetaFst r)

def lambdaApplicationComputationStep
    (body : A → B) (arg : A) :
    Step (Path.app (Path.lamCongr (fun x => Path.refl (body x))) arg)
      (Path.refl (body arg)) := by
  simpa [Path.app] using
    (Step.fun_app_beta (A := B) (α := A)
      (p := fun x => Path.refl (body x)) (a := arg))

def lambdaApplicationComputationRwEq
    (body : A → B) (arg : A) :
    RwEq (Path.app (Path.lamCongr (fun x => Path.refl (body x))) arg)
      (Path.refl (body arg)) :=
  RwEq.step (lambdaApplicationComputationStep body arg)

theorem betaEtaNormalFormsUnique
    {X : Type u} {x y : X} {p q : Path x y}
    (h : RwEq p q) :
    normalizeForm (A := X) (a := x) (b := y) p =
      normalizeForm (A := X) (a := x) (b := y) q :=
  normalizeForm_eq_of_rweq h

end ConfluenceAndComputation

end ComputationalPaths.TypeFormers
