import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
-- import ComputationalPaths.TypeFormers.BetaEtaDeep  -- TEMPORARILY DISABLED: compilation errors
namespace ComputationalPaths.TypeFormers

open ComputationalPaths
open ComputationalPaths.Path

universe u

section Products

variable {X A B : Type u}
variable {x y : X}

@[simp] noncomputable def pairPath (f : X → A) (g : X → B) (p : Path x y) :
    Path (f x, g x) (f y, g y) :=
  Path.prodMk (Path.congrArg f p) (Path.congrArg g p)

@[simp] noncomputable def fstPairStep (f : X → A) (g : X → B) (p : Path x y) :
    Step (Path.fst (pairPath f g p)) (Path.congrArg f p) := by
  simpa [pairPath, Path.fst, Path.prodMk] using
    (Step.prod_fst_beta (A := A) (B := B)
      (p := Path.congrArg f p) (q := Path.congrArg g p))

@[simp] noncomputable def sndPairStep (f : X → A) (g : X → B) (p : Path x y) :
    Step (Path.snd (pairPath f g p)) (Path.congrArg g p) := by
  simpa [pairPath, Path.snd, Path.prodMk] using
    (Step.prod_snd_beta (A := B) (B := A)
      (p := Path.congrArg f p) (q := Path.congrArg g p))

@[simp] noncomputable def fstPairRwEq (f : X → A) (g : X → B) (p : Path x y) :
    RwEq (Path.fst (pairPath f g p)) (Path.congrArg f p) :=
  rweq_of_step (fstPairStep f g p)

@[simp] noncomputable def sndPairRwEq (f : X → A) (g : X → B) (p : Path x y) :
    RwEq (Path.snd (pairPath f g p)) (Path.congrArg g p) :=
  rweq_of_step (sndPairStep f g p)

noncomputable def prod_factor_through_pairing
    {a₁ a₂ : A} {b₁ b₂ : B}
    (r : Path (a₁, b₁) (a₂, b₂)) :
    RwEq r (Path.prodMk (Path.fst r) (Path.snd r)) :=
  rweq_symm (rweq_prod_eta r)

noncomputable def prod_pairing_unique
    {a₁ a₂ : A} {b₁ b₂ : B}
    {r : Path (a₁, b₁) (a₂, b₂)}
    {p : Path a₁ a₂} {q : Path b₁ b₂}
    (hp : RwEq (Path.fst r) p)
    (hq : RwEq (Path.snd r) q) :
    RwEq r (Path.prodMk p q) := by
  have hη : RwEq r (Path.prodMk (Path.fst r) (Path.snd r)) :=
    prod_factor_through_pairing (A := A) (B := B) r
  have hpair :
      RwEq (Path.prodMk (Path.fst r) (Path.snd r)) (Path.prodMk p q) :=
    rweq_map2_of_rweq (A := A) (B := B) (C := A × B) (f := Prod.mk) hp hq
  exact rweq_trans hη hpair

end Products

section Coproducts

variable {A B C : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

@[simp] noncomputable def inlPath (p : Path a₁ a₂) :
    Path (Sum.inl a₁ : Sum A B) (Sum.inl a₂) :=
  Path.inlCongr p

@[simp] noncomputable def inrPath (p : Path b₁ b₂) :
    Path (Sum.inr b₁ : Sum A B) (Sum.inr b₂) :=
  Path.inrCongr p

-- copair is imported from BetaEtaDeep

@[simp] noncomputable def caseInlStep (f : A → C) (g : B → C) (p : Path a₁ a₂) :
    Step (Path.congrArg (copair f g) (inlPath p)) (Path.congrArg f p) := by
  simpa [copair, inlPath] using
    (Step.sum_rec_inl_beta (A := C) (α := A) (β := B)
      (f := f) (g := g) (p := p))

@[simp] noncomputable def caseInrStep (f : A → C) (g : B → C) (p : Path b₁ b₂) :
    Step (Path.congrArg (copair f g) (inrPath p)) (Path.congrArg g p) := by
  simpa [copair, inrPath] using
    (Step.sum_rec_inr_beta (A := C) (α := A) (β := B)
      (f := f) (g := g) (p := p))

@[simp] noncomputable def caseInlRwEq (f : A → C) (g : B → C) (p : Path a₁ a₂) :
    RwEq (Path.congrArg (copair f g) (inlPath p)) (Path.congrArg f p) :=
  rweq_of_step (caseInlStep f g p)

@[simp] noncomputable def caseInrRwEq (f : A → C) (g : B → C) (p : Path b₁ b₂) :
    RwEq (Path.congrArg (copair f g) (inrPath p)) (Path.congrArg g p) :=
  rweq_of_step (caseInrStep f g p)

noncomputable def copairFactorPath
    {h : Sum A B → C} {f : A → C} {g : B → C}
    (hl : ∀ a : A, Path (h (Sum.inl a)) (f a))
    (hr : ∀ b : B, Path (h (Sum.inr b)) (g b)) :
    Path h (copair f g) :=
  Path.lamCongr (fun s =>
    match s with
    | Sum.inl a => hl a
    | Sum.inr b => hr b)

noncomputable def copairFactor_unique
    {h : Sum A B → C} {f : A → C} {g : B → C}
    (hl : ∀ a : A, Path (h (Sum.inl a)) (f a))
    (hr : ∀ b : B, Path (h (Sum.inr b)) (g b))
    (p : Path h (copair f g))
    (hp : ∀ s : Sum A B,
      RwEq (Path.app p s)
        (match s with
        | Sum.inl a => hl a
        | Sum.inr b => hr b)) :
    RwEq p (copairFactorPath (A := A) (B := B) (C := C) hl hr) := by
  have hη : RwEq p (Path.lamCongr (fun s => Path.app p s)) :=
    rweq_symm (rweq_fun_eta p)
  have hlam :
      RwEq (Path.lamCongr (fun s => Path.app p s))
        (Path.lamCongr (fun s =>
          match s with
          | Sum.inl a => hl a
          | Sum.inr b => hr b)) :=
    rweq_lamCongr_of_rweq hp
  simpa [copairFactorPath] using rweq_trans hη hlam

end Coproducts

section Functions

variable {A B C : Type u}
variable {f g : A → B}

@[simp] noncomputable def lamAppStep
    (p : ∀ x : A, Path (f x) (g x)) (a : A) :
    Step (Path.app (Path.lamCongr p) a) (p a) := by
  simpa [Path.app] using
    (Step.fun_app_beta (A := B) (α := A) (p := p) (a := a))

@[simp] noncomputable def lamEtaStep (p : Path f g) :
    Step (Path.lamCongr (fun x => Path.app p x)) p :=
  Step.fun_eta p

@[simp] noncomputable def lamAppRwEq
    (p : ∀ x : A, Path (f x) (g x)) (a : A) :
    RwEq (Path.app (Path.lamCongr p) a) (p a) :=
  rweq_of_step (lamAppStep p a)

@[simp] noncomputable def lamEtaRwEq (p : Path f g) :
    RwEq (Path.lamCongr (fun x => Path.app p x)) p :=
  rweq_of_step (lamEtaStep p)

@[simp] noncomputable def curryFn (h : A × B → C) : A → B → C := fun a b => h (a, b)

@[simp] noncomputable def uncurryFn (k : A → B → C) : A × B → C := fun ab => k ab.1 ab.2

noncomputable def curryAdjunctionRwEq
    {h₁ h₂ : A × B → C}
    (p : Path h₁ h₂) :
    RwEq
      (Path.lamCongr (fun a =>
        Path.lamCongr (fun b => Path.app (Path.app (Path.congrArg curryFn p) a) b)))
      (Path.congrArg curryFn p) := by
  have hinner :
      RwEq
        (Path.lamCongr (fun a =>
          Path.lamCongr (fun b => Path.app (Path.app (Path.congrArg curryFn p) a) b)))
        (Path.lamCongr (fun a => Path.app (Path.congrArg curryFn p) a)) := by
    apply rweq_lamCongr_of_rweq
    intro a
    exact rweq_fun_eta (Path.app (Path.congrArg curryFn p) a)
  exact rweq_trans hinner (rweq_fun_eta (Path.congrArg curryFn p))

noncomputable def uncurryAdjunctionRwEq
    {k₁ k₂ : A → B → C}
    (p : Path k₁ k₂) :
    RwEq
      (Path.lamCongr (fun ab => Path.app (Path.congrArg uncurryFn p) ab))
      (Path.congrArg uncurryFn p) :=
  rweq_fun_eta (Path.congrArg uncurryFn p)

end Functions

end ComputationalPaths.TypeFormers
