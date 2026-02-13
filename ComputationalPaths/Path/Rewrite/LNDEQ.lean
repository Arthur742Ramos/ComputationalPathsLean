import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq

/-
# LNDEQ rewrite tags

Enumerates the rewrite mnemonics from Definition 3.21 (plus the two `tt` completions)
and packages their associated `Step`/`Rw` witnesses.
-/

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace LNDEQ

universe u

/-- Enumerates the paper's rule names. -/
inductive Rule where
  | sr
  | ss
  | tr
  | tsr
  | rrr
  | lrr
  | slr
  | srr
  | slss
  | slsss
  | srsr
  | srrrr
  | mx2l1
  | mx2l2
  | mx2r1
  | mx2r2
  | mx3l
  | mx3r
  | mxlam
  | mxsigmaFst
  | mxsigmaSnd
  | mxetaProd
  | mxcase
  | mxetaFun
  | mxetaSigma
  | stss
  | ssbl
  | ssbr
  | sx
  | sxss
  | smss
  | smfst
  | smsnd
  | smcase
  | smsigma
  | tsbll
  | tsbrl
  | tsblr
  | tsbrr
  | tt
  | ttsv
  | tstu
  -- Rules 40-47 from Chapter 5
  | tf      -- Rule 40: τ(μ(r),μ(s)) = μ(τ(r,s)) - definitional
  | cf      -- Rule 41: μ_g(μ_f(p)) = μ_{g∘f}(p) - definitional
  | ci      -- Rule 42: μ_{Id}(p) = p - definitional
  | hp      -- Rule 43: τ(H(x), μ_g(p)) = τ(μ_f(p), H(y)) - homotopy naturality
  | mxc     -- Rule 44: μ_f(ε_∧(p,q)) = ε_∧(μ_g(p), μ_h(q)) - product map congruence
  | mxp     -- Rule 45: μ_f(ρ_x) = ρ_{f(x)} - definitional
  | nxp     -- Rule 46: ν(ρ) = ρ_{f(x)} - definitional
  | xxp     -- Rule 47: ξ(ρ) = ρ - definitional
  deriving DecidableEq, Repr

/-- A tagged `Step` witness along with its source/target paths. -/
structure Instantiation where
  {A : Type u}
  {a b : A}
  (rule : Rule)
  (p q : Path a b)
  (step : Step (A := A) p q)

attribute [simp] Instantiation.step

namespace Instantiation

variable {i : Instantiation}

/-- Recover the underlying `Step`. -/
@[simp] def toStep : Step (A := _) i.p i.q :=
  i.step

/-- Promote the instantiation to a single-step `Rw`. -/
@[simp] def toRw : Rw (A := _) i.p i.q :=
  rw_of_step i.step

/-- Promote the instantiation to the symmetric closure. -/
@[simp] def toRwEq : RwEq (A := _) i.p i.q :=
  rweq_of_step i.step

end Instantiation

/- Smart constructors producing tagged steps for the primitive rules. -/
namespace Builder

section

variable {A : Type u}

@[simp] def instSr (a : A) : Instantiation :=
  { rule := Rule.sr
    , p := Path.symm (Path.refl a)
    , q := Path.refl a
    , step := Step.symm_refl (A := A) a }

@[simp] def instSs {a b : A} (p : Path a b) : Instantiation :=
  { rule := Rule.ss
    , p := Path.symm (Path.symm p)
    , q := p
    , step := Step.symm_symm (A := A) (p := p) }

@[simp] def instTr {x y : A} (p : Path x y) : Instantiation :=
  { rule := Rule.tr
    , p := Path.trans p (Path.symm p)
    , q := Path.refl x
    , step := Step.trans_symm (A := A) (p := p) }

@[simp] def instTsr {x y : A} (p : Path x y) : Instantiation :=
  { rule := Rule.tsr
    , p := Path.trans (Path.symm p) p
    , q := Path.refl y
    , step := Step.symm_trans (A := A) (p := p) }

@[simp] def instRrr {x y : A} (p : Path x y) : Instantiation :=
  { rule := Rule.rrr
    , p := Path.trans p (Path.refl y)
    , q := p
    , step := Step.trans_refl_right (A := A) (p := p) }

@[simp] def instLrr {x y : A} (p : Path x y) : Instantiation :=
  { rule := Rule.lrr
    , p := Path.trans (Path.refl x) p
    , q := p
    , step := Step.trans_refl_left (A := A) (p := p) }

end

section

@[simp] def instSlr (C : Context A B) {a₁ a₂ : A} (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.slr
    , p := Context.substLeft (A := A) (B := B) C (Path.refl (C.fill a₁)) p
    , q := Context.map (A := A) (B := B) C p
    , step := Step.context_subst_left_refl_left (A := A) (B := B) (C := C) (p := p) }

@[simp] def instSrr (C : Context A B) {a₁ a₂ : A} (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.srr
    , p := Context.substRight (A := A) (B := B) C p (Path.refl (C.fill a₂))
    , q := Context.map (A := A) (B := B) C p
    , step := Step.context_subst_right_refl_right (A := A) (B := B) (C := C) (p := p) }

@[simp] def instSlss (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.slss
    , p := Context.substLeft (A := A) (B := B) C
        (Context.substLeft (A := A) (B := B) C r (Path.refl a₁)) p
    , q := Context.substLeft (A := A) (B := B) C r p
    , step := Step.context_subst_left_idempotent (A := A) (B := B)
        (C := C) (r := r) (p := p) }

@[simp] def instSlsss (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.slsss
    , p := Path.symm
        (Context.substLeft (A := A) (B := B) C
          (Context.substLeft (A := A) (B := B) C r (Path.refl a₁)) p)
    , q := Path.symm (Context.substLeft (A := A) (B := B) C r p)
    , step :=
        Step.symm_congr
          (Step.context_subst_left_idempotent (A := A) (B := B)
            (C := C) (r := r) (p := p)) }

@[simp] def instSrsr (C : Context A B) {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) : Instantiation :=
  { rule := Rule.srsr
    , p := Context.substRight (A := A) (B := B) C p
        (Context.substRight (A := A) (B := B) C (Path.refl a₂) t)
    , q := Context.substRight (A := A) (B := B) C p t
    , step := Step.context_subst_right_cancel_inner (A := A)
        (B := B) (C := C) (p := p) (t := t) }

@[simp] def instSrrrr (C : Context A B) {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) : Instantiation :=
  { rule := Rule.srrrr
    , p := Context.substRight (A := A) (B := B) C (Path.refl a₁)
        (Context.substRight (A := A) (B := B) C p t)
    , q := Context.substRight (A := A) (B := B) C p t
    , step := Step.context_subst_right_cancel_outer (A := A)
        (B := B) (C := C) (p := p) (t := t) }

@[simp] def instTsbll (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.tsbll
    , p := Path.trans r (Context.map (A := A) (B := B) C p)
    , q := Context.substLeft (A := A) (B := B) C r p
    , step := Step.context_subst_left_beta (A := A) (B := B)
        (C := C) (r := r) (p := p) }

@[simp] def instTsbrl (C : Context A B) {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) : Instantiation :=
  { rule := Rule.tsbrl
    , p := Path.trans (Context.map (A := A) (B := B) C p) t
    , q := Context.substRight (A := A) (B := B) C p t
    , step := Step.context_subst_right_beta (A := A) (B := B)
        (C := C) (p := p) (t := t) }

@[simp] def instTsblr (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) (t : Path (C.fill a₂) y) : Instantiation :=
  { rule := Rule.tsblr
    , p := Path.trans (Context.substLeft (A := A) (B := B) C r p) t
    , q := Path.trans r (Context.substRight (A := A) (B := B) C p t)
    , step := Step.context_subst_left_assoc (A := A) (B := B)
        (C := C) (r := r) (p := p) (t := t) }

@[simp] def instTsbrr (C : Context A B) {a₁ a₂ : A} {y z : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) (u : Path y z) : Instantiation :=
  { rule := Rule.tsbrr
    , p := Path.trans (Context.substRight (A := A) (B := B) C p t) u
    , q := Context.substRight (A := A) (B := B) C p (Path.trans t u)
    , step := Step.context_subst_right_assoc (A := A) (B := B)
        (C := C) (p := p) (t := t) (u := u) }

end

section

variable {A : Type u} {B : Type u}

@[simp] def instMx2l1 {a₁ a₂ : A} {b₁ b₂ : B}
  (p : Path a₁ a₂) (q : Path b₁ b₂) : Instantiation :=
  { rule := Rule.mx2l1
    , p := Path.congrArg Prod.fst
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q)
    , q := p
    , step := Step.prod_fst_beta (A := A) (B := B) (p := p) (q := q) }

@[simp] def instMx2l2 {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) : Instantiation :=
  { rule := Rule.mx2l2
    , p := Path.congrArg Prod.fst
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q)
    , q := p
    , step := Step.prod_fst_beta (A := A) (B := B) (p := p) (q := q) }

@[simp] def instMx2r1 {a₁ a₂ : A} {b₁ b₂ : B}
    (p : Path a₁ a₂) (q : Path b₁ b₂) : Instantiation :=
  { rule := Rule.mx2r1
    , p := Path.congrArg Prod.snd
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q)
    , q := q
    , step := Step.prod_snd_beta (A := B) (B := A)
        (p := p) (q := q) }

@[simp] def instMx2r2 {a : A} {b₁ b₂ : B}
    (q : Path b₁ b₂) : Instantiation :=
  { rule := Rule.mx2r2
    , p := Path.congrArg Prod.snd
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk
          (Path.refl a) q)
    , q := q
    , step := Step.prod_snd_beta (A := B) (B := A)
        (p := Path.refl a) (q := q) }

@[simp] def instMxetaProd {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) : Instantiation :=
  { rule := Rule.mxetaProd
    , p := Path.prodMk (Path.fst p) (Path.snd p)
    , q := p
    , step := Step.prod_eta (α := α) (β := β) (p := p) }

end

section

variable {A : Type u} {α β : Type u}

@[simp] noncomputable def instMx3l {a₁ a₂ : α} (f : α → A) (g : β → A)
    (p : Path a₁ a₂) : Instantiation :=
  let h : Sum α β → A := fun
    | Sum.inl a => f a
    | Sum.inr b => g b
  let hEq : Sum.rec f g = h := by
    funext x
    cases x <;> rfl
  { rule := Rule.mx3l
    , p := Path.congrArg h (Path.congrArg Sum.inl p)
    , q := Path.congrArg f p
    , step := by
        simpa [h, hEq] using
          (Step.sum_rec_inl_beta (A := A) (α := α) (β := β)
            (f := f) (g := g) (p := p)) }

@[simp] noncomputable def instMx3r {b₁ b₂ : β} (f : α → A) (g : β → A)
    (p : Path b₁ b₂) : Instantiation :=
  let h : Sum α β → A := fun
    | Sum.inl a => f a
    | Sum.inr b => g b
  let hEq : Sum.rec f g = h := by
    funext x
    cases x <;> rfl
  { rule := Rule.mx3r
    , p := Path.congrArg h (Path.congrArg Sum.inr p)
    , q := Path.congrArg g p
    , step := by
        simpa [h, hEq] using
          (Step.sum_rec_inr_beta (A := A) (α := α) (β := β)
            (f := f) (g := g) (p := p)) }

@[simp] noncomputable def instMxcase {a₁ a₂ : Sum α β}
    (f : α → A) (g : β → A)
    {p q : Path a₁ a₂} (h : Step (A := Sum α β) p q) : Instantiation :=
  let C : Context (Sum α β) A := ⟨Sum.rec f g⟩
  { rule := Rule.mxcase
    , p := Context.map (A := Sum α β) (B := A) C p
    , q := Context.map (A := Sum α β) (B := A) C q
    , step := Step.context_congr (A := Sum α β) (B := A)
        (C := C) (p := p) (q := q) h }

@[simp] def instSx {a₁ a₂ : α}
    (p : Path a₁ a₂) : Instantiation :=
  let C : Context α (Sum α β) := ⟨fun a => Sum.inl a⟩
  { rule := Rule.sx
    , p := Path.symm (Context.map (A := α) (B := Sum α β) C p)
    , q := Context.map (A := α) (B := Sum α β) C (Path.symm p)
    , step := Step.context_map_symm (A := α) (B := Sum α β)
        (C := C) (p := p) }

@[simp] def instSxss {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path a₁ a₂) (q : Path b₁ b₂) : Instantiation :=
  { rule := Rule.sxss
    , p := Path.symm (Path.prodMk (p := p) (q := q))
    , q := Path.prodMk (Path.symm p) (Path.symm q)
    , step := Step.prod_mk_symm (A := α) (B := β) (p := p) (q := q) }

@[simp] noncomputable def instSmcase {a₁ a₂ : Sum α β}
    (f : α → A) (g : β → A)
    (p : Path a₁ a₂) : Instantiation :=
  let C : Context (Sum α β) A := ⟨Sum.rec f g⟩
  { rule := Rule.smcase
    , p := Path.symm (Context.map (A := Sum α β) (B := A) C p)
    , q := Context.map (A := Sum α β) (B := A) C (Path.symm p)
    , step := Step.context_map_symm (A := Sum α β) (B := A)
        (C := C) (p := p) }

@[simp] def instMxlam {f g : α → A} (p : ∀ x : α, Path (f x) (g x)) (a : α) : Instantiation :=
  { rule := Rule.mxlam
    , p := Path.congrArg (fun h : α → A => h a)
        (Path.lamCongr (f := f) (g := g) p)
    , q := p a
    , step := Step.fun_app_beta (A := A) (α := α) (f := f) (g := g)
        (p := p) (a := a) }

@[simp] def instSmss {f g : α → A}
    (p : ∀ x : α, Path (f x) (g x)) : Instantiation :=
  { rule := Rule.smss
    , p := Path.symm (Path.lamCongr (f := f) (g := g) p)
    , q := Path.lamCongr (f := g) (g := f) (fun x => Path.symm (p x))
    , step := Step.lam_congr_symm (α := α) (β := A)
        (f := f) (g := g) (p := p) }

@[simp] def instMxetaFun {α β : Type u}
    {f g : α → β} (p : Path f g) : Instantiation :=
  { rule := Rule.mxetaFun
    , p := Path.lamCongr (fun x => Path.app p x)
    , q := p
    , step := Step.fun_eta (α := α) (β := β) (p := p) }

end

section

variable {A : Type u} {B : A → Type u}

@[simp] def instMxsigmaFst {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) : Instantiation :=
  { rule := Rule.mxsigmaFst
    , p := Path.congrArg Sigma.fst (Path.sigmaMk (B := B) p q)
    , q := Path.stepChain (A := A) p.toEq
    , step := Step.sigma_fst_beta (A := A) (B := B)
        (p := p) (q := q) }

@[simp] def instMxsigmaSnd {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path a₁ a₂)
    (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) : Instantiation :=
  { rule := Rule.mxsigmaSnd
    , p := Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q)
    , q := Path.stepChain (A := B a₂)
        (a := Path.transport (A := A) (D := fun a => B a)
                (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b₁)
        (b := b₂) q.toEq
    , step := Step.sigma_snd_beta (A₀ := A) (B := B)
        (p := p) (q := q) }

@[simp] def instMxetaSigma {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
    (p : Path (A := Sigma B) ⟨a₁, b₁⟩ ⟨a₂, b₂⟩) : Instantiation :=
  { rule := Rule.mxetaSigma
    , p := Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)
    , q := p
    , step := Step.sigma_eta (A := A) (B := B) (p := p) }

@[simp] def instSmsigma (C : DepContext A B)
    {a₁ a₂ : A} (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.smsigma
    , p := Path.symm (DepContext.map (A := A) (B := B) C p)
    , q := DepContext.symmMap (A := A) (B := B) C p
    , step := Step.depContext_map_symm (A := A) (B := B)
        (C := C) (p := p) }

end

section

variable {A : Type u} {B : Type u}

@[simp] def instSmfst {a₁ a₂ : Prod A B}
    (p : Path a₁ a₂) : Instantiation :=
  let C : Context (Prod A B) A := ⟨Prod.fst⟩
  { rule := Rule.smfst
    , p := Path.symm (Context.map (A := Prod A B) (B := A) C p)
    , q := Context.map (A := Prod A B) (B := A) C (Path.symm p)
    , step := Step.context_map_symm (A := Prod A B) (B := A)
        (C := C) (p := p) }

@[simp] def instSmsnd {a₁ a₂ : Prod A B}
    (p : Path a₁ a₂) : Instantiation :=
  let C : Context (Prod A B) B := ⟨Prod.snd⟩
  { rule := Rule.smsnd
    , p := Path.symm (Context.map (A := Prod A B) (B := B) C p)
    , q := Context.map (A := Prod A B) (B := B) C (Path.symm p)
    , step := Step.context_map_symm (A := Prod A B) (B := B)
        (C := C) (p := p) }

end

section

variable {A : Type u}

@[simp] def instStss {a b c : A} (p : Path a b) (q : Path b c) : Instantiation :=
  { rule := Rule.stss
    , p := Path.symm (Path.trans p q)
    , q := Path.trans (Path.symm q) (Path.symm p)
    , step := Step.symm_trans_congr (A := A) (p := p) (q := q) }

@[simp] def instSsbl (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) : Instantiation :=
  { rule := Rule.ssbl
    , p := Path.symm (Path.trans r (Context.map (A := A) (B := B) C p))
    , q := Path.symm (Context.substLeft (A := A) (B := B) C r p)
    , step :=
        Step.symm_congr
          (Step.context_subst_left_beta (A := A) (B := B)
            (C := C) (r := r) (p := p)) }

@[simp] def instSsbr (C : Context A B) {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) : Instantiation :=
  { rule := Rule.ssbr
    , p := Path.symm (Path.trans (Context.map (A := A) (B := B) C p) t)
    , q := Path.symm (Context.substRight (A := A) (B := B) C p t)
    , step :=
        Step.symm_congr
          (Step.context_subst_right_beta (A := A) (B := B)
            (C := C) (p := p) (t := t)) }

@[simp] def instTt {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) : Instantiation :=
  { rule := Rule.tt
    , p := Path.trans (Path.trans p q) r
    , q := Path.trans p (Path.trans q r)
    , step := Step.trans_assoc (A := A) (p := p) (q := q) (r := r) }

@[simp] def instTtsv (C : Context A B) {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (v : Path (C.fill a₁) y) : Instantiation :=
  { rule := Rule.ttsv
    , p := Path.trans
        (Context.map (A := A) (B := B) C p)
        (Path.trans
          (Context.map (A := A) (B := B) C (Path.symm p)) v)
    , q := Path.trans
        (Context.map (A := A) (B := B) C
          (Path.trans p (Path.symm p)))
        v
    , step := Step.context_tt_cancel_left (A := A) (B := B)
        (C := C) (p := p) (v := v) }

@[simp] def instTstu (C : Context A B) {a₁ a₂ : A} {x : B}
    (p : Path a₁ a₂) (v : Path x (C.fill a₁)) : Instantiation :=
  { rule := Rule.tstu
    , p := Path.trans
        (Path.trans v (Context.map (A := A) (B := B) C p))
        (Context.map (A := A) (B := B) C (Path.symm p))
    , q := Path.trans v
        (Context.map (A := A) (B := B) C
          (Path.trans p (Path.symm p)))
    , step := Step.context_tt_cancel_right (A := A) (B := B)
        (C := C) (p := p) (v := v) }

/-- Rule 44 (mxc): μ_f(ε_∧(p,q)) ▷ ε_∧(μ_g(p), μ_h(q))
    Product map congruence: congrArg of (g, h) on prodMk equals prodMk of congrArgs -/
@[simp] def instMxc {A B A' B' : Type u}
    {a₁ a₂ : A} {b₁ b₂ : B}
    (g : A → A') (h : B → B')
    (p : Path a₁ a₂) (q : Path b₁ b₂) : Instantiation :=
  { rule := Rule.mxc
    , p := Path.congrArg (fun x : Prod A B => (g x.fst, h x.snd))
        (Path.prodMk p q)
    , q := Path.prodMk (Path.congrArg g p) (Path.congrArg h q)
    , step := Step.prod_map_congrArg (A := A) (B := B) (A' := A') (B' := B')
        (g := g) (h := h) (p := p) (q := q) }

end

/-!
## Definitional Rules (40-42, 45-47)

The following rules are satisfied definitionally in Lean and don't need Step witnesses:

- Rule 40 (tf): `congrArg f (trans p q) = trans (congrArg f p) (congrArg f q)` - by `congrArg_trans`
- Rule 41 (cf): `congrArg g (congrArg f p) = congrArg (g ∘ f) p` - by `congrArg_comp`
- Rule 42 (ci): `congrArg id p = p` - by `congrArg_id`
- Rule 43 (hp): Homotopy naturality - proven as `homotopy_naturality_toEq` in HoTT.lean
- Rule 45 (mxp): `congrArg f (refl a) = refl (f a)` - by rfl
- Rule 46 (nxp): `app (refl f) a = refl (f a)` - by rfl
- Rule 47 (xxp): `lamCongr (fun x => refl (f x)) = refl f` - by rfl

These can be witnessed via `rfl`:
-/

example {A B : Type u} (f : A → B) {a b c : A} (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) = Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

example {A B C : Type u} (f : B → C) (g : A → B) {a b : A} (p : Path a b) :
    Path.congrArg (fun x => f (g x)) p = Path.congrArg f (Path.congrArg g p) :=
  Path.congrArg_comp f g p

example {A : Type u} {a b : A} (p : Path a b) :
    Path.congrArg (fun x => x) p = p :=
  Path.congrArg_id p

example {A B : Type u} (f : A → B) (a : A) :
    Path.congrArg f (Path.refl a) = Path.refl (f a) := rfl

example {A B : Type u} (f : A → B) (a : A) :
    Path.app (Path.refl f) a = Path.refl (f a) := rfl

example {A B : Type u} (f : A → B) :
    Path.lamCongr (fun x => Path.refl (f x)) = Path.refl f := rfl

end Builder

end LNDEQ
end Rewrite
end Path
end ComputationalPaths
