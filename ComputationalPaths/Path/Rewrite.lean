/-
# Rewriting system on computational paths

This module captures the fragment of the `rw`-rewrite system from the paper
concerned with symmetry and transitivity.  We provide the basic rewrite steps
and the reflexive/transitive closure `Rw`, together with its symmetric
reflexive/transitive closure `RwEq`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.SimpleEquiv
import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.LNDEQ
import ComputationalPaths.Path.Rewrite.Termination

/-!
  This file now serves as an umbrella import for the modular rewrite system.
  The legacy monolithic implementation is kept below `#exit` for reference.
-/

#exit

namespace ComputationalPaths.Path

open scoped Quot

universe u v w x

/-- Lightweight equivalence structure used to package mutually inverse maps
without pulling in additional dependencies. -/
structure SimpleEquiv (α : Sort u) (β : Sort v) where
  /-- Forward map. -/
  toFun : α → β
  /-- Inverse map. -/
  invFun : β → α
  /-- Inverse applied after the forward map is the identity. -/
  left_inv : ∀ x : α, invFun (toFun x) = x
  /-- Forward map applied after the inverse is the identity. -/
  right_inv : ∀ y : β, toFun (invFun y) = y

namespace SimpleEquiv

variable {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x}

instance : CoeFun (SimpleEquiv α β) (fun _ => α → β) :=
  ⟨SimpleEquiv.toFun⟩

@[simp] theorem coe_apply (e : SimpleEquiv α β) (x : α) :
    e x = e.toFun x := rfl

/-- Equivalence in the opposite direction. -/
@[simp] def symm (e : SimpleEquiv α β) : SimpleEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

@[simp] theorem symm_apply (e : SimpleEquiv α β) (y : β) :
    e.symm y = e.invFun y := rfl

@[simp] theorem symm_inv_apply (e : SimpleEquiv α β) (x : α) :
    e.symm.invFun x = e x := rfl

/-- Identity equivalence. -/
@[simp] def refl (α : Sort u) : SimpleEquiv α α where
  toFun := id
  invFun := id
  left_inv := by intro x; rfl
  right_inv := by intro x; rfl

/-- Composition of equivalences. -/
@[simp] def comp (e : SimpleEquiv α β) (f : SimpleEquiv β γ) :
    SimpleEquiv α γ where
  toFun := fun x => f.toFun (e.toFun x)
  invFun := fun z => e.invFun (f.invFun z)
  left_inv := by
    intro x
    have hf := f.left_inv (e.toFun x)
    have he := e.left_inv x
    simpa [hf]
  right_inv := by
    intro z
    have he := e.right_inv (f.invFun z)
    have hf := f.right_inv z
    simpa [he]

@[simp] theorem symm_symm (e : SimpleEquiv α β) :
    e.symm.symm = e := rfl

@[simp] theorem comp_apply (e : SimpleEquiv α β)
    (f : SimpleEquiv β γ) (x : α) :
    comp e f x = f (e x) := rfl

@[simp] theorem comp_inv_apply (e : SimpleEquiv α β)
    (f : SimpleEquiv β γ) (z : γ) :
    (comp e f).invFun z = e.invFun (f.invFun z) := rfl

@[simp] theorem comp_refl (e : SimpleEquiv α β) :
    comp e (refl β) = e := by
  cases e
  rfl

@[simp] theorem refl_comp (e : SimpleEquiv α β) :
    comp (refl α) e = e := by
  cases e
  rfl

@[simp] theorem comp_assoc (e : SimpleEquiv α β)
    (f : SimpleEquiv β γ) (g : SimpleEquiv γ δ) :
    comp (comp e f) g = comp e (comp f g) := by
  cases e
  cases f
  cases g
  rfl

@[simp] theorem apply_symm_apply (e : SimpleEquiv α β) (y : β) :
    e (e.symm y) = y := by
  change e.toFun (e.invFun y) = y
  exact e.right_inv y

@[simp] theorem symm_apply_apply (e : SimpleEquiv α β) (x : α) :
    e.symm (e x) = x := by
  change e.invFun (e.toFun x) = x
  exact e.left_inv x

@[ext] theorem ext {e₁ e₂ : SimpleEquiv α β}
    (h₁ : ∀ x : α, e₁ x = e₂ x)
    (h₂ : ∀ y : β, e₁.invFun y = e₂.invFun y) :
    e₁ = e₂ := by
  classical
  cases e₁ with
  | mk toFun₁ invFun₁ left_inv₁ right_inv₁ =>
      cases e₂ with
      | mk toFun₂ invFun₂ left_inv₂ right_inv₂ =>
          have h_toFun : toFun₁ = toFun₂ := funext h₁
          have h_invFun : invFun₁ = invFun₂ := funext h₂
          subst h_toFun
          subst h_invFun
          simp

@[simp] theorem symm_comp (e : SimpleEquiv α β) :
    comp (symm e) e = refl β := by
  apply SimpleEquiv.ext
  · intro y
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.right_inv y
  · intro x
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.right_inv x

@[simp] theorem comp_symm (e : SimpleEquiv α β) :
    comp e (symm e) = refl α := by
  apply SimpleEquiv.ext
  · intro x
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.left_inv x
  · intro y
    simpa [SimpleEquiv.comp, SimpleEquiv.symm, SimpleEquiv.refl]
      using e.left_inv y

end SimpleEquiv

/-- A single rewrite step between computational paths. -/
inductive Step :
  {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  | symm_refl {A : Type u} (a : A) :
      Step (A := A) (symm (Path.refl a)) (Path.refl a)
  | symm_symm {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (symm (symm p)) p
  | trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans (Path.refl a) p) p
  | trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans p (Path.refl b)) p
  | trans_symm {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans p (symm p)) (Path.refl a)
  | symm_trans {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans (symm p) p) (Path.refl b)
  | symm_trans_congr {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
      Step (A := A) (symm (trans p q)) (trans (symm q) (symm p))
  | trans_assoc {A : Type u} {a b c d : A}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      Step (A := A) (trans (trans p q) r) (trans p (trans q r))
  | map2_subst
    {A : Type u} {A₁ : Type u} {B : Type u}
      {a1 a2 : A₁} {b1 b2 : B}
      (f : A₁ → B → A)
      (p : Path (A := A₁) a1 a2)
      (q : Path (A := B) b1 b2) :
      Step (A := A)
        (Path.map2 (A := A₁) (B := B) (C := A) f p q)
        (Path.trans
          (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
          (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2))
  | prod_fst_beta
    {A : Type u} {B : Type u}
      {a1 a2 : A} {b1 b2 : B}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg Prod.fst
          (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q))
        p
  | prod_snd_beta
    {A : Type u} {B : Type u}
      {a1 a2 : B} {b1 b2 : A}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg Prod.snd
          (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q))
        q
  | prod_rec_beta
    {A : Type u} {α β : Type u}
      {a1 a2 : α} {b1 b2 : β}
      (f : α → β → A)
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg (Prod.rec f)
          (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
        (Path.map2 (A := α) (B := β) (C := A) f p q)
  | prod_eta
    {α β : Type u}
      {a₁ a₂ : α} {b₁ b₂ : β}
      (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
      Step (A := Prod α β)
        (Path.prodMk (Path.fst p) (Path.snd p)) p
  | sigma_fst_beta
    {A : Type u} {B : A → Type u}
      {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      (p : Path a1 a2)
      (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
      Step (A := A)
        (Path.congrArg Sigma.fst
        (Path.sigmaMk (B := B) p q))
        (Path.ofEq (A := A) p.toEq)
  | sigma_snd_beta
    {A₀ : Type u} {B : A₀ → Type u}
      {a1 a2 : A₀} {b1 : B a1} {b2 : B a2}
      (p : Path a1 a2)
      (q :
        Path (transport (A := A₀) (D := fun a => B a) p b1) b2) :
      Step (A := B a2)
        (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
        (Path.ofEq
          (A := B a2)
          (a := transport (A := A₀) (D := fun a => B a)
                (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b1)
          (b := b2) q.toEq)
  | sigma_eta
    {A : Type u} {B : A → Type u}
      {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
      Step (A := Sigma B)
        (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p
  | sum_rec_inl_beta
    {A : Type u} {α β : Type u}
      {a1 a2 : α}
      (f : α → A) (g : β → A)
      (p : Path a1 a2) :
      Step (A := A)
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p))
        (Path.congrArg f p)
  | sum_rec_inr_beta
    {A : Type u} {α β : Type u}
      {b1 b2 : β}
      (f : α → A) (g : β → A)
      (p : Path b1 b2) :
      Step (A := A)
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p))
        (Path.congrArg g p)
  | fun_app_beta
    {A : Type u} {α : Type u}
      {f g : α → A}
      (p : ∀ x : α, Path (f x) (g x)) (a : α) :
      Step (A := A)
        (Path.congrArg (fun h : α → A => h a)
          (Path.lamCongr (f := f) (g := g) p))
        (p a)
  | fun_eta
    {α β : Type u}
      {f g : α → β} (p : Path f g) :
      Step (A := α → β)
        (Path.lamCongr (fun x => Path.app p x)) p
  | apd_refl
    {A : Type u} {B : A → Type u}
      (f : ∀ x : A, B x) (a : A) :
      Step (A := B a)
        (Path.apd (A := A) (B := B) f (Path.refl a))
        (Path.refl (f a))
  | transport_refl_beta
    {A : Type u} {B : A → Type u}
      {a : A} (x : B a) :
      Step (A := B a)
        (Path.ofEq (A := B a)
          (a := transport (A := A) (D := fun t => B t)
                  (Path.refl a) x)
          (b := x)
          (transport_refl (A := A) (D := fun t => B t)
            (a := a) (x := x)))
        (Path.refl x)
  | context_congr
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := B)
          (Context.map (A := A) (B := B) C p)
          (Context.map (A := A) (B := B) C q)
  | context_subst_left_beta
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Path.trans r (Context.map (A := A) (B := B) C p))
        (Context.substLeft (A := A) (B := B) C r p)
  | context_subst_left_of_right
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Path.trans r
          (Context.substRight (A := A) (B := B) C p
            (Path.refl (C.fill a₂))))
        (Context.substLeft (A := A) (B := B) C r p)
  | context_subst_left_assoc
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂)
      (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Path.trans (Context.substLeft (A := A) (B := B) C r p) t)
        (Path.trans r
          (Context.substRight (A := A) (B := B) C p t))
  | context_subst_right_assoc
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y z : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y)
      (u : Path y z) :
      Step (A := B)
        (Path.trans
          (Context.substRight (A := A) (B := B) C p t) u)
        (Context.substRight (A := A) (B := B) C p
          (Path.trans t u))
  | biContext_mapLeft_congr
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := C)
          (BiContext.mapLeft (A := A) (B := B) (C := C) K p b)
          (BiContext.mapLeft (A := A) (B := B) (C := C) K q b)
  | biContext_mapRight_congr
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) (a : A) {b₁ b₂ : B}
      {p q : Path b₁ b₂} :
      Step (A := B) p q →
        Step (A := C)
          (BiContext.mapRight (A := A) (B := B) (C := C) K a p)
          (BiContext.mapRight (A := A) (B := B) (C := C) K a q)
  | biContext_map2_congr_left
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
      {p q : Path a₁ a₂} (r : Path b₁ b₂) :
      Step (A := A) p q →
        Step (A := C)
          (BiContext.map2 (A := A) (B := B) (C := C) K p r)
          (BiContext.map2 (A := A) (B := B) (C := C) K q r)
  | biContext_map2_congr_right
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) {q r : Path b₁ b₂} :
      Step (A := B) q r →
        Step (A := C)
          (BiContext.map2 (A := A) (B := B) (C := C) K p q)
          (BiContext.map2 (A := A) (B := B) (C := C) K p r)
  | mapLeft_congr
    {A : Type u} {B : Type u}
      (f : A → B → A) {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := A) (Path.mapLeft (A := A) (B := B) (C := A) f p b)
          (Path.mapLeft (A := A) (B := B) (C := A) f q b)
  | mapRight_congr
    {A : Type u} (f : A → A → A) (a : A) {b₁ b₂ : A}
      {p q : Path b₁ b₂} :
      Step (A := A) p q →
        Step (A := A) (Path.mapRight (A := A) (B := A) (C := A) f a p)
          (Path.mapRight (A := A) (B := A) (C := A) f a q)
  | mapLeft_ofEq
    {A : Type u} {B : Type u}
      (f : A → B → A) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
      Step (A := A)
        (Path.mapLeft (A := A) (B := B) (C := A) f
          (Path.ofEq (A := A) (a := a₁) (b := a₂) h) b)
        (Path.ofEq (A := A) (a := f a₁ b) (b := f a₂ b)
          (_root_.congrArg (fun x => f x b) h))
  | mapRight_ofEq
    {A : Type u} (f : A → A → A) (a : A) {b₁ b₂ : A} (h : b₁ = b₂) :
      Step (A := A)
        (Path.mapRight (A := A) (B := A) (C := A) f a
          (Path.ofEq (A := A) (a := b₁) (b := b₂) h))
        (Path.ofEq (A := A) (a := f a b₁) (b := f a b₂)
          (_root_.congrArg (f a) h))
  | canon {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) p (Path.ofEq p.toEq)
  | symm_congr {A : Type u} {a b : A} {p q : Path a b} :
      Step (A := A) p q → Step (A := A) (Path.symm p) (Path.symm q)
  | trans_congr_left {A : Type u} {a b c : A}
      {p q : Path a b} (r : Path b c) :
      Step (A := A) p q → Step (A := A) (Path.trans p r) (Path.trans q r)
  | trans_congr_right {A : Type u} {a b c : A}
      (p : Path a b) {q r : Path b c} :
      Step (A := A) q r → Step (A := A) (Path.trans p q) (Path.trans p r)

attribute [simp] Step.symm_refl Step.symm_symm Step.trans_refl_left
  Step.trans_refl_right Step.trans_symm Step.symm_trans Step.symm_trans_congr
  Step.trans_assoc Step.map2_subst Step.prod_fst_beta Step.prod_snd_beta
  Step.prod_rec_beta Step.prod_eta Step.sigma_fst_beta Step.sigma_snd_beta Step.sigma_eta
  Step.sum_rec_inl_beta Step.sum_rec_inr_beta Step.fun_app_beta Step.fun_eta Step.apd_refl
  Step.transport_refl_beta
  Step.transport_refl_beta
  Step.context_congr Step.context_subst_left_beta Step.context_subst_left_of_right
  Step.context_subst_left_assoc Step.context_subst_right_assoc
  Step.biContext_mapLeft_congr Step.biContext_mapRight_congr
  Step.biContext_map2_congr_left Step.biContext_map2_congr_right
  Step.mapLeft_congr Step.mapRight_congr Step.mapLeft_ofEq Step.mapRight_ofEq
  Step.symm_congr Step.trans_congr_left Step.trans_congr_right
  Step.context_subst_left_beta Step.context_subst_left_of_right
  Step.context_subst_left_assoc Step.context_subst_right_assoc

@[simp] theorem step_toEq {A : Type u} {a b : A}
    {p q : Path a b} (h : Step p q) :
    p.toEq = q.toEq := by
  induction h with
  | symm_refl _ => simp
  | symm_symm _ => simp
  | trans_refl_left _ => simp
  | trans_refl_right _ => simp
  | trans_symm _ => simp
  | symm_trans _ => simp
  | symm_trans_congr _ _ => simp
  | trans_assoc _ _ _ => simp
  | map2_subst _ _ _ => simp
  | prod_fst_beta _ _ => simp
  | prod_snd_beta _ _ => simp
  | prod_eta _ => simp
  | prod_rec_beta _ _ _ => simp
  | sigma_fst_beta _ _ => simp
  | sigma_snd_beta _ _ => simp
  | sigma_eta _ => simp
  | sum_rec_inl_beta _ _ _ => simp
  | sum_rec_inr_beta _ _ _ => simp
  | fun_app_beta _ _ => simp
  | fun_eta _ => simp
  | apd_refl _ _ => simp
  | transport_refl_beta _ =>
    simp
  | context_congr _ _ ih =>
    cases ih
    rfl
  | context_subst_left_beta _ _ _ =>
    simp [Context.substLeft]
  | context_subst_left_of_right _ _ _ =>
    simp [Context.substLeft, Context.substRight]
  | context_subst_left_assoc _ _ _ _ =>
    simp [Context.substLeft, Context.substRight, Path.trans_assoc]
  | context_subst_right_assoc _ _ _ _ =>
    simp [Context.substRight, Path.trans_assoc]
  | biContext_mapLeft_congr _ _ _ ih =>
    cases ih
    rfl
  | biContext_mapRight_congr _ _ _ ih =>
    cases ih
    rfl
  | biContext_map2_congr_left _ _ _ ih =>
    cases ih
    rfl
  | biContext_map2_congr_right _ _ _ ih =>
    cases ih
    rfl
  | mapLeft_congr _ _ _ ih =>
      cases ih
      simp
  | mapRight_congr _ _ _ ih =>
      cases ih
      simp
  | mapLeft_ofEq _ _ _ =>
      simp
  | mapRight_ofEq _ _ _ =>
      simp
  | symm_congr _ ih =>
      cases ih
      simp
  | trans_congr_left _ _ ih =>
      cases ih
      simp
  | trans_congr_right _ _ ih =>
      cases ih
      simp
  | canon _ =>
      simp

/-- Reflexive/transitive closure of rewrite steps (`rw`-reduction). -/
inductive Rw {A : Type u} {a b : A} : Path a b → Path a b → Prop
  | refl (p : Path a b) : Rw p p
  | tail {p q r : Path a b} : Rw p q → Step (A := A) q r → Rw p r

variable {A : Type u} {a b c : A}

@[simp] theorem rw_toEq {p q : Path a b} (h : Rw p q) :
    p.toEq = q.toEq := by
  induction h with
  | refl => rfl
  | tail h step ih =>
      exact ih.trans (step_toEq step)

@[simp] theorem rw_refl (p : Path a b) : Rw p p :=
  Rw.refl p

theorem rw_of_step {p q : Path a b} (h : Step p q) : Rw p q :=
  Rw.tail (Rw.refl p) h

@[simp] theorem rw_symm_trans_congr {p : Path a b} {q : Path b c} :
    Rw (symm (trans p q)) (trans (symm q) (symm p)) :=
  rw_of_step (Step.symm_trans_congr p q)

@[simp] theorem rw_of_eq {p q : Path a b} (h : p = q) : Rw p q := by
  cases h
  exact rw_refl _

@[simp] theorem rw_congrArg_trans {B : Type v}
    {a b c : A} (f : A → B) (p : Path a b) (q : Path b c) :
    Rw (Path.congrArg f (Path.trans p q))
      (Path.trans (Path.congrArg f p) (Path.congrArg f q)) :=
  rw_of_eq (Path.congrArg_trans (f := f) (p := p) (q := q))

@[simp] theorem rw_congrArg_symm {B : Type v}
    {a b : A} (f : A → B) (p : Path a b) :
    Rw (Path.congrArg f (Path.symm p))
      (Path.symm (Path.congrArg f p)) :=
  rw_of_eq (Path.congrArg_symm (f := f) (p := p))

@[simp] theorem rw_mapLeft_trans {B : Type v} {C : Type w}
    {a1 a2 a3 : A} (f : A → B → C)
    (p : Path a1 a2) (q : Path a2 a3) (b : B) :
    Rw (Path.mapLeft f (Path.trans p q) b)
      (Path.trans (Path.mapLeft f p b) (Path.mapLeft f q b)) :=
  rw_of_eq (Path.mapLeft_trans (f := f) (p := p) (q := q) (b := b))

@[simp] theorem rw_mapLeft_symm {B : Type v} {C : Type w}
    {a1 a2 : A} (f : A → B → C)
    (p : Path a1 a2) (b : B) :
    Rw (Path.mapLeft f (Path.symm p) b)
      (Path.symm (Path.mapLeft f p b)) :=
  rw_of_eq (Path.mapLeft_symm (f := f) (p := p) (b := b))

@[simp] theorem rw_mapLeft_refl {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) (b : B) :
    Rw (Path.mapLeft f (Path.refl a) b) (Path.refl (f a b)) :=
  rw_of_eq (Path.mapLeft_refl (f := f) (a := a) (b := b))

@[simp] theorem rw_mapLeft_ofEq {B : Type v} {C : Type w}
    (f : A → B → C) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
    Rw (Path.mapLeft (A := A) (B := B) (C := C) f
          (Path.ofEq (A := A) (a := a₁) (b := a₂) h) b)
      (Path.ofEq (A := C) (a := f a₁ b) (b := f a₂ b)
        (_root_.congrArg (fun x => f x b) h)) :=
  rw_of_eq (by
    simp [Path.mapLeft, Path.ofEq, Path.congrArg, List.map])

@[simp] theorem rw_mapRight_trans {B : Type v} {C : Type w}
    {b1 b2 b3 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) (q : Path b2 b3) :
    Rw (Path.mapRight f a (Path.trans p q))
      (Path.trans (Path.mapRight f a p) (Path.mapRight f a q)) :=
  rw_of_eq (Path.mapRight_trans (f := f) (a := a) (p := p) (q := q))

@[simp] theorem rw_mapRight_refl {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) (b : B) :
    Rw (Path.mapRight f a (Path.refl b)) (Path.refl (f a b)) :=
  rw_of_eq (Path.mapRight_refl (f := f) (a := a) (b := b))

@[simp] theorem rw_mapRight_ofEq {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) {b₁ b₂ : B} (h : b₁ = b₂) :
    Rw (Path.mapRight (A := A) (B := B) (C := C) f a
          (Path.ofEq (A := B) (a := b₁) (b := b₂) h))
      (Path.ofEq (A := C) (a := f a b₁) (b := f a b₂)
        (_root_.congrArg (f a) h)) :=
  rw_of_eq (by
    simp [Path.mapRight, Path.ofEq, Path.congrArg, List.map])

@[simp] theorem rw_map2_trans
    {A₁ : Type u} {B : Type u}
    {a1 a2 a3 : A₁} {b1 b2 b3 : B}
    (f : A₁ → B → A)
    (p1 : Path (A := A₁) a1 a2) (p2 : Path (A := A₁) a2 a3)
    (q1 : Path (A := B) b1 b2) (q2 : Path (A := B) b2 b3) :
    Rw
      (Path.map2 (A := A₁) (B := B) (C := A) f
        (Path.trans p1 p2) (Path.trans q1 q2))
      (Path.trans
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p1 b1)
        (Path.trans
          (Path.mapLeft (A := A₁) (B := B) (C := A) f p2 b1)
          (Path.trans
            (Path.mapRight (A := A₁) (B := B) (C := A) f a3 q1)
            (Path.mapRight (A := A₁) (B := B) (C := A) f a3 q2)))) :=
  rw_of_eq
    (Path.map2_trans (A := A₁) (B := B) (C := A) (f := f)
      (p1 := p1) (p2 := p2) (q1 := q1) (q2 := q2))

@[simp] theorem rw_map2_refl
    {A₁ : Type u} {B : Type u} (f : A₁ → B → A) (a : A₁) (b : B) :
    Rw (Path.map2 (A := A₁) (B := B) (C := A) f (Path.refl a) (Path.refl b))
      (Path.refl (f a b)) :=
  rw_of_eq (Path.map2_refl (A := A₁) (B := B) (C := A) (f := f) (a := a) (b := b))

@[simp] theorem rw_mapRight_symm {B : Type v} {C : Type w}
    {b1 b2 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) :
    Rw (Path.mapRight f a (Path.symm p))
      (Path.symm (Path.mapRight f a p)) :=
  rw_of_eq (Path.mapRight_symm (f := f) (a := a) (p := p))

/-- Subterm substitution for `map2`. -/
@[simp] theorem rw_map2_subst
    {A₁ : Type u} {B : Type u}
    {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2)
    (q : Path (A := B) b1 b2) :
    Rw
      (Path.map2 (A := A₁) (B := B) (C := A) f p q)
      (Path.trans
        (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2)) :=
  rw_of_step (Step.map2_subst (A₁ := A₁) (B := B) (f := f) p q)

@[simp] theorem rw_transport_refl_beta
    {A : Type u} {B : A → Type u}
    {a : A} (x : B a) :
    Rw
      (Path.ofEq (A := B a)
        (a := transport (A := A) (D := fun t => B t)
                (Path.refl a) x)
        (b := x)
        (transport_refl (A := A) (D := fun t => B t)
          (a := a) (x := x)))
      (Path.refl x) :=
  rw_of_step (Step.transport_refl_beta (A := A) (B := B) (a := a) x)

@[simp] theorem rw_context_subst_left_beta
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    Rw (Path.trans r (Context.map (A := A) (B := B) C p))
      (Context.substLeft (A := A) (B := B) C r p) :=
  rw_of_step
    (Step.context_subst_left_beta (A := A) (B := B) C r p)

@[simp] theorem rw_context_subst_left_of_right
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    Rw (Path.trans r
        (Context.substRight (A := A) (B := B) C p
          (Path.refl (C.fill a₂))))
      (Context.substLeft (A := A) (B := B) C r p) :=
  rw_of_step
    (Step.context_subst_left_of_right (A := A) (B := B) C r p)

@[simp] theorem rw_context_subst_left_assoc
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂)
    (t : Path (C.fill a₂) y) :
    Rw (Path.trans
        (Context.substLeft (A := A) (B := B) C r p) t)
      (Path.trans r
        (Context.substRight (A := A) (B := B) C p t)) :=
  rw_of_step
    (Step.context_subst_left_assoc (A := A) (B := B) C r p t)

@[simp] theorem rw_context_subst_right_assoc
    {A : Type u} {B : Type u}
    (C : Context A B) {a₁ a₂ : A} {y z : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y)
    (u : Path y z) :
    Rw (Path.trans
        (Context.substRight (A := A) (B := B) C p t) u)
      (Context.substRight (A := A) (B := B) C p (Path.trans t u)) :=
  rw_of_step
    (Step.context_subst_right_assoc (A := A) (B := B) C p t u)

@[simp] theorem rw_trans_congr_left {a b c : A}
  {p q : Path a b} (r : Path b c) (h : Rw p q) :
  Rw (Path.trans p r) (Path.trans q r) := by
  induction h with
  | refl =>
    exact Rw.refl (Path.trans p r)
  | tail _ step ih =>
    exact Rw.tail ih (Step.trans_congr_left r step)

@[simp] theorem rw_trans_congr_right {a b c : A}
  (p : Path a b) {q r : Path b c} (h : Rw q r) :
  Rw (Path.trans p q) (Path.trans p r) := by
  induction h with
  | refl =>
    exact Rw.refl (Path.trans p q)
  | tail _ step ih =>
    exact Rw.tail ih (Step.trans_congr_right p step)

/-- A unary action on paths that is compatible with rewrite steps. -/
structure RewriteLift (A : Type u) (B : Type u) where
  /-- Object function describing how endpoints are transported. -/
  obj : A → B
  /-- Map a path in `A` to a path in `B`. -/
  map :
    ∀ {a b : A},
      Path (A := A) a b → Path (A := B) (obj a) (obj b)
  /-- Transport of rewrite steps along the action. -/
  step_congr :
    ∀ {a b : A} {p q : Path (A := A) a b},
      Step (A := A) p q →
        Step (A := B) (map p) (map q)

namespace RewriteLift

variable {A : Type u} {B : Type u}

@[simp] theorem rw_of_rw (F : RewriteLift A B)
    {a b : A} {p q : Path (A := A) a b}
    (h : Rw (A := A) p q) :
    Rw (A := B) (F.map p) (F.map q) := by
  induction h with
  | refl =>
      exact Rw.refl (F.map p)
  | tail _ step ih =>
      exact Rw.tail ih (F.step_congr step)

@[simp] def ofContext (C : Context A B) : RewriteLift A B where
  obj := C.fill
  map := fun {_ _} p => Context.map (A := A) (B := B) C p
  step_congr := fun {_ _ _ _} step =>
    Step.context_congr (A := A) (B := B) C step

@[simp] def ofBiContextLeft (K : BiContext A B C) (b₀ : B) :
  RewriteLift A C where
  obj := fun a => K.fill a b₀
  map := fun {_ _} p =>
    BiContext.mapLeft (A := A) (B := B) (C := C) K p b₀
  step_congr := fun {_ _ _ _} step =>
    Step.biContext_mapLeft_congr (A := A) (B := B) (C := C)
      (K := K) (b := b₀) step

@[simp] def ofBiContextRight (K : BiContext A B C) (a : A) :
  RewriteLift B C where
  obj := fun b => K.fill a b
  map := fun {_ _} p =>
    BiContext.mapRight (A := A) (B := B) (C := C) K a p
  step_congr := fun {_ _ _ _} step =>
    Step.biContext_mapRight_congr (A := A) (B := B) (C := C)
      (K := K) (a := a) step

end RewriteLift

@[simp] theorem rw_context_map_of_rw {A : Type u} {B : Type u}
  (Ctx : Context A B) {a₁ a₂ : A}
  {p q : Path a₁ a₂} (h : Rw (A := A) p q) :
  Rw (Context.map (A := A) (B := B) Ctx p)
    (Context.map (A := A) (B := B) Ctx q) := by
  simpa using
    (RewriteLift.ofContext (A := A) (B := B) Ctx).rw_of_rw h

@[simp] theorem rw_biContext_mapLeft_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} (b : B)
  {p q : Path a₁ a₂} (h : Rw (A := A) p q) :
  Rw (BiContext.mapLeft (A := A) (B := B) (C := C) K p b)
    (BiContext.mapLeft (A := A) (B := B) (C := C) K q b) := by
  simpa using
    (RewriteLift.ofBiContextLeft (A := A) (B := B) (C := C)
      (K := K) (b₀ := b)).rw_of_rw h

@[simp] theorem rw_biContext_mapRight_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) (a : A) {b₁ b₂ : B}
  {p q : Path b₁ b₂} (h : Rw (A := B) p q) :
  Rw (BiContext.mapRight (A := A) (B := B) (C := C) K a p)
    (BiContext.mapRight (A := A) (B := B) (C := C) K a q) := by
  simpa using
    (RewriteLift.ofBiContextRight (A := A) (B := B) (C := C)
      (K := K) (a := a)).rw_of_rw h

@[simp] theorem rw_biContext_map2_left_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} (r : Path b₁ b₂) (h : Rw (A := A) p q) :
  Rw (BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (BiContext.map2 (A := A) (B := B) (C := C) K q r) := by
  induction h with
  | refl =>
      exact Rw.refl (BiContext.map2 (A := A) (B := B) (C := C) K p r)
  | tail _ step ih =>
      exact Rw.tail ih
        (Step.biContext_map2_congr_left (A := A) (B := B) (C := C)
          (K := K) (r := r) step)

@[simp] theorem rw_biContext_map2_right_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  (p : Path a₁ a₂) {q r : Path b₁ b₂} (h : Rw (A := B) q r) :
  Rw (BiContext.map2 (A := A) (B := B) (C := C) K p q)
    (BiContext.map2 (A := A) (B := B) (C := C) K p r) := by
  induction h with
  | refl =>
      exact Rw.refl (BiContext.map2 (A := A) (B := B) (C := C) K p q)
  | tail _ step ih =>
      exact Rw.tail ih
        (Step.biContext_map2_congr_right (A := A) (B := B) (C := C)
          (K := K) (p := p) step)

@[simp] theorem rw_mapLeft_of_rw {B : Type u}
  (f : A → B → A) {a₁ a₂ : A} (b : B)
  {p q : Path a₁ a₂} (h : Rw p q) :
  Rw (Path.mapLeft f p b) (Path.mapLeft f q b) := by
  classical
  let Ctx : Context A A := ⟨fun a => f a b⟩
  simpa [Ctx, Context.map, Path.mapLeft] using
    (rw_context_map_of_rw (A := A) (B := A) (Ctx := Ctx) h)

@[simp] theorem rw_mapRight_of_rw
  (f : A → A → A) (a : A) {b₁ b₂ : A}
  {p q : Path b₁ b₂} (h : Rw p q) :
  Rw (Path.mapRight f a p) (Path.mapRight f a q) := by
  classical
  let Ctx : Context A A := ⟨fun b => f a b⟩
  simpa [Ctx, Context.map, Path.mapRight] using
    (rw_context_map_of_rw (A := A) (B := A) (Ctx := Ctx) h)



@[simp] theorem rw_trans {p q r : Path a b}
    (h1 : Rw p q) (h2 : Rw q r) : Rw p r :=
  match h2 with
  | Rw.refl _ => h1
  | Rw.tail h2 step => Rw.tail (rw_trans h1 h2) step

@[simp] theorem rw_biContext_map2_of_rw {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} {r s : Path b₁ b₂}
  (hp : Rw (A := A) p q) (hq : Rw (A := B) r s) :
  Rw (BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (BiContext.map2 (A := A) (B := B) (C := C) K q s) := by
  refine (rw_trans (A := C)
    (a := K.fill a₁ b₁)
    (b := K.fill a₂ b₂)
    (p := BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (q := BiContext.map2 (A := A) (B := B) (C := C) K q r)
    (r := BiContext.map2 (A := A) (B := B) (C := C) K q s) ?_ ?_)
  · exact
      (rw_biContext_map2_left_of_rw (A := A) (B := B) (C := C)
        (K := K) (r := r) hp)
  · exact
      (rw_biContext_map2_right_of_rw (A := A) (B := B) (C := C)
        (K := K) (p := q) hq)

@[simp] theorem rw_map2_of_rw {A : Type u} {B : Type u} {C : Type u}
  (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} {r s : Path b₁ b₂}
  (hp : Rw (A := A) p q) (hq : Rw (A := B) r s) :
  Rw (Path.map2 (A := A) (B := B) (C := C) f p r)
    (Path.map2 (A := A) (B := B) (C := C) f q s) := by
  simpa using
    (rw_biContext_map2_of_rw
      (A := A) (B := B) (C := C) (K := ⟨f⟩)
      (p := p) (q := q) (r := r) (s := s) hp hq)

/-- Symmetry for `map2` paths. -/
@[simp] theorem rw_map2_symm
    {A₁ : Type u} {B : Type u}
    {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2)
    (q : Path (A := B) b1 b2) :
    Rw
      (Path.map2 (A := A₁) (B := B) (C := A) f (Path.symm p) (Path.symm q))
      (Path.symm (Path.map2 (A := A₁) (B := B) (C := A) f p q)) := by
  have h :=
    rw_of_step
      (Step.map2_subst (A₁ := A₁) (B := B) (f := f)
        (p := Path.symm p) (q := Path.symm q))
  have h2 :=
    Path.map2_symm (A := A₁) (B := B) (C := A) f p q
  exact rw_trans h (rw_of_eq h2.symm)

/-- The paper's `sr` reduction: `symm (refl a)` collapses to `refl a`. -/
@[simp] theorem rw_sr {A : Type u} (a : A) :
    Rw (Path.symm (Path.refl a)) (Path.refl a) :=
  rw_of_step (Step.symm_refl (A := A) a)

/-- The paper's `ss` reduction: applying symmetry twice is a no-op. -/
@[simp] theorem rw_ss {A : Type u} {a b : A} (p : Path a b) :
    Rw (Path.symm (Path.symm p)) p :=
  rw_of_step (Step.symm_symm (A := A) (p := p))

/-- The paper's `tt` reduction: reassociate triple compositions. -/
@[simp] theorem rw_tt {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    Rw (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rw_of_step (Step.trans_assoc (A := A) (a := a) (b := b)
    (c := c) (d := d) p q r)

@[simp] theorem rw_cmpA_refl_left {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans (Path.refl a) p) p :=
  rw_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p)

@[simp] theorem rw_cmpA_refl_right {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans p (Path.refl b)) p :=
  rw_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) p)

@[simp] theorem rw_cmpA_inv_right {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans p (Path.symm p)) (Path.refl a) :=
  rw_of_step (Step.trans_symm (A := A) (a := a) (b := b) p)

@[simp] theorem rw_cmpA_inv_left {A : Type u} {a b : A}
    (p : Path a b) :
    Rw (Path.trans (Path.symm p) p) (Path.refl b) :=
  rw_of_step (Step.symm_trans (A := A) (a := a) (b := b) p)

/-- Beta-style reduction for `Prod.fst` applied to a path produced from component paths. -/
@[simp] theorem rw_prod_fst_beta {A : Type u} {B : Type u}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    Rw (Path.congrArg Prod.fst
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q)) p :=
  rw_of_step (Step.prod_fst_beta (B := B) p q)

/-- Beta-style reduction for `Prod.snd` applied to a path produced from component paths. -/
@[simp] theorem rw_prod_snd_beta {B : Type u} {A : Type u}
    {a1 a2 : B} {b1 b2 : A}
    (p : Path a1 a2) (q : Path b1 b2) :
    Rw (Path.congrArg Prod.snd
        (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q)) q :=
  rw_of_step (Step.prod_snd_beta (B := B) p q)

/-- Beta-style reduction for `Prod.rec` applied to a pair path. -/
@[simp] theorem rw_prod_rec_beta {α β : Type u} {A : Type u}
    (f : α → β → A)
    {a1 a2 : α} {b1 b2 : β}
    (p : Path a1 a2) (q : Path b1 b2) :
    Rw
      (Path.congrArg (Prod.rec f)
        (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
      (Path.map2 (A := α) (B := β) (C := A) f p q) :=
  rw_of_step (Step.prod_rec_beta (α := α) (β := β) (f := f) p q)

/-- Eta-style reduction for product paths built from their projections. -/
@[simp] theorem rw_prod_eta {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
    Rw (Path.prodMk (Path.fst p) (Path.snd p)) p :=
  rw_of_step (Step.prod_eta (α := α) (β := β) p)

@[simp] theorem rw_sigma_fst_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Rw
      (Path.congrArg Sigma.fst
        (Path.sigmaMk (B := B) p q))
      (Path.ofEq (A := A) p.toEq) :=
  rw_of_step (Step.sigma_fst_beta (A := A) (B := B) p q)

@[simp] theorem rw_sigma_snd_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    Rw
      (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.ofEq
        (A := B a2)
        (a := transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b1)
        (b := b2) q.toEq) :=
  rw_of_step (Step.sigma_snd_beta (A₀ := A) (B := B) p q)

/-- Eta-style reduction for dependent pairs built from their projections. -/
@[simp] theorem rw_sigma_eta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
    Rw (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p :=
  rw_of_step (Step.sigma_eta (A := A) (B := B) p)

@[simp] theorem rw_apd_refl {A : Type u} {B : A → Type u}
    (f : ∀ x : A, B x) (a : A) :
    Rw
      (Path.apd (A := A) (B := B) f (Path.refl a))
      (Path.refl (f a)) :=
  rw_of_step (Step.apd_refl (A := A) (B := B) f a)

/-- Beta-style reduction for `Sum.rec` applied to a left injection. -/
@[simp] theorem rw_sum_rec_inl_beta {α β : Type u} {A : Type u}
    {a1 a2 : α} (f : α → A) (g : β → A) (p : Path a1 a2) :
    Rw
      (Path.congrArg (Sum.rec f g)
        (Path.congrArg Sum.inl p))
      (Path.congrArg f p) :=
  rw_of_step (Step.sum_rec_inl_beta (α := α) (β := β) (f := f) (g := g) p)

/-- Beta-style reduction for `Sum.rec` applied to a right injection. -/
@[simp] theorem rw_sum_rec_inr_beta {α β : Type u} {A : Type u}
    {b1 b2 : β} (f : α → A) (g : β → A) (p : Path b1 b2) :
    Rw
      (Path.congrArg (Sum.rec f g)
        (Path.congrArg Sum.inr p))
      (Path.congrArg g p) :=
  rw_of_step (Step.sum_rec_inr_beta (α := α) (β := β) (f := f) (g := g) p)

/-- Beta-style reduction for evaluating a lambda-generated path at an argument. -/
@[simp] theorem rw_fun_app_beta {α : Type u}
    {f g : α → A} (p : ∀ x : α, Path (f x) (g x)) (a : α) :
    Rw
      (Path.congrArg (fun h : α → A => h a)
        (Path.lamCongr (f := f) (g := g) p))
      (p a) :=
  rw_of_step (Step.fun_app_beta (A := A) (α := α) p a)

/-- Eta-style reduction rebuilding a function path from pointwise applications. -/
@[simp] theorem rw_fun_eta {α β : Type u}
    {f g : α → β} (p : Path f g) :
    Rw
      (Path.lamCongr (fun x => Path.app p x))
      p :=
  rw_of_step (Step.fun_eta (α := α) (β := β) (p := p))

/-- Pointwise `Rw` hypotheses lift to a path between functions. -/
@[simp] theorem rw_lamCongr_of_rw {A : Type u} {B : Type v}
    {f g : A → B}
    {p q : ∀ x : A, Path (f x) (g x)}
    (h : ∀ x : A, Rw (p x) (q x)) :
    Rw (Path.lamCongr p) (Path.lamCongr q) := by
  classical
  have hxProof :
      ∀ x, (p x).proof = (q x).proof := fun x => by
        have hx := rw_toEq (h x)
        cases hx
        simp
  have hx : Path.lamCongr p = Path.lamCongr q := by
    have hxFun := funext hxProof
    cases hxFun
    simp [Path.lamCongr]
  exact rw_of_eq hx

/-! ### Normal forms and normalization -/

/-- Predicate asserting that a computational path is already in canonical
normal form, i.e. it agrees with the `Path.ofEq` representative of its
propositional equality witness. -/
def IsNormal {A : Type u} {a b : A} (p : Path a b) : Prop :=
  p = Path.ofEq p.toEq

@[simp] theorem isNormal_iff {A : Type u} {a b : A} (p : Path a b) :
    IsNormal (A := A) (a := a) (b := b) p ↔ p = Path.ofEq p.toEq :=
  Iff.rfl

@[simp] theorem isNormal_ofEq {A : Type u} {a b : A} (h : a = b) :
    IsNormal (A := A) (a := a) (b := b) (Path.ofEq (A := A) (a := a) (b := b) h) := by
  unfold IsNormal
  simp

/-- The canonical normal form associated to a computational path. -/
@[simp] def normalize {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Path.ofEq (A := A) (a := a) (b := b) p.toEq

@[simp] theorem normalize_isNormal {A : Type u} {a b : A}
    (p : Path a b) :
    IsNormal (A := A) (a := a) (b := b) (normalize p) := by
  unfold normalize IsNormal
  simp

/-- Normal forms packaged with their witnesses. -/
structure NormalForm (A : Type u) (a b : A) where
  /-- Canonical representative of the `Rw`-class. -/
  path : Path a b
  /-- Proof that `path` is already in normal form. -/
  isNormal : IsNormal (A := A) (a := a) (b := b) path

/-- Compute the normal form of a computational path. -/
@[simp] def normalizeForm {A : Type u} {a b : A}
    (p : Path a b) : NormalForm A a b :=
  { path := normalize p
    isNormal := normalize_isNormal (A := A) (a := a) (b := b) p }

@[simp] theorem normalizeForm_path {A : Type u} {a b : A}
    (p : Path a b) :
    (normalizeForm (A := A) (a := a) (b := b) p).path = normalize p := rfl

theorem normalizeForm_sound {A : Type u} {a b : A} (p : Path a b) :
    Rw (A := A) (a := a) (b := b) p
      (normalizeForm (A := A) (a := a) (b := b) p).path :=
  by simpa using rw_normalizes (A := A) (a := a) (b := b) (p := p)

theorem normalizeForm_unique {A : Type u} {a b : A}
    (p : Path a b) {n : NormalForm A a b}
    (h : Rw (A := A) (a := a) (b := b) p n.path) :
    n.path = normalize p := by
  have := normalize_eq_of_rw (A := A) (a := a) (b := b)
      (p := p) (q := n.path) h n.isNormal
  simpa [normalizeForm_path] using this

/-- Eta-style reduction rebuilding a function path from pointwise applications. -/
/- Symmetric reflexive/transitive closure generated by rewrite steps. -/
inductive RwEq {A : Type u} {a b : A} : Path a b → Path a b → Prop
  | refl (p : Path a b) : RwEq p p
  | step {p q : Path a b} : Step p q → RwEq p q
  | symm {p q : Path a b} : RwEq p q → RwEq q p
  | trans {p q r : Path a b} : RwEq p q → RwEq q r → RwEq p r

@[simp] theorem rweq_refl (p : Path a b) : RwEq p p :=
  RwEq.refl p

theorem rweq_of_step {p q : Path a b} (h : Step p q) : RwEq p q :=
  RwEq.step h

@[simp] theorem rweq_toEq {p q : Path a b} (h : RwEq p q) :
    p.toEq = q.toEq := by
  induction h with
  | refl => rfl
  | step h => exact step_toEq h
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

@[simp] theorem normalize_of_rweq {p q : Path a b} (h : RwEq p q) :
    normalize (A := A) (a := a) (b := b) p =
      normalize (A := A) (a := a) (b := b) q := by
  unfold normalize
  have := rweq_toEq (A := A) (a := a) (b := b) (p := p) (q := q) h
  cases this
  rfl

@[simp] theorem normalizeForm_eq_of_rweq {p q : Path a b} (h : RwEq p q) :
    normalizeForm (A := A) (a := a) (b := b) p =
      normalizeForm (A := A) (a := a) (b := b) q := by
  unfold normalizeForm
  have hnorm := normalize_of_rweq (A := A) (a := a) (b := b) (p := p) (q := q) h
  cases hnorm
  simp


@[simp] theorem rweq_symm {p q : Path a b} (h : RwEq p q) : RwEq q p :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step h => RwEq.symm (RwEq.step h)
  | RwEq.symm h => h
  | RwEq.trans h1 h2 => RwEq.trans (rweq_symm h2) (rweq_symm h1)

@[simp] theorem rweq_trans {p q r : Path a b} (h1 : RwEq p q) (h2 : RwEq q r) :
    RwEq p r :=
  RwEq.trans h1 h2

namespace RewriteLift

variable {A : Type u} {B : Type u}

@[simp] theorem rweq_of_rweq (F : RewriteLift A B)
  {a b : A} {p q : Path (A := A) a b}
  (h : RwEq p q) :
  RwEq (F.map p) (F.map q) :=
  by
  induction h with
  | refl _ => exact RwEq.refl _
  | step hStep =>
    exact RwEq.step (F.step_congr hStep)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ =>
    exact RwEq.trans ih₁ ih₂

end RewriteLift

@[simp] theorem rweq_context_map_of_rweq {A : Type u} {B : Type u}
  (Ctx : Context A B) {a₁ a₂ : A}
  {p q : Path a₁ a₂} (h : RwEq p q) :
  RwEq (Context.map (A := A) (B := B) Ctx p)
    (Context.map (A := A) (B := B) Ctx q) := by
  simpa using
    (RewriteLift.rweq_of_rweq
      (A := A) (B := B)
      (F := RewriteLift.ofContext (A := A) (B := B) Ctx)
      (p := p) (q := q) h)

@[simp] theorem rweq_biContext_mapLeft_of_rweq
  {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} (b : B)
  {p q : Path a₁ a₂} (h : RwEq p q) :
  RwEq (BiContext.mapLeft (A := A) (B := B) (C := C) K p b)
    (BiContext.mapLeft (A := A) (B := B) (C := C) K q b) := by
  simpa using
    (RewriteLift.rweq_of_rweq
      (A := A) (B := C)
      (F := RewriteLift.ofBiContextLeft (A := A) (B := B) (C := C)
        (K := K) (b₀ := b))
      (p := p) (q := q) h)

@[simp] theorem rweq_biContext_mapRight_of_rweq
  {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) (a : A) {b₁ b₂ : B}
  {p q : Path b₁ b₂} (h : RwEq p q) :
  RwEq (BiContext.mapRight (A := A) (B := B) (C := C) K a p)
    (BiContext.mapRight (A := A) (B := B) (C := C) K a q) := by
  simpa using
    (RewriteLift.rweq_of_rweq
      (A := B) (B := C)
      (F := RewriteLift.ofBiContextRight (A := A) (B := B) (C := C)
        (K := K) (a := a))
      (p := p) (q := q) h)

@[simp] theorem rweq_mapLeft_of_rweq {B : Type u}
  (f : A → B → A) {a₁ a₂ : A} (b : B)
  {p q : Path a₁ a₂} (h : RwEq p q) :
  RwEq (Path.mapLeft f p b) (Path.mapLeft f q b) := by
  classical
  let Ctx : Context A A := ⟨fun a => f a b⟩
  simpa [Ctx, Context.map, Path.mapLeft] using
    (rweq_context_map_of_rweq (A := A) (B := A) (Ctx := Ctx) h)

@[simp] theorem rweq_mapRight_of_rweq
  (f : A → A → A) (a : A) {b₁ b₂ : A}
  {p q : Path b₁ b₂} (h : RwEq p q) :
  RwEq (Path.mapRight f a p) (Path.mapRight f a q) := by
  classical
  let Ctx : Context A A := ⟨fun b => f a b⟩
  simpa [Ctx, Context.map, Path.mapRight] using
    (rweq_context_map_of_rweq (A := A) (B := A) (Ctx := Ctx) h)

@[simp] theorem rweq_biContext_map2_left_of_rweq
  {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} (r : Path b₁ b₂) (h : RwEq p q) :
  RwEq (BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (BiContext.map2 (A := A) (B := B) (C := C) K q r) := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step step =>
      exact RwEq.step
        (Step.biContext_map2_congr_left (A := A) (B := B) (C := C)
          (K := K) (r := r) step)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

@[simp] theorem rweq_biContext_map2_right_of_rweq
  {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  (p : Path a₁ a₂) {q r : Path b₁ b₂} (h : RwEq q r) :
  RwEq (BiContext.map2 (A := A) (B := B) (C := C) K p q)
    (BiContext.map2 (A := A) (B := B) (C := C) K p r) := by
  induction h with
  | refl _ => exact RwEq.refl _
  | step step =>
      exact RwEq.step
        (Step.biContext_map2_congr_right (A := A) (B := B) (C := C)
          (K := K) (p := p) step)
  | symm _ ih => exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ => exact RwEq.trans ih₁ ih₂

@[simp] theorem rweq_biContext_map2_of_rweq
  {A : Type u} {B : Type u} {C : Type u}
  (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} {r s : Path b₁ b₂}
  (hp : RwEq p q) (hq : RwEq r s) :
  RwEq (BiContext.map2 (A := A) (B := B) (C := C) K p r)
    (BiContext.map2 (A := A) (B := B) (C := C) K q s) :=
  rweq_trans
    (rweq_biContext_map2_left_of_rweq (A := A) (B := B) (C := C)
      (K := K) (r := r) hp)
    (rweq_biContext_map2_right_of_rweq (A := A) (B := B) (C := C)
      (K := K) (p := q) (h := hq))

@[simp] theorem rweq_map2_of_rweq {A : Type u} {B : Type u} {C : Type u}
  (f : A → B → C) {a₁ a₂ : A} {b₁ b₂ : B}
  {p q : Path a₁ a₂} {r s : Path b₁ b₂}
  (hp : RwEq p q) (hq : RwEq r s) :
  RwEq (Path.map2 (A := A) (B := B) (C := C) f p r)
    (Path.map2 (A := A) (B := B) (C := C) f q s) :=
  rweq_biContext_map2_of_rweq
    (A := A) (B := B) (C := C)
    (K := ⟨f⟩) (p := p) (q := q) (r := r) (s := s) hp hq

@[simp] theorem rweq_context_subst_left_beta
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    RwEq (Path.trans r (Context.map (A := A) (B := B) C p))
      (Context.substLeft (A := A) (B := B) C r p) :=
  rweq_of_step
    (Step.context_subst_left_beta (A := A) (B := B) C r p)

@[simp] theorem rweq_context_subst_left_of_right
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
    RwEq (Path.trans r
        (Context.substRight (A := A) (B := B) C p
          (Path.refl (C.fill a₂))))
      (Context.substLeft (A := A) (B := B) C r p) :=
  rweq_of_step
    (Step.context_subst_left_of_right (A := A) (B := B) C r p)

@[simp] theorem rweq_context_subst_left_assoc
    {A : Type u} {B : Type u}
    (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
    (r : Path x (C.fill a₁)) (p : Path a₁ a₂)
    (t : Path (C.fill a₂) y) :
    RwEq (Path.trans
        (Context.substLeft (A := A) (B := B) C r p) t)
      (Path.trans r
        (Context.substRight (A := A) (B := B) C p t)) :=
  rweq_of_step
    (Step.context_subst_left_assoc (A := A) (B := B) C r p t)

@[simp] theorem rweq_context_subst_right_assoc
    {A : Type u} {B : Type u}
    (C : Context A B) {a₁ a₂ : A} {y z : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y)
    (u : Path y z) :
    RwEq (Path.trans
        (Context.substRight (A := A) (B := B) C p t) u)
      (Context.substRight (A := A) (B := B) C p (Path.trans t u)) :=
  rweq_of_step
    (Step.context_subst_right_assoc (A := A) (B := B) C p t u)

@[simp] theorem rweq_transport_refl_beta
    {A : Type u} {B : A → Type u}
    {a : A} (x : B a) :
    RwEq
      (Path.ofEq (A := B a)
        (a := transport (A := A) (D := fun t => B t)
                (Path.refl a) x)
        (b := x)
        (transport_refl (A := A) (D := fun t => B t)
          (a := a) (x := x)))
      (Path.refl x) :=
  rweq_of_step (Step.transport_refl_beta (A := A) (B := B) (a := a) x)

@[simp] theorem rweq_sr {A : Type u} (a : A) :
    RwEq (Path.symm (Path.refl a)) (Path.refl a) :=
  rweq_of_step (Step.symm_refl (A := A) a)

@[simp] theorem rweq_ss {A : Type u} {a b : A} (p : Path a b) :
    RwEq (Path.symm (Path.symm p)) p :=
  rweq_of_step (Step.symm_symm (A := A) (p := p))

@[simp] theorem rweq_tt {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) :
    RwEq (Path.trans (Path.trans p q) r)
      (Path.trans p (Path.trans q r)) :=
  rweq_of_step (Step.trans_assoc (A := A) (a := a) (b := b)
    (c := c) (d := d) p q r)

@[simp] theorem rweq_cmpA_refl_left {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (Path.trans (Path.refl a) p) p :=
  rweq_of_step (Step.trans_refl_left (A := A) (a := a) (b := b) p)

@[simp] theorem rweq_cmpA_refl_right {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_of_step (Step.trans_refl_right (A := A) (a := a) (b := b) p)

@[simp] theorem rweq_cmpA_inv_right {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_step (Step.trans_symm (A := A) (a := a) (b := b) p)

@[simp] theorem rweq_cmpA_inv_left {A : Type u} {a b : A}
    (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_step (Step.symm_trans (A := A) (a := a) (b := b) p)

section Setoid

/-- Rewrite equality induces a setoid on computational paths. -/
def rwEqSetoid (A : Type u) (a b : A) : Setoid (Path a b) where
  r := RwEq
  iseqv :=
    { refl := fun p => rweq_refl (p := p)
      symm := fun {_ _} h => rweq_symm h
      trans := fun {_ _ _} h₁ h₂ => rweq_trans h₁ h₂ }

@[simp] theorem rwEqSetoid_r {A : Type u} {a b : A} :
    (rwEqSetoid A a b).r = RwEq :=
  rfl

instance pathRwEqSetoid (A : Type u) (a b : A) :
    Setoid (Path a b) :=
  rwEqSetoid A a b

/-- Paths modulo rewrite equality, mirroring the paper's notion of canonical proofs. -/
abbrev PathRwQuot (A : Type u) (a b : A) :=
  Quot (rwEqSetoid A a b).r

end Setoid

@[simp] theorem rweq_of_eq {p q : Path a b} (h : p = q) : RwEq p q := by
  cases h
  exact RwEq.refl _

@[simp] theorem rweq_symm_congr {p q : Path a b}
    (h : RwEq p q) : RwEq (Path.symm p) (Path.symm q) :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step s => RwEq.step (Step.symm_congr s)
  | RwEq.symm h => RwEq.symm (rweq_symm_congr h)
  | RwEq.trans h₁ h₂ =>
      RwEq.trans (rweq_symm_congr h₁) (rweq_symm_congr h₂)

@[simp] theorem rweq_trans_congr_left {a b c : A}
    {p q : Path a b} (r : Path b c) (h : RwEq p q) :
    RwEq (Path.trans p r) (Path.trans q r) :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step s => RwEq.step (Step.trans_congr_left r s)
  | RwEq.symm h => RwEq.symm (rweq_trans_congr_left r h)
  | RwEq.trans h₁ h₂ =>
      RwEq.trans (rweq_trans_congr_left r h₁)
        (rweq_trans_congr_left r h₂)

@[simp] theorem rweq_trans_congr_right {a b c : A}
    (p : Path a b) {q r : Path b c} (h : RwEq q r) :
    RwEq (Path.trans p q) (Path.trans p r) :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step s => RwEq.step (Step.trans_congr_right p s)
  | RwEq.symm h => RwEq.symm (rweq_trans_congr_right p h)
  | RwEq.trans h₁ h₂ =>
      RwEq.trans (rweq_trans_congr_right p h₁)
        (rweq_trans_congr_right p h₂)

@[simp] theorem rweq_trans_congr {a b c : A}
    {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : RwEq p₁ p₂) (hq : RwEq q₁ q₂) :
    RwEq (Path.trans p₁ q₁) (Path.trans p₂ q₂) :=
  rweq_trans (rweq_trans_congr_left (a := a) (b := b) (c := c)
      (p := p₁) (q := p₂) (r := q₁) hp)
    (rweq_trans_congr_right (a := a) (b := b) (c := c)
      (p := p₂) (q := q₁) (r := q₂) hq)


@[simp] theorem rweq_mapLeft_congr
    {B : Type u} (f : A → B → A)
    {a₁ a₂ : A} (b : B)
    {p q : Path a₁ a₂} (h : RwEq p q) :
    RwEq (Path.mapLeft f p b) (Path.mapLeft f q b) :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step s =>
      RwEq.step (Step.mapLeft_congr (f := f) (b := b) s)
  | RwEq.symm h =>
      RwEq.symm (rweq_mapLeft_congr (f := f) (b := b) h)
  | RwEq.trans h₁ h₂ =>
      RwEq.trans
        (rweq_mapLeft_congr (f := f) (b := b) h₁)
        (rweq_mapLeft_congr (f := f) (b := b) h₂)

@[simp] theorem rweq_mapRight_congr
    (f : A → A → A) (a : A) {b₁ b₂ : A}
    {p q : Path b₁ b₂} (h : RwEq p q) :
    RwEq (Path.mapRight f a p) (Path.mapRight f a q) :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step s =>
      RwEq.step (Step.mapRight_congr (f := f) (a := a) s)
  | RwEq.symm h =>
      RwEq.symm (rweq_mapRight_congr (f := f) (a := a) h)
  | RwEq.trans h₁ h₂ =>
      RwEq.trans
        (rweq_mapRight_congr (f := f) (a := a) h₁)
        (rweq_mapRight_congr (f := f) (a := a) h₂)

namespace PathRwQuot

variable {A : Type u} {a b : A}

open Quot

/-- Reflexive element in the quotient. -/
def refl (a : A) : PathRwQuot A a a :=
  Quot.mk _ (Path.refl a)

/-- Symmetry descends to the quotient. -/
def symm {a b : A} :
    PathRwQuot A a b → PathRwQuot A b a := fun x =>
  Quot.liftOn x (fun p => Quot.mk _ (Path.symm p))
    (by
      intro p q h
      exact Quot.sound (rweq_symm_congr (A := A) h))

/-- Composition descends to the quotient. -/
def trans {a b c : A} :
    PathRwQuot A a b → PathRwQuot A b c → PathRwQuot A a c :=
  fun x y =>
    Quot.liftOn x
      (fun p : Path a b =>
        Quot.liftOn y
          (fun q : Path b c => Quot.mk _ (Path.trans p q))
          (by
            intro q₁ q₂ hq
            exact Quot.sound
              (rweq_trans_congr_right (A := A) (a := a) (b := b) (c := c)
                (p := p) (q := q₁) (r := q₂) hq)) )
      (by
        intro p₁ p₂ hp
        refine Quot.inductionOn y (fun q =>
          Quot.sound
            (rweq_trans_congr_left (A := A) (a := a) (b := b) (c := c)
              (p := p₁) (q := p₂) (r := q) hp)))

/-- Coerce a propositional equality to the path quotient. -/
@[simp] def ofEq {a b : A} (h : a = b) : PathRwQuot A a b :=
  Quot.mk _ (Path.ofEq h)

/-- Forget the rewrite trace and recover the underlying equality. -/
def toEq {a b : A} : PathRwQuot A a b → a = b :=
  Quot.lift (fun p : Path a b => p.toEq)
    (by
      intro p q h
      exact rweq_toEq h)

@[simp] theorem toEq_mk {a b : A} (p : Path a b) :
    toEq (A := A) (Quot.mk _ p) = p.toEq := rfl

@[simp] theorem toEq_refl (a : A) :
    toEq (A := A) (refl (A := A) a) = rfl := rfl

@[simp] theorem toEq_ofEq {a b : A} (h : a = b) :
    toEq (A := A) (ofEq (A := A) h) = h := rfl

@[simp] theorem toEq_symm {a b : A} (x : PathRwQuot A a b) :
    toEq (A := A) (symm (A := A) x) = (toEq (A := A) x).symm := by
  refine Quot.inductionOn x (fun p => by simp)

@[simp] theorem toEq_trans {a b c : A}
    (x : PathRwQuot A a b) (y : PathRwQuot A b c) :
    toEq (A := A) (trans (A := A) x y) =
      (toEq (A := A) x).trans (toEq (A := A) y) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q => by simp))

@[simp] theorem symm_mk {a b : A} (p : Path a b) :
    symm (A := A) (Quot.mk _ p) = Quot.mk _ (Path.symm p) := rfl

@[simp] theorem trans_mk {a b c : A}
    (p : Path a b) (q : Path b c) :
    trans (A := A) (Quot.mk _ p) (Quot.mk _ q) =
      Quot.mk _ (Path.trans p q) := rfl

@[simp] theorem symm_symm {a b : A}
    (x : PathRwQuot A a b) :
    symm (A := A) (symm x) = x := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.symm_symm (A := A) p))

@[simp] theorem trans_refl_left {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) (refl a) x = x := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.trans_refl_left (A := A) p))

@[simp] theorem trans_refl_right {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) x (refl b) = x := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.trans_refl_right (A := A) p))

@[simp] theorem trans_symm {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) x (symm x) = refl a := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.trans_symm (A := A) p))

@[simp] theorem symm_trans {a b : A}
    (x : PathRwQuot A a b) :
    trans (A := A) (symm x) x = refl b := by
  refine Quot.inductionOn x (fun p => by
    apply Quot.sound
    exact rweq_of_step (Step.symm_trans (A := A) p))

@[simp] theorem trans_assoc {a b c d : A}
    (x : PathRwQuot A a b)
    (y : PathRwQuot A b c)
    (z : PathRwQuot A c d) :
    trans (A := A) (trans x y) z =
      trans x (trans y z) := by
  refine Quot.inductionOn x (fun p =>
    Quot.inductionOn y (fun q =>
      Quot.inductionOn z (fun r => by
        apply Quot.sound
        exact rweq_of_step (Step.trans_assoc (A := A) (p := p) (q := q) (r := r)))))

@[simp] def normalPath {a b : A} (x : PathRwQuot A a b) : Path a b :=
  Path.ofEq (A := A) (a := a) (b := b) (toEq x)

@[simp] theorem normalPath_isNormal {a b : A}
    (x : PathRwQuot A a b) :
    IsNormal (A := A) (a := a) (b := b) (normalPath (A := A) (x := x)) := by
  unfold normalPath IsNormal
  rfl

@[simp] theorem normalPath_mk {a b : A} (p : Path a b) :
    normalPath (A := A) (x := Quot.mk _ p) =
      normalize (A := A) (a := a) (b := b) p := rfl

@[simp] def normalForm {a b : A}
    (x : PathRwQuot A a b) : NormalForm A a b :=
  { path := normalPath (A := A) (x := x)
    isNormal := normalPath_isNormal (A := A) (x := x) }

@[simp] theorem normalForm_path {a b : A} (x : PathRwQuot A a b) :
    (normalForm (A := A) (x := x)).path =
      normalPath (A := A) (x := x) := rfl

@[simp] theorem normalForm_mk {a b : A} (p : Path a b) :
    normalForm (A := A) (x := Quot.mk _ p) =
      normalizeForm (A := A) (a := a) (b := b) p := by
  unfold normalForm normalizeForm normalPath normalize
  rfl

/-- The canonical normal path has the same propositional equality as the quotient representative. -/
@[simp] theorem normalPath_toEq {a b : A}
    (x : PathRwQuot A a b) :
    (normalPath (A := A) (x := x)).toEq =
      PathRwQuot.toEq (A := A) x := rfl

end PathRwQuot

@[simp] theorem rweq_congrArg_trans {B : Type v}
    {a b c : A} (f : A → B) (p : Path a b) (q : Path b c) :
    RwEq (Path.congrArg f (Path.trans p q))
      (Path.trans (Path.congrArg f p) (Path.congrArg f q)) :=
  rweq_of_eq (Path.congrArg_trans (f := f) (p := p) (q := q))

@[simp] theorem rweq_congrArg_symm {B : Type v}
    {a b : A} (f : A → B) (p : Path a b) :
    RwEq (Path.congrArg f (Path.symm p))
      (Path.symm (Path.congrArg f p)) :=
  rweq_of_eq (Path.congrArg_symm (f := f) (p := p))

@[simp] theorem rweq_mapLeft_trans {B : Type v} {C : Type w}
    {a1 a2 a3 : A} (f : A → B → C)
    (p : Path a1 a2) (q : Path a2 a3) (b : B) :
    RwEq (Path.mapLeft f (Path.trans p q) b)
      (Path.trans (Path.mapLeft f p b) (Path.mapLeft f q b)) :=
  rweq_of_eq (Path.mapLeft_trans (f := f) (p := p) (q := q) (b := b))

@[simp] theorem rweq_mapLeft_symm {B : Type v} {C : Type w}
    {a1 a2 : A} (f : A → B → C)
    (p : Path a1 a2) (b : B) :
    RwEq (Path.mapLeft f (Path.symm p) b)
      (Path.symm (Path.mapLeft f p b)) :=
  rweq_of_eq (Path.mapLeft_symm (f := f) (p := p) (b := b))

@[simp] theorem rweq_mapLeft_refl {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) (b : B) :
    RwEq (Path.mapLeft f (Path.refl a) b) (Path.refl (f a b)) :=
  rweq_of_eq (Path.mapLeft_refl (f := f) (a := a) (b := b))

@[simp] theorem rweq_mapLeft_ofEq {B : Type v} {C : Type w}
    (f : A → B → C) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
    RwEq (Path.mapLeft (A := A) (B := B) (C := C) f
        (Path.ofEq (A := A) (a := a₁) (b := a₂) h) b)
      (Path.ofEq (A := C) (a := f a₁ b) (b := f a₂ b)
        (_root_.congrArg (fun x => f x b) h)) :=
  rweq_of_eq (by
    simp [Path.mapLeft, Path.ofEq, Path.congrArg, List.map])

@[simp] theorem rweq_mapRight_trans {B : Type v} {C : Type w}
    {b1 b2 b3 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) (q : Path b2 b3) :
    RwEq (Path.mapRight f a (Path.trans p q))
      (Path.trans (Path.mapRight f a p) (Path.mapRight f a q)) :=
  rweq_of_eq (Path.mapRight_trans (f := f) (a := a) (p := p) (q := q))

@[simp] theorem rweq_mapRight_refl {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) (b : B) :
    RwEq (Path.mapRight f a (Path.refl b)) (Path.refl (f a b)) :=
  rweq_of_eq (Path.mapRight_refl (f := f) (a := a) (b := b))

@[simp] theorem rweq_mapRight_ofEq {B : Type v} {C : Type w}
    (f : A → B → C) (a : A) {b₁ b₂ : B} (h : b₁ = b₂) :
    RwEq (Path.mapRight (A := A) (B := B) (C := C) f a
          (Path.ofEq (A := B) (a := b₁) (b := b₂) h))
      (Path.ofEq (A := C) (a := f a b₁) (b := f a b₂)
        (_root_.congrArg (f a) h)) :=
  rweq_of_eq (by
    simp [Path.mapRight, Path.ofEq, Path.congrArg, List.map])

@[simp] theorem rweq_map2_trans
    {A₁ : Type u} {B : Type u}
    {a1 a2 a3 : A₁} {b1 b2 b3 : B}
    (f : A₁ → B → A)
    (p1 : Path (A := A₁) a1 a2) (p2 : Path (A := A₁) a2 a3)
    (q1 : Path (A := B) b1 b2) (q2 : Path (A := B) b2 b3) :
    RwEq
      (Path.map2 (A := A₁) (B := B) (C := A) f
        (Path.trans p1 p2) (Path.trans q1 q2))
      (Path.trans
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p1 b1)
        (Path.trans
          (Path.mapLeft (A := A₁) (B := B) (C := A) f p2 b1)
          (Path.trans
            (Path.mapRight (A := A₁) (B := B) (C := A) f a3 q1)
            (Path.mapRight (A := A₁) (B := B) (C := A) f a3 q2)))) :=
  rweq_of_eq
    (Path.map2_trans (A := A₁) (B := B) (C := A) (f := f)
      (p1 := p1) (p2 := p2) (q1 := q1) (q2 := q2))

@[simp] theorem rweq_map2_refl
    {A₁ : Type u} {B : Type u} (f : A₁ → B → A) (a : A₁) (b : B) :
    RwEq (Path.map2 (A := A₁) (B := B) (C := A) f
        (Path.refl a) (Path.refl b)) (Path.refl (f a b)) :=
  rweq_of_eq (Path.map2_refl (A := A₁) (B := B) (C := A) (f := f) (a := a) (b := b))

@[simp] theorem rweq_mapRight_symm {B : Type v} {C : Type w}
    {b1 b2 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) :
    RwEq (Path.mapRight f a (Path.symm p))
      (Path.symm (Path.mapRight f a p)) :=
  rweq_of_eq (Path.mapRight_symm (f := f) (a := a) (p := p))

/-- Subterm substitution lifted to `RwEq`. -/
@[simp] theorem rweq_map2_subst
    {A₁ : Type u} {B : Type u}
    {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2)
    (q : Path (A := B) b1 b2) :
    RwEq
      (Path.map2 (A := A₁) (B := B) (C := A) f p q)
      (Path.trans
        (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
        (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2)) :=
  rweq_of_step (Step.map2_subst (A₁ := A₁) (B := B) (f := f) p q)

@[simp] theorem rweq_map2_symm
    {A₁ : Type u} {B : Type u}
    {a1 a2 : A₁} {b1 b2 : B}
    (f : A₁ → B → A)
    (p : Path (A := A₁) a1 a2)
    (q : Path (A := B) b1 b2) :
    RwEq
      (Path.map2 (A := A₁) (B := B) (C := A) f (Path.symm p) (Path.symm q))
      (Path.symm (Path.map2 (A := A₁) (B := B) (C := A) f p q)) := by
  have h :=
    rweq_of_step
      (Step.map2_subst (A₁ := A₁) (B := B) (f := f)
        (p := Path.symm p) (q := Path.symm q))
  have h2 :=
    Path.map2_symm (A := A₁) (B := B) (C := A) f p q
  exact rweq_trans h (rweq_of_eq h2.symm)

@[simp] theorem rweq_prod_fst_beta {A : Type u} {B : Type u}
    {a1 a2 : A} {b1 b2 : B}
    (p : Path a1 a2) (q : Path b1 b2) :
    RwEq (Path.congrArg Prod.fst
        (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q)) p :=
  rweq_of_step (Step.prod_fst_beta (B := B) p q)

@[simp] theorem rweq_prod_snd_beta {B : Type u} {A : Type u}
    {a1 a2 : B} {b1 b2 : A}
    (p : Path a1 a2) (q : Path b1 b2) :
    RwEq (Path.congrArg Prod.snd
        (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q)) q :=
  rweq_of_step (Step.prod_snd_beta (B := B) p q)

/-- Beta-style reduction in `RwEq` for `Prod.rec` applied to a pair path. -/
@[simp] theorem rweq_prod_rec_beta {α β : Type u} {A : Type u}
    (f : α → β → A)
    {a1 a2 : α} {b1 b2 : β}
    (p : Path a1 a2) (q : Path b1 b2) :
    RwEq
      (Path.congrArg (Prod.rec f)
        (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
      (Path.map2 (A := α) (B := β) (C := A) f p q) :=
  rweq_of_step (Step.prod_rec_beta (α := α) (β := β) (f := f) p q)

@[simp] theorem rweq_sigma_fst_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    RwEq
      (Path.congrArg Sigma.fst
        (Path.sigmaMk (B := B) p q))
      (Path.ofEq (A := A) p.toEq) :=
  rweq_of_step (Step.sigma_fst_beta (A := A) (B := B) p q)

@[simp] theorem rweq_sigma_snd_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    RwEq
      (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
      (Path.ofEq
        (A := B a2)
        (a := transport (A := A) (D := fun a => B a)
              (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b1)
        (b := b2) q.toEq) :=
  rweq_of_eq
    (Path.sigmaSnd_sigmaMk_eq_ofEq
      (B := B) (p := p) (q := q))

@[simp] theorem rweq_apd_refl {A : Type u} {B : A → Type u}
    (f : ∀ x : A, B x) (a : A) :
    RwEq
      (Path.apd (A := A) (B := B) f (Path.refl a))
      (Path.refl (f a)) :=
  RwEq.step (Step.apd_refl (A := A) (B := B) f a)

/-- Beta-style reduction in `RwEq` for `Sum.rec` applied to a left injection. -/
@[simp] theorem rweq_sum_rec_inl_beta {α β : Type u} {A : Type u}
    {a1 a2 : α} (f : α → A) (g : β → A) (p : Path a1 a2) :
    RwEq
      (Path.congrArg (Sum.rec f g)
        (Path.congrArg Sum.inl p))
      (Path.congrArg f p) :=
  rweq_of_step (Step.sum_rec_inl_beta (α := α) (β := β) (f := f) (g := g) p)

/-- Beta-style reduction in `RwEq` for `Sum.rec` applied to a right injection. -/
@[simp] theorem rweq_sum_rec_inr_beta {α β : Type u} {A : Type u}
    {b1 b2 : β} (f : α → A) (g : β → A) (p : Path b1 b2) :
    RwEq
      (Path.congrArg (Sum.rec f g)
        (Path.congrArg Sum.inr p))
      (Path.congrArg g p) :=
  rweq_of_step (Step.sum_rec_inr_beta (α := α) (β := β) (f := f) (g := g) p)

/-- Beta-style reduction in `RwEq` for evaluating a lambda-generated path. -/
@[simp] theorem rweq_fun_app_beta {α : Type u}
    {f g : α → A} (p : ∀ x : α, Path (f x) (g x)) (a : α) :
    RwEq
      (Path.congrArg (fun h : α → A => h a)
        (Path.lamCongr (f := f) (g := g) p))
      (p a) :=
  rweq_of_step (Step.fun_app_beta (α := α) p a)

/-- Eta-style reduction in `RwEq` rebuilding a function path from its applications. -/
@[simp] theorem rweq_of_rw {p q : Path a b} (h : Rw p q) : RwEq p q :=
  match h with
  | Rw.refl _ => RwEq.refl _
  | Rw.tail h step => RwEq.trans (rweq_of_rw h) (RwEq.step step)

/-- Pointwise `RwEq` hypotheses lift to a path between functions. -/
@[simp] theorem rweq_lamCongr_of_rweq {A : Type u} {B : Type v}
    {f g : A → B}
    {p q : ∀ x : A, Path (f x) (g x)}
    (h : ∀ x : A, RwEq (p x) (q x)) :
    RwEq (Path.lamCongr p) (Path.lamCongr q) := by
  classical
  have hxProof :
      ∀ x, (p x).proof = (q x).proof := fun x => by
        have hx := rweq_toEq (h x)
        cases hx
        simp
  have hx : Path.lamCongr p = Path.lamCongr q := by
    have hxFun := funext hxProof
    cases hxFun
    simp [Path.lamCongr]
  cases hx
  exact RwEq.refl _

/-- Pointwise `Rw` hypotheses lift to a symmetric path between functions. -/
@[simp] theorem rweq_lamCongr_of_rw {A : Type u} {B : Type v}
    {f g : A → B}
    {p q : ∀ x : A, Path (f x) (g x)}
    (h : ∀ x : A, Rw (p x) (q x)) :
    RwEq (Path.lamCongr p) (Path.lamCongr q) :=
  rweq_lamCongr_of_rweq (A := A) (B := B) (f := f) (g := g)
    (p := p) (q := q) (h := fun x => rweq_of_rw (h x))

@[simp] theorem rw_congr_rweq {p q r : Path a b}
    (hpq : Rw p q) (hqr : RwEq q r) : RwEq p r :=
  rweq_trans (rweq_of_rw hpq) hqr

@[simp] theorem rweq_congr_rw {p q r : Path a b}
    (hpq : RwEq p q) (hqr : Rw q r) : RwEq p r :=
  rweq_trans hpq (rweq_of_rw hqr)

@[simp] theorem rweq_symm_trans_congr {p : Path a b} {q : Path b c} :
    RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
  rweq_of_rw (rw_symm_trans_congr (p := p) (q := q))

/-- Eta-style reduction in `RwEq` rebuilding a product path from its projections. -/
@[simp] theorem rweq_prod_eta {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
    RwEq (Path.prodMk (Path.fst p) (Path.snd p)) p := by
  classical
  exact rweq_of_rw (rw_prod_eta (α := α) (β := β) (p := p))

/-- Eta-style reduction in `RwEq` rebuilding a function path from its pointwise applications. -/
@[simp] theorem rweq_fun_eta {α β : Type u}
    {f g : α → β} (p : Path f g) :
    RwEq (Path.lamCongr (fun x => Path.app p x)) p := by
  classical
  exact rweq_of_rw (rw_fun_eta (α := α) (β := β) (p := p))

/-- Eta-style reduction in `RwEq` rebuilding a dependent pair path from its projections. -/
@[simp] theorem rweq_sigma_eta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
    RwEq (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p := by
  classical
  exact rweq_of_rw (rw_sigma_eta (A := A) (B := B) (p := p))

@[simp] theorem rweq_sigmaMk_refl {A : Type u} {B : A → Type u}
    (a : A) (b : B a) :
    RwEq
      (Path.sigmaMk (B := B) (Path.refl a)
        (Path.ofEq (A := B a) (a := b) (b := b) rfl))
      (Path.refl (Sigma.mk a b)) := by
  classical
  have hfst :
      Path.sigmaFst (B := B) (Path.refl (Sigma.mk a b)) =
        Path.refl a := by
    unfold Path.sigmaFst
    simp [Path.congrArg, Path.refl]
  have hsnd :
      Path.sigmaSnd (B := B) (Path.refl (Sigma.mk a b)) =
        Path.ofEq (A := B a) (a := b) (b := b) rfl := by
    unfold Path.sigmaSnd
    simp [transport, Path.refl]
  have h :=
    rweq_sigma_eta (A := A) (B := B)
      (p := Path.refl (Sigma.mk a b))
  cases hfst
  cases hsnd
  exact h

namespace PathRwQuot

@[simp] theorem sum_rec_inl_beta {α β : Type u} {A : Type u}
    {a1 a2 : α} (f : α → A) (g : β → A) (p : Path a1 a2) :
    (Quot.mk _
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p)) :
        PathRwQuot A (f a1) (f a2)) =
      Quot.mk _ (Path.congrArg f p) := by
  apply Quot.sound
  exact rweq_sum_rec_inl_beta (α := α) (β := β) (A := A)
    (f := f) (g := g) (p := p)

@[simp] theorem sum_rec_inr_beta {α β : Type u} {A : Type u}
    {b1 b2 : β} (f : α → A) (g : β → A) (p : Path b1 b2) :
    (Quot.mk _
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p)) :
        PathRwQuot A (g b1) (g b2)) =
      Quot.mk _ (Path.congrArg g p) := by
  apply Quot.sound
  exact rweq_sum_rec_inr_beta (α := α) (β := β) (A := A)
    (f := f) (g := g) (p := p)

@[simp] theorem prod_eta {α β : Type u}
    {a₁ a₂ : α} {b₁ b₂ : β}
    (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
    (Quot.mk _ (Path.prodMk (Path.fst p) (Path.snd p)) :
        PathRwQuot (Prod α β) (a₁, b₁) (a₂, b₂))
      = Quot.mk _ p := by
  apply Quot.sound
  exact rweq_prod_eta (α := α) (β := β) (p := p)

@[simp] theorem sigma_eta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
    (Quot.mk _ (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) :
        PathRwQuot (Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) =
      Quot.mk _ p := by
  apply Quot.sound
  exact rweq_sigma_eta (A := A) (B := B) (p := p)

@[simp] theorem sigma_snd_beta {A : Type u} {B : A → Type u}
    {a1 a2 : A} {b1 : B a1} {b2 : B a2}
    (p : Path a1 a2)
    (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
    (Quot.mk _
        (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q)) :
        PathRwQuot (B a2)
          (transport (A := A) (D := fun a => B a) p b1) b2) =
      Quot.mk _ q := by
  apply Quot.sound
  exact rweq_sigmaSnd_sigmaMk (A := A) (B := B) (p := p) (q := q)

@[simp] theorem sigma_refl_ofEq {A : Type u} {B : A → Type u}
    (a : A) (b : B a) :
    (Quot.mk _
        (Path.sigmaMk (B := B) (Path.refl a)
          (Path.ofEq (A := B a) (a := b) (b := b) rfl)) :
        PathRwQuot (Sigma B) (Sigma.mk a b) (Sigma.mk a b)) =
      PathRwQuot.refl (A := Sigma B) (Sigma.mk a b) := by
  apply Quot.sound
  exact
    rweq_sigmaMk_refl (A := A) (B := B) (a := a) (b := b)

@[simp] theorem fun_eta {α β : Type u}
    {f g : α → β} (p : Path f g) :
    (Quot.mk _ (Path.lamCongr (fun x => Path.app p x)) :
        PathRwQuot (α → β) f g) = Quot.mk _ p := by
  apply Quot.sound
  exact rweq_fun_eta (α := α) (β := β) (p := p)

end PathRwQuot

end ComputationalPaths.Path
