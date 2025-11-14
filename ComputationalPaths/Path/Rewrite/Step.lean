/-
# Primitive rewrite steps on computational paths

Defines the `Step` relation capturing single `rw`-style reductions, together
with their `[simp]` registration and the `step_toEq` lemma.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Context
import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths
namespace Path

open scoped Quot

universe u

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
  Step.context_congr Step.context_subst_left_beta Step.context_subst_left_of_right
  Step.context_subst_left_assoc Step.context_subst_right_assoc
  Step.biContext_mapLeft_congr Step.biContext_mapRight_congr
  Step.biContext_map2_congr_left Step.biContext_map2_congr_right
  Step.mapLeft_congr Step.mapRight_congr Step.mapLeft_ofEq Step.mapRight_ofEq Step.canon
  Step.symm_congr Step.trans_congr_left Step.trans_congr_right

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
    simp
  | context_subst_left_of_right _ _ _ =>
    simp
  | context_subst_left_assoc _ _ _ _ =>
    simp
  | context_subst_right_assoc _ _ _ _ =>
    simp
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

end Path
end ComputationalPaths
