/-
# Rewriting system on computational paths

This module captures the fragment of the `rw`-rewrite system from the paper
concerned with symmetry and transitivity.  We provide the basic rewrite steps
and the reflexive/transitive closure `Rw`, together with its symmetric
reflexive/transitive closure `RwEq`.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths.Path

universe u v w

/-- A single rewrite step between computational paths. -/
inductive Step {A : Type u} :
    {a b : A} → Path a b → Path a b → Prop
  | symm_refl (a : A) :
      Step (symm (Path.refl a)) (Path.refl a)
  | symm_symm {a b : A} (p : Path a b) :
      Step (symm (symm p)) p
  | trans_refl_left {a b : A} (p : Path a b) :
      Step (trans (Path.refl a) p) p
  | trans_refl_right {a b : A} (p : Path a b) :
      Step (trans p (Path.refl b)) p
  | trans_symm {a b : A} (p : Path a b) :
      Step (trans p (symm p)) (Path.refl a)
  | symm_trans {a b : A} (p : Path a b) :
      Step (trans (symm p) p) (Path.refl b)
  | symm_trans_congr {a b c : A} (p : Path a b) (q : Path b c) :
      Step (symm (trans p q)) (trans (symm q) (symm p))
  | trans_assoc {a b c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
      Step (trans (trans p q) r) (trans p (trans q r))
  | map2_subst
      {A₁ : Type u} {B : Type u}
      {a1 a2 : A₁} {b1 b2 : B}
      (f : A₁ → B → A)
      (p : Path (A := A₁) a1 a2)
      (q : Path (A := B) b1 b2) :
      Step
        (Path.map2 (A := A₁) (B := B) (C := A) f p q)
        (Path.trans
          (Path.mapRight (A := A₁) (B := B) (C := A) f a1 q)
          (Path.mapLeft (A := A₁) (B := B) (C := A) f p b2))
  | prod_fst_beta
      {B : Type u}
      {a1 a2 : A} {b1 b2 : B}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step
        (Path.congrArg Prod.fst
          (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q))
        p
  | prod_snd_beta
      {B : Type u}
      {a1 a2 : B} {b1 b2 : A}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step
        (Path.congrArg Prod.snd
          (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q))
        q
  | prod_rec_beta
      {α β : Type u}
      {a1 a2 : α} {b1 b2 : β}
      (f : α → β → A)
      (p : Path a1 a2) (q : Path b1 b2) :
      Step
        (Path.congrArg (Prod.rec f)
          (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
        (Path.map2 (A := α) (B := β) (C := A) f p q)
  | sum_rec_inl_beta
      {α β : Type u}
      {a1 a2 : α}
      (f : α → A) (g : β → A)
      (p : Path a1 a2) :
      Step
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p))
        (Path.congrArg f p)
  | sum_rec_inr_beta
      {α β : Type u}
      {b1 b2 : β}
      (f : α → A) (g : β → A)
      (p : Path b1 b2) :
      Step
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p))
        (Path.congrArg g p)
  | fun_app_beta
      {α : Type u}
      {f g : α → A}
      (p : ∀ x : α, Path (f x) (g x)) (a : α) :
      Step
        (Path.congrArg (fun h : α → A => h a)
          (Path.lamCongr (f := f) (g := g) p))
        (p a)

attribute [simp] Step.symm_refl Step.symm_symm Step.trans_refl_left
  Step.trans_refl_right Step.trans_symm Step.symm_trans Step.symm_trans_congr
  Step.trans_assoc Step.map2_subst Step.prod_fst_beta Step.prod_snd_beta
  Step.prod_rec_beta
  Step.sum_rec_inl_beta Step.sum_rec_inr_beta Step.fun_app_beta

/-- Reflexive/transitive closure of rewrite steps (`rw`-reduction). -/
inductive Rw {A : Type u} {a b : A} : Path a b → Path a b → Prop
  | refl (p : Path a b) : Rw p p
  | tail {p q r : Path a b} : Rw p q → Step q r → Rw p r

variable {A : Type u} {a b c : A}

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

@[simp] theorem rw_mapRight_trans {B : Type v} {C : Type w}
    {b1 b2 b3 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) (q : Path b2 b3) :
    Rw (Path.mapRight f a (Path.trans p q))
      (Path.trans (Path.mapRight f a p) (Path.mapRight f a q)) :=
  rw_of_eq (Path.mapRight_trans (f := f) (a := a) (p := p) (q := q))

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

@[simp] theorem rw_trans {p q r : Path a b}
    (h1 : Rw p q) (h2 : Rw q r) : Rw p r :=
  match h2 with
  | Rw.refl _ => h1
  | Rw.tail h2 step => Rw.tail (rw_trans h1 h2) step

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
  rw_of_step (Step.fun_app_beta (α := α) p a)

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

@[simp] theorem rweq_symm {p q : Path a b} (h : RwEq p q) : RwEq q p :=
  match h with
  | RwEq.refl _ => RwEq.refl _
  | RwEq.step h => RwEq.symm (RwEq.step h)
  | RwEq.symm h => h
  | RwEq.trans h1 h2 => RwEq.trans (rweq_symm h2) (rweq_symm h1)

@[simp] theorem rweq_trans {p q r : Path a b} (h1 : RwEq p q) (h2 : RwEq q r) :
    RwEq p r :=
  RwEq.trans h1 h2

@[simp] theorem rweq_of_eq {p q : Path a b} (h : p = q) : RwEq p q := by
  cases h
  exact RwEq.refl _

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

@[simp] theorem rweq_mapRight_trans {B : Type v} {C : Type w}
    {b1 b2 b3 : B} (f : A → B → C)
    (a : A) (p : Path b1 b2) (q : Path b2 b3) :
    RwEq (Path.mapRight f a (Path.trans p q))
      (Path.trans (Path.mapRight f a p) (Path.mapRight f a q)) :=
  rweq_of_eq (Path.mapRight_trans (f := f) (a := a) (p := p) (q := q))

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

@[simp] theorem rw_congr_rweq {p q r : Path a b}
    (hpq : Rw p q) (hqr : RwEq q r) : RwEq p r :=
  rweq_trans (rweq_of_rw hpq) hqr

@[simp] theorem rweq_congr_rw {p q r : Path a b}
    (hpq : RwEq p q) (hqr : Rw q r) : RwEq p r :=
  rweq_trans hpq (rweq_of_rw hqr)

@[simp] theorem rweq_symm_trans_congr {p : Path a b} {q : Path b c} :
    RwEq (symm (trans p q)) (trans (symm q) (symm p)) :=
  rweq_of_rw (rw_symm_trans_congr (p := p) (q := q))

end ComputationalPaths.Path
