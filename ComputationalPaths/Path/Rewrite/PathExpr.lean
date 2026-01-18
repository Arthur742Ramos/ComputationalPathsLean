/-
# Syntactic path expressions (core fragment)

This module introduces a minimal syntax tree for paths so that rewrite steps are
syntactic reductions (no definitional reflexivity). We start with the core
groupoid rules and a termination proof based on a simple size measure; the
expression language can be extended later to cover the full TRS.
-/

import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Basic.Context

namespace ComputationalPaths
namespace Path
namespace Rewrite

universe u

/-- Syntactic path expressions for the core groupoid fragment. -/
inductive PathExpr {A : Type u} : {a b : A} → Type u
  | atom {a b : A} (p : Path a b) : PathExpr (a := a) (b := b)
  | refl (a : A) : PathExpr (a := a) (b := a)
  | symm {a b : A} (p : PathExpr (a := a) (b := b)) : PathExpr (a := b) (b := a)
  | trans {a b c : A}
      (p : PathExpr (a := a) (b := b)) (q : PathExpr (a := b) (b := c)) :
      PathExpr (a := a) (b := c)
  | context_map {A : Type u} {B : Type u}
      (C : Context A B) {a b : A}
      (p : PathExpr (A := A) (a := a) (b := b)) :
      PathExpr (A := B) (a := C.fill a) (b := C.fill b)
  | context_subst_left {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : PathExpr (A := B) (a := x) (b := C.fill a₁))
      (p : PathExpr (A := A) (a := a₁) (b := a₂)) :
      PathExpr (A := B) (a := x) (b := C.fill a₂)
  | context_subst_right {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (t : PathExpr (A := B) (a := C.fill a₂) (b := y)) :
      PathExpr (A := B) (a := C.fill a₁) (b := y)

namespace PathExpr

variable {A : Type u} {a b c d : A}

/-! ## Evaluation -/

@[simp] def eval : PathExpr (A := A) (a := a) (b := b) → Path a b
  | atom p => p
  | refl a => Path.refl a
  | symm p => Path.symm (eval p)
  | trans p q => Path.trans (eval p) (eval q)
  | context_map C p => Context.map (A := A) (B := _) C (eval p)
  | context_subst_left C r p =>
      Context.substLeft (A := A) (B := _) C (eval r) (eval p)
  | context_subst_right C p t =>
      Context.substRight (A := A) (B := _) C (eval p) (eval t)

/-! ## Size Measures -/

@[simp] def size : PathExpr (A := A) (a := a) (b := b) → Nat
  | atom _ => 1
  | refl _ => 1
  | symm p => size p + 1
  | trans p q => size p + size q + 1
  | context_map _ p => size p + 1
  | context_subst_left _ r p => size r + size p + 1
  | context_subst_right _ p t => size p + size t + 1

@[simp] def leftSpine : PathExpr (A := A) (a := a) (b := b) → Nat
  | atom _ => 0
  | refl _ => 0
  | symm p => leftSpine p
  | trans p _ => leftSpine p + 1
  | context_map _ p => leftSpine p
  | context_subst_left _ r _ => leftSpine r + 1
  | context_subst_right _ p _ => leftSpine p

@[simp] def complexity (p : PathExpr (A := A) (a := a) (b := b)) : Nat :=
  (size p) * (size p) + leftSpine p

theorem leftSpine_le_size (p : PathExpr (A := A) (a := a) (b := b)) :
    leftSpine p ≤ size p := by
  induction p with
  | atom => simp [leftSpine, size]
  | refl => simp [leftSpine, size]
  | symm _ ih =>
      simp [leftSpine, size] at *
      omega
  | trans p q ihp ihq =>
      have hleft := ihp
      have hright := ihq
      simp [leftSpine, size] at *
      omega
  | context_map _ p ih =>
      simp [leftSpine, size] at *
      omega
  | context_subst_left _ r p ihr ihp =>
      simp [leftSpine, size] at *
      omega
  | context_subst_right _ p t ihp iht =>
      simp [leftSpine, size] at *
      omega

theorem complexity_lt_of_size_lt {p q : PathExpr (A := A) (a := a) (b := b)}
    (hsize : size q < size p) : complexity q < complexity p := by
  have hle : leftSpine q ≤ size q := leftSpine_le_size (A := A) (a := a) (b := b) q
  simp [complexity] at *
  omega

/-! ## Rewrite Steps -/

inductive Step {A : Type u} {a b : A} :
    PathExpr (A := A) (a := a) (b := b) →
    PathExpr (A := A) (a := a) (b := b) → Prop
  | symm_refl (a : A) :
      Step (PathExpr.symm (PathExpr.refl a)) (PathExpr.refl a)
  | symm_symm {a b : A} (p : PathExpr (A := A) (a := a) (b := b)) :
      Step (PathExpr.symm (PathExpr.symm p)) p
  | trans_refl_left {a b : A} (p : PathExpr (A := A) (a := a) (b := b)) :
      Step (PathExpr.trans (PathExpr.refl a) p) p
  | trans_refl_right {a b : A} (p : PathExpr (A := A) (a := a) (b := b)) :
      Step (PathExpr.trans p (PathExpr.refl b)) p
  | trans_symm {a b : A} (p : PathExpr (A := A) (a := a) (b := b)) :
      Step (PathExpr.trans p (PathExpr.symm p)) (PathExpr.refl a)
  | symm_trans {a b : A} (p : PathExpr (A := A) (a := a) (b := b)) :
      Step (PathExpr.trans (PathExpr.symm p) p) (PathExpr.refl b)
  | trans_assoc {a b c d : A}
      (p : PathExpr (A := A) (a := a) (b := b))
      (q : PathExpr (A := A) (a := b) (b := c))
      (r : PathExpr (A := A) (a := c) (b := d)) :
      Step (PathExpr.trans (PathExpr.trans p q) r)
        (PathExpr.trans p (PathExpr.trans q r))
  | symm_congr {a b : A} {p q : PathExpr (A := A) (a := a) (b := b)} :
      Step p q → Step (PathExpr.symm p) (PathExpr.symm q)
  | trans_congr_left {a b c : A} {p q : PathExpr (A := A) (a := a) (b := b)}
      (r : PathExpr (A := A) (a := b) (b := c)) :
      Step p q → Step (PathExpr.trans p r) (PathExpr.trans q r)
  | trans_congr_right {a b c : A} (p : PathExpr (A := A) (a := a) (b := b))
      {q r : PathExpr (A := A) (a := b) (b := c)} :
      Step q r → Step (PathExpr.trans p q) (PathExpr.trans p r)
  | context_congr
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      {p q : PathExpr (A := A) (a := a₁) (b := a₂)} :
      Step p q →
        Step (A := B)
          (PathExpr.context_map (A := A) (B := B) C p)
          (PathExpr.context_map (A := A) (B := B) C q)
  | context_map_refl
      {A : Type u} {B : Type u}
      (C : Context A B) (a : A) :
      Step (A := B)
        (PathExpr.context_map (A := A) (B := B) C (PathExpr.refl a))
        (PathExpr.refl (C.fill a))
  | context_tt_cancel_left
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (v : PathExpr (A := B) (a := C.fill a₁) (b := y)) :
      Step (A := B)
        (PathExpr.trans
          (PathExpr.context_map (A := A) (B := B) C p)
          (PathExpr.trans
            (PathExpr.context_map (A := A) (B := B) C (PathExpr.symm p)) v))
        (PathExpr.trans
          (PathExpr.context_map (A := A) (B := B) C
            (PathExpr.trans p (PathExpr.symm p)))
          v)
  | context_tt_cancel_right
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {x : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (v : PathExpr (A := B) (a := x) (b := C.fill a₁)) :
      Step (A := B)
        (PathExpr.trans
          (PathExpr.trans v (PathExpr.context_map (A := A) (B := B) C p))
          (PathExpr.context_map (A := A) (B := B) C (PathExpr.symm p)))
        (PathExpr.trans
          v
          (PathExpr.context_map (A := A) (B := B) C
            (PathExpr.trans p (PathExpr.symm p))))
  | context_subst_left_beta
      {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : PathExpr (A := B) (a := x) (b := C.fill a₁))
      (p : PathExpr (A := A) (a := a₁) (b := a₂)) :
      Step (A := B)
        (PathExpr.trans r (PathExpr.context_map (A := A) (B := B) C p))
        (PathExpr.context_subst_left (A := A) (B := B) C r p)
  | context_subst_left_of_right
      {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : PathExpr (A := B) (a := x) (b := C.fill a₁))
      (p : PathExpr (A := A) (a := a₁) (b := a₂)) :
      Step (A := B)
        (PathExpr.trans r
          (PathExpr.context_subst_right (A := A) (B := B) C p
            (PathExpr.refl (C.fill a₂))))
        (PathExpr.context_subst_left (A := A) (B := B) C r p)
  | context_subst_left_assoc
      {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
      (r : PathExpr (A := B) (a := x) (b := C.fill a₁))
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (t : PathExpr (A := B) (a := C.fill a₂) (b := y)) :
      Step (A := B)
        (PathExpr.trans
          (PathExpr.context_subst_left (A := A) (B := B) C r p) t)
        (PathExpr.trans r
          (PathExpr.context_subst_right (A := A) (B := B) C p t))
  | context_subst_right_beta
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (t : PathExpr (A := B) (a := C.fill a₂) (b := y)) :
      Step (A := B)
        (PathExpr.trans (PathExpr.context_map (A := A) (B := B) C p) t)
        (PathExpr.context_subst_right (A := A) (B := B) C p t)
  | context_subst_right_assoc
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y z : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (t : PathExpr (A := B) (a := C.fill a₂) (b := y))
      (u : PathExpr (A := B) (a := y) (b := z)) :
      Step (A := B)
        (PathExpr.trans
          (PathExpr.context_subst_right (A := A) (B := B) C p t) u)
        (PathExpr.context_subst_right (A := A) (B := B) C p
          (PathExpr.trans t u))
  | context_subst_left_refl_right
      {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a : A}
      (r : PathExpr (A := B) (a := x) (b := C.fill a)) :
      Step (A := B)
        (PathExpr.context_subst_left (A := A) (B := B) C r (PathExpr.refl a)) r
  | context_subst_left_refl_left
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : PathExpr (A := A) (a := a₁) (b := a₂)) :
      Step (A := B)
        (PathExpr.context_subst_left (A := A) (B := B) C
          (PathExpr.refl (C.fill a₁)) p)
        (PathExpr.context_map (A := A) (B := B) C p)
  | context_subst_right_refl_left
      {A : Type u} {B : Type u}
      (C : Context A B) {a : A} {y : B}
      (r : PathExpr (A := B) (a := C.fill a) (b := y)) :
      Step (A := B)
        (PathExpr.context_subst_right (A := A) (B := B) C (PathExpr.refl a) r) r
  | context_subst_right_refl_right
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : PathExpr (A := A) (a := a₁) (b := a₂)) :
      Step (A := B)
        (PathExpr.context_subst_right (A := A) (B := B) C p
          (PathExpr.refl (C.fill a₂)))
        (PathExpr.context_map (A := A) (B := B) C p)
  | context_subst_left_idempotent
      {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : PathExpr (A := B) (a := x) (b := C.fill a₁))
      (p : PathExpr (A := A) (a := a₁) (b := a₂)) :
      Step (A := B)
        (PathExpr.context_subst_left (A := A) (B := B) C
          (PathExpr.context_subst_left (A := A) (B := B) C r (PathExpr.refl a₁)) p)
        (PathExpr.context_subst_left (A := A) (B := B) C r p)
  | context_subst_right_cancel_inner
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (t : PathExpr (A := B) (a := C.fill a₂) (b := y)) :
      Step (A := B)
        (PathExpr.context_subst_right (A := A) (B := B) C p
          (PathExpr.context_subst_right (A := A) (B := B) C (PathExpr.refl a₂) t))
        (PathExpr.context_subst_right (A := A) (B := B) C p t)
  | context_subst_right_cancel_outer
      {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : PathExpr (A := A) (a := a₁) (b := a₂))
      (t : PathExpr (A := B) (a := C.fill a₂) (b := y)) :
      Step (A := B)
        (PathExpr.context_subst_right (A := A) (B := B) C (PathExpr.refl a₁)
          (PathExpr.context_subst_right (A := A) (B := B) C p t))
        (PathExpr.context_subst_right (A := A) (B := B) C p t)

attribute [simp] Step.symm_refl Step.symm_symm Step.trans_refl_left
  Step.trans_refl_right Step.trans_symm Step.symm_trans Step.trans_assoc
  Step.symm_congr Step.trans_congr_left Step.trans_congr_right
  Step.context_congr Step.context_map_refl Step.context_tt_cancel_left Step.context_tt_cancel_right
  Step.context_subst_left_beta Step.context_subst_left_of_right
  Step.context_subst_left_assoc Step.context_subst_right_beta
  Step.context_subst_right_assoc Step.context_subst_left_refl_right
  Step.context_subst_left_refl_left Step.context_subst_right_refl_left
  Step.context_subst_right_refl_right Step.context_subst_left_idempotent
  Step.context_subst_right_cancel_inner Step.context_subst_right_cancel_outer

theorem step_complexity_lt {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : Step p q) : complexity q < complexity p := by
  cases h with
  | symm_refl a =>
      simp [complexity, size, leftSpine]
  | symm_symm p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | trans_refl_left p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | trans_refl_right p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | trans_symm p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | symm_trans p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | trans_assoc p q r =>
      simp [complexity, size, leftSpine]
      omega
  | symm_congr _ ih =>
      simp [complexity, size, leftSpine] at *
      omega
  | trans_congr_left _ _ ih =>
      simp [complexity, size, leftSpine] at *
      omega
  | trans_congr_right _ _ ih =>
      simp [complexity, size, leftSpine] at *
      omega
  | context_congr _ _ ih =>
      simp [complexity, size, leftSpine] at *
      omega
  | context_map_refl _ _ =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_tt_cancel_left _ p v =>
      simp [complexity, size, leftSpine]
      omega
  | context_tt_cancel_right _ p v =>
      simp [complexity, size, leftSpine]
      omega
  | context_subst_left_beta _ r p =>
      simp [complexity, size, leftSpine]
      omega
  | context_subst_left_of_right _ r p =>
      simp [complexity, size, leftSpine]
      omega
  | context_subst_left_assoc _ r p t =>
      simp [complexity, size, leftSpine]
      omega
  | context_subst_right_beta _ p t =>
      simp [complexity, size, leftSpine]
      omega
  | context_subst_right_assoc _ p t u =>
      simp [complexity, size, leftSpine]
      omega
  | context_subst_left_refl_right _ r =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_subst_left_refl_left _ p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_subst_right_refl_left _ r =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_subst_right_refl_right _ p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_subst_left_idempotent _ r p =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_subst_right_cancel_inner _ p t =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega
  | context_subst_right_cancel_outer _ p t =>
      apply complexity_lt_of_size_lt
      simp [size]
      omega

/-! ## Reflexive-Transitive Closures -/

inductive Rw {A : Type u} {a b : A} :
    PathExpr (A := A) (a := a) (b := b) →
    PathExpr (A := A) (a := a) (b := b) → Prop
  | refl (p : PathExpr (A := A) (a := a) (b := b)) : Rw p p
  | tail {p q r : PathExpr (A := A) (a := a) (b := b)} :
      Rw p q → Step q r → Rw p r

inductive RwPlus {A : Type u} {a b : A} :
    PathExpr (A := A) (a := a) (b := b) →
    PathExpr (A := A) (a := a) (b := b) → Prop
  | single {p q : PathExpr (A := A) (a := a) (b := b)} : Step p q → RwPlus p q
  | tail {p q r : PathExpr (A := A) (a := a) (b := b)} :
      RwPlus p q → Step q r → RwPlus p r

theorem rwPlus_complexity_lt {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : RwPlus p q) : complexity q < complexity p := by
  induction h with
  | single hstep =>
      exact step_complexity_lt hstep
  | tail _ hstep ih =>
      have hstep_lt := step_complexity_lt hstep
      exact lt_trans hstep_lt ih

/-! ## Termination -/

def Terminating {A : Type u} {a b : A} : Prop :=
  WellFounded (fun p q =>
    RwPlus (A := A) (a := a) (b := b) q p)

theorem acc_of_subrelation {α : Type u} {r s : α → α → Prop}
    (h : ∀ {a b}, r a b → s a b) {a : α} (ha : Acc s a) : Acc r a := by
  induction ha with
  | intro a hacc ih =>
      refine Acc.intro a ?_
      intro b hr
      exact ih _ (h hr)

theorem wellFounded_of_subrelation {α : Type u} {r s : α → α → Prop}
    (h : ∀ {a b}, r a b → s a b) (wf : WellFounded s) :
    WellFounded r :=
  ⟨fun a => acc_of_subrelation h (wf.apply a)⟩

theorem terminating (A : Type u) (a b : A) : Terminating (A := A) (a := a) (b := b) := by
  have wf :
      WellFounded (fun p q : PathExpr (A := A) (a := a) (b := b) =>
        complexity p < complexity q) :=
    InvImage.wf complexity Nat.lt_wfRel.wf
  refine wellFounded_of_subrelation ?_ wf
  intro p q hplus
  exact rwPlus_complexity_lt (A := A) (a := a) (b := b) hplus

/-! ## Compatibility with Path rewrites -/

theorem eval_step {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : Step p q) : Path.Rw (A := A) (a := a) (b := b) (eval p) (eval q) := by
  cases h with
  | symm_refl a =>
      simpa using Path.rw_of_step (Path.Step.symm_refl (A := A) a)
  | symm_symm p =>
      simpa using Path.rw_of_step (Path.Step.symm_symm (A := A) (p := eval p))
  | trans_refl_left p =>
      simpa using Path.rw_of_step (Path.Step.trans_refl_left (A := A) (p := eval p))
  | trans_refl_right p =>
      simpa using Path.rw_of_step (Path.Step.trans_refl_right (A := A) (p := eval p))
  | trans_symm p =>
      simpa using Path.rw_of_step (Path.Step.trans_symm (A := A) (p := eval p))
  | symm_trans p =>
      simpa using Path.rw_of_step (Path.Step.symm_trans (A := A) (p := eval p))
  | trans_assoc p q r =>
      simpa using Path.rw_of_step (Path.Step.trans_assoc (A := A)
        (p := eval p) (q := eval q) (r := eval r))
  | symm_congr _ hstep =>
      simpa using Path.rw_of_step
        (Path.Step.symm_congr (A := A) (p := eval _) (q := eval _) hstep)
  | trans_congr_left r hstep =>
      simpa using Path.rw_of_step
        (Path.Step.trans_congr_left (A := A) (r := eval r) hstep)
  | trans_congr_right p hstep =>
      simpa using Path.rw_of_step
        (Path.Step.trans_congr_right (A := A) (p := eval p) hstep)
  | context_congr C hstep =>
      simpa using Path.rw_of_step
        (Path.Step.context_congr (A := A) (B := _) (C := C) hstep)
  | context_map_refl C a =>
      simpa using
        Path.rw_of_eq (Context.map_refl (A := A) (B := _) (C := C) (a := a))
  | context_tt_cancel_left C p v =>
      simpa using Path.rw_of_step
        (Path.Step.context_tt_cancel_left (A := A) (B := _) (C := C)
          (p := eval p) (v := eval v))
  | context_tt_cancel_right C p v =>
      simpa using Path.rw_of_step
        (Path.Step.context_tt_cancel_right (A := A) (B := _) (C := C)
          (p := eval p) (v := eval v))
  | context_subst_left_beta C r p =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_left_beta (A := A) (B := _) (C := C)
          (r := eval r) (p := eval p))
  | context_subst_left_of_right C r p =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_left_of_right (A := A) (B := _) (C := C)
          (r := eval r) (p := eval p))
  | context_subst_left_assoc C r p t =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_left_assoc (A := A) (B := _) (C := C)
          (r := eval r) (p := eval p) (t := eval t))
  | context_subst_right_beta C p t =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_right_beta (A := A) (B := _) (C := C)
          (p := eval p) (t := eval t))
  | context_subst_right_assoc C p t u =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_right_assoc (A := A) (B := _) (C := C)
          (p := eval p) (t := eval t) (u := eval u))
  | context_subst_left_refl_right C r =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_left_refl_right (A := A) (B := _) (C := C)
          (r := eval r))
  | context_subst_left_refl_left C p =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_left_refl_left (A := A) (B := _) (C := C)
          (p := eval p))
  | context_subst_right_refl_left C r =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_right_refl_left (A := A) (B := _) (C := C)
          (r := eval r))
  | context_subst_right_refl_right C p =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_right_refl_right (A := A) (B := _) (C := C)
          (p := eval p))
  | context_subst_left_idempotent C r p =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_left_idempotent (A := A) (B := _) (C := C)
          (r := eval r) (p := eval p))
  | context_subst_right_cancel_inner C p t =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_right_cancel_inner (A := A) (B := _) (C := C)
          (p := eval p) (t := eval t))
  | context_subst_right_cancel_outer C p t =>
      simpa using Path.rw_of_step
        (Path.Step.context_subst_right_cancel_outer (A := A) (B := _) (C := C)
          (p := eval p) (t := eval t))

theorem eval_rw {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : Rw p q) :
    Path.Rw (A := A) (a := a) (b := b) (eval p) (eval q) := by
  induction h with
  | refl p =>
      exact Path.Rw.refl (eval p)
  | tail _ hstep ih =>
      exact Path.rw_trans ih (eval_step hstep)

/-! ## Confluence (Prop-Level) -/

/-- Join witnesses for expression rewrites. -/
structure Join {A : Type u} {a b : A}
    (p q : PathExpr (A := A) (a := a) (b := b)) where
  meet : PathExpr (A := A) (a := a) (b := b)
  left : Rw p meet
  right : Rw q meet

theorem join_refl {p : PathExpr (A := A) (a := a) (b := b)} :
    ∃ s, Rw p s ∧ Rw p s :=
  ⟨p, Rw.refl p, Rw.refl p⟩

@[simp] theorem rw_of_step {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : Step p q) : Rw p q :=
  Rw.tail (Rw.refl _) h

theorem rw_append {p q r : PathExpr (A := A) (a := a) (b := b)}
    (h1 : Rw p q) (h2 : Rw q r) : Rw p r := by
  induction h2 with
  | refl => exact h1
  | tail _ step ih => exact Rw.tail ih step

theorem rw_symm_congr {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : Rw p q) : Rw (PathExpr.symm p) (PathExpr.symm q) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih (Step.symm_congr step)

theorem rw_trans_congr_left
    {p q : PathExpr (A := A) (a := a) (b := b)}
    (r : PathExpr (A := A) (a := b) (b := c))
    (h : Rw p q) : Rw (PathExpr.trans p r) (PathExpr.trans q r) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih (Step.trans_congr_left r step)

theorem rw_trans_congr_right
    (p : PathExpr (A := A) (a := a) (b := b))
    {q r : PathExpr (A := A) (a := b) (b := c)}
    (h : Rw q r) : Rw (PathExpr.trans p q) (PathExpr.trans p r) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih (Step.trans_congr_right p step)

theorem rw_context_congr {A : Type u} {B : Type u}
    (C : Context A B) {a₁ a₂ : A}
    {p q : PathExpr (A := A) (a := a₁) (b := a₂)}
    (h : Rw p q) :
    Rw (PathExpr.context_map (A := A) (B := B) C p)
      (PathExpr.context_map (A := A) (B := B) C q) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih (Step.context_congr (C := C) step)

theorem rw_of_plus {p q : PathExpr (A := A) (a := a) (b := b)}
    (h : RwPlus p q) : Rw p q := by
  induction h with
  | single hstep => exact rw_of_step hstep
  | tail hplus hstep ih => exact Rw.tail ih hstep

theorem rw_plus_trans {p q r : PathExpr (A := A) (a := a) (b := b)}
    (h1 : RwPlus p q) (h2 : Rw q r) : RwPlus p r := by
  induction h2 with
  | refl => exact h1
  | tail _ step ih => exact RwPlus.tail ih step

theorem rw_uncons {p q : PathExpr (A := A) (a := a) (b := b)} (h : Rw p q) :
    p = q ∨ ∃ r, Step p r ∧ Rw r q := by
  induction h with
  | refl => exact Or.inl rfl
  | tail h step ih =>
    cases ih with
    | inl hpeq =>
        refine Or.inr ?_
        refine ⟨_, ?_, Rw.refl _⟩
        simpa [hpeq] using step
    | inr hdata =>
        rcases hdata with ⟨r, hstep, hrq⟩
        refine Or.inr ⟨r, hstep, ?_⟩
        exact Rw.tail hrq step

class HasLocalConfluenceProp.{v} : Prop where
  local_confluence : ∀ {A : Type v} {a b : A}
    {p q r : PathExpr (A := A) (a := a) (b := b)},
    Step p q → Step p r → ∃ s, Rw q s ∧ Rw r s

theorem local_confluence_prop [h : HasLocalConfluenceProp.{u}]
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Step p q) (hr : Step p r) : ∃ s, Rw q s ∧ Rw r s :=
  h.local_confluence hq hr

theorem confluence_prop [HasLocalConfluenceProp.{u}]
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Rw p q) (hr : Rw p r) :
    ∃ s, Rw q s ∧ Rw r s := by
  classical
  revert q r hq hr
  induction p using (terminating (A := A) (a := a) (b := b)).induction with
  | h p ih =>
    intro q r hq hr
    cases rw_uncons hq with
    | inl hq_eq =>
        refine ⟨r, ?_, Rw.refl r⟩
        simpa [hq_eq] using hr
    | inr hq_data =>
        rcases hq_data with ⟨p1, hp1, hq_rest⟩
        cases rw_uncons hr with
        | inl hr_eq =>
            refine ⟨q, Rw.refl q, ?_⟩
            simpa [hr_eq] using hq
        | inr hr_data =>
            rcases hr_data with ⟨p2, hp2, hr_rest⟩
            obtain ⟨s, hp1s, hp2s⟩ := local_confluence_prop (A := A) (a := a) (b := b) hp1 hp2
            obtain ⟨s1, hq_s1, hs_s1⟩ := ih p1 (RwPlus.single hp1) hq_rest hp1s
            obtain ⟨s2, hr_s2, hs_s2⟩ := ih p2 (RwPlus.single hp2) hr_rest hp2s
            have hplus_ps : RwPlus (A := A) (a := a) (b := b) p s :=
              rw_plus_trans (RwPlus.single hp1) hp1s
            obtain ⟨t, hs1t, hs2t⟩ := ih s hplus_ps hs_s1 hs_s2
            exact ⟨t, rw_append hq_s1 hs1t, rw_append hr_s2 hs2t⟩

theorem strip_lemma_prop [HasLocalConfluenceProp.{u}]
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hstep : Step p q) (hmulti : Rw p r) :
    ∃ s, Rw q s ∧ Rw r s :=
  confluence_prop (hq := rw_of_step hstep) (hr := hmulti)

noncomputable def confluence_of_local [HasLocalConfluenceProp.{u}]
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Rw p q) (hr : Rw p r) : Join q r :=
  have h := confluence_prop (A := A) (a := a) (b := b) hq hr
  let s := Classical.choose h
  let ⟨hqs, hrs⟩ := Classical.choose_spec h
  { meet := s, left := hqs, right := hrs }

theorem eval_confluence_prop [HasLocalConfluenceProp.{u}]
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Rw p q) (hr : Rw p r) :
    ∃ s : Path a b, Path.Rw (A := A) (a := a) (b := b) (eval q) s ∧
      Path.Rw (A := A) (a := a) (b := b) (eval r) s := by
  let j := confluence_of_local (A := A) (a := a) (b := b) hq hr
  exact ⟨eval j.meet, eval_rw j.left, eval_rw j.right⟩

/-! ## Core Critical Pairs (PathExpr) -/

section CriticalPairs

variable {A : Type u} {a b c d e : A}

@[simp] def idContext (A : Type u) : Context A A := ⟨id⟩

def join_of_rw_to_same {p q : PathExpr (A := A) (a := a) (b := b)}
    (s : PathExpr (A := A) (a := a) (b := b))
    (hq : Rw p s) (hr : Rw q s) : Join p q :=
  { meet := s, left := hq, right := hr }

def commute_trans_left_right
    {p₁ p₂ : PathExpr (A := A) (a := a) (b := b)}
    {q₁ q₂ : PathExpr (A := A) (a := b) (b := c)}
    (hp : Step p₁ p₂) (hq : Step q₁ q₂) :
    Join (PathExpr.trans p₂ q₁) (PathExpr.trans p₁ q₂) :=
  { meet := PathExpr.trans p₂ q₂
  , left := Rw.tail (Rw.refl _) (Step.trans_congr_right p₂ hq)
  , right := Rw.tail (Rw.refl _) (Step.trans_congr_left q₂ hp) }

def local_confluence_tt_rrr (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := b) (b := c)) :
    Join
      (PathExpr.trans p (PathExpr.trans q (PathExpr.refl c)))
      (PathExpr.trans p q) :=
  { meet := PathExpr.trans p q
  , left := Rw.tail (Rw.refl _) (Step.trans_congr_right p (Step.trans_refl_right q))
  , right := Rw.refl _ }

def local_confluence_tt_lrr (q : PathExpr (A := A) (a := a) (b := b))
    (r : PathExpr (A := A) (a := b) (b := c)) :
    Join
      (PathExpr.trans (PathExpr.refl a) (PathExpr.trans q r))
      (PathExpr.trans q r) :=
  { meet := PathExpr.trans q r
  , left := Rw.tail (Rw.refl _) (Step.trans_refl_left _)
  , right := Rw.refl _ }

def local_confluence_tt_tt (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := b) (b := c))
    (r : PathExpr (A := A) (a := c) (b := d))
    (s : PathExpr (A := A) (a := d) (b := e)) :
    Join
      (PathExpr.trans (PathExpr.trans p (PathExpr.trans q r)) s)
      (PathExpr.trans (PathExpr.trans p q) (PathExpr.trans r s)) :=
  { meet := PathExpr.trans p (PathExpr.trans q (PathExpr.trans r s))
  , left := Rw.tail
      (Rw.tail (Rw.refl _) (Step.trans_assoc p (PathExpr.trans q r) s))
      (Step.trans_congr_right p (Step.trans_assoc q r s))
  , right := Rw.tail (Rw.refl _) (Step.trans_assoc p q (PathExpr.trans r s)) }

def local_confluence_ss_sr (a : A) :
    Join
      (PathExpr.refl a)
      (PathExpr.symm (PathExpr.refl a)) :=
  { meet := PathExpr.refl a
  , left := Rw.refl _
  , right := Rw.tail (Rw.refl _) (Step.symm_refl a) }

def local_confluence_ss_stss
    (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := b) (b := c)) :
    Join
      (PathExpr.trans p q)
      (PathExpr.symm (PathExpr.trans (PathExpr.symm q) (PathExpr.symm p))) :=
  { meet := PathExpr.trans p q
  , left := Rw.refl _
  , right := Rw.tail
      (Rw.tail
        (Rw.tail (Rw.refl _) (Step.symm_congr (Step.trans_assoc (PathExpr.symm q) (PathExpr.symm p) (PathExpr.refl a))))
        (Step.trans_congr_left (PathExpr.symm (PathExpr.symm q)) (Step.symm_symm p)))
      (Step.trans_congr_right p (Step.symm_symm q)) }

def step_cancel_left_reassoc
    (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := a) (b := c)) :
    Step
      (PathExpr.trans p (PathExpr.trans (PathExpr.symm p) q))
      (PathExpr.trans (PathExpr.trans p (PathExpr.symm p)) q) := by
  have ctx_step :=
    Step.context_tt_cancel_left (C := (idContext A))
      (p := p) (v := q)
  simpa [idContext, Context.map, PathExpr.context_map] using ctx_step

def step_cancel_right_reassoc
    (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := b) (b := c)) :
    Step
      (PathExpr.trans (PathExpr.symm p) (PathExpr.trans p q))
      (PathExpr.trans (PathExpr.trans (PathExpr.symm p) p) q) := by
  have ctx_step :=
    Step.context_tt_cancel_left (C := (idContext A))
      (p := PathExpr.symm p) (v := q)
  simpa [idContext, Context.map, PathExpr.context_map, Path.symm_symm] using ctx_step

def local_confluence_tt_ts
    (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := a) (b := c)) :
    Join
      (PathExpr.trans p (PathExpr.trans (PathExpr.symm p) q))
      (PathExpr.trans (PathExpr.refl a) q) :=
  { meet := q
  , left := Rw.tail
      (Rw.tail
        (Rw.tail (Rw.refl _) (step_cancel_left_reassoc p q))
        (Step.trans_congr_left q (Step.trans_symm p)))
      (Step.trans_refl_left q)
  , right := Rw.tail (Rw.refl _) (Step.trans_refl_left q) }

def local_confluence_tt_st
    (p : PathExpr (A := A) (a := a) (b := b))
    (q : PathExpr (A := A) (a := b) (b := c)) :
    Join
      (PathExpr.trans (PathExpr.symm p) (PathExpr.trans p q))
      (PathExpr.trans (PathExpr.refl b) q) :=
  { meet := q
  , left := Rw.tail
      (Rw.tail
        (Rw.tail (Rw.refl _) (step_cancel_right_reassoc p q))
        (Step.trans_congr_left q (Step.symm_trans p)))
      (Step.trans_refl_left q)
  , right := Rw.tail (Rw.refl _) (Step.trans_refl_left q) }

end CriticalPairs

/-!
Local confluence for PathExpr is partially discharged by explicit critical pairs.
Remaining cases are still axiomatized, but the proof skeleton shows how the
critical pairs are wired.
-/

theorem pathExpr_local_confluence
    {p q r : PathExpr (A := A) (a := a) (b := b)}
    (hq : Step p q) (hr : Step p r) :
    ∃ s, Rw q s ∧ Rw r s := by
  classical
  have join_from : ∀ {x y : PathExpr (A := A) (a := a) (b := b)}, Join x y →
      ∃ s, Rw x s ∧ Rw y s := by
    intro x y j
    exact ⟨j.meet, j.left, j.right⟩
  induction hq generalizing r hr with
  | symm_congr hq ih =>
      cases hr with
      | symm_congr hr =>
          obtain ⟨s, hq_s, hr_s⟩ := ih hr
          refine ⟨PathExpr.symm s, ?_, ?_⟩
          · exact rw_symm_congr hq_s
          · exact rw_symm_congr hr_s
      | symm_refl _ =>
          cases hq
      | symm_symm _ =>
          cases hq
      | _ =>
          cases hr
  | trans_congr_left r hq ih =>
      cases hr with
      | trans_congr_left _ hr =>
          obtain ⟨s, hq_s, hr_s⟩ := ih hr
          refine ⟨PathExpr.trans s r, ?_, ?_⟩
          · exact rw_trans_congr_left r hq_s
          · exact rw_trans_congr_left r hr_s
      | trans_congr_right p hr =>
          refine ⟨_, (commute_trans_left_right hq hr).left, (commute_trans_left_right hq hr).right⟩
      | _ =>
          cases hr
  | trans_congr_right p hq ih =>
      cases hr with
      | trans_congr_right _ hr =>
          obtain ⟨s, hq_s, hr_s⟩ := ih hr
          refine ⟨PathExpr.trans p s, ?_, ?_⟩
          · exact rw_trans_congr_right p hq_s
          · exact rw_trans_congr_right p hr_s
      | context_subst_left_of_right C r p' =>
          cases hq with
          | context_subst_right_refl_right C' p'' =>
              refine ⟨PathExpr.context_subst_left (A := A) (B := _) C r p', ?_, ?_⟩
              · exact Rw.tail (Rw.refl _) (Step.context_subst_left_beta (C := C) (r := r) (p := p'))
              · exact Rw.refl _
      | trans_congr_left r hr =>
          refine ⟨_, (commute_trans_left_right hr hq).right, (commute_trans_left_right hr hq).left⟩
      | _ =>
          cases hr
  | context_congr C hq ih =>
      cases hr with
      | context_congr _ hr =>
          obtain ⟨s, hq_s, hr_s⟩ := ih hr
          refine ⟨PathExpr.context_map (A := A) (B := _) C s, ?_, ?_⟩
          · exact rw_context_congr (C := C) hq_s
          · exact rw_context_congr (C := C) hr_s
      | context_map_refl _ _ =>
          cases hq
      | _ =>
          cases hr
  | trans_assoc p q (PathExpr.refl c) =>
      cases hr with
      | trans_refl_right _ =>
          exact join_from (local_confluence_tt_rrr (A := A) (a := a) (b := b) (c := c) p q)
      | _ =>
          cases hr
  | trans_refl_right (PathExpr.trans p q) =>
      cases hr with
      | trans_assoc _ _ (PathExpr.refl c) =>
          exact join_from (local_confluence_tt_rrr (A := A) (a := a) (b := b) (c := c) p q)
      | _ =>
          cases hr
  | trans_assoc (PathExpr.refl a) q r =>
      cases hr with
      | trans_refl_left _ =>
          exact join_from (local_confluence_tt_lrr (A := A) (a := a) (b := b) (c := c) q r)
      | _ =>
          cases hr
  | trans_refl_left (PathExpr.trans q r) =>
      cases hr with
      | trans_assoc (PathExpr.refl a) _ _ =>
          exact join_from (local_confluence_tt_lrr (A := A) (a := a) (b := b) (c := c) q r)
      | _ =>
          cases hr
  | trans_assoc (PathExpr.trans p q) r s =>
      cases hr with
      | trans_assoc _ _ (PathExpr.trans _ _) =>
          exact join_from (local_confluence_tt_tt (A := A) (a := a) (b := b) (c := c) (d := d)
            (e := e) p q r s)
      | _ =>
          cases hr
  | symm_refl a =>
      cases hr with
      | symm_refl _ =>
          exact join_refl
      | _ =>
          cases (impossible (hq := Step.symm_refl a) (hr := hr))
  | symm_symm (PathExpr.refl a) =>
      cases hr with
      | symm_congr (Step.symm_refl _) =>
          exact join_from (local_confluence_ss_sr (A := A) (a := a))
      | _ =>
          cases hr
  | symm_symm p =>
      cases hr with
      | symm_symm _ =>
          exact join_refl
      | symm_congr _ =>
          cases hr
      | _ =>
          cases hr
  | trans_refl_left p =>
      cases hr with
      | trans_refl_left _ =>
          exact join_refl
      | trans_congr_right (PathExpr.refl a) hr =>
          refine ⟨_, ?_, ?_⟩
          · exact Rw.tail (Rw.refl _) hr
          · exact Rw.tail (Rw.refl _) (Step.trans_refl_left _)
      | _ =>
          cases hr
  | trans_refl_right p =>
      cases hr with
      | trans_refl_right _ =>
          exact join_refl
      | trans_congr_left (PathExpr.refl b) hr =>
          refine ⟨_, ?_, ?_⟩
          · exact Rw.tail (Rw.refl _) hr
          · exact Rw.tail (Rw.refl _) (Step.trans_refl_right _)
      | _ =>
          cases hr
  | trans_symm p =>
      cases hr with
      | trans_symm _ =>
          exact join_refl
      | _ =>
          cases hr
  | symm_trans p =>
      cases hr with
      | symm_trans _ =>
          exact join_refl
      | _ =>
          cases hr
  | trans_assoc p q r =>
      cases hr with
      | trans_assoc _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | trans_assoc p (PathExpr.symm p) q =>
      cases hr with
      | trans_congr_left _ (Step.trans_symm _) =>
          exact join_from (local_confluence_tt_ts (A := A) (a := a) (b := b) (c := c) p q)
      | _ =>
          cases hr
  | trans_assoc (PathExpr.symm p) p q =>
      cases hr with
      | trans_congr_left _ (Step.symm_trans _) =>
          exact join_from (local_confluence_tt_st (A := A) (a := a) (b := b) (c := c) p q)
      | _ =>
          cases hr
  | context_tt_cancel_left C p v =>
      cases hr with
      | context_tt_cancel_left _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | context_map_refl C a =>
      cases hr with
      | context_map_refl _ _ =>
          exact join_refl
      | context_congr _ h =>
          cases h
      | _ =>
          cases hr
  | context_tt_cancel_right C p v =>
      cases hr with
      | context_tt_cancel_right _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | context_subst_left_beta C r p =>
      cases hr with
      | context_subst_left_beta _ _ _ =>
          exact join_refl
      | trans_congr_right _ (Step.context_map_refl _ a) =>
          cases p with
          | refl _ =>
              refine ⟨r, ?_, ?_⟩
              · exact rw_of_step (Step.context_subst_left_refl_right (C := C) (r := r))
              · exact Rw.tail (Rw.refl _) (Step.trans_refl_right r)
      | _ =>
          cases hr
  | context_subst_left_of_right C r p =>
      cases hr with
      | context_subst_left_of_right _ _ _ =>
          exact join_refl
      | trans_congr_right _ (Step.context_subst_right_refl_right _ p') =>
          refine ⟨PathExpr.context_subst_left (A := A) (B := _) C r p, ?_, ?_⟩
          · exact Rw.refl _
          · exact Rw.tail (Rw.refl _) (Step.context_subst_left_beta (C := C) (r := r) (p := p))
      | _ =>
          cases hr
  | context_subst_left_assoc C r p t =>
      cases hr with
      | context_subst_left_assoc _ _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | context_subst_right_beta C p t =>
      cases hr with
      | context_subst_right_beta _ _ _ =>
          exact join_refl
      | trans_congr_left _ (Step.context_map_refl _ a) =>
          cases p with
          | refl _ =>
              refine ⟨t, ?_, ?_⟩
              · exact rw_of_step (Step.context_subst_right_refl_left (C := C) (r := t))
              · exact Rw.tail (Rw.refl _) (Step.trans_refl_left t)
      | _ =>
          cases hr
  | context_subst_right_assoc C p t u =>
      cases hr with
      | context_subst_right_assoc _ _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | context_subst_left_refl_right C r =>
      cases hr with
      | context_subst_left_refl_right _ _ =>
          exact join_refl
      | context_subst_left_refl_left _ p =>
          cases r with
          | refl _ =>
              cases p with
              | refl _ =>
                  refine ⟨PathExpr.refl (C.fill _), ?_, ?_⟩
                  · exact Rw.refl _
                  · exact Rw.tail (Rw.refl _) (Step.context_map_refl (C := C) (a := _))
      | _ =>
          cases hr
  | context_subst_left_refl_left C p =>
      cases hr with
      | context_subst_left_refl_left _ _ =>
          exact join_refl
      | context_subst_left_refl_right _ r =>
          cases r with
          | refl _ =>
              cases p with
              | refl _ =>
                  refine ⟨PathExpr.refl (C.fill _), ?_, ?_⟩
                  · exact Rw.tail (Rw.refl _) (Step.context_map_refl (C := C) (a := _))
                  · exact Rw.refl _
      | _ =>
          cases hr
  | context_subst_right_refl_left C r =>
      cases hr with
      | context_subst_right_refl_left _ _ =>
          exact join_refl
      | context_subst_right_refl_right _ p =>
          cases r with
          | refl _ =>
              cases p with
              | refl _ =>
                  refine ⟨PathExpr.refl (C.fill _), ?_, ?_⟩
                  · exact Rw.refl _
                  · exact Rw.tail (Rw.refl _) (Step.context_map_refl (C := C) (a := _))
      | _ =>
          cases hr
  | context_subst_right_refl_right C p =>
      cases hr with
      | context_subst_right_refl_right _ _ =>
          exact join_refl
      | context_subst_right_refl_left _ r =>
          cases r with
          | refl _ =>
              cases p with
              | refl _ =>
                  refine ⟨PathExpr.refl (C.fill _), ?_, ?_⟩
                  · exact Rw.tail (Rw.refl _) (Step.context_map_refl (C := C) (a := _))
                  · exact Rw.refl _
      | _ =>
          cases hr
  | context_subst_left_idempotent C r p =>
      cases hr with
      | context_subst_left_idempotent _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | context_subst_right_cancel_inner C p t =>
      cases hr with
      | context_subst_right_cancel_inner _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | context_subst_right_cancel_outer C p t =>
      cases hr with
      | context_subst_right_cancel_outer _ _ _ =>
          exact join_refl
      | _ =>
          cases hr
  | _ =>
      cases hr

noncomputable instance instHasLocalConfluenceProp : HasLocalConfluenceProp.{u} where
  local_confluence := pathExpr_local_confluence

end PathExpr
end Rewrite
end Path
end ComputationalPaths
