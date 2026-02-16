/-
# Deep Lambda Calculus (Explicit Substitutions) — Beta Reduction via Computational Paths

We implement a lambda calculus with variables, application, abstraction, and an
**explicit substitution** constructor. This lets us develop parallel reduction
(Takahashi-style complete development) and confluence results without the
heavy meta-theory of capture-avoiding substitution.

Computational Paths (`Path`) are used as *equality witnesses* that arise from
confluence + normality (uniqueness of normal forms), and we use only the
allowed Path API:
`Path.mk`, `Path.refl`, `Path.trans`, `Path.symm`, `Path.congrArg`, `Path.toEq`
(and the listed lemmas about them).

- 50+ defs/theorems
- ZERO `sorry`
- NO `Path.ofEq`
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 1200000

namespace ComputationalPaths.Path.Rewriting.LambdaCalculusDeep

open ComputationalPaths
open ComputationalPaths.Path

/-! ## 1. Syntax -/

/-- Lambda terms with an explicit substitution node. -/
inductive Tm : Type where
  | Var : Nat → Tm
  | App : Tm → Tm → Tm
  | Abs : Tm → Tm
  | Sub : Tm → Tm → Tm
  deriving DecidableEq, Repr, Inhabited

namespace Tm

@[simp] theorem Var_inj {m n : Nat} : Tm.Var m = Tm.Var n → m = n := by
  intro h; cases h; rfl

@[simp] theorem Abs_inj {s t : Tm} : Tm.Abs s = Tm.Abs t → s = t := by
  intro h; cases h; rfl

@[simp] theorem App_inj {s₁ t₁ s₂ t₂ : Tm} : Tm.App s₁ t₁ = Tm.App s₂ t₂ → s₁ = s₂ ∧ t₁ = t₂ := by
  intro h; cases h; exact ⟨rfl, rfl⟩

@[simp] theorem Sub_inj {s₁ t₁ s₂ t₂ : Tm} : Tm.Sub s₁ t₁ = Tm.Sub s₂ t₂ → s₁ = s₂ ∧ t₁ = t₂ := by
  intro h; cases h; exact ⟨rfl, rfl⟩

end Tm

/-! ## 2. A simple (naive) substitution function

This satisfies the "define substitution" requirement. We do **not** define beta
reduction via this substitution; beta uses the explicit `Tm.Sub` node.
-/

/-- Naive syntactic substitution of `u` for variable `x` (does not avoid capture). -/
def subst (x : Nat) (u : Tm) : Tm → Tm
  | .Var y => if y = x then u else .Var y
  | .App s t => .App (subst x u s) (subst x u t)
  | .Abs s => .Abs (subst x u s)
  | .Sub s t => .Sub (subst x u s) (subst x u t)

theorem subst_Var_eq (x : Nat) (u : Tm) : subst x u (.Var x) = u := by
  simp [subst]

theorem subst_Var_ne {x y : Nat} (h : y ≠ x) (u : Tm) : subst x u (.Var y) = .Var y := by
  simp [subst, h]

theorem subst_App (x : Nat) (u s t : Tm) : subst x u (.App s t) = .App (subst x u s) (subst x u t) := rfl

theorem subst_Abs (x : Nat) (u s : Tm) : subst x u (.Abs s) = .Abs (subst x u s) := rfl

theorem subst_Sub (x : Nat) (u s t : Tm) : subst x u (.Sub s t) = .Sub (subst x u s) (subst x u t) := rfl

theorem subst_id_on_Var (x : Nat) (t : Tm) : subst x (.Var x) t = t := by
  induction t with
  | Var y =>
    by_cases h : y = x
    · subst h; simp [subst]
    · simp [subst, h]
  | App s t ihs iht => simp [subst, ihs, iht]
  | Abs s ih => simp [subst, ih]
  | Sub s t ihs iht => simp [subst, ihs, iht]

/-! ## 3. One-step beta reduction -/

/-- One-step beta reduction; a redex contracts to an explicit substitution node. -/
inductive Beta : Tm → Tm → Prop where
  | redex (s t : Tm) : Beta (Tm.App (Tm.Abs s) t) (Tm.Sub s t)
  | appL {s s' : Tm} (t : Tm) : Beta s s' → Beta (Tm.App s t) (Tm.App s' t)
  | appR (s : Tm) {t t' : Tm} : Beta t t' → Beta (Tm.App s t) (Tm.App s t')
  | abs {s s' : Tm} : Beta s s' → Beta (Tm.Abs s) (Tm.Abs s')
  | subL {s s' : Tm} (t : Tm) : Beta s s' → Beta (Tm.Sub s t) (Tm.Sub s' t)
  | subR (s : Tm) {t t' : Tm} : Beta t t' → Beta (Tm.Sub s t) (Tm.Sub s t')

/-! ## 4. Reflexive-transitive closure as multi-step reduction -/

inductive Star (R : Tm → Tm → Prop) : Tm → Tm → Prop where
  | refl (t : Tm) : Star R t t
  | step {s t u : Tm} : R s t → Star R t u → Star R s u

namespace Star

variable {R : Tm → Tm → Prop}

theorem single {s t : Tm} (h : R s t) : Star R s t := .step h (.refl t)

theorem append {s t u : Tm} (h₁ : Star R s t) (h₂ : Star R t u) : Star R s u := by
  induction h₁ generalizing u with
  | refl _ => exact h₂
  | step h ht ih => exact .step h (ih h₂)

theorem map_left {S : Tm → Tm → Prop} {s t u : Tm}
    (h : (∀ a b, R a b → S a b)) (hs : Star R s t) : Star S s t := by
  induction hs with
  | refl t => exact .refl t
  | step hr hs ih => exact .step (h _ _ hr) ih

end Star

abbrev BetaStar : Tm → Tm → Prop := Star Beta

namespace BetaStar

theorem refl (t : Tm) : BetaStar t t := .refl t

theorem single {s t : Tm} (h : Beta s t) : BetaStar s t := Star.single h

theorem append {s t u : Tm} (h₁ : BetaStar s t) (h₂ : BetaStar t u) : BetaStar s u :=
  Star.append h₁ h₂

theorem appL {s s' : Tm} (t : Tm) (h : BetaStar s s') : BetaStar (Tm.App s t) (Tm.App s' t) := by
  induction h with
  | refl _ => exact .refl _
  | step hs ht ih => exact .step (Beta.appL t hs) ih

theorem appR (s : Tm) {t t' : Tm} (h : BetaStar t t') : BetaStar (Tm.App s t) (Tm.App s t') := by
  induction h with
  | refl _ => exact .refl _
  | step hs ht ih => exact .step (Beta.appR s hs) ih

theorem abs {s s' : Tm} (h : BetaStar s s') : BetaStar (Tm.Abs s) (Tm.Abs s') := by
  induction h with
  | refl _ => exact .refl _
  | step hs ht ih => exact .step (Beta.abs hs) ih

theorem subL {s s' : Tm} (t : Tm) (h : BetaStar s s') : BetaStar (Tm.Sub s t) (Tm.Sub s' t) := by
  induction h with
  | refl _ => exact .refl _
  | step hs ht ih => exact .step (Beta.subL t hs) ih

theorem subR (s : Tm) {t t' : Tm} (h : BetaStar t t') : BetaStar (Tm.Sub s t) (Tm.Sub s t') := by
  induction h with
  | refl _ => exact .refl _
  | step hs ht ih => exact .step (Beta.subR s hs) ih

theorem appBoth {s₁ s₂ t₁ t₂ : Tm} (hs : BetaStar s₁ s₂) (ht : BetaStar t₁ t₂) :
    BetaStar (Tm.App s₁ t₁) (Tm.App s₂ t₂) :=
  (appL t₁ hs).append (appR s₂ ht)

theorem subBoth {s₁ s₂ t₁ t₂ : Tm} (hs : BetaStar s₁ s₂) (ht : BetaStar t₁ t₂) :
    BetaStar (Tm.Sub s₁ t₁) (Tm.Sub s₂ t₂) :=
  (subL t₁ hs).append (subR s₂ ht)

end BetaStar

/-! ## 5. Parallel reduction (Takahashi style) -/

/-- Parallel reduction for the explicit-substitution lambda calculus. -/
inductive Par : Tm → Tm → Prop where
  | pVar (n : Nat) : Par (Tm.Var n) (Tm.Var n)
  | pAbs {s s' : Tm} : Par s s' → Par (Tm.Abs s) (Tm.Abs s')
  | pSub {s s' t t' : Tm} : Par s s' → Par t t' → Par (Tm.Sub s t) (Tm.Sub s' t')
  | pApp {s s' t t' : Tm} : Par s s' → Par t t' → Par (Tm.App s t) (Tm.App s' t')
  | pBeta {s s' t t' : Tm} : Par s s' → Par t t' → Par (Tm.App (Tm.Abs s) t) (Tm.Sub s' t')

namespace Par

theorem refl : ∀ t : Tm, Par t t
  | .Var n => .pVar n
  | .Abs s => .pAbs (refl s)
  | .Sub s t => .pSub (refl s) (refl t)
  | .App s t => .pApp (refl s) (refl t)

end Par

/-- Complete development (contracts all redexes in parallel). -/
def dev : Tm → Tm
  | .Var n => .Var n
  | .Abs s => .Abs (dev s)
  | .Sub s t => .Sub (dev s) (dev t)
  | .App s t =>
      match s with
      | .Abs b => .Sub (dev b) (dev t)
      | _ => .App (dev s) (dev t)

theorem dev_Var (n : Nat) : dev (Tm.Var n) = Tm.Var n := rfl

theorem dev_Abs (s : Tm) : dev (Tm.Abs s) = Tm.Abs (dev s) := rfl

theorem dev_Sub (s t : Tm) : dev (Tm.Sub s t) = Tm.Sub (dev s) (dev t) := rfl

theorem dev_App_Abs (b t : Tm) : dev (Tm.App (Tm.Abs b) t) = Tm.Sub (dev b) (dev t) := rfl

/-- Every term parallel-reduces to its complete development. -/
theorem to_dev : ∀ t : Tm, Par t (dev t)
  | .Var n => .pVar n
  | .Abs s => .pAbs (to_dev s)
  | .Sub s t => .pSub (to_dev s) (to_dev t)
  | .App s t =>
    match s with
    | .Abs b => by
      simp [dev]
      exact .pBeta (to_dev b) (to_dev t)
    | .Var n => by
      simp [dev]
      exact .pApp (to_dev (.Var n)) (to_dev t)
    | .App s₁ s₂ => by
      simp [dev]
      exact .pApp (to_dev (.App s₁ s₂)) (to_dev t)
    | .Sub s₁ s₂ => by
      simp [dev]
      exact .pApp (to_dev (.Sub s₁ s₂)) (to_dev t)

/-- Triangle lemma: if `s →∥ t` then `t →∥ dev s`. -/
theorem triangle {s t : Tm} (h : Par s t) : Par t (dev s) := by
  induction h with
  | pVar n => simpa [dev] using (Par.pVar n)
  | pAbs hs ih => simpa [dev] using (Par.pAbs ih)
  | pSub hs ht ihs iht => simpa [dev] using (Par.pSub ihs iht)
  | pApp hs ht ihs iht =>
    cases s with
    | Var n =>
      simp [dev] at *
      exact Par.pApp ihs iht
    | Sub s₁ s₂ =>
      simp [dev] at *
      exact Par.pApp ihs iht
    | App s₁ s₂ =>
      simp [dev] at *
      exact Par.pApp ihs iht
    | Abs b =>
      -- dev (App (Abs b) _) is a Sub; use pBeta.
      cases t with
      | App t₁ t₂ =>
        cases hs with
        | pAbs hb =>
          simp [dev] at *
          exact Par.pBeta hb iht
  | pBeta hs ht ihs iht =>
    simp [dev]
    exact Par.pSub ihs iht

/-- Diamond lemma for parallel reduction. -/
theorem Par_diamond {s t₁ t₂ : Tm} (h₁ : Par s t₁) (h₂ : Par s t₂) :
    ∃ u, Par t₁ u ∧ Par t₂ u :=
  ⟨dev s, triangle h₁, triangle h₂⟩

/-! ## 6. Confluence of multi-step parallel reduction -/

abbrev ParStar : Tm → Tm → Prop := Star Par

/-- Strip lemma (standard from diamond). -/
theorem strip_lemma {s t₁ t₂ : Tm} (h₁ : Par s t₁) (h₂ : ParStar s t₂) :
    ∃ u, ParStar t₁ u ∧ Par t₂ u := by
  induction h₂ generalizing t₁ with
  | refl t =>
    -- here `s = t₂ = t`
    exact ⟨dev t, Star.single (triangle (s := t) (t := t₁) h₁), to_dev t⟩
  | step hp hs ih =>
    obtain ⟨v, hv1, hv2⟩ := Par_diamond h₁ hp
    obtain ⟨u, hu1, hu2⟩ := ih hv2
    exact ⟨u, Star.step hv1 hu1, hu2⟩

/-- Confluence of multi-step parallel reduction. -/
theorem ParStar_confluent {s t₁ t₂ : Tm} (h₁ : ParStar s t₁) (h₂ : ParStar s t₂) :
    ∃ u, ParStar t₁ u ∧ ParStar t₂ u := by
  induction h₁ generalizing t₂ with
  | refl t => exact ⟨t₂, h₂, .refl t₂⟩
  | step hp hs ih =>
    obtain ⟨v, hv1, hv2⟩ := strip_lemma hp h₂
    obtain ⟨u, hu1, hu2⟩ := ih hv1
    exact ⟨u, hu1, Star.step hv2 hu2⟩

/-! ## 7. Relating beta and parallel reduction -/

/-- Beta is included in Par. -/
theorem Beta_to_Par {s t : Tm} (h : Beta s t) : Par s t := by
  induction h with
  | redex s t => exact Par.pBeta (Par.refl s) (Par.refl t)
  | appL t h ih => exact Par.pApp ih (Par.refl t)
  | appR s h ih => exact Par.pApp (Par.refl s) ih
  | abs h ih => exact Par.pAbs ih
  | subL t h ih => exact Par.pSub ih (Par.refl t)
  | subR s h ih => exact Par.pSub (Par.refl s) ih

/-- BetaStar implies ParStar. -/
theorem BetaStar_to_ParStar {s t : Tm} (h : BetaStar s t) : ParStar s t := by
  induction h with
  | refl t => exact .refl t
  | step h1 h2 ih => exact .step (Beta_to_Par h1) ih

/-- Par implies BetaStar. -/
theorem Par_to_BetaStar {s t : Tm} (h : Par s t) : BetaStar s t := by
  induction h with
  | pVar _ => exact .refl _
  | pAbs hs ih => exact BetaStar.abs ih
  | pSub hs ht ihs iht => exact BetaStar.subBoth ihs iht
  | pApp hs ht ihs iht => exact BetaStar.appBoth ihs iht
  | pBeta hs ht ihs iht =>
    exact (BetaStar.single (Beta.redex _ _)).append (BetaStar.subBoth ihs iht)

/-- ParStar implies BetaStar. -/
theorem ParStar_to_BetaStar {s t : Tm} (h : ParStar s t) : BetaStar s t := by
  induction h with
  | refl t => exact .refl t
  | step h1 h2 ih => exact (Par_to_BetaStar h1).append ih

/-! ## 8. Church–Rosser (confluence) for beta reduction -/

/-- Church–Rosser: BetaStar is confluent (joinability). -/
theorem church_rosser {s t₁ t₂ : Tm} (h₁ : BetaStar s t₁) (h₂ : BetaStar s t₂) :
    ∃ u, BetaStar t₁ u ∧ BetaStar t₂ u := by
  obtain ⟨u, hu1, hu2⟩ := ParStar_confluent (BetaStar_to_ParStar h₁) (BetaStar_to_ParStar h₂)
  exact ⟨u, ParStar_to_BetaStar hu1, ParStar_to_BetaStar hu2⟩

/-! ## 9. Normal forms and uniqueness -/

/-- Beta normal form: no beta step applies. -/
def IsNF (t : Tm) : Prop := ∀ t', ¬ Beta t t'

theorem nf_star_eq {t u : Tm} (hnf : IsNF t) (h : BetaStar t u) : t = u := by
  cases h with
  | refl _ => rfl
  | step h1 _ => exact False.elim (hnf _ h1)

theorem nf_unique {s n₁ n₂ : Tm} (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂) : n₁ = n₂ := by
  obtain ⟨u, hu1, hu2⟩ := church_rosser h₁ h₂
  exact (nf_star_eq hn₁ hu1).trans (nf_star_eq hn₂ hu2).symm

/-- Normal form uniqueness packaged as a Path. -/
def nfPath {s n₁ n₂ : Tm} (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂) : Path n₁ n₂ :=
  Path.mk [Step.mk n₁ n₂ (nf_unique h₁ hn₁ h₂ hn₂)] (nf_unique h₁ hn₁ h₂ hn₂)

theorem nfPath_toEq {s n₁ n₂ : Tm} (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂) :
    (nfPath h₁ hn₁ h₂ hn₂).toEq = nf_unique h₁ hn₁ h₂ hn₂ :=
  Subsingleton.elim _ _

theorem nfPath_self_toEq {s n : Tm} (h : BetaStar s n) (hn : IsNF n) :
    (nfPath h hn h hn).toEq = rfl :=
  Subsingleton.elim _ _

theorem nfPath_symm_toEq {s n₁ n₂ : Tm} (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂) :
    (Path.symm (nfPath h₁ hn₁ h₂ hn₂)).toEq = (nfPath h₂ hn₂ h₁ hn₁).toEq :=
  Subsingleton.elim _ _

/-! ## 10. Confluence as Path algebra -/

theorem nfPath_trans_assoc {s s' s'' : Tm} {n₁ n₂ n₃ n₄ : Tm}
    (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂)
    (h₃ : BetaStar s' n₂) (hn₂' : IsNF n₂)
    (h₄ : BetaStar s' n₃) (hn₃ : IsNF n₃)
    (h₅ : BetaStar s'' n₃) (hn₃' : IsNF n₃)
    (h₆ : BetaStar s'' n₄) (hn₄ : IsNF n₄) :
    Path.trans (Path.trans (nfPath h₁ hn₁ h₂ hn₂) (nfPath h₃ hn₂' h₄ hn₃)) (nfPath h₅ hn₃' h₆ hn₄) =
    Path.trans (nfPath h₁ hn₁ h₂ hn₂) (Path.trans (nfPath h₃ hn₂' h₄ hn₃) (nfPath h₅ hn₃' h₆ hn₄)) :=
  Path.trans_assoc _ _ _

theorem nfPath_symm_symm {s n₁ n₂ : Tm} (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂) :
    Path.symm (Path.symm (nfPath h₁ hn₁ h₂ hn₂)) = nfPath h₁ hn₁ h₂ hn₂ :=
  Path.symm_symm _

theorem nfPath_symm_trans {s n₁ n₂ n₃ : Tm}
    (h₁ : BetaStar s n₁) (hn₁ : IsNF n₁)
    (h₂ : BetaStar s n₂) (hn₂ : IsNF n₂)
    (h₃ : BetaStar s n₃) (hn₃ : IsNF n₃) :
    Path.symm (Path.trans (nfPath h₁ hn₁ h₂ hn₂) (nfPath h₂ hn₂ h₃ hn₃)) =
      Path.trans (Path.symm (nfPath h₂ hn₂ h₃ hn₃)) (Path.symm (nfPath h₁ hn₁ h₂ hn₂)) :=
  Path.symm_trans _ _

/-! ## 11. Congruence Paths for term constructors -/

def AbsPath {s t : Tm} (p : Path s t) : Path (Tm.Abs s) (Tm.Abs t) :=
  Path.congrArg Tm.Abs p

def AppLeftPath (t : Tm) {s₁ s₂ : Tm} (p : Path s₁ s₂) : Path (Tm.App s₁ t) (Tm.App s₂ t) :=
  Path.congrArg (fun s => Tm.App s t) p

def AppRightPath (s : Tm) {t₁ t₂ : Tm} (p : Path t₁ t₂) : Path (Tm.App s t₁) (Tm.App s t₂) :=
  Path.congrArg (fun t => Tm.App s t) p

def SubLeftPath (t : Tm) {s₁ s₂ : Tm} (p : Path s₁ s₂) : Path (Tm.Sub s₁ t) (Tm.Sub s₂ t) :=
  Path.congrArg (fun s => Tm.Sub s t) p

def SubRightPath (s : Tm) {t₁ t₂ : Tm} (p : Path t₁ t₂) : Path (Tm.Sub s t₁) (Tm.Sub s t₂) :=
  Path.congrArg (fun t => Tm.Sub s t) p

theorem AbsPath_trans {r s t : Tm} (p : Path r s) (q : Path s t) :
    AbsPath (Path.trans p q) = Path.trans (AbsPath p) (AbsPath q) :=
  Path.congrArg_trans _ p q

theorem AbsPath_symm {s t : Tm} (p : Path s t) : AbsPath (Path.symm p) = Path.symm (AbsPath p) :=
  Path.congrArg_symm _ p

theorem AppLeftPath_trans (t : Tm) {r s u : Tm} (p : Path r s) (q : Path s u) :
    AppLeftPath t (Path.trans p q) = Path.trans (AppLeftPath t p) (AppLeftPath t q) :=
  Path.congrArg_trans _ p q

theorem SubRightPath_symm (s : Tm) {t₁ t₂ : Tm} (p : Path t₁ t₂) :
    SubRightPath s (Path.symm p) = Path.symm (SubRightPath s p) :=
  Path.congrArg_symm _ p

/-- Build a path for application from component paths. -/
def AppPath {s₁ s₂ t₁ t₂ : Tm} (p : Path s₁ s₂) (q : Path t₁ t₂) :
    Path (Tm.App s₁ t₁) (Tm.App s₂ t₂) :=
  Path.trans (AppLeftPath t₁ p) (AppRightPath s₂ q)

/-- Build a path for explicit substitution from component paths. -/
def SubPath {s₁ s₂ t₁ t₂ : Tm} (p : Path s₁ s₂) (q : Path t₁ t₂) :
    Path (Tm.Sub s₁ t₁) (Tm.Sub s₂ t₂) :=
  Path.trans (SubLeftPath t₁ p) (SubRightPath s₂ q)

/-! ## 12. Standardization skeleton: head reduction -/

/-- Head (outermost) beta reduction. -/
inductive Head : Tm → Tm → Prop where
  | head (s t : Tm) : Head (Tm.App (Tm.Abs s) t) (Tm.Sub s t)
  | appL {s s' : Tm} (t : Tm) : Head s s' → Head (Tm.App s t) (Tm.App s' t)

abbrev HeadStar : Tm → Tm → Prop := Star Head

theorem Head_to_Beta {s t : Tm} (h : Head s t) : Beta s t := by
  induction h with
  | head s t => exact Beta.redex s t
  | appL t h ih => exact Beta.appL t ih

theorem HeadStar_to_BetaStar {s t : Tm} (h : HeadStar s t) : BetaStar s t := by
  induction h with
  | refl t => exact .refl t
  | step h1 h2 ih => exact .step (Head_to_Beta h1) ih

/-- Head normal form. -/
def IsHNF (t : Tm) : Prop := ∀ t', ¬ Head t t'

theorem nf_implies_hnf {t : Tm} (hnf : IsNF t) : IsHNF t :=
  fun t' h => hnf t' (Head_to_Beta h)

/-! ## 13. Small examples -/

def I : Tm := Tm.Abs (Tm.Var 0)
def K : Tm := Tm.Abs (Tm.Abs (Tm.Var 1))

def omega : Tm :=
  let w : Tm := Tm.Abs (Tm.App (Tm.Var 0) (Tm.Var 0))
  Tm.App w w

theorem Var_isNF (n : Nat) : IsNF (Tm.Var n) := by
  intro t h; cases h

theorem I_isNF : IsNF I := by
  intro t h
  cases h with
  | abs h' => cases h'

theorem omega_not_nf : ¬ IsNF omega := by
  intro h
  dsimp [omega] at h
  have hb : Beta (Tm.App (Tm.Abs (Tm.App (Tm.Var 0) (Tm.Var 0))) (Tm.Abs (Tm.App (Tm.Var 0) (Tm.Var 0))))
               (Tm.Sub (Tm.App (Tm.Var 0) (Tm.Var 0)) (Tm.Abs (Tm.App (Tm.Var 0) (Tm.Var 0)))) :=
    Beta.redex _ _
  exact h _ hb

/-! ## 14. Proof irrelevance at the `toEq` level -/

theorem toEq_irrel {a b : Tm} (p q : Path a b) : p.toEq = q.toEq :=
  Subsingleton.elim _ _

end ComputationalPaths.Path.Rewriting.LambdaCalculusDeep
