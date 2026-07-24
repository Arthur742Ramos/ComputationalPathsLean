/-
# Scoped raw syntax for a bounded predicative MLTT fragment

This module gives the source language used by the raw adequacy theorem.  It is
independent of Lean's dependent type theory and of the target rewrite system:
variables are de Bruijn indices, binders change the scope index in the type of
an expression, and renaming and simultaneous substitution are defined by
structural recursion.

The fragment contains dependent products and sums, level-indexed lifted natural
numbers, Tarski-style predicative universe codes, identity types, and the
explicitly supported equality-factored identity eliminator.  `nat level`,
`zero level`, and `succ level` remain in one universe throughout decoding and
computation.  The identity eliminator binds an endpoint and an identity proof
in its motive; it is deliberately not an eliminator whose motive can inspect a
target `Path.steps` trace.

The main metatheoretic result in this file is the complete substitution
algebra.  In particular, `Ren.lift` and `Sub.lift` are explicit definitions and
the proofs below establish their interaction with identity, composition, and
one- and two-variable instantiation.  No binder law is postulated.
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace RawMLTT

universe u

/-! ## Expressions and contexts -/

/-- Well-scoped raw expressions with `n` available de Bruijn variables.

The two arguments of `pi` and `sigma` use the usual convention that the
codomain has one additional variable.  The motive of `eqJ` has two additional
variables: first the endpoint and then its identity proof.  The successor case
of `natElim` similarly binds the predecessor and the induction hypothesis. -/
inductive Expr : Nat -> Type where
  | var {n : Nat} : Fin n -> Expr n
  | sort {n : Nat} : Nat -> Expr n
  | pi {n : Nat} : Expr n -> Expr (n + 1) -> Expr n
  | sigma {n : Nat} : Expr n -> Expr (n + 1) -> Expr n
  | lam {n : Nat} : Expr (n + 1) -> Expr n
  | app {n : Nat} : Expr n -> Expr n -> Expr n
  | pair {n : Nat} : Expr n -> Expr n -> Expr n
  | fst {n : Nat} : Expr n -> Expr n
  | snd {n : Nat} : Expr n -> Expr n
  | nat {n : Nat} : Nat -> Expr n
  | zero {n : Nat} : Nat -> Expr n
  | succ {n : Nat} : Nat -> Expr n -> Expr n
  | natElim {n : Nat} :
      Nat -> Expr (n + 1) -> Expr n -> Expr (n + 2) -> Expr n -> Expr n
  | codeNat {n : Nat} : Nat -> Expr n
  | codePi {n : Nat} : Expr n -> Expr (n + 1) -> Expr n
  | codeSigma {n : Nat} : Expr n -> Expr (n + 1) -> Expr n
  | codeId {n : Nat} : Expr n -> Expr n -> Expr n -> Expr n
  | el {n : Nat} : Expr n -> Expr n
  | id {n : Nat} : Expr n -> Expr n -> Expr n -> Expr n
  | refl {n : Nat} : Expr n -> Expr n
  | eqJ {n : Nat} :
      Expr (n + 2) -> Expr n -> Expr n -> Expr n -> Expr n
  deriving DecidableEq, Repr

/-- A raw context assigns a raw type, in the same ambient scope, to every
available variable.  `Ctx.extend` below performs the required weakening. -/
abbrev Ctx (n : Nat) := Fin n -> Expr n

/-- Renamings from an `n`-variable scope into an `m`-variable scope. -/
abbrev Ren (n m : Nat) := Fin n -> Fin m

namespace Ren

/-- Identity renaming. -/
def id (n : Nat) : Ren n n := fun i => i

/-- Composition, in the order in which renamings act on syntax. -/
def comp {n m k : Nat} (rho : Ren n m) (tau : Ren m k) : Ren n k :=
  fun i => tau (rho i)

/-- Weakening under one fresh binder. -/
def wk (n : Nat) : Ren n (n + 1) := Fin.succ

/-- Lift a renaming through one binder, fixing the newly bound variable. -/
def lift {n m : Nat} (rho : Ren n m) : Ren (n + 1) (m + 1) :=
  fun i => Fin.cases 0 (fun j => Fin.succ (rho j)) i

@[simp] theorem lift_zero {n m : Nat} (rho : Ren n m) :
    lift rho 0 = 0 := rfl

@[simp] theorem lift_succ {n m : Nat} (rho : Ren n m) (i : Fin n) :
    lift rho i.succ = (rho i).succ := rfl

@[simp] theorem comp_id_left {n m : Nat} (rho : Ren n m) :
    comp (id n) rho = rho := rfl

@[simp] theorem comp_id_right {n m : Nat} (rho : Ren n m) :
    comp rho (id m) = rho := rfl

@[simp] theorem comp_assoc {n m k l : Nat}
    (rho : Ren n m) (tau : Ren m k) (upsilon : Ren k l) :
    comp (comp rho tau) upsilon = comp rho (comp tau upsilon) := rfl

@[simp] theorem lift_id (n : Nat) :
    lift (id n) = id (n + 1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

@[simp] theorem lift_comp {n m k : Nat} (rho : Ren n m) (tau : Ren m k) :
    lift (comp rho tau) = comp (lift rho) (lift tau) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Weakening commutes with a lifted renaming.  This is the binder square used
in the renaming/substitution fusion proofs. -/
theorem wk_lift_natural {n m : Nat} (rho : Ren n m) :
    comp (wk n) (lift rho) = comp rho (wk m) := by
  funext i
  rfl

end Ren

/-! ## Renaming -/

/-- Capture-avoiding renaming.  Every binder recursively uses `Ren.lift`. -/
def rename {n m : Nat} (rho : Ren n m) : Expr n -> Expr m
  | .var i => .var (rho i)
  | .sort level => .sort level
  | .pi A B => .pi (rename rho A) (rename (Ren.lift rho) B)
  | .sigma A B => .sigma (rename rho A) (rename (Ren.lift rho) B)
  | .lam body => .lam (rename (Ren.lift rho) body)
  | .app f a => .app (rename rho f) (rename rho a)
  | .pair a b => .pair (rename rho a) (rename rho b)
  | .fst p => .fst (rename rho p)
  | .snd p => .snd (rename rho p)
  | .nat level => .nat level
  | .zero level => .zero level
  | .succ level t => .succ level (rename rho t)
  | .natElim level motive zeroCase succCase scrutinee =>
      .natElim
        level
        (rename (Ren.lift rho) motive)
        (rename rho zeroCase)
        (rename (Ren.lift (Ren.lift rho)) succCase)
        (rename rho scrutinee)
  | .codeNat level => .codeNat level
  | .codePi A B => .codePi (rename rho A) (rename (Ren.lift rho) B)
  | .codeSigma A B => .codeSigma (rename rho A) (rename (Ren.lift rho) B)
  | .codeId A a b => .codeId (rename rho A) (rename rho a) (rename rho b)
  | .el code => .el (rename rho code)
  | .id A a b => .id (rename rho A) (rename rho a) (rename rho b)
  | .refl a => .refl (rename rho a)
  | .eqJ motive reflCase endpoint proof =>
      .eqJ
        (rename (Ren.lift (Ren.lift rho)) motive)
        (rename rho reflCase)
        (rename rho endpoint)
        (rename rho proof)

@[simp] theorem rename_var {n m : Nat} (rho : Ren n m) (i : Fin n) :
    rename rho (.var i) = .var (rho i) := rfl

@[simp] theorem rename_id {n : Nat} (t : Expr n) :
    rename (Ren.id n) t = t := by
  induction t with
  | var i => rfl
  | sort level => rfl
  | pi A B ihA ihB => simp [rename, ihA, ihB]
  | sigma A B ihA ihB => simp [rename, ihA, ihB]
  | lam body ih => simp [rename, ih]
  | app f a ihf iha => simp [rename, ihf, iha]
  | pair a b iha ihb => simp [rename, iha, ihb]
  | fst p ih => simp [rename, ih]
  | snd p ih => simp [rename, ih]
  | nat level => rfl
  | zero level => rfl
  | succ level t ih => simp [rename, ih]
  | natElim level motive zeroCase succCase scrutinee ihm ihz ihs ihn =>
      simp [rename, ihm, ihz, ihs, ihn]
  | codeNat level => rfl
  | codePi A B ihA ihB => simp [rename, ihA, ihB]
  | codeSigma A B ihA ihB => simp [rename, ihA, ihB]
  | codeId A a b ihA iha ihb => simp [rename, ihA, iha, ihb]
  | el code ih => simp [rename, ih]
  | id A a b ihA iha ihb => simp [rename, ihA, iha, ihb]
  | refl a ih => simp [rename, ih]
  | eqJ motive reflCase endpoint proof ihm ihr ihe ihp =>
      simp [rename, ihm, ihr, ihe, ihp]

@[simp] theorem rename_comp {n m k : Nat}
    (rho : Ren n m) (tau : Ren m k) (t : Expr n) :
    rename tau (rename rho t) = rename (Ren.comp rho tau) t := by
  induction t generalizing m k with
  | var i => rfl
  | sort level => rfl
  | pi A B ihA ihB =>
      simp [rename, ihA, ihB, Ren.lift_comp]
  | sigma A B ihA ihB =>
      simp [rename, ihA, ihB, Ren.lift_comp]
  | lam body ih => simp [rename, ih, Ren.lift_comp]
  | app f a ihf iha => simp [rename, ihf, iha]
  | pair a b iha ihb => simp [rename, iha, ihb]
  | fst p ih => simp [rename, ih]
  | snd p ih => simp [rename, ih]
  | nat level => rfl
  | zero level => rfl
  | succ level t ih => simp [rename, ih]
  | natElim level motive zeroCase succCase scrutinee ihm ihz ihs ihn =>
      simp [rename, ihm, ihz, ihs, ihn, Ren.lift_comp]
  | codeNat level => rfl
  | codePi A B ihA ihB =>
      simp [rename, ihA, ihB, Ren.lift_comp]
  | codeSigma A B ihA ihB =>
      simp [rename, ihA, ihB, Ren.lift_comp]
  | codeId A a b ihA iha ihb => simp [rename, ihA, iha, ihb]
  | el code ih => simp [rename, ih]
  | id A a b ihA iha ihb => simp [rename, ihA, iha, ihb]
  | refl a ih => simp [rename, ih]
  | eqJ motive reflCase endpoint proof ihm ihr ihe ihp =>
      simp [rename, ihm, ihr, ihe, ihp, Ren.lift_comp]

/-! ## Simultaneous substitution -/

/-- Simultaneous substitutions from an `n`-variable scope into an `m`-variable
scope. -/
abbrev Sub (n m : Nat) := Fin n -> Expr m

namespace Sub

/-- Turn a renaming into the corresponding variable-only substitution. -/
def ofRen {n m : Nat} (rho : Ren n m) : Sub n m :=
  fun i => .var (rho i)

/-- Identity substitution. -/
def id (n : Nat) : Sub n n := ofRen (Ren.id n)

/-- Lift a simultaneous substitution through one binder.  Old images are
weakened explicitly, while index zero maps to the new variable. -/
def lift {n m : Nat} (sigma : Sub n m) : Sub (n + 1) (m + 1) :=
  fun i => Fin.cases (.var 0)
    (fun j => rename (Ren.wk m) (sigma j)) i

@[simp] theorem lift_zero {n m : Nat} (sigma : Sub n m) :
    lift sigma 0 = .var 0 := rfl

@[simp] theorem lift_succ {n m : Nat} (sigma : Sub n m) (i : Fin n) :
    lift sigma i.succ = rename (Ren.wk m) (sigma i) := rfl

@[simp] theorem lift_ofRen {n m : Nat} (rho : Ren n m) :
    lift (ofRen rho) = ofRen (Ren.lift rho) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

@[simp] theorem lift_id (n : Nat) :
    lift (id n) = id (n + 1) := by
  simp [id, Ren.lift_id]

end Sub

/-- Capture-avoiding simultaneous substitution. -/
def subst {n m : Nat} (sigma : Sub n m) : Expr n -> Expr m
  | .var i => sigma i
  | .sort level => .sort level
  | .pi A B => .pi (subst sigma A) (subst (Sub.lift sigma) B)
  | .sigma A B => .sigma (subst sigma A) (subst (Sub.lift sigma) B)
  | .lam body => .lam (subst (Sub.lift sigma) body)
  | .app f a => .app (subst sigma f) (subst sigma a)
  | .pair a b => .pair (subst sigma a) (subst sigma b)
  | .fst p => .fst (subst sigma p)
  | .snd p => .snd (subst sigma p)
  | .nat level => .nat level
  | .zero level => .zero level
  | .succ level t => .succ level (subst sigma t)
  | .natElim level motive zeroCase succCase scrutinee =>
      .natElim
        level
        (subst (Sub.lift sigma) motive)
        (subst sigma zeroCase)
        (subst (Sub.lift (Sub.lift sigma)) succCase)
        (subst sigma scrutinee)
  | .codeNat level => .codeNat level
  | .codePi A B => .codePi (subst sigma A) (subst (Sub.lift sigma) B)
  | .codeSigma A B => .codeSigma (subst sigma A) (subst (Sub.lift sigma) B)
  | .codeId A a b => .codeId (subst sigma A) (subst sigma a) (subst sigma b)
  | .el code => .el (subst sigma code)
  | .id A a b => .id (subst sigma A) (subst sigma a) (subst sigma b)
  | .refl a => .refl (subst sigma a)
  | .eqJ motive reflCase endpoint proof =>
      .eqJ
        (subst (Sub.lift (Sub.lift sigma)) motive)
        (subst sigma reflCase)
        (subst sigma endpoint)
        (subst sigma proof)

namespace Sub

/-- Composition, in the order in which simultaneous substitutions act. -/
def comp {n m k : Nat} (sigma : Sub n m) (tau : Sub m k) : Sub n k :=
  fun i => subst tau (sigma i)

end Sub

@[simp] theorem subst_ofRen {n m : Nat} (rho : Ren n m) (t : Expr n) :
    subst (Sub.ofRen rho) t = rename rho t := by
  induction t generalizing m with
  | var i => rfl
  | sort level => rfl
  | pi A B ihA ihB => simp [subst, rename, ihA, ihB]
  | sigma A B ihA ihB => simp [subst, rename, ihA, ihB]
  | lam body ih => simp [subst, rename, ih]
  | app f a ihf iha => simp [subst, rename, ihf, iha]
  | pair a b iha ihb => simp [subst, rename, iha, ihb]
  | fst p ih => simp [subst, rename, ih]
  | snd p ih => simp [subst, rename, ih]
  | nat level => rfl
  | zero level => rfl
  | succ level t ih => simp [subst, rename, ih]
  | natElim level motive zeroCase succCase scrutinee ihm ihz ihs ihn =>
      simp [subst, rename, ihm, ihz, ihs, ihn]
  | codeNat level => rfl
  | codePi A B ihA ihB => simp [subst, rename, ihA, ihB]
  | codeSigma A B ihA ihB => simp [subst, rename, ihA, ihB]
  | codeId A a b ihA iha ihb => simp [subst, rename, ihA, iha, ihb]
  | el code ih => simp [subst, rename, ih]
  | id A a b ihA iha ihb => simp [subst, rename, ihA, iha, ihb]
  | refl a ih => simp [subst, rename, ih]
  | eqJ motive reflCase endpoint proof ihm ihr ihe ihp =>
      simp [subst, rename, ihm, ihr, ihe, ihp]

@[simp] theorem subst_id {n : Nat} (t : Expr n) :
    subst (Sub.id n) t = t := by
  simp [Sub.id, subst_ofRen]

/-- Lifting commutes with post-renaming the images of a substitution. -/
theorem lift_rename {n m k : Nat} (sigma : Sub n m) (rho : Ren m k) :
    Sub.lift (fun i => rename rho (sigma i)) =
      fun i => rename (Ren.lift rho) (Sub.lift sigma i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Sub.lift_succ, rename_comp]
    rw [Ren.wk_lift_natural]

/-- Renaming after substitution fuses into a single simultaneous substitution. -/
theorem rename_subst {n m k : Nat} (rho : Ren m k)
    (sigma : Sub n m) (t : Expr n) :
    rename rho (subst sigma t) =
      subst (fun i => rename rho (sigma i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | sort level => rfl
  | pi A B ihA ihB =>
      simp only [subst, rename, ihA, ihB]
      rw [lift_rename]
  | sigma A B ihA ihB =>
      simp only [subst, rename, ihA, ihB]
      rw [lift_rename]
  | lam body ih =>
      simp only [subst, rename, ih]
      rw [lift_rename]
  | app f a ihf iha => simp [subst, rename, ihf, iha]
  | pair a b iha ihb => simp [subst, rename, iha, ihb]
  | fst p ih => simp [subst, rename, ih]
  | snd p ih => simp [subst, rename, ih]
  | nat level => rfl
  | zero level => rfl
  | succ level t ih => simp [subst, rename, ih]
  | natElim level motive zeroCase succCase scrutinee ihm ihz ihs ihn =>
      simp only [subst, rename, ihm, ihz, ihs, ihn]
      rw [lift_rename]
      rw [lift_rename]
  | codeNat level => rfl
  | codePi A B ihA ihB =>
      simp only [subst, rename, ihA, ihB]
      rw [lift_rename]
  | codeSigma A B ihA ihB =>
      simp only [subst, rename, ihA, ihB]
      rw [lift_rename]
  | codeId A a b ihA iha ihb => simp [subst, rename, ihA, iha, ihb]
  | el code ih => simp [subst, rename, ih]
  | id A a b ihA iha ihb => simp [subst, rename, ihA, iha, ihb]
  | refl a ih => simp [subst, rename, ih]
  | eqJ motive reflCase endpoint proof ihm ihr ihe ihp =>
      simp only [subst, rename, ihm, ihr, ihe, ihp]
      rw [lift_rename]
      rw [lift_rename]

/-- Lifting commutes with pre-renaming the variables of a substitution. -/
theorem lift_precomp {n m k : Nat} (rho : Ren n m) (sigma : Sub m k) :
    (fun i => Sub.lift sigma (Ren.lift rho i)) =
      Sub.lift (fun i => sigma (rho i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

/-- Substitution after renaming fuses by precomposing the substitution. -/
theorem subst_rename {n m k : Nat} (sigma : Sub m k)
    (rho : Ren n m) (t : Expr n) :
    subst sigma (rename rho t) =
      subst (fun i => sigma (rho i)) t := by
  induction t generalizing m k with
  | var i => rfl
  | sort level => rfl
  | pi A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [lift_precomp]
  | sigma A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [lift_precomp]
  | lam body ih =>
      simp only [rename, subst, ih]
      rw [lift_precomp]
  | app f a ihf iha => simp [rename, subst, ihf, iha]
  | pair a b iha ihb => simp [rename, subst, iha, ihb]
  | fst p ih => simp [rename, subst, ih]
  | snd p ih => simp [rename, subst, ih]
  | nat level => rfl
  | zero level => rfl
  | succ level t ih => simp [rename, subst, ih]
  | natElim level motive zeroCase succCase scrutinee ihm ihz ihs ihn =>
      simp only [rename, subst, ihm, ihz, ihs, ihn]
      rw [lift_precomp]
      rw [lift_precomp]
      rw [lift_precomp]
  | codeNat level => rfl
  | codePi A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [lift_precomp]
  | codeSigma A B ihA ihB =>
      simp only [rename, subst, ihA, ihB]
      rw [lift_precomp]
  | codeId A a b ihA iha ihb => simp [rename, subst, ihA, iha, ihb]
  | el code ih => simp [rename, subst, ih]
  | id A a b ihA iha ihb => simp [rename, subst, ihA, iha, ihb]
  | refl a ih => simp [rename, subst, ih]
  | eqJ motive reflCase endpoint proof ihm ihr ihe ihp =>
      simp only [rename, subst, ihm, ihr, ihe, ihp]
      rw [lift_precomp]
      rw [lift_precomp]

/-- Lifting preserves substitution composition. -/
theorem lift_comp {n m k : Nat} (sigma : Sub n m) (tau : Sub m k) :
    Sub.lift (Sub.comp sigma tau) =
      Sub.comp (Sub.lift sigma) (Sub.lift tau) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Sub.lift_succ, Sub.comp]
    rw [subst_rename, rename_subst]
    rfl

/-- Associativity of simultaneous substitution on every expression. -/
@[simp] theorem subst_comp {n m k : Nat}
    (sigma : Sub n m) (tau : Sub m k) (t : Expr n) :
    subst tau (subst sigma t) = subst (Sub.comp sigma tau) t := by
  induction t generalizing m k with
  | var i => rfl
  | sort level => rfl
  | pi A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [lift_comp]
  | sigma A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [lift_comp]
  | lam body ih =>
      simp only [subst, ih]
      rw [lift_comp]
  | app f a ihf iha => simp [subst, ihf, iha]
  | pair a b iha ihb => simp [subst, iha, ihb]
  | fst p ih => simp [subst, ih]
  | snd p ih => simp [subst, ih]
  | nat level => rfl
  | zero level => rfl
  | succ level t ih => simp [subst, ih]
  | natElim level motive zeroCase succCase scrutinee ihm ihz ihs ihn =>
      simp only [subst, ihm, ihz, ihs, ihn]
      rw [lift_comp]
      rw [lift_comp]
  | codeNat level => rfl
  | codePi A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [lift_comp]
  | codeSigma A B ihA ihB =>
      simp only [subst, ihA, ihB]
      rw [lift_comp]
  | codeId A a b ihA iha ihb => simp [subst, ihA, iha, ihb]
  | el code ih => simp [subst, ih]
  | id A a b ihA iha ihb => simp [subst, ihA, iha, ihb]
  | refl a ih => simp [subst, ih]
  | eqJ motive reflCase endpoint proof ihm ihr ihe ihp =>
      simp only [subst, ihm, ihr, ihe, ihp]
      rw [lift_comp]
      rw [lift_comp]

/-! ## Instantiation and contexts -/

/-- Substitute one expression for the most recently bound variable. -/
def instantiate {n : Nat} (body : Expr (n + 1)) (argument : Expr n) : Expr n :=
  subst (fun i => Fin.cases argument (fun j => .var j) i) body

/-- Substitute an endpoint and a proof into a two-variable motive. -/
def instantiate₂ {n : Nat} (motive : Expr (n + 2))
    (endpoint proof : Expr n) : Expr n :=
  subst
    (fun i => Fin.cases proof
      (fun j => Fin.cases endpoint (fun k => .var k) j) i)
    motive

@[simp] theorem instantiate_weaken {n : Nat} (t argument : Expr n) :
    instantiate (rename (Ren.wk n) t) argument = t := by
  unfold instantiate
  rw [subst_rename]
  change subst (Sub.id n) t = t
  exact subst_id t

@[simp] theorem instantiate₂_weaken {n : Nat} (t : Expr (n + 1))
    (endpoint proof : Expr n) :
    instantiate₂ (rename (Ren.wk (n + 1)) t) endpoint proof =
      instantiate t endpoint := by
  unfold instantiate₂ instantiate
  rw [subst_rename]
  rfl

@[simp] theorem instantiate₂_weaken₂ {n : Nat} (t : Expr n)
    (endpoint proof : Expr n) :
    instantiate₂
        (rename (Ren.wk (n + 1)) (rename (Ren.wk n) t))
        endpoint proof =
      t := by
  rw [instantiate₂_weaken, instantiate_weaken]

@[simp] theorem instantiate_rename {n m : Nat} (rho : Ren n m)
    (body : Expr (n + 1)) (argument : Expr n) :
    rename rho (instantiate body argument) =
      instantiate (rename (Ren.lift rho) body) (rename rho argument) := by
  simp only [instantiate, rename_subst, subst_rename]
  apply _root_.congrArg (fun sigma => subst sigma body)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · rfl

@[simp] theorem instantiate_subst {n m : Nat} (sigma : Sub n m)
    (body : Expr (n + 1)) (argument : Expr n) :
    subst sigma (instantiate body argument) =
      instantiate (subst (Sub.lift sigma) body) (subst sigma argument) := by
  simp only [instantiate, subst_comp]
  apply _root_.congrArg (fun tau => subst tau body)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · simp only [Sub.comp, Sub.lift_succ, subst_rename]
    change sigma j = subst (Sub.id m) (sigma j)
    exact (subst_id (sigma j)).symm

@[simp] theorem instantiate₂_rename {n m : Nat} (rho : Ren n m)
    (motive : Expr (n + 2)) (endpoint proof : Expr n) :
    rename rho (instantiate₂ motive endpoint proof) =
      instantiate₂ (rename (Ren.lift (Ren.lift rho)) motive)
        (rename rho endpoint) (rename rho proof) := by
  simp only [instantiate₂, rename_subst, subst_rename]
  apply _root_.congrArg (fun tau => subst tau motive)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · rfl

@[simp] theorem instantiate₂_subst {n m : Nat} (sigma : Sub n m)
    (motive : Expr (n + 2)) (endpoint proof : Expr n) :
    subst sigma (instantiate₂ motive endpoint proof) =
      instantiate₂ (subst (Sub.lift (Sub.lift sigma)) motive)
        (subst sigma endpoint) (subst sigma proof) := by
  simp only [instantiate₂, subst_comp]
  apply _root_.congrArg (fun tau => subst tau motive)
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · simp only [Sub.comp, Sub.lift_succ, subst_rename]
      change sigma k = subst (Sub.id m) (sigma k)
      exact (subst_id (sigma k)).symm

namespace Ctx

/-- The empty context. -/
def empty : Ctx 0 := Fin.elim0

/-- Extend a context by one type, explicitly weakening every declaration. -/
def extend {n : Nat} (Gamma : Ctx n) (A : Expr n) : Ctx (n + 1) :=
  fun i => Fin.cases (rename (Ren.wk n) A)
    (fun j => rename (Ren.wk n) (Gamma j)) i

@[simp] theorem extend_zero {n : Nat} (Gamma : Ctx n) (A : Expr n) :
    extend Gamma A 0 = rename (Ren.wk n) A := rfl

@[simp] theorem extend_succ {n : Nat} (Gamma : Ctx n)
    (A : Expr n) (i : Fin n) :
    extend Gamma A i.succ = rename (Ren.wk n) (Gamma i) := rfl

end Ctx

/-! ## Computational-path certificates for the structural laws -/

/-- Typed evidence that the two fundamental structural equations are not merely
prose: each is exposed as a trace-carrying `Path`, and the identity path has a
genuine target-system unit coherence. -/
structure StructuralPathCertificate {n m k : Nat}
    (t : Expr n) (sigma : Sub n m) (tau : Sub m k) where
  renamingIdentity : Path (rename (Ren.id n) t) t
  substitutionIdentity : Path (subst (Sub.id n) t) t
  substitutionComposition :
    Path (subst tau (subst sigma t)) (subst (Sub.comp sigma tau) t)
  identityUnit :
    RwEq
      (Path.trans renamingIdentity (Path.refl t))
      renamingIdentity

/-- Build the structural certificate from the proved laws.  `stepChain` records
the structural equations as explicit trace entries rather than erasing them. -/
noncomputable def structuralPathCertificate {n m k : Nat}
    (t : Expr n) (sigma : Sub n m) (tau : Sub m k) :
    StructuralPathCertificate t sigma tau := by
  let pRen : Path (rename (Ren.id n) t) t :=
    Path.stepChain (rename_id t)
  let pSub : Path (subst (Sub.id n) t) t :=
    Path.stepChain (subst_id t)
  let pComp :
      Path (subst tau (subst sigma t)) (subst (Sub.comp sigma tau) t) :=
    Path.stepChain (subst_comp sigma tau t)
  exact
    { renamingIdentity := pRen
      substitutionIdentity := pSub
      substitutionComposition := pComp
      identityUnit :=
        rweq_of_step (Path.Step.trans_refl_right pRen) }

end RawMLTT
end TypeTheory
end Path
end ComputationalPaths
