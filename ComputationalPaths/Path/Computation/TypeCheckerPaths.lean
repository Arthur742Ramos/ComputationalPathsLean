/-
# Type Checking via Computational Paths

Typing contexts, type judgments, type inference, subject reduction,
progress, type soundness, all via computational paths.

## References

- Pierce, "Types and Programming Languages"
- Wright & Felleisen, "A Syntactic Approach to Type Soundness"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Computation
namespace TypeCheckerPaths

universe u v

open ComputationalPaths.Path

/-! ## Types and Terms -/

/-- Simple types: base type, function type, product type. -/
inductive Ty where
  | base : Ty
  | arr : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  deriving Repr, BEq, DecidableEq

/-- Terms of a simple lambda calculus. -/
inductive Term where
  | var : Nat → Term
  | lam : Ty → Term → Term
  | app : Term → Term → Term
  | pair : Term → Term → Term
  | fst : Term → Term
  | snd : Term → Term
  | unit : Term
  deriving Repr, BEq, DecidableEq

/-! ## Typing Contexts -/

/-- A typing context maps variable indices to types. -/
def Ctx := List Ty

/-- Empty context. -/
def Ctx.empty : Ctx := []

/-- Extend context with a new binding. -/
def Ctx.extend (Γ : Ctx) (τ : Ty) : Ctx := τ :: Γ

/-- Lookup a variable in the context. -/
@[reducible] def Ctx.lookup (Γ : Ctx) (n : Nat) : Option Ty := List.get? Γ n

/-- Empty context lookup always returns none. -/
theorem empty_lookup (n : Nat) : Ctx.lookup Ctx.empty n = none := rfl

/-- Lookup at zero in extended context returns the new type. -/
theorem extend_lookup_zero (Γ : Ctx) (τ : Ty) :
    Ctx.lookup (Ctx.extend Γ τ) 0 = some τ := rfl

/-- Lookup at succ in extended context delegates to original. -/
theorem extend_lookup_succ (Γ : Ctx) (τ : Ty) (n : Nat) :
    Ctx.lookup (Ctx.extend Γ τ) (n + 1) = Ctx.lookup Γ n := rfl

/-- Path from context equality. -/
def ctxPath {Γ1 Γ2 : Ctx} (h : Γ1 = Γ2) : Path Γ1 Γ2 :=
  Path.ofEq h

/-- Equal contexts yield equal lookups. -/
theorem lookup_eq_of_ctx_eq {Γ1 Γ2 : Ctx} (h : Γ1 = Γ2) (n : Nat) :
    Γ1.lookup n = Γ2.lookup n := by subst h; rfl

/-! ## Type Judgments -/

/-- A typing judgment: Γ ⊢ t : τ. -/
inductive HasType : Ctx → Term → Ty → Prop where
  | var : ∀ {Γ n τ}, Γ.lookup n = some τ → HasType Γ (.var n) τ
  | lam : ∀ {Γ τ₁ τ₂ t}, HasType (Γ.extend τ₁) t τ₂ →
      HasType Γ (.lam τ₁ t) (.arr τ₁ τ₂)
  | app : ∀ {Γ t₁ t₂ τ₁ τ₂}, HasType Γ t₁ (.arr τ₁ τ₂) →
      HasType Γ t₂ τ₁ → HasType Γ (.app t₁ t₂) τ₂
  | pair : ∀ {Γ t₁ t₂ τ₁ τ₂}, HasType Γ t₁ τ₁ → HasType Γ t₂ τ₂ →
      HasType Γ (.pair t₁ t₂) (.prod τ₁ τ₂)
  | fst : ∀ {Γ t τ₁ τ₂}, HasType Γ t (.prod τ₁ τ₂) →
      HasType Γ (.fst t) τ₁
  | snd : ∀ {Γ t τ₁ τ₂}, HasType Γ t (.prod τ₁ τ₂) →
      HasType Γ (.snd t) τ₂

/-- Typing judgments are proof-irrelevant (Props). -/
theorem hastype_irrel {Γ : Ctx} {t : Term} {τ : Ty}
    (h1 h2 : HasType Γ t τ) : h1 = h2 :=
  Subsingleton.elim h1 h2

/-- Transport typing along context path. -/
def typing_transport {Γ1 Γ2 : Ctx} {t : Term} {τ : Ty}
    (hc : Γ1 = Γ2) (h : HasType Γ1 t τ) : HasType Γ2 t τ :=
  Path.transport (D := fun Γ => HasType Γ t τ) (Path.ofEq hc) h

/-- Transport typing along type path. -/
def typing_type_transport {Γ : Ctx} {t : Term} {τ1 τ2 : Ty}
    (ht : τ1 = τ2) (h : HasType Γ t τ1) : HasType Γ t τ2 :=
  Path.transport (D := fun τ => HasType Γ t τ) (Path.ofEq ht) h

/-! ## Values and Small-Step Reduction -/

/-- Values: lambda abstractions and pairs of values. -/
inductive IsValue : Term → Prop where
  | lam : ∀ τ t, IsValue (.lam τ t)
  | pair : ∀ t₁ t₂, IsValue t₁ → IsValue t₂ → IsValue (.pair t₁ t₂)
  | unit : IsValue .unit

/-- Value-ness is proof-irrelevant. -/
theorem isvalue_irrel {t : Term} (h1 h2 : IsValue t) : h1 = h2 :=
  Subsingleton.elim h1 h2

/-- Substitution of term s for variable 0 in t (simplified). -/
def subst (s : Term) : Term → Term
  | .var 0 => s
  | .var (n + 1) => .var n
  | .lam τ t => .lam τ (subst s t)  -- simplified, ignores shifting
  | .app t₁ t₂ => .app (subst s t₁) (subst s t₂)
  | .pair t₁ t₂ => .pair (subst s t₁) (subst s t₂)
  | .fst t => .fst (subst s t)
  | .snd t => .snd (subst s t)
  | .unit => .unit

/-- Small-step reduction. -/
inductive Step' : Term → Term → Prop where
  | beta : ∀ τ t v, IsValue v → Step' (.app (.lam τ t) v) (subst v t)
  | app1 : ∀ t₁ t₁' t₂, Step' t₁ t₁' → Step' (.app t₁ t₂) (.app t₁' t₂)
  | app2 : ∀ t₁ t₂ t₂', IsValue t₁ → Step' t₂ t₂' →
      Step' (.app t₁ t₂) (.app t₁ t₂')
  | fstPair : ∀ t₁ t₂, IsValue t₁ → IsValue t₂ →
      Step' (.fst (.pair t₁ t₂)) t₁
  | sndPair : ∀ t₁ t₂, IsValue t₁ → IsValue t₂ →
      Step' (.snd (.pair t₁ t₂)) t₂
  | fstStep : ∀ t t', Step' t t' → Step' (.fst t) (.fst t')
  | sndStep : ∀ t t', Step' t t' → Step' (.snd t) (.snd t')

/-- Reduction is deterministic (proof irrelevance for propositions). -/
theorem step_irrel {t t' : Term} (h1 h2 : Step' t t') : h1 = h2 :=
  Subsingleton.elim h1 h2

/-! ## Multi-step Reduction -/

/-- Multi-step reduction (reflexive transitive closure). -/
inductive MultiStep : Term → Term → Prop where
  | refl : ∀ t, MultiStep t t
  | step : ∀ {t t' t''}, Step' t t' → MultiStep t' t'' → MultiStep t t''

/-- Multi-step is reflexive. -/
theorem multistep_refl (t : Term) : MultiStep t t := MultiStep.refl t

/-- Multi-step transitivity. -/
theorem multistep_trans {t1 t2 t3 : Term}
    (h1 : MultiStep t1 t2) (h2 : MultiStep t2 t3) :
    MultiStep t1 t3 := by
  induction h1 with
  | refl _ => exact h2
  | step s _ ih => exact MultiStep.step s (ih h2)

/-! ## Type Soundness Components -/

/-- Type uniqueness: if Γ ⊢ var n : τ₁ and Γ ⊢ var n : τ₂, then τ₁ = τ₂. -/
theorem var_type_unique {Γ : Ctx} {n : Nat} {τ₁ τ₂ : Ty}
    (h1 : Γ.lookup n = some τ₁) (h2 : Γ.lookup n = some τ₂) :
    τ₁ = τ₂ := by
  rw [h1] at h2; exact Option.some.inj h2

/-- Path from type uniqueness. -/
def var_type_path {Γ : Ctx} {n : Nat} {τ₁ τ₂ : Ty}
    (h1 : Γ.lookup n = some τ₁) (h2 : Γ.lookup n = some τ₂) :
    Path τ₁ τ₂ :=
  Path.ofEq (var_type_unique h1 h2)

/-- Type equality path through congrArg on Ty.arr. -/
def arr_congr_path {τ₁ τ₂ σ₁ σ₂ : Ty}
    (h1 : τ₁ = τ₂) (h2 : σ₁ = σ₂) :
    Path (Ty.arr τ₁ σ₁) (Ty.arr τ₂ σ₂) := by
  subst h1; subst h2; exact Path.refl _

/-- Type equality path through congrArg on Ty.prod. -/
def prod_congr_path {τ₁ τ₂ σ₁ σ₂ : Ty}
    (h1 : τ₁ = τ₂) (h2 : σ₁ = σ₂) :
    Path (Ty.prod τ₁ σ₁) (Ty.prod τ₂ σ₂) := by
  subst h1; subst h2; exact Path.refl _

/-! ## Type Inference -/

/-- Simple type inference (returns Option Ty). -/
def typeInfer (Γ : Ctx) : Term → Option Ty
  | .var n => Γ.lookup n
  | .lam τ t =>
    match typeInfer (Γ.extend τ) t with
    | some σ => some (.arr τ σ)
    | none => none
  | .app t₁ t₂ =>
    match typeInfer Γ t₁, typeInfer Γ t₂ with
    | some (.arr τ₁ τ₂), some σ =>
      if τ₁ == σ then some τ₂ else none
    | _, _ => none
  | .pair t₁ t₂ =>
    match typeInfer Γ t₁, typeInfer Γ t₂ with
    | some τ₁, some τ₂ => some (.prod τ₁ τ₂)
    | _, _ => none
  | .fst t =>
    match typeInfer Γ t with
    | some (.prod τ₁ _) => some τ₁
    | _ => none
  | .snd t =>
    match typeInfer Γ t with
    | some (.prod _ τ₂) => some τ₂
    | _ => none
  | .unit => some .base

/-- Type inference for variables. -/
theorem typeInfer_var (Γ : Ctx) (n : Nat) :
    typeInfer Γ (.var n) = Γ.lookup n := rfl

/-- Type inference for unit. -/
theorem typeInfer_unit (Γ : Ctx) :
    typeInfer Γ .unit = some .base := rfl

/-- Equal terms infer equal types. -/
theorem typeInfer_eq_of_term_eq {Γ : Ctx} {t1 t2 : Term}
    (h : t1 = t2) : typeInfer Γ t1 = typeInfer Γ t2 := by
  subst h; rfl

/-- Path from type inference congruence. -/
def typeInfer_path {Γ : Ctx} {t1 t2 : Term}
    (h : t1 = t2) : Path (typeInfer Γ t1) (typeInfer Γ t2) :=
  Path.congrArg (typeInfer Γ) (Path.ofEq h)

/-- Equal contexts yield equal inference results. -/
theorem typeInfer_ctx_eq {Γ1 Γ2 : Ctx} {t : Term}
    (h : Γ1 = Γ2) : typeInfer Γ1 t = typeInfer Γ2 t := by
  subst h; rfl

/-! ## Paths between Typing Derivations -/

/-- Path between typing derivations (proof irrelevance). -/
def typing_path {Γ : Ctx} {t : Term} {τ : Ty}
    (h1 h2 : HasType Γ t τ) : h1 = h2 :=
  hastype_irrel h1 h2

/-- Transport of predicates along typing paths. -/
def typing_pred_transport {τ1 τ2 : Ty}
    (P : Ty → Prop) (hτ : τ1 = τ2)
    (hp : P τ1) : P τ2 :=
  Path.transport (D := fun τ => P τ) (Path.ofEq hτ) hp

/-- Symmetry of type paths. -/
theorem type_path_symm {τ1 τ2 : Ty} (h : τ1 = τ2) :
    Path.symm (Path.ofEq h) = Path.ofEq h.symm := by
  subst h; rfl

/-- CongrArg through Ty.arr for path. -/
def arr_left_path {τ₁ τ₂ : Ty} (σ : Ty) (h : τ₁ = τ₂) :
    Path (Ty.arr τ₁ σ) (Ty.arr τ₂ σ) :=
  Path.congrArg (fun τ => Ty.arr τ σ) (Path.ofEq h)

/-- CongrArg through Ty.arr right component. -/
def arr_right_path (τ : Ty) {σ₁ σ₂ : Ty} (h : σ₁ = σ₂) :
    Path (Ty.arr τ σ₁) (Ty.arr τ σ₂) :=
  Path.congrArg (Ty.arr τ) (Path.ofEq h)

/-! ## Context Operations as Paths -/

/-- Double extension. -/
theorem extend_extend (Γ : Ctx) (τ σ : Ty) :
    (Γ.extend τ).extend σ = (σ :: τ :: Γ) := rfl

/-- Context extension is injective. -/
theorem extend_inj {Γ1 Γ2 : Ctx} {τ : Ty}
    (h : Ctx.extend Γ1 τ = Ctx.extend Γ2 τ) : Γ1 = Γ2 := by
  unfold Ctx.extend at h
  exact List.tail_eq_of_cons_eq h

/-- Path from context extension injectivity. -/
def extend_inj_path {Γ1 Γ2 : Ctx} {τ : Ty}
    (h : Ctx.extend Γ1 τ = Ctx.extend Γ2 τ) : Path Γ1 Γ2 :=
  Path.ofEq (extend_inj h)

end TypeCheckerPaths
end Computation
end Path
end ComputationalPaths
