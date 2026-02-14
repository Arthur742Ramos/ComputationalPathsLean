/-
# Primitive rewrite steps on computational paths

This module defines the `Step` relation capturing single `rw`-style reductions
between computational paths. These are the atomic rewrites that form the basis
of the computational paths rewriting system.

## Overview

The `Step` relation implements the rewrite rules from the computational paths
theory. Each constructor corresponds to a specific algebraic law for path
operations (symmetry, transitivity, congruence, etc.).

## Rule Categories

The constructors are organized into several categories:

### Basic Path Algebra (Rules 1-8)
- `symm_refl`, `symm_symm`: Symmetry simplifications
- `trans_refl_left`, `trans_refl_right`: Identity laws for composition
- `trans_symm`, `symm_trans`: Inverse laws
- `symm_trans_congr`: Contravariance of symmetry over composition
- `trans_assoc`: Associativity of path composition

### Product Types (Rules 9-16)
- `prod_fst_beta`, `prod_snd_beta`: Projection β-rules
- `prod_rec_beta`: Recursor β-rule
- `prod_eta`: η-expansion for products
- `prod_mk_symm`, `prod_map_congrArg`: Structural rules

### Dependent Pairs / Sigma Types (Rules 17-22)
- `sigma_fst_beta`, `sigma_snd_beta`: Projection β-rules
- `sigma_eta`: η-expansion for sigma types
- `sigma_mk_symm`: Symmetry for sigma constructor

### Sum Types (Rules 23-24)
- `sum_rec_inl_beta`, `sum_rec_inr_beta`: Recursor β-rules for coproducts

### Function Types (Rules 25-28)
- `fun_app_beta`: Application β-rule
- `fun_eta`: η-expansion for functions
- `lam_congr_symm`: Symmetry for function congruence

### Dependent Application (Rule 29)
- `apd_refl`: Dependent application on reflexivity

### Transport (Rules 30-36)
- `transport_refl_beta`: Transport along reflexivity
- `transport_trans_beta`: Transport along composition
- `transport_symm_left_beta`, `transport_symm_right_beta`: Transport with symmetry
- `transport_sigmaMk_*`: Transport through sigma constructors

### Context Rules (Rules 37-52)
- `context_congr`, `context_map_symm`: Basic context operations
- `context_subst_*`: Substitution rules for contexts
- `depContext_*`: Dependent context variants
- `biContext_*`, `depBiContext_*`: Binary context rules

### Structural Rules (Rules 53-56)
- `symm_congr`, `trans_congr_left`, `trans_congr_right`: Congruence closure
- `trans_cancel_left`, `trans_cancel_right`: Completion rules for confluence

## Usage

The `Step` relation is typically used through its closures:
- `Rw`: Reflexive-transitive closure (multi-step rewriting)
- `RwEq`: Equivalence closure (bidirectional rewriting)

All rules are registered as `[simp]` lemmas via `step_toEq`.

## References

- de Queiroz, de Oliveira & Ramos, "Propositional equality, identity types,
  and direct computational paths", SAJL 2016
- Ramos et al., "Explicit Computational Paths", SAJL 2018
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Basic.Context
import ComputationalPaths.Path.Basic.Congruence
import ComputationalPaths.Path.Basic.Congruence

namespace ComputationalPaths
namespace Path

open scoped Quot

universe u v w

/-- A single rewrite step between computational paths.

Each constructor represents an atomic rewrite rule. The relation captures
the computational content of path equality: two paths are related by `Step`
if one can be obtained from the other by applying a single rewrite rule.

See the module documentation for a complete list of rule categories. -/
inductive Step :
  {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Rule 1: Symmetry of reflexivity is reflexivity. `symm(refl) ▷ refl` -/
  | symm_refl {A : Type u} (a : A) :
      Step (A := A) (symm (Path.refl a)) (Path.refl a)
  /-- Rule 2: Double symmetry cancels. `symm(symm(p)) ▷ p` -/
  | symm_symm {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (symm (symm p)) p
  /-- Rule 3: Left identity for composition. `refl ∘ p ▷ p` -/
  | trans_refl_left {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans (Path.refl a) p) p
  /-- Rule 4: Right identity for composition. `p ∘ refl ▷ p` -/
  | trans_refl_right {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans p (Path.refl b)) p
  /-- Rule 5: Right inverse law. `p ∘ symm(p) ▷ refl` -/
  | trans_symm {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans p (symm p)) (Path.refl a)
  /-- Rule 6: Left inverse law. `symm(p) ∘ p ▷ refl` -/
  | symm_trans {A : Type u} {a b : A} (p : Path a b) :
      Step (A := A) (trans (symm p) p) (Path.refl b)
  /-- Rule 7: Contravariance of symmetry. `symm(p ∘ q) ▷ symm(q) ∘ symm(p)` -/
  | symm_trans_congr {A : Type u} {a b c : A} (p : Path a b) (q : Path b c) :
      Step (A := A) (symm (trans p q)) (trans (symm q) (symm p))
  /-- Rule 8: Associativity of composition. `(p ∘ q) ∘ r ▷ p ∘ (q ∘ r)` -/
  | trans_assoc {A : Type u} {a b c d : A}
      (p : Path a b) (q : Path b c) (r : Path c d) :
      Step (A := A) (trans (trans p q) r) (trans p (trans q r))
  /-- Rule 9: Decomposition of binary map. `map2 f p q ▷ mapRight f a₁ q ∘ mapLeft f p b₂` -/
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
  /-- Rule 10: First projection β-rule. `fst(mk(p, q)) ▷ p` -/
  | prod_fst_beta
    {A : Type u} {B : Type u}
      {a1 a2 : A} {b1 b2 : B}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg Prod.fst
          (Path.map2 (A := A) (B := B) (C := Prod A B) Prod.mk p q))
        p
  /-- Rule 11: Second projection β-rule. `snd(mk(p, q)) ▷ q` -/
  | prod_snd_beta
    {A : Type u} {B : Type u}
      {a1 a2 : B} {b1 b2 : A}
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg Prod.snd
          (Path.map2 (A := B) (B := A) (C := Prod B A) Prod.mk p q))
        q
  /-- Rule 12: Product recursor β-rule. `rec f (mk(p, q)) ▷ map2 f p q` -/
  | prod_rec_beta
    {A : Type u} {α β : Type u}
      {a1 a2 : α} {b1 b2 : β}
      (f : α → β → A)
      (p : Path a1 a2) (q : Path b1 b2) :
      Step (A := A)
        (Path.congrArg (Prod.rec f)
          (Path.map2 (A := α) (B := β) (C := Prod α β) Prod.mk p q))
        (Path.map2 (A := α) (B := β) (C := A) f p q)
  /-- Rule 13: Product η-expansion. `mk(fst(p), snd(p)) ▷ p` -/
  | prod_eta
    {α β : Type u}
      {a₁ a₂ : α} {b₁ b₂ : β}
      (p : Path (A := Prod α β) (a₁, b₁) (a₂, b₂)) :
      Step (A := Prod α β)
        (Path.prodMk (Path.fst p) (Path.snd p)) p
  /-- Rule 14: Symmetry distributes over product constructor. `symm(mk(p, q)) ▷ mk(symm(p), symm(q))` -/
  | prod_mk_symm
    {A : Type u} {B : Type u}
      {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) (q : Path b₁ b₂) :
      Step (A := Prod A B)
        (Path.symm (Path.prodMk (p := p) (q := q)))
        (Path.prodMk (Path.symm p) (Path.symm q))
  /-- Rule 15: Componentwise map through products.
      For f(x) = (g(fst x), h(snd x)), congrArg f (mk(p,q)) ▷ mk(congrArg g p, congrArg h q) -/
  | prod_map_congrArg
    {A : Type u} {B : Type u} {A' : Type u} {B' : Type u}
      {a₁ a₂ : A} {b₁ b₂ : B}
      (g : A → A') (h : B → B')
      (p : Path a₁ a₂) (q : Path b₁ b₂) :
      Step (A := Prod A' B')
        (Path.congrArg (fun x : Prod A B => (g x.fst, h x.snd))
          (Path.prodMk p q))
        (Path.prodMk (Path.congrArg g p) (Path.congrArg h q))
  /-- Rule 16: Sigma first projection β-rule. `fst(sigmaMk(p, q)) ▷ ofEq(p.toEq)` -/
  | sigma_fst_beta
    {A : Type u} {B : A → Type u}
      {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      (p : Path a1 a2)
      (q : Path (transport (A := A) (D := fun a => B a) p b1) b2) :
      Step (A := A)
        (Path.congrArg Sigma.fst
        (Path.sigmaMk (B := B) p q))
        (Path.stepChain (A := A) p.toEq)
  /-- Rule 17: Sigma second projection β-rule. Extracts the second component path. -/
  | sigma_snd_beta
    {A₀ : Type u} {B : A₀ → Type u}
      {a1 a2 : A₀} {b1 : B a1} {b2 : B a2}
      (p : Path a1 a2)
      (q :
        Path (transport (A := A₀) (D := fun a => B a) p b1) b2) :
      Step (A := B a2)
        (Path.sigmaSnd (B := B) (Path.sigmaMk (B := B) p q))
        (Path.stepChain
          (A := B a2)
          (a := transport (A := A₀) (D := fun a => B a)
                (Path.sigmaFst (B := B) (Path.sigmaMk (B := B) p q)) b1)
          (b := b2) q.toEq)
  /-- Rule 18: Sigma η-expansion. `sigmaMk(sigmaFst(p), sigmaSnd(p)) ▷ p` -/
  | sigma_eta
    {A : Type u} {B : A → Type u}
      {a1 a2 : A} {b1 : B a1} {b2 : B a2}
      (p : Path (A := Sigma B) ⟨a1, b1⟩ ⟨a2, b2⟩) :
      Step (A := Sigma B)
        (Path.sigmaMk (Path.sigmaFst p) (Path.sigmaSnd p)) p
  /-- Rule 19: Symmetry distributes over sigma constructor. -/
  | sigma_mk_symm
    {A : Type u} {B : A → Type u}
      {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
      (p : Path a₁ a₂)
      (q : Path (Path.transport (A := A) (D := fun a => B a) p b₁) b₂) :
      Step (A := Sigma B)
        (Path.symm (Path.sigmaMk (B := B) p q))
        (Path.sigmaMk (Path.symm p)
          (sigmaSymmSnd (B := B) (p := p) (q := q)))
  /-- Rule 20: Sum recursor β-rule for left injection. `rec f g (inl p) ▷ f p` -/
  | sum_rec_inl_beta
    {A : Type u} {α β : Type u}
      {a1 a2 : α}
      (f : α → A) (g : β → A)
      (p : Path a1 a2) :
      Step (A := A)
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inl p))
        (Path.congrArg f p)
  /-- Rule 21: Sum recursor β-rule for right injection. `rec f g (inr p) ▷ g p` -/
  | sum_rec_inr_beta
    {A : Type u} {α β : Type u}
      {b1 b2 : β}
      (f : α → A) (g : β → A)
      (p : Path b1 b2) :
      Step (A := A)
        (Path.congrArg (Sum.rec f g)
          (Path.congrArg Sum.inr p))
        (Path.congrArg g p)
  /-- Rule 22: Function application β-rule. `(λx.p x) a ▷ p a` -/
  | fun_app_beta
    {A : Type u} {α : Type u}
      {f g : α → A}
      (p : ∀ x : α, Path (f x) (g x)) (a : α) :
      Step (A := A)
        (Path.congrArg (fun h : α → A => h a)
          (Path.lamCongr (f := f) (g := g) p))
        (p a)
  /-- Rule 23: Function η-expansion. `λx.(app p x) ▷ p` -/
  | fun_eta
    {α β : Type u}
      {f g : α → β} (p : Path f g) :
      Step (A := α → β)
        (Path.lamCongr (fun x => Path.app p x)) p
  /-- Rule 24: Symmetry distributes into lambda. `symm(λx.p x) ▷ λx.symm(p x)` -/
  | lam_congr_symm
    {α β : Type u}
      {f g : α → β}
      (p : ∀ x : α, Path (f x) (g x)) :
      Step (A := α → β)
        (Path.symm (Path.lamCongr (f := f) (g := g) p))
        (Path.lamCongr (f := g) (g := f) (fun x => Path.symm (p x)))
  /-- Rule 25: Dependent application on reflexivity. `apd f refl ▷ refl` -/
  | apd_refl
    {A : Type u} {B : A → Type u}
      (f : ∀ x : A, B x) (a : A) :
      Step (A := B a)
        (Path.apd (A := A) (B := B) f (Path.refl a))
        (Path.refl (f a))
  /-- Rule 26: Transport along reflexivity is identity. `transport refl x ▷ x` -/
  | transport_refl_beta
    {A : Type u} {B : A → Type u}
      {a : A} (x : B a) :
      Step (A := B a)
        (Path.stepChain (A := B a)
          (a := transport (A := A) (D := fun t => B t)
                  (Path.refl a) x)
          (b := x)
          (transport_refl (A := A) (D := fun t => B t)
            (a := a) (x := x)))
        (Path.refl x)
  /-- Rule 27: Transport along composition. `transport (p∘q) x ▷ transport q (transport p x)` -/
  | transport_trans_beta
      {A : Type u} {B : A → Type u}
        {a₁ a₂ a₃ : A}
        (p : Path a₁ a₂) (q : Path a₂ a₃) (x : B a₁) :
        Step (A := B a₃)
          (Path.stepChain (A := B a₃)
            (a := Path.transport (A := A) (D := fun t => B t)
                    (Path.trans p q) x)
            (b := Path.transport (A := A) (D := fun t => B t) q
                    (Path.transport (A := A) (D := fun t => B t) p x))
            (Path.transport_trans (A := A) (D := fun t => B t)
              (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := B a₃)
                (Path.transport (A := A) (D := fun t => B t)
                  (Path.trans p q) x) y)
            (Path.refl
              (Path.transport (A := A) (D := fun t => B t)
                (Path.trans p q) x))
            (Path.transport_trans (A := A) (D := fun t => B t)
              (p := p) (q := q) (x := x)))
  /-- Rule 28: Left inverse for transport. `transport (symm p) (transport p x) ▷ x` -/
  | transport_symm_left_beta
      {A : Type u} {B : A → Type u}
        {a₁ a₂ : A} (p : Path a₁ a₂) (x : B a₁) :
        Step (A := B a₁)
          (Path.stepChain (A := B a₁)
            (a := Path.transport (A := A) (D := fun t => B t)
                    (Path.symm p)
                    (Path.transport (A := A) (D := fun t => B t) p x))
            (b := x)
            (Path.transport_symm_left (A := A) (D := fun t => B t)
              (p := p) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := B a₁)
                (Path.transport (A := A) (D := fun t => B t)
                  (Path.symm p)
                  (Path.transport (A := A) (D := fun t => B t) p x)) y)
            (Path.refl
              (Path.transport (A := A) (D := fun t => B t)
                (Path.symm p)
                (Path.transport (A := A) (D := fun t => B t) p x)))
            (Path.transport_symm_left (A := A) (D := fun t => B t)
              (p := p) (x := x)))
  /-- Rule 29: Right inverse for transport. `transport p (transport (symm p) y) ▷ y` -/
  | transport_symm_right_beta
      {A : Type u} {B : A → Type u}
        {a₁ a₂ : A} (p : Path a₁ a₂) (y : B a₂) :
        Step (A := B a₂)
          (Path.stepChain (A := B a₂)
            (a := Path.transport (A := A) (D := fun t => B t) p
                    (Path.transport (A := A) (D := fun t => B t)
                      (Path.symm p) y))
            (b := y)
            (Path.transport_symm_right (A := A) (D := fun t => B t)
              (p := p) (y := y)))
          (Eq.ndrec
            (motive := fun y' =>
              Path (A := B a₂)
                (Path.transport (A := A) (D := fun t => B t) p
                  (Path.transport (A := A) (D := fun t => B t)
                    (Path.symm p) y)) y')
            (Path.refl
              (Path.transport (A := A) (D := fun t => B t) p
                (Path.transport (A := A) (D := fun t => B t)
                  (Path.symm p) y)))
            (Path.transport_symm_right (A := A) (D := fun t => B t)
              (p := p) (y := y)))
  /-- Rule 30: Transport through sigma along first projection. -/
  | transport_sigmaMk_fst_beta
      {A : Type u} {B : A → Type u}
        {D : A → Type u}
        {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        (p : Path a₁ a₂)
        (q : Path (transport (A := A) (D := fun a => B a) p b₁) b₂)
        (x : D a₁) :
        Step (A := D a₂)
          (Path.stepChain (A := D a₂)
            (a := transport (A := Sigma B)
                    (D := fun z => D z.fst) (Path.sigmaMk (B := B) p q) x)
            (b := transport (A := A) (D := D) p x)
            (transport_sigmaMk_fst (A := A) (B := B)
              (D := D) (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := D a₂)
                (transport (A := Sigma B)
                  (D := fun z => D z.fst)
                  (Path.sigmaMk (B := B) p q) x) y)
            (Path.refl
              (transport (A := Sigma B)
                (D := fun z => D z.fst)
                (Path.sigmaMk (B := B) p q) x))
            (transport_sigmaMk_fst (A := A) (B := B)
              (D := D) (p := p) (q := q) (x := x)))
    | transport_sigmaMk_dep_beta
      {A : Type u} {B : A → Type u}
        {D : ∀ a, B a → Type u}
        {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        (p : Path a₁ a₂)
        (q : Path (transport (A := A) (D := fun a => B a) p b₁) b₂)
        (x : D a₁ b₁) :
        Step (A := D a₂ b₂)
          (Path.stepChain (A := D a₂ b₂)
            (a := transport (A := Sigma B)
                    (D := fun z => D z.fst z.snd)
                    (Path.sigmaMk (B := B) p q) x)
            (b := transportSigma (A := A) (B := B) (D := D) p q x)
            (transport_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := D a₂ b₂)
                (transport (A := Sigma B)
                  (D := fun z => D z.fst z.snd)
                  (Path.sigmaMk (B := B) p q) x) y)
            (Path.refl
              (transport (A := Sigma B)
                (D := fun z => D z.fst z.snd)
                (Path.sigmaMk (B := B) p q) x))
            (transport_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
    | subst_sigmaMk_dep_beta
      {A : Type u} {B : A → Type u}
        {D : ∀ a, B a → Type u}
        {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        (p : Path a₁ a₂)
        (q : Path (transport (A := A) (D := fun a => B a) p b₁) b₂)
        (x : D a₁ b₁) :
        Step (A := D a₂ b₂)
          (Path.stepChain (A := D a₂ b₂)
            (a := transport (A := Sigma B)
                    (D := fun z => D z.fst z.snd)
                    (Path.sigmaMk (B := B) p q) x)
            (b := substSigma (A := A) (B := B) (D := D) x p q)
            (subst_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
          (Eq.ndrec
            (motive := fun y =>
              Path (A := D a₂ b₂)
                (transport (A := Sigma B)
                  (D := fun z => D z.fst z.snd)
                  (Path.sigmaMk (B := B) p q) x) y)
            (Path.refl
              (transport (A := Sigma B)
                (D := fun z => D z.fst z.snd)
                (Path.sigmaMk (B := B) p q) x))
            (subst_sigmaMk_dep (A := A) (B := B) (D := D)
              (p := p) (q := q) (x := x)))
  /-- Rule 33: Context congruence. If `p ▷ q` then `C[p] ▷ C[q]` for any context C. -/
  | context_congr
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := B)
          (Context.map (A := A) (B := B) C p)
          (Context.map (A := A) (B := B) C q)
  /-- Rule 34: Symmetry commutes with context. `symm(C[p]) ▷ C[symm(p)]` -/
  | context_map_symm
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B)
        (Path.symm (Context.map (A := A) (B := B) C p))
        (Context.map (A := A) (B := B) C (Path.symm p))
  /-- Rule 35: Left cancellation in context. -/
  | context_tt_cancel_left
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (v : Path (C.fill a₁) y) :
      Step (A := B)
        (Path.trans
          (Context.map (A := A) (B := B) C p)
          (Path.trans
            (Context.map (A := A) (B := B) C (Path.symm p)) v))
        (Path.trans
          (Context.map (A := A) (B := B) C
            (Path.trans p (Path.symm p)))
          v)
  /-- Rule 36: Right cancellation in context. -/
  | context_tt_cancel_right
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {x : B}
      (p : Path a₁ a₂) (v : Path x (C.fill a₁)) :
      Step (A := B)
        (Path.trans
          (Path.trans v (Context.map (A := A) (B := B) C p))
          (Context.map (A := A) (B := B) C (Path.symm p)))
        (Path.trans
          v
          (Context.map (A := A) (B := B) C
            (Path.trans p (Path.symm p))))
  /-- Rule 37: Left substitution β-rule. `r ∘ C[p] ▷ substLeft C r p` -/
  | context_subst_left_beta
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Path.trans r (Context.map (A := A) (B := B) C p))
        (Context.substLeft (A := A) (B := B) C r p)
  /-- Rule 38: Relating left and right substitution. -/
  | context_subst_left_of_right
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Path.trans r
          (Context.substRight (A := A) (B := B) C p
            (Path.refl (C.fill a₂))))
        (Context.substLeft (A := A) (B := B) C r p)
  /-- Rule 39: Associativity for left substitution. -/
  | context_subst_left_assoc
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A} {y : B}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂)
      (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Path.trans (Context.substLeft (A := A) (B := B) C r p) t)
        (Path.trans r
          (Context.substRight (A := A) (B := B) C p t))
  /-- Rule 40: Right substitution β-rule. `C[p] ∘ t ▷ substRight C p t` -/
  | context_subst_right_beta
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Path.trans (Context.map (A := A) (B := B) C p) t)
        (Context.substRight (A := A) (B := B) C p t)
  /-- Rule 41: Associativity for right substitution. -/
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
  /-- Rule 42: Left substitution with refl on right simplifies. `substLeft C r refl ▷ r` -/
  | context_subst_left_refl_right
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a : A}
      (r : Path x (C.fill a)) :
      Step (A := B)
        (Context.substLeft C r (Path.refl a)) r
  /-- Rule 43: Left substitution with refl on left simplifies. `substLeft C refl p ▷ C[p]` -/
  | context_subst_left_refl_left
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B)
        (Context.substLeft C (Path.refl (C.fill a₁)) p)
        (Context.map C p)
  /-- Rule 44: Right substitution with refl on left simplifies. `substRight C refl r ▷ r` -/
  | context_subst_right_refl_left
    {A : Type u} {B : Type u}
      (C : Context A B) {a : A} {y : B}
      (r : Path (C.fill a) y) :
      Step (A := B)
        (Context.substRight C (Path.refl a) r) r
  /-- Rule 45: Right substitution with refl on right simplifies. `substRight C p refl ▷ C[p]` -/
  | context_subst_right_refl_right
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B)
        (Context.substRight C p (Path.refl (C.fill a₂)))
        (Context.map C p)
  /-- Rule 46: Idempotence for nested left substitutions. -/
  | context_subst_left_idempotent
    {A : Type u} {B : Type u}
      (C : Context A B) {x : B} {a₁ a₂ : A}
      (r : Path x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B)
        (Context.substLeft C
          (Context.substLeft C r (Path.refl a₁)) p)
        (Context.substLeft C r p)
  /-- Rule 47: Inner cancellation for nested right substitutions. -/
  | context_subst_right_cancel_inner
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Context.substRight C p
          (Context.substRight C (Path.refl a₂) t))
        (Context.substRight C p t)
  /-- Rule 48: Outer cancellation for nested right substitutions. -/
  | context_subst_right_cancel_outer
    {A : Type u} {B : Type u}
      (C : Context A B) {a₁ a₂ : A} {y : B}
      (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
      Step (A := B)
        (Context.substRight C (Path.refl a₁)
          (Context.substRight C p t))
        (Context.substRight C p t)
  /-- Rule 49: Dependent context congruence. If `p ▷ q` then `C[p] ▷ C[q]` for dependent context C. -/
  | depContext_congr
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := B a₂)
          (DepContext.map (A := A) (B := B) C p)
          (DepContext.map (A := A) (B := B) C q)
  /-- Rule 50: Symmetry with dependent context. `symm(C[p]) ▷ C.symmMap(p)` -/
  | depContext_map_symm
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (Path.symm (DepContext.map (A := A) (B := B) C p))
        (DepContext.symmMap (A := A) (B := B) C p)
  /-- Rule 51: Dependent context left substitution β-rule. -/
  | depContext_subst_left_beta
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {x : B a₁}
      (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂) :
      Step (A := B a₂)
        (Path.trans
          (Context.map (A := B a₁) (B := B a₂)
            (DepContext.transportContext (A := A) (B := B) p) r)
          (DepContext.map (A := A) (B := B) C p))
        (DepContext.substLeft (A := A) (B := B) C r p)
  /-- Rule 52: Dependent context left substitution associativity. -/
  | depContext_subst_left_assoc
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {x : B a₁} {y : B a₂}
      (r : Path (A := B a₁) x (C.fill a₁)) (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y) :
      Step (A := B a₂)
        (Path.trans
          (DepContext.substLeft (A := A) (B := B) C r p) t)
        (Path.trans
          (Context.map (A := B a₁) (B := B a₂)
            (DepContext.transportContext (A := A) (B := B) p) r)
          (DepContext.substRight (A := A) (B := B) C p t))
  /-- Rule 53: Dependent context right substitution β-rule. -/
  | depContext_subst_right_beta
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {y : B a₂}
      (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y) :
      Step (A := B a₂)
        (Path.trans
          (DepContext.map (A := A) (B := B) C p) t)
        (DepContext.substRight (A := A) (B := B) C p t)
  /-- Rule 54: Dependent context right substitution associativity. -/
  | depContext_subst_right_assoc
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {y z : B a₂}
      (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y)
      (u : Path (A := B a₂) y z) :
      Step (A := B a₂)
        (Path.trans
          (DepContext.substRight (A := A) (B := B) C p t) u)
        (DepContext.substRight (A := A) (B := B) C p
          (Path.trans t u))
  /-- Rule 55: Dependent left substitution with refl simplifies. -/
  | depContext_subst_left_refl_right
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a : A} {x : B a}
      (r : Path (A := B a) x (C.fill a)) :
      Step (A := B a)
        (DepContext.substLeft (A := A) (B := B) C r (Path.refl a)) r
  /-- Rule 56: Dependent left substitution with refl on left simplifies. -/
  | depContext_subst_left_refl_left
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (DepContext.substLeft (A := A) (B := B) C
          (Path.refl (C.fill a₁)) p)
        (DepContext.map (A := A) (B := B) C p)
  /-- Rule 57: Dependent right substitution with refl simplifies. -/
  | depContext_subst_right_refl_left
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a : A} {y : B a}
      (r : Path (A := B a) (C.fill a) y) :
      Step (A := B a)
        (DepContext.substRight (A := A) (B := B) C
          (Path.refl a) r) r
  /-- Rule 58: Dependent right substitution with refl on right simplifies. -/
  | depContext_subst_right_refl_right
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A}
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (DepContext.substRight (A := A) (B := B) C p
          (Path.refl (C.fill a₂)))
        (DepContext.map (A := A) (B := B) C p)
  /-- Rule 59: Idempotence for nested dependent left substitutions. -/
  | depContext_subst_left_idempotent
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {x : B a₁}
      (r : Path (A := B a₁) x (C.fill a₁))
      (p : Path a₁ a₂) :
      Step (A := B a₂)
        (DepContext.substLeft (A := A) (B := B) C
          (DepContext.substLeft (A := A) (B := B) C r (Path.refl a₁)) p)
        (DepContext.substLeft (A := A) (B := B) C r p)
  /-- Rule 60: Inner cancellation for nested dependent right substitutions. -/
  | depContext_subst_right_cancel_inner
    {A : Type u} {B : A → Type u}
      (C : DepContext A B) {a₁ a₂ : A} {y : B a₂}
      (p : Path a₁ a₂)
      (t : Path (A := B a₂) (C.fill a₂) y) :
      Step (A := B a₂)
        (DepContext.substRight (A := A) (B := B) C p
          (DepContext.substRight (A := A) (B := B) C (Path.refl a₂) t))
        (DepContext.substRight (A := A) (B := B) C p t)
  /-- Rule 61: Dependent bicontext left map congruence. -/
  | depBiContext_mapLeft_congr
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := C a₂ b)
          (_root_.ComputationalPaths.Path.DepBiContext.mapLeft
            (A := A) (B := B) (C := C) K p b)
          (_root_.ComputationalPaths.Path.DepBiContext.mapLeft
            (A := A) (B := B) (C := C) K q b)
  /-- Rule 62: Dependent bicontext right map congruence. -/
  | depBiContext_mapRight_congr
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      (a : A) {b₁ b₂ : B}
      {p q : Path b₁ b₂} :
      Step (A := B) p q →
        Step (A := C a b₂)
          (_root_.ComputationalPaths.Path.DepBiContext.mapRight
            (A := A) (B := B) (C := C) K a p)
          (_root_.ComputationalPaths.Path.DepBiContext.mapRight
            (A := A) (B := B) (C := C) K a q)
  /-- Rule 63: Dependent bicontext map2 left congruence. -/
  | depBiContext_map2_congr_left
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      {a₁ a₂ : A} {b₁ b₂ : B}
      {p q : Path a₁ a₂} (r : Path b₁ b₂) :
      Step (A := A) p q →
        Step (A := C a₂ b₂)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K p r)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K q r)
  /-- Rule 64: Dependent bicontext map2 right congruence. -/
  | depBiContext_map2_congr_right
    {A : Type u} {B : Type u} {C : A → B → Type u}
      (K : _root_.ComputationalPaths.Path.DepBiContext A B C)
      {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) {q r : Path b₁ b₂} :
      Step (A := B) q r →
        Step (A := C a₂ b₂)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K p q)
          (_root_.ComputationalPaths.Path.DepBiContext.map2
            (A := A) (B := B) (C := C) K p r)
  /-- Rule 65: Bicontext left map congruence. -/
  | biContext_mapLeft_congr
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := C)
          (BiContext.mapLeft (A := A) (B := B) (C := C) K p b)
          (BiContext.mapLeft (A := A) (B := B) (C := C) K q b)
  /-- Rule 66: Bicontext right map congruence. -/
  | biContext_mapRight_congr
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) (a : A) {b₁ b₂ : B}
      {p q : Path b₁ b₂} :
      Step (A := B) p q →
        Step (A := C)
          (BiContext.mapRight (A := A) (B := B) (C := C) K a p)
          (BiContext.mapRight (A := A) (B := B) (C := C) K a q)
  /-- Rule 67: Bicontext map2 left congruence. -/
  | biContext_map2_congr_left
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
      {p q : Path a₁ a₂} (r : Path b₁ b₂) :
      Step (A := A) p q →
        Step (A := C)
          (BiContext.map2 (A := A) (B := B) (C := C) K p r)
          (BiContext.map2 (A := A) (B := B) (C := C) K q r)
  /-- Rule 68: Bicontext map2 right congruence. -/
  | biContext_map2_congr_right
    {A : Type u} {B : Type u} {C : Type u}
      (K : BiContext A B C) {a₁ a₂ : A} {b₁ b₂ : B}
      (p : Path a₁ a₂) {q r : Path b₁ b₂} :
      Step (A := B) q r →
        Step (A := C)
          (BiContext.map2 (A := A) (B := B) (C := C) K p q)
          (BiContext.map2 (A := A) (B := B) (C := C) K p r)
  /-- Rule 69: Left map congruence for binary operations. -/
  | mapLeft_congr
    {A : Type u} {B : Type u}
      (f : A → B → A) {a₁ a₂ : A} (b : B)
      {p q : Path a₁ a₂} :
      Step (A := A) p q →
        Step (A := A) (Path.mapLeft (A := A) (B := B) (C := A) f p b)
          (Path.mapLeft (A := A) (B := B) (C := A) f q b)
  /-- Rule 70: Right map congruence for binary operations. -/
  | mapRight_congr
    {A : Type u} (f : A → A → A) (a : A) {b₁ b₂ : A}
      {p q : Path b₁ b₂} :
      Step (A := A) p q →
        Step (A := A) (Path.mapRight (A := A) (B := A) (C := A) f a p)
          (Path.mapRight (A := A) (B := A) (C := A) f a q)
  /-- Rule 71: Left map with propositional equality. -/
  | mapLeft_ofEq
    {A : Type u} {B : Type u}
      (f : A → B → A) {a₁ a₂ : A} (h : a₁ = a₂) (b : B) :
      Step (A := A)
        (Path.mapLeft (A := A) (B := B) (C := A) f
          (Path.stepChain (A := A) (a := a₁) (b := a₂) h) b)
        (Path.stepChain (A := A) (a := f a₁ b) (b := f a₂ b)
          (_root_.congrArg (fun x => f x b) h))
  /-- Rule 72: Right map with propositional equality. -/
  | mapRight_ofEq
    {A : Type u} (f : A → A → A) (a : A) {b₁ b₂ : A} (h : b₁ = b₂) :
      Step (A := A)
        (Path.mapRight (A := A) (B := A) (C := A) f a
          (Path.stepChain (A := A) (a := b₁) (b := b₂) h))
        (Path.stepChain (A := A) (a := f a b₁) (b := f a b₂)
          (_root_.congrArg (f a) h))
  /-- Rule 73: Symmetry congruence (structural). If `p ▷ q` then `symm(p) ▷ symm(q)`. -/
  | symm_congr {A : Type u} {a b : A} {p q : Path a b} :
      Step (A := A) p q → Step (A := A) (Path.symm p) (Path.symm q)
  /-- Rule 75: Left transitivity congruence (structural). If `p ▷ q` then `p ∘ r ▷ q ∘ r`. -/
  | trans_congr_left {A : Type u} {a b c : A}
      {p q : Path a b} (r : Path b c) :
      Step (A := A) p q → Step (A := A) (Path.trans p r) (Path.trans q r)
  /-- Rule 76: Right transitivity congruence (structural). If `q ▷ r` then `p ∘ q ▷ p ∘ r`. -/
  | trans_congr_right {A : Type u} {a b c : A}
      (p : Path a b) {q r : Path b c} :
      Step (A := A) q r → Step (A := A) (Path.trans p q) (Path.trans p r)
  /-- Rule 77: Left cancellation. `p ∘ (σ(p) ∘ q) ▷ q`.
      This is the completion rule that closes the critical pair between
      `trans_assoc` and `trans_symm`. Together with `trans_cancel_right`,
      it makes the groupoid fragment confluent without UIP/Step.canon.
      See `GroupoidConfluence.lean` for the free group confluence proof. -/
  | trans_cancel_left {A : Type u} {a b c : A}
      (p : Path a b) (q : Path a c) :
      Step (A := A) (Path.trans p (Path.trans (Path.symm p) q)) q
  /-- Rule 78: Right cancellation. `σ(p) ∘ (p ∘ q) ▷ q`.
      Dual of `trans_cancel_left`. Closes the critical pair between
      `trans_assoc` and `symm_trans`. -/
  | trans_cancel_right {A : Type u} {a b c : A}
      (p : Path a b) (q : Path b c) :
      Step (A := A) (Path.trans (Path.symm p) (Path.trans p q)) q
  /-- Rule 79: Step list reduction. Any path with a non-empty step list
      can drop its head step.  Step lists are computational *witnesses* /
      traces that record the construction history of a path.  Dropping
      a step forgets one layer of this trace while preserving the
      underlying equality proof.

      Unlike the former `Step.canon` (which jumped directly to a
      canonical form referencing `toEq`), this rule operates purely on
      the step-list structure and does not reference equality proofs.

      Together with proof irrelevance of `Eq` (which ensures all `Path a b`
      values share the same `proof` field), repeated application of
      `step_drop` normalises every path to `Path.mk [] h`, yielding
      unique normal forms and hence confluence (see `ConfluenceProof.lean`). -/
  | step_drop {A : Type u} {a b : A}
      (s : ComputationalPaths.Step A) (rest : List (ComputationalPaths.Step A))
      (h : a = b) :
      Step (A := A) (Path.mk (s :: rest) h) (Path.mk rest h)

/-- Step-oriented path constructor for reflexivity. -/
@[simp] def Step.refl {A : Type u} (a : A) : Path a a :=
  Path.refl a

/-- Step-oriented path constructor for symmetry. -/
@[simp] def Step.symm {A : Type u} {a b : A} (p : Path a b) : Path b a :=
  Path.symm p

/-- Step-oriented path constructor for composition. -/
@[simp] def Step.trans {A : Type u} {a b c : A}
    (p : Path a b) (q : Path b c) : Path a c :=
  Path.trans p q

/-- Step-oriented congruence for composition of functions. -/
@[simp] def Step.congr_comp {A : Type u} {B : Type v} {C : Type w}
    (f : A → B) (g : B → C) {a b : A} (p : Path a b) :
    Path (g (f a)) (g (f b)) :=
  Path.congrArg g (Path.congrArg f p)

/-- Step-oriented right-associated composition. -/
@[simp] def Step.assoc {A : Type u} {a b c d : A}
    (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Step.trans p (Step.trans q r)

/-- Step-oriented left unit insertion. -/
@[simp] def Step.unit_left {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Step.trans (Step.refl a) p

/-- Step-oriented right unit insertion. -/
@[simp] def Step.unit_right {A : Type u} {a b : A} (p : Path a b) : Path a b :=
  Step.trans p (Step.refl b)

attribute [simp] Step.symm_refl Step.symm_symm Step.trans_refl_left
  Step.trans_refl_right Step.trans_symm Step.symm_trans Step.symm_trans_congr
  Step.trans_assoc Step.map2_subst Step.prod_fst_beta Step.prod_snd_beta
  Step.prod_rec_beta Step.prod_eta Step.prod_mk_symm Step.prod_map_congrArg
  Step.sigma_fst_beta Step.sigma_snd_beta Step.sigma_eta
  Step.sigma_mk_symm
  Step.sum_rec_inl_beta Step.sum_rec_inr_beta Step.fun_app_beta Step.fun_eta Step.apd_refl
  Step.transport_refl_beta Step.transport_trans_beta Step.transport_symm_left_beta
  Step.transport_symm_right_beta Step.transport_sigmaMk_fst_beta
  Step.transport_sigmaMk_dep_beta Step.subst_sigmaMk_dep_beta
  Step.context_congr Step.context_map_symm Step.context_tt_cancel_left Step.context_tt_cancel_right
  Step.context_subst_left_beta Step.context_subst_left_of_right
  Step.context_subst_left_assoc Step.context_subst_right_beta Step.context_subst_right_assoc
  Step.context_subst_left_refl_right Step.context_subst_left_refl_left
  Step.context_subst_right_refl_left Step.context_subst_right_refl_right
  Step.context_subst_left_idempotent Step.context_subst_right_cancel_inner
  Step.context_subst_right_cancel_outer
  Step.depContext_congr Step.depContext_map_symm Step.depContext_subst_left_beta
  Step.depContext_subst_left_assoc Step.depContext_subst_right_beta
  Step.depContext_subst_right_assoc Step.depContext_subst_left_refl_right
  Step.depContext_subst_left_refl_left Step.depContext_subst_right_refl_left
  Step.depContext_subst_right_refl_right Step.depContext_subst_left_idempotent
  Step.depContext_subst_right_cancel_inner
  Step.depBiContext_mapLeft_congr Step.depBiContext_mapRight_congr
  Step.depBiContext_map2_congr_left Step.depBiContext_map2_congr_right
  Step.biContext_mapLeft_congr Step.biContext_mapRight_congr
  Step.biContext_map2_congr_left Step.biContext_map2_congr_right
  Step.mapLeft_congr Step.mapRight_congr Step.mapLeft_ofEq Step.mapRight_ofEq
  Step.symm_congr Step.trans_congr_left Step.trans_congr_right
  Step.trans_cancel_left Step.trans_cancel_right

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
  | prod_mk_symm _ _ => simp
  | prod_map_congrArg _ _ _ _ => simp
  | prod_rec_beta _ _ _ => simp
  | sigma_fst_beta _ _ => simp
  | sigma_snd_beta _ _ => simp
  | sigma_eta _ => simp
  | sigma_mk_symm _ _ => simp
  | sum_rec_inl_beta _ _ _ => simp
  | sum_rec_inr_beta _ _ _ => simp
  | fun_app_beta _ _ => simp
  | fun_eta _ => simp
  | lam_congr_symm _ => simp
  | apd_refl _ _ => simp
  | transport_refl_beta _ =>
    simp
  | transport_trans_beta _ _ _ =>
    simp
  | transport_symm_left_beta _ _ =>
    simp
  | transport_symm_right_beta _ _ =>
    simp
  | transport_sigmaMk_fst_beta _ _ _ =>
    simp
  | transport_sigmaMk_dep_beta _ _ _ =>
    simp
  | subst_sigmaMk_dep_beta _ _ _ =>
    simp
  | context_congr _ _ ih =>
    cases ih
    rfl
  | context_map_symm _ _ =>
    simp
  | context_tt_cancel_left _ _ _ =>
    simp
  | context_tt_cancel_right _ _ _ =>
    simp
  | context_subst_left_beta _ _ _ =>
    simp
  | context_subst_left_of_right _ _ _ =>
    simp
  | context_subst_left_assoc _ _ _ _ =>
    simp
  | context_subst_right_beta _ _ _ =>
    simp
  | context_subst_right_assoc _ _ _ _ =>
    simp
  | context_subst_left_refl_right _ _ =>
    simp
  | context_subst_left_refl_left _ _ =>
    simp
  | context_subst_right_refl_left _ _ =>
    simp
  | context_subst_right_refl_right _ _ =>
    simp
  | context_subst_left_idempotent _ _ _ =>
    simp
  | context_subst_right_cancel_inner _ _ _ =>
    simp
  | context_subst_right_cancel_outer _ _ _ =>
    simp
  | depContext_congr _ _ ih =>
    cases ih
    rfl
  | depContext_map_symm _ _ =>
    simp
  | depContext_subst_left_beta _ _ _ =>
    simp
  | depContext_subst_left_assoc _ _ _ _ =>
    simp
  | depContext_subst_right_beta _ _ _ =>
    simp
  | depContext_subst_right_assoc _ _ _ _ =>
    simp
  | depContext_subst_left_refl_right _ _ =>
    simp
  | depContext_subst_left_refl_left _ _ =>
    simp
  | depContext_subst_right_refl_left _ _ =>
    simp
  | depContext_subst_right_refl_right _ _ =>
    simp
  | depContext_subst_left_idempotent _ _ _ =>
    simp
  | depContext_subst_right_cancel_inner _ _ _ =>
    simp
  | depBiContext_mapLeft_congr _ _ _ ih =>
    cases ih
    rfl
  | depBiContext_mapRight_congr _ _ _ ih =>
    cases ih
    rfl
  | depBiContext_map2_congr_left _ _ _ ih =>
    cases ih
    rfl
  | depBiContext_map2_congr_right _ _ _ ih =>
    cases ih
    rfl
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
  | trans_cancel_left _ _ => simp
  | trans_cancel_right _ _ => simp
  | step_drop _ _ _ => simp

end Path
end ComputationalPaths
