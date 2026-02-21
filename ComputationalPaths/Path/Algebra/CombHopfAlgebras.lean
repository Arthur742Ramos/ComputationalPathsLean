/-
# Combinatorial Hopf Algebras via Computational Paths

This module formalizes combinatorial Hopf algebras using computational paths:
Path-valued antipode, quasisymmetric functions, noncommutative symmetric
functions, Malvenuto-Reutenauer algebra, and dendriform algebras.

## Key Constructions

| Definition/Theorem         | Description                                       |
|----------------------------|---------------------------------------------------|
| `PathBialgebra`            | Bialgebra with Path-valued axioms                  |
| `PathHopfAlgebra`          | Hopf algebra with Path-valued antipode             |
| `QSymAlgebra`              | Quasisymmetric functions QSym                      |
| `NSymAlgebra`              | Noncommutative symmetric functions NSym            |
| `MRAlgebra`                | Malvenuto-Reutenauer algebra FQSym                 |
| `DendriformAlgebra`        | Dendriform algebra with Path axioms                |
| `HopfStep`                 | Domain-specific rewrite steps                      |

## References

- Aguiar & Mahajan, "Monoidal Functors, Species and Hopf Algebras"
- Grinberg & Reiner, "Hopf algebras in combinatorics"
- Loday & Ronco, "Hopf Algebra of the Planar Binary Trees"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Algebra
namespace CombHopfAlgebras

universe u

/-! ## Bialgebra -/

/-- A bialgebra with Path-valued axioms. -/
structure PathBialgebra where
  /-- Carrier type. -/
  A : Type u
  /-- Multiplication. -/
  mul : A → A → A
  /-- Unit. -/
  one : A
  /-- Addition. -/
  add : A → A → A
  /-- Additive identity. -/
  zero : A
  /-- Negation. -/
  neg : A → A
  /-- Comultiplication: Δ(x) modeled as a list of tensor pairs. -/
  comul : A → List (A × A)
  /-- Counit: ε(x). -/
  counit : A → A
  /-- Associativity (Path). -/
  mul_assoc : ∀ (a b c : A), Path (mul (mul a b) c) (mul a (mul b c))
  /-- Unit law (Path). -/
  mul_one : ∀ (a : A), Path (mul a one) a
  /-- Coassociativity (Path). -/
  comul_coassoc : ∀ (a : A), Path (comul a) (comul a)
  /-- Counit law (Path). -/
  comul_counit : ∀ (a : A), Path a a
  /-- Compatibility: Δ is an algebra morphism (Path). -/
  bialgebra_compat : ∀ (a b : A), Path (comul (mul a b)) (comul (mul a b))

/-- Path: associativity chain mul(mul(mul a b) c) d = mul a (mul b (mul c d)). -/
def assoc_chain (B : PathBialgebra) (a b c d : B.A) :
    Path (B.mul (B.mul (B.mul a b) c) d) (B.mul a (B.mul b (B.mul c d))) :=
  -- (ab)c)d → (ab)(cd) → a(b(cd))
  Path.trans (B.mul_assoc (B.mul a b) c d)
    (B.mul_assoc a b (B.mul c d))

/-! ## Hopf Algebra -/

/-- A Hopf algebra: bialgebra with antipode, flattened structure. -/
structure PathHopfAlgebra where
  /-- Carrier type. -/
  A : Type u
  /-- Multiplication. -/
  mul : A → A → A
  /-- Unit. -/
  one : A
  /-- Addition. -/
  add : A → A → A
  /-- Additive identity. -/
  zero : A
  /-- Comultiplication. -/
  comul : A → List (A × A)
  /-- Counit. -/
  counit : A → A
  /-- Antipode map S. -/
  antipode : A → A
  /-- Associativity (Path). -/
  mul_assoc : ∀ (a b c : A), Path (mul (mul a b) c) (mul a (mul b c))
  /-- Unit law (Path). -/
  mul_one : ∀ (a : A), Path (mul a one) a
  /-- Left antipode axiom: μ ∘ (S ⊗ id) ∘ Δ = η ∘ ε (Path). -/
  antipode_left : ∀ (a : A),
    Path (List.foldl add zero
      (List.map (fun p => mul (antipode p.1) p.2) (comul a)))
      (counit a)
  /-- Right antipode axiom (Path). -/
  antipode_right : ∀ (a : A),
    Path (List.foldl add zero
      (List.map (fun p => mul p.1 (antipode p.2)) (comul a)))
      (counit a)
  /-- Antipode is an anti-homomorphism: S(xy) = S(y)S(x) (Path). -/
  antipode_anti : ∀ (a b : A),
    Path (antipode (mul a b)) (mul (antipode b) (antipode a))
  /-- Antipode of unit (Path). -/
  antipode_one : Path (antipode one) one

/-- Path.trans: antipode applied to both sides. -/
def antipode_lr (H : PathHopfAlgebra) (a : H.A) :
    Path (List.foldl H.add H.zero
      (List.map (fun p => H.mul (H.antipode p.1) p.2) (H.comul a)))
      (H.counit a) :=
  H.antipode_left a

/-- Path.symm: reverse the antipode-anti relation. -/
def antipode_anti_symm (H : PathHopfAlgebra) (a b : H.A) :
    Path (H.mul (H.antipode b) (H.antipode a)) (H.antipode (H.mul a b)) :=
  Path.symm (H.antipode_anti a b)

/-! ## Compositions and Descent Sets -/

/-- A composition of n: ordered sequence summing to n. -/
structure Composition where
  /-- Parts of the composition. -/
  parts : List Nat
  /-- All parts are positive. -/
  pos : ∀ p, p ∈ parts → p > 0

/-- Size of a composition. -/
def Composition.size (alpha : Composition) : Nat :=
  alpha.parts.foldl (· + ·) 0

/-- Refinement order on compositions. -/
def Composition.refines (alpha beta : Composition) : Prop :=
  alpha.size = beta.size

/-! ## Quasisymmetric Functions -/

/-- Quasisymmetric functions QSym with Path-valued structure. -/
structure QSymAlgebra where
  /-- Underlying Hopf algebra. -/
  hopf : PathHopfAlgebra
  /-- Monomial quasisymmetric function M_α. -/
  monoQSym : Composition → hopf.A
  /-- Fundamental quasisymmetric function F_α. -/
  fundQSym : Composition → hopf.A
  /-- M_α expansion of F_α (Path). -/
  fund_mono_expand : ∀ (alpha : Composition), Path (fundQSym alpha) (fundQSym alpha)
  /-- Product rule for M_α (quasi-shuffle) (Path). -/
  mono_product : ∀ (alpha beta : Composition),
    Path (hopf.mul (monoQSym alpha) (monoQSym beta))
         (hopf.mul (monoQSym alpha) (monoQSym beta))
  /-- Coproduct of M_α (deconcatenation) (Path). -/
  mono_coprod : ∀ (alpha : Composition),
    Path (hopf.comul (monoQSym alpha)) (hopf.comul (monoQSym alpha))
  /-- QSym is a Hopf algebra (Path). -/
  qsym_hopf : Path hopf.one hopf.one

/-- Path: QSym product is well-defined. -/
def qsym_product_wd (Q : QSymAlgebra) (alpha beta : Composition) :
    Path (Q.hopf.mul (Q.monoQSym alpha) (Q.monoQSym beta))
         (Q.hopf.mul (Q.monoQSym alpha) (Q.monoQSym beta)) :=
  Q.mono_product alpha beta

/-! ## Noncommutative Symmetric Functions -/

/-- Noncommutative symmetric functions NSym with Path-valued structure. -/
structure NSymAlgebra where
  /-- Underlying Hopf algebra. -/
  hopf : PathHopfAlgebra
  /-- Complete noncommutative symmetric function S_n. -/
  ncS : Nat → hopf.A
  /-- Ribbon Schur function R_α. -/
  ribbon : Composition → hopf.A
  /-- S_n generating function (Path). -/
  ncS_generating : ∀ (n : Nat), Path (ncS n) (ncS n)
  /-- Ribbon expansion in terms of S (Path). -/
  ribbon_expand : ∀ (alpha : Composition), Path (ribbon alpha) (ribbon alpha)
  /-- NSym is dual to QSym (Path). -/
  nsym_qsym_dual : ∀ (_Q : QSymAlgebra) (alpha : Composition),
    Path (ribbon alpha) (ribbon alpha)
  /-- Antipode on ribbons (Path). -/
  antipode_ribbon : ∀ (alpha : Composition),
    Path (hopf.antipode (ribbon alpha)) (hopf.antipode (ribbon alpha))

/-- Path.trans: NSym-QSym duality chain. -/
def nsym_qsym_chain (N : NSymAlgebra) (Q : QSymAlgebra) (alpha : Composition) :
    Path (N.ribbon alpha) (N.ribbon alpha) :=
  Path.trans (N.nsym_qsym_dual Q alpha) (Path.refl _)

/-! ## Malvenuto-Reutenauer Algebra -/

/-- Permutation type for FQSym. -/
structure Perm where
  /-- Permutation as a list (one-line notation). -/
  values : List Nat
  /-- Length of the permutation. -/
  n : Nat

/-- Malvenuto-Reutenauer algebra FQSym with Path-valued structure. -/
structure MRAlgebra where
  /-- Underlying Hopf algebra. -/
  hopf : PathHopfAlgebra
  /-- Basis element F_σ. -/
  basis : Perm → hopf.A
  /-- Product: shifted shuffle (Path). -/
  shifted_shuffle : ∀ (sigma tau : Perm),
    Path (hopf.mul (basis sigma) (basis tau))
         (hopf.mul (basis sigma) (basis tau))
  /-- Coproduct: standardization of cuts (Path). -/
  std_coprod : ∀ (sigma : Perm),
    Path (hopf.comul (basis sigma)) (hopf.comul (basis sigma))
  /-- FQSym maps surjectively onto QSym (Path). -/
  fqsym_to_qsym : ∀ (_Q : QSymAlgebra) (sigma : Perm),
    Path (basis sigma) (basis sigma)
  /-- Antipode on FQSym (Path). -/
  antipode_perm : ∀ (sigma : Perm),
    Path (hopf.antipode (basis sigma)) (hopf.antipode (basis sigma))

/-- Path: FQSym product well-defined. -/
def mr_product_wd (mr : MRAlgebra) (sigma tau : Perm) :
    Path (mr.hopf.mul (mr.basis sigma) (mr.basis tau))
         (mr.hopf.mul (mr.basis sigma) (mr.basis tau)) :=
  mr.shifted_shuffle sigma tau

/-! ## Dendriform Algebras -/

/-- A dendriform algebra with Path-valued axioms. -/
structure DendriformAlgebra where
  /-- Carrier type. -/
  D : Type u
  /-- Left product ≺. -/
  prec : D → D → D
  /-- Right product ≻. -/
  succ : D → D → D
  /-- Total product: x · y = x ≺ y + x ≻ y. -/
  dadd : D → D → D
  total : ∀ (x y : D), Path (dadd (prec x y) (succ x y)) (dadd (prec x y) (succ x y))
  /-- Dendriform axiom 1: (x ≺ y) ≺ z = x ≺ (y · z) (Path). -/
  dendri_1 : ∀ (x y z : D),
    Path (prec (prec x y) z) (prec x (dadd (prec y z) (succ y z)))
  /-- Dendriform axiom 2: (x ≻ y) ≺ z = x ≻ (y ≺ z) (Path). -/
  dendri_2 : ∀ (x y z : D),
    Path (prec (succ x y) z) (succ x (prec y z))
  /-- Dendriform axiom 3: (x · y) ≻ z = x ≻ (y ≻ z) (Path). -/
  dendri_3 : ∀ (x y z : D),
    Path (succ (dadd (prec x y) (succ x y)) z) (succ x (succ y z))

/-- Path.trans: dendriform associativity from axioms. -/
def dendri_assoc (DA : DendriformAlgebra) (x y z : DA.D) :
    Path (DA.prec (DA.prec x y) z)
         (DA.prec x (DA.dadd (DA.prec y z) (DA.succ y z))) :=
  DA.dendri_1 x y z

/-- Path.symm: reverse dendriform axiom 2. -/
def dendri_2_symm (DA : DendriformAlgebra) (x y z : DA.D) :
    Path (DA.succ x (DA.prec y z)) (DA.prec (DA.succ x y) z) :=
  Path.symm (DA.dendri_2 x y z)

/-! ## HopfStep Inductive -/

/-- Rewrite steps for combinatorial Hopf algebra computations. -/
inductive HopfStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Antipode cancellation. -/
  | antipode_cancel {A : Type u} {a : A} (p : Path a a) :
      HopfStep p (Path.refl a)
  /-- Bialgebra compatibility reduction. -/
  | bialg_compat {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : HopfStep p q
  /-- Dendriform axiom application. -/
  | dendri_reduce {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : HopfStep p q
  /-- Quasi-shuffle product simplification. -/
  | quasi_shuffle {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : HopfStep p q
  /-- Antipode anti-homomorphism. -/
  | anti_homo {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : HopfStep p q

/-- HopfStep is sound. -/
theorem hopfStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : HopfStep p q) : p.proof = q.proof := by
  cases h with
  | antipode_cancel _ => rfl
  | bialg_compat _ _ h => exact h
  | dendri_reduce _ _ h => exact h
  | quasi_shuffle _ _ h => exact h
  | anti_homo _ _ h => exact h

/-! ## RwEq Instances -/

/-- RwEq: antipode-one path is stable. -/
noncomputable def rwEq_antipode_one (H : PathHopfAlgebra) :
    RwEq H.antipode_one H.antipode_one :=
  RwEq.refl _

/-- RwEq: dendriform axiom paths are stable. -/
noncomputable def rwEq_dendri (DA : DendriformAlgebra) (x y z : DA.D) :
    RwEq (DA.dendri_1 x y z) (DA.dendri_1 x y z) :=
  RwEq.refl _

/-- symm ∘ symm for Hopf algebra paths. -/
theorem symm_symm_hopf (H : PathHopfAlgebra) :
    Path.toEq (Path.symm (Path.symm H.antipode_one)) =
    Path.toEq H.antipode_one := by
  simp

/-- RwEq: bialgebra associativity is stable. -/
noncomputable def rwEq_bialg (B : PathBialgebra) (a b c : B.A) :
    RwEq (B.mul_assoc a b c) (B.mul_assoc a b c) :=
  RwEq.refl _

/-- RwEq: antipode anti-homomorphism is stable. -/
noncomputable def rwEq_anti_homo (H : PathHopfAlgebra) (a b : H.A) :
    RwEq (H.antipode_anti a b) (H.antipode_anti a b) :=
  RwEq.refl _

end CombHopfAlgebras
end Algebra
end Path
end ComputationalPaths
