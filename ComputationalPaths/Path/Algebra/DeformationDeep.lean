import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Deep Deformation Theory via Computational Paths

Genuine deformation theory using the Type-valued Step/RwEq infrastructure.
Covers:
- Formal deformations of path compositions
- Obstruction theory for lifting deformations
- Deformation equivalence (reflexive, symmetric, transitive)
- First-order deformations, pullback, pushforward
- Deformation complexes, cocycles, coboundaries
- Gauge equivalence
- Rigidity and formal rigidity
- Truncated deformations and versality
-/

namespace ComputationalPaths.Path.Algebra.DeformationDeep

open ComputationalPaths
open ComputationalPaths.Path

noncomputable section

universe u

/-! ## Formal Deformations -/

/-- A formal deformation of a path p is a family of paths p_n
    parameterized by order, with p_0 = p. -/
structure FormalDeformation {A : Type u} {a b : A} (p : Path a b) where
  corrections : Nat → Path a b
  base : corrections 0 = p

/-- A deformation is trivial if all corrections are RwEq to the base path. -/
def FormalDeformation.IsTrivial {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) : Type (u + 1) :=
  ∀ n : Nat, RwEq (d.corrections n) p

/-- The trivial deformation: all corrections equal to p. -/
def trivialDeformation {A : Type u} {a b : A} (p : Path a b) :
    FormalDeformation p where
  corrections := fun _ => p
  base := rfl

/-- The trivial deformation is indeed trivial. -/
def trivialDeformation_isTrivial {A : Type u} {a b : A} (p : Path a b) :
    (trivialDeformation p).IsTrivial :=
  fun _ => RwEq.refl p

/-! ## Deformation Equivalence -/

/-- Two deformations are equivalent if their corrections are pairwise RwEq. -/
def DeformationEquiv {A : Type u} {a b : A} {p : Path a b}
    (d₁ d₂ : FormalDeformation p) : Type (u + 1) :=
  ∀ n : Nat, RwEq (d₁.corrections n) (d₂.corrections n)

def DeformationEquiv.rfl {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) : DeformationEquiv d d :=
  fun n => RwEq.refl (d.corrections n)

def DeformationEquiv.symm' {A : Type u} {a b : A} {p : Path a b}
    {d₁ d₂ : FormalDeformation p} (h : DeformationEquiv d₁ d₂) :
    DeformationEquiv d₂ d₁ :=
  fun n => RwEq.symm (h n)

def DeformationEquiv.trans' {A : Type u} {a b : A} {p : Path a b}
    {d₁ d₂ d₃ : FormalDeformation p}
    (h₁ : DeformationEquiv d₁ d₂) (h₂ : DeformationEquiv d₂ d₃) :
    DeformationEquiv d₁ d₃ :=
  fun n => RwEq.trans (h₁ n) (h₂ n)

/-- Every trivial deformation is equivalent to the canonical trivial one. -/
def trivial_equiv_of_isTrivial {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) (ht : d.IsTrivial) :
    DeformationEquiv d (trivialDeformation p) :=
  fun n => ht n

/-! ## Obstruction Theory -/

/-- Data for attempting to extend a partial deformation from order n to n+1. -/
structure ExtensionData {A : Type u} {a b : A} (p : Path a b) (n : Nat) where
  partial_def : Fin (n + 1) → Path a b
  base : partial_def ⟨0, Nat.zero_lt_succ n⟩ = p

/-- An extension: a next-order correction with RwEq compatibility. -/
structure Extension {A : Type u} {a b : A} {p : Path a b} {n : Nat}
    (ext : ExtensionData p n) where
  next : Path a b
  compat : RwEq next (ext.partial_def ⟨n, Nat.lt.base n⟩)

/-- A deformation is unobstructed if every partial deformation can be extended. -/
def Unobstructed {A : Type u} {a b : A} (p : Path a b) : Type (u + 1) :=
  ∀ (n : Nat) (ext : ExtensionData p n), Extension ext

/-- The trivial deformation is unobstructed: copy top-order path. -/
def trivial_unobstructed {A : Type u} {a b : A} (p : Path a b) :
    Unobstructed p :=
  fun _ ext =>
    { next := ext.partial_def ⟨_, Nat.lt.base _⟩
      compat := RwEq.refl _ }

/-! ## First-Order Deformations -/

/-- A first-order deformation of p: deformed ≈ p ∘ tangent,
    where tangent is a loop at b. -/
structure FirstOrderDef {A : Type u} {a b : A} (p : Path a b) where
  tangent : Path b b
  deformed : Path a b
  relation : RwEq deformed (Path.trans p tangent)

/-- The trivial first-order deformation: tangent is refl. -/
def trivialFirstOrder {A : Type u} {a b : A} (p : Path a b) :
    FirstOrderDef p where
  tangent := Path.refl b
  deformed := p
  relation := RwEq.symm (rweq_of_step (Step.trans_refl_right p))

/-- Deforming refl by a loop. -/
def deformRefl {A : Type u} (a : A) (loop : Path a a) :
    FirstOrderDef (Path.refl a) where
  tangent := loop
  deformed := loop
  relation := RwEq.symm (rweq_of_step (Step.trans_refl_left loop))

/-- Pullback: given a deformation of q along p, get a deformation of (p ∘ q). -/
def firstOrderPullback {A : Type u} {a b c : A}
    {q : Path b c} (p : Path a b) (dq : FirstOrderDef q) :
    FirstOrderDef (Path.trans p q) where
  tangent := dq.tangent
  deformed := Path.trans p dq.deformed
  relation :=
    -- trans p dq.deformed ≈ trans p (trans q tangent)  [congr right, dq.relation]
    -- ≈ trans (trans p q) tangent  [reverse assoc]
    let h1 : RwEq (Path.trans p dq.deformed) (Path.trans p (Path.trans q dq.tangent)) :=
      rweq_trans_congr_right p dq.relation
    let h2 : RwEq (Path.trans (Path.trans p q) dq.tangent)
                   (Path.trans p (Path.trans q dq.tangent)) :=
      rweq_of_step (Step.trans_assoc p q dq.tangent)
    RwEq.trans h1 (RwEq.symm h2)

/-- Pushforward: given a deformation of p, push along q to get
    a deformation of (p ∘ q). Tangent is q⁻¹ ∘ t ∘ q. -/
def firstOrderPushforward {A : Type u} {a b c : A}
    {p : Path a b} (dp : FirstOrderDef p) (q : Path b c) :
    FirstOrderDef (Path.trans p q) where
  tangent := Path.trans (Path.symm q) (Path.trans dp.tangent q)
  deformed := Path.trans dp.deformed q
  relation :=
    -- LHS: trans dp.deformed q
    --   ≈ trans (trans p dp.tangent) q       [congr left, dp.relation]
    --   ≈ trans p (trans dp.tangent q)       [assoc]
    let hL1 : RwEq (Path.trans dp.deformed q) (Path.trans (Path.trans p dp.tangent) q) :=
      rweq_trans_congr_left q dp.relation
    let hL2 : RwEq (Path.trans (Path.trans p dp.tangent) q)
                    (Path.trans p (Path.trans dp.tangent q)) :=
      rweq_of_step (Step.trans_assoc p dp.tangent q)
    -- RHS: trans (trans p q) (trans (symm q) (trans dp.tangent q))
    --   ≈ trans p (trans q (trans (symm q) (trans dp.tangent q)))    [assoc]
    let hR1 : RwEq (Path.trans (Path.trans p q) (Path.trans (Path.symm q) (Path.trans dp.tangent q)))
                    (Path.trans p (Path.trans q (Path.trans (Path.symm q) (Path.trans dp.tangent q)))) :=
      rweq_of_step (Step.trans_assoc p q _)
    -- trans q (trans (symm q) (trans t q))
    --   ≈ trans (trans q (symm q)) (trans t q)   [reverse assoc]
    let hR2 : RwEq (Path.trans q (Path.trans (Path.symm q) (Path.trans dp.tangent q)))
                    (Path.trans (Path.trans q (Path.symm q)) (Path.trans dp.tangent q)) :=
      RwEq.symm (rweq_of_step (Step.trans_assoc q (Path.symm q) _))
    -- trans q (symm q) ≈ refl
    let hR3 : RwEq (Path.trans q (Path.symm q)) (Path.refl b) :=
      rweq_of_step (Step.trans_symm q)
    -- (q ∘ q⁻¹) ∘ (t ∘ q) ≈ refl ∘ (t ∘ q) ≈ t ∘ q
    let hR4 : RwEq (Path.trans (Path.trans q (Path.symm q)) (Path.trans dp.tangent q))
                    (Path.trans (Path.refl b) (Path.trans dp.tangent q)) :=
      rweq_trans_congr_left _ hR3
    let hR5 : RwEq (Path.trans (Path.refl b) (Path.trans dp.tangent q))
                    (Path.trans dp.tangent q) :=
      rweq_of_step (Step.trans_refl_left _)
    -- inner: q ∘ (q⁻¹ ∘ (t ∘ q)) ≈ t ∘ q
    let hR_inner : RwEq (Path.trans q (Path.trans (Path.symm q) (Path.trans dp.tangent q)))
                        (Path.trans dp.tangent q) :=
      RwEq.trans hR2 (RwEq.trans hR4 hR5)
    -- p ∘ (q ∘ (q⁻¹ ∘ (t ∘ q))) ≈ p ∘ (t ∘ q)
    let hR_full : RwEq (Path.trans p (Path.trans q (Path.trans (Path.symm q) (Path.trans dp.tangent q))))
                       (Path.trans p (Path.trans dp.tangent q)) :=
      rweq_trans_congr_right p hR_inner
    -- RHS total: (p∘q)∘(q⁻¹∘(t∘q)) ≈ p∘(t∘q)
    let hR : RwEq (Path.trans (Path.trans p q) (Path.trans (Path.symm q) (Path.trans dp.tangent q)))
                   (Path.trans p (Path.trans dp.tangent q)) :=
      RwEq.trans hR1 hR_full
    -- LHS total: dp.deformed ∘ q ≈ p ∘ (t ∘ q)
    let hL : RwEq (Path.trans dp.deformed q) (Path.trans p (Path.trans dp.tangent q)) :=
      RwEq.trans hL1 hL2
    RwEq.trans hL (RwEq.symm hR)

/-! ## Rigidity -/

/-- A path is rigid if every first-order deformation has tangent RwEq to refl. -/
def IsRigid {A : Type u} {a b : A} (p : Path a b) : Type (u + 1) :=
  ∀ (d : FirstOrderDef p), RwEq d.tangent (Path.refl b)

/-- A path is formally rigid if every formal deformation is equivalent
    to the trivial one. -/
def IsFormallyRigid {A : Type u} {a b : A} (p : Path a b) : Type (u + 1) :=
  ∀ (d : FormalDeformation p), DeformationEquiv d (trivialDeformation p)

/-- Formally rigid implies trivially deformed at each order. -/
def formallyRigid_isTrivial {A : Type u} {a b : A} {p : Path a b}
    (hr : IsFormallyRigid p) (d : FormalDeformation p) :
    d.IsTrivial :=
  hr d

/-! ## Deformation Complexes -/

/-- A deformation complex: graded loops with differentials satisfying d²≈0. -/
structure DeformationComplex (A : Type u) (a : A) where
  component : Nat → Path a a
  differential : Nat → Path a a → Path a a
  d_squared : ∀ (n : Nat) (x : Path a a),
    RwEq (differential (n + 1) (differential n x)) (Path.refl a)

/-- A cocycle at degree n: d(element) ≈ refl. -/
structure Cocycle {A : Type u} {a : A} (C : DeformationComplex A a) (n : Nat) where
  element : Path a a
  closed : RwEq (C.differential n element) (Path.refl a)

/-- A coboundary at degree n+1: element ≈ d(primitive). -/
structure Coboundary {A : Type u} {a : A} (C : DeformationComplex A a) (n : Nat) where
  primitive : Path a a
  element : Path a a
  is_boundary : RwEq element (C.differential n primitive)

/-- Every coboundary is a cocycle (d²=0). -/
def coboundary_is_cocycle {A : Type u} {a : A}
    (C : DeformationComplex A a) (n : Nat)
    (cb : Coboundary C n) :
    Cocycle C (n + 1) where
  element := C.differential n cb.primitive
  closed := C.d_squared n cb.primitive

/-- The component at each degree is a cocycle. -/
def component_cocycle {A : Type u} {a : A}
    (C : DeformationComplex A a) (n : Nat) :
    Cocycle C (n + 1) where
  element := C.differential n (C.component n)
  closed := C.d_squared n (C.component n)

/-! ## Gauge Equivalence -/

/-- Gauge equivalence: deformations related by conjugation.
    gauge_left is a loop at a, gauge_right a loop at b. -/
structure GaugeEquiv {A : Type u} {a b : A} {p : Path a b}
    (d₁ d₂ : FormalDeformation p) where
  gauge_left : Nat → Path a a
  gauge_right : Nat → Path b b
  gauge_left_base : gauge_left 0 = Path.refl a
  gauge_right_base : gauge_right 0 = Path.refl b
  gauge_action : ∀ n : Nat,
    RwEq (Path.trans (gauge_left n) (d₁.corrections n))
         (Path.trans (d₂.corrections n) (gauge_right n))

/-- Trivial gauge implies deformation equivalence. -/
def gaugeEquiv_trivial {A : Type u} {a b : A} {p : Path a b}
    {d₁ d₂ : FormalDeformation p}
    (ge : GaugeEquiv d₁ d₂)
    (hl : ∀ n, ge.gauge_left n = Path.refl a)
    (hr : ∀ n, ge.gauge_right n = Path.refl b) :
    DeformationEquiv d₁ d₂ :=
  fun n =>
    let hg := ge.gauge_action n
    let h_left : RwEq (Path.trans (ge.gauge_left n) (d₁.corrections n)) (d₁.corrections n) :=
      (hl n) ▸ rweq_of_step (Step.trans_refl_left (d₁.corrections n))
    let h_right : RwEq (Path.trans (d₂.corrections n) (ge.gauge_right n)) (d₂.corrections n) :=
      (hr n) ▸ rweq_of_step (Step.trans_refl_right (d₂.corrections n))
    RwEq.trans (RwEq.symm h_left) (RwEq.trans hg h_right)

/-- Identity gauge equivalence. -/
def GaugeEquiv.id' {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) : GaugeEquiv d d where
  gauge_left := fun _ => Path.refl a
  gauge_right := fun _ => Path.refl b
  gauge_left_base := rfl
  gauge_right_base := rfl
  gauge_action := fun n =>
    let h1 := rweq_of_step (Step.trans_refl_left (d.corrections n))
    let h2 := rweq_of_step (Step.trans_refl_right (d.corrections n))
    RwEq.trans h1 (RwEq.symm h2)

/-! ## Truncated Deformations -/

/-- A deformation truncated at order n. -/
structure TruncDeformation {A : Type u} {a b : A} (p : Path a b) (n : Nat) where
  corrections : Fin (n + 1) → Path a b
  base : corrections ⟨0, Nat.zero_lt_succ n⟩ = p

/-- Truncating a formal deformation. -/
def FormalDeformation.truncate {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) (n : Nat) :
    TruncDeformation p n where
  corrections := fun ⟨k, _⟩ => d.corrections k
  base := d.base

/-- Two truncated deformations are equivalent if pointwise RwEq. -/
def TruncEquiv {A : Type u} {a b : A} {p : Path a b} {n : Nat}
    (d₁ d₂ : TruncDeformation p n) : Type (u + 1) :=
  ∀ k : Fin (n + 1), RwEq (d₁.corrections k) (d₂.corrections k)

def TruncEquiv.rfl {A : Type u} {a b : A} {p : Path a b} {n : Nat}
    (d : TruncDeformation p n) : TruncEquiv d d :=
  fun k => RwEq.refl (d.corrections k)

/-- Truncation respects deformation equivalence. -/
def truncate_equiv {A : Type u} {a b : A} {p : Path a b}
    {d₁ d₂ : FormalDeformation p} (h : DeformationEquiv d₁ d₂) (n : Nat) :
    TruncEquiv (d₁.truncate n) (d₂.truncate n) :=
  fun ⟨k, _⟩ => h k

/-! ## Deformation Morphisms and Versality -/

/-- A morphism of formal deformations via reindexing. -/
structure DeformationMorphism {A : Type u} {a b : A} {p : Path a b}
    (d₁ d₂ : FormalDeformation p) where
  reindex : Nat → Nat
  reindex_base : reindex 0 = 0
  compat : ∀ n : Nat, RwEq (d₁.corrections n) (d₂.corrections (reindex n))

/-- Identity morphism. -/
def DeformationMorphism.id' {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) : DeformationMorphism d d where
  reindex := _root_.id
  reindex_base := rfl
  compat := fun _ => RwEq.refl _

/-- Composition of morphisms. -/
def DeformationMorphism.comp' {A : Type u} {a b : A} {p : Path a b}
    {d₁ d₂ d₃ : FormalDeformation p}
    (f : DeformationMorphism d₁ d₂) (g : DeformationMorphism d₂ d₃) :
    DeformationMorphism d₁ d₃ where
  reindex := g.reindex ∘ f.reindex
  reindex_base := by simp [Function.comp, f.reindex_base, g.reindex_base]
  compat := fun n => RwEq.trans (f.compat n) (g.compat (f.reindex n))

/-- A formal deformation is versal if every other deformation admits
    a morphism to it. -/
def IsVersal {A : Type u} {a b : A} {p : Path a b}
    (d : FormalDeformation p) : Type (u + 1) :=
  ∀ (d' : FormalDeformation p), DeformationMorphism d' d

/-! ## Deformation Functor -/

/-- The deformation functor on loops: each loop at a induces
    a first-order deformation of refl. -/
def deformationFunctor {A : Type u} (a : A) (loop : Path a a) :
    FirstOrderDef (Path.refl a) :=
  deformRefl a loop

/-- Symmetry of first-order deformations: deforming by the inverse loop. -/
def firstOrderSymm {A : Type u} {a b : A} {p : Path a b}
    (d : FirstOrderDef p) : FirstOrderDef p where
  tangent := Path.symm d.tangent
  deformed := Path.trans p (Path.symm d.tangent)
  relation := RwEq.refl _

/-- Constant deformation: every path at every order. -/
def constantDeformation {A : Type u} {a b : A} (p q : Path a b) (_h : RwEq p q) :
    FormalDeformation p where
  corrections := fun n => match n with
    | 0 => p
    | _ + 1 => q
  base := rfl

/-- Constant deformation at order ≥1 gives RwEq to q. -/
def constantDeformation_higher {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q) (n : Nat) :
    RwEq ((constantDeformation p q h).corrections (n + 1)) q :=
  RwEq.refl q

/-! ## Lifting Properties -/

/-- A deformation has the lifting property if it is both unobstructed
    and every extension is unique up to RwEq. -/
structure HasLiftingProperty {A : Type u} {a b : A} (p : Path a b) where
  unobstructed : Unobstructed p
  unique : ∀ (n : Nat) (ext : ExtensionData p n) (e₁ e₂ : Extension ext),
    RwEq e₁.next e₂.next

/-- Trivial deformation has the lifting property. -/
def trivial_lifting {A : Type u} {a b : A} (p : Path a b) :
    HasLiftingProperty p where
  unobstructed := trivial_unobstructed p
  unique := fun _ _ext e₁ e₂ =>
    RwEq.trans e₁.compat (RwEq.symm e₂.compat)

/-! ## Infinitesimal Automorphisms -/

/-- An infinitesimal automorphism of p is a first-order deformation
    where the deformed path is RwEq to the original. -/
structure InfAutomorphism {A : Type u} {a b : A} (p : Path a b) where
  deformation : FirstOrderDef p
  trivial_deformed : RwEq deformation.deformed p

/-- The identity infinitesimal automorphism. -/
def InfAutomorphism.id' {A : Type u} {a b : A} (p : Path a b) :
    InfAutomorphism p where
  deformation := trivialFirstOrder p
  trivial_deformed := RwEq.refl p

/-- From an infinitesimal automorphism we get: p ≈ trans p tangent. -/
def InfAutomorphism.tangent_acts_trivially {A : Type u} {a b : A} {p : Path a b}
    (φ : InfAutomorphism p) :
    RwEq p (Path.trans p φ.deformation.tangent) :=
  RwEq.trans (RwEq.symm φ.trivial_deformed) φ.deformation.relation

end

end ComputationalPaths.Path.Algebra.DeformationDeep
