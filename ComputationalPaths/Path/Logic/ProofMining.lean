/-
# Proof Mining via Computational Paths

This module formalizes proof mining concepts: Dialectica interpretation,
modified realizability, monotone functional interpretation, and
proof-theoretic bounds with Path coherences.

## Key Results

| Definition/Theorem                | Description                                   |
|----------------------------------|-----------------------------------------------|
| `PMStep`                         | Rewrite steps for proof transformations        |
| `DialecticaFormula`             | Dialectica-interpreted formulas                |
| `DialecticaWitness`            | Witnessing data for Dialectica                 |
| `MonotoneFunctional`           | Monotone functional interpretation             |
| `ProofTheoreticBound`          | Extracted bounds with Path certificates        |
| `HerbrandWitness`              | Herbrand normal form data                      |

## References

- Kohlenbach, "Applied Proof Theory"
- Avigad & Feferman, "Gödel's Functional (Dialectica) Interpretation"
-/

import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ProofMining

universe u v

open ComputationalPaths.Path

/-! ## Rewrite Steps -/

inductive PMStep : Type 1
  | dialectica_conj
  | dialectica_impl
  | mr_forall
  | monotone_weaken
  | interp_compose
  | bound_extract

/-! ## Dialectica Interpretation -/

/-- Dialectica-interpreted formula: ∃x.∀y.A_D(x,y). -/
structure DialecticaFormula where
  witnessType : Type
  challengeType : Type
  kernel : witnessType → challengeType → Prop

/-- Dialectica for conjunction. -/
noncomputable def dialectica_conj (A B : DialecticaFormula) : DialecticaFormula where
  witnessType := A.witnessType × B.witnessType
  challengeType := A.challengeType ⊕ B.challengeType
  kernel := fun ⟨wa, wb⟩ c =>
    match c with
    | Sum.inl ca => A.kernel wa ca
    | Sum.inr cb => B.kernel wb cb

/-- Dialectica for implication. -/
noncomputable def dialectica_impl (A B : DialecticaFormula) : DialecticaFormula where
  witnessType := (A.witnessType → B.witnessType) ×
                 (A.witnessType → B.challengeType → A.challengeType)
  challengeType := A.witnessType × B.challengeType
  kernel := fun ⟨f, g⟩ ⟨wa, cb⟩ =>
    A.kernel wa (g wa cb) → B.kernel (f wa) cb

/-- A Dialectica witness. -/
structure DialecticaWitness (D : DialecticaFormula) where
  witness : D.witnessType
  correct : (c : D.challengeType) → Path (D.kernel witness c : Prop) True

/-- Soundness: conjunction witness from component witnesses. -/
noncomputable def dialectica_conj_sound (A B : DialecticaFormula)
    (wA : DialecticaWitness A) (wB : DialecticaWitness B) :
    DialecticaWitness (dialectica_conj A B) where
  witness := (wA.witness, wB.witness)
  correct := fun c =>
    match c with
    | Sum.inl ca => wA.correct ca
    | Sum.inr cb => wB.correct cb

/-- Path: soundness proof relates component and conjunction witnesses. -/
noncomputable def dialectica_soundness_path {A B : DialecticaFormula}
    (wA : DialecticaWitness A) (wB : DialecticaWitness B)
    (c : (dialectica_conj A B).challengeType) :
    Path ((dialectica_conj_sound A B wA wB).correct c)
         (match c with
          | Sum.inl ca => wA.correct ca
          | Sum.inr cb => wB.correct cb) := by
  cases c with
  | inl _ => exact Path.refl _
  | inr _ => exact Path.refl _

/-! ## Monotone Functionals -/

/-- A monotone functional: Nat → Nat with monotonicity. -/
structure MonotoneFunctional where
  func : Nat → Nat
  mono : (m n : Nat) → m ≤ n → func m ≤ func n

/-- Composition of monotone functionals. -/
noncomputable def MonotoneFunctional.compose (f g : MonotoneFunctional) :
    MonotoneFunctional where
  func := fun n => f.func (g.func n)
  mono := fun m n hmn =>
    f.mono (g.func m) (g.func n) (g.mono m n hmn)

/-- Identity monotone functional. -/
noncomputable def MonotoneFunctional.idMF : MonotoneFunctional where
  func := fun n => n
  mono := fun _ _ h => h

/-- Path: composition is associative. -/
noncomputable def compose_assoc_path (f g h : MonotoneFunctional) :
    Path (MonotoneFunctional.compose (MonotoneFunctional.compose f g) h).func
         (MonotoneFunctional.compose f (MonotoneFunctional.compose g h)).func :=
  Path.refl _

/-- Majorization: f ≤ g pointwise. -/
structure Majorizes (f g : MonotoneFunctional) where
  bound : (n : Nat) → f.func n ≤ g.func n

/-- Majorization is transitive. -/
noncomputable def Majorizes.trans_maj {f g h : MonotoneFunctional}
    (m₁ : Majorizes f g) (m₂ : Majorizes g h) :
    Majorizes f h where
  bound := fun n => Nat.le_trans (m₁.bound n) (m₂.bound n)

/-- Majorization is reflexive. -/
noncomputable def Majorizes.refl_maj (f : MonotoneFunctional) :
    Majorizes f f where
  bound := fun _ => Nat.le_refl _

/-! ## Proof-Theoretic Bounds -/

/-- A proof-theoretic bound: rate of convergence or quantitative bound. -/
structure ProofTheoreticBound where
  bound : Nat → Nat
  property : Nat → Nat → Prop
  valid : (k n : Nat) → n ≥ bound k → property k n

/-- Path from bound validity to True. -/
noncomputable def bound_path (b : ProofTheoreticBound) (k n : Nat) (hn : n ≥ b.bound k) :
    Path (b.property k n : Prop) True :=
  Path.stepChain (by
    simp only [eq_iff_iff]
    exact ⟨fun _ => trivial, fun _ => b.valid k n hn⟩)

/-- Composition of bounds. -/
noncomputable def ProofTheoreticBound.compose
    (b₁ b₂ : ProofTheoreticBound)
    (connection : ∀ k n, b₁.property k n → b₂.property k n) :
    ProofTheoreticBound where
  bound := fun k => Nat.max (b₁.bound k) (b₂.bound k)
  property := b₂.property
  valid := fun k n hn =>
    connection k n (b₁.valid k n (Nat.le_trans (Nat.le_max_left _ _) hn))

/-- RwEq: bound_path is self-consistent. -/
noncomputable def bound_rweq (b : ProofTheoreticBound) (k n : Nat) (hn : n ≥ b.bound k) :
    RwEq (bound_path b k n hn) (bound_path b k n hn) :=
  RwEq.refl _

/-! ## Metastability -/

/-- Tao's metastability: finitary version of convergence. -/
structure MetastabilityWitness where
  seq : Nat → Nat
  epsilon : Nat
  fluctuation_bound : MonotoneFunctional
  interval_start : Nat
  metastable : (m n : Nat) →
    m ≥ interval_start → m ≤ fluctuation_bound.func interval_start →
    n ≥ interval_start → n ≤ fluctuation_bound.func interval_start →
    Path (Int.natAbs (↑(seq m) - ↑(seq n)) ≤ epsilon : Prop) True

/-- Metastability Path. -/
noncomputable def metastability_path (w : MetastabilityWitness) :
    Path (w.interval_start = w.interval_start : Prop) True :=
  Path.stepChain (by simp)

/-! ## Herbrand Analysis -/

/-- Herbrand normal form data. -/
structure HerbrandWitness where
  challenge : Nat
  witnesses : List Nat
  property : Nat → Nat → Prop
  valid : ∃ w, w ∈ witnesses ∧ property challenge w

/-- Herbrand as Path to True. -/
noncomputable def herbrand_path (h : HerbrandWitness) :
    Path (∃ w, w ∈ h.witnesses ∧ h.property h.challenge w : Prop) True :=
  Path.stepChain (by
    simp only [eq_iff_iff]
    exact ⟨fun _ => trivial, fun _ => h.valid⟩)

/-- Herbrand combination: merge witness lists. -/
noncomputable def HerbrandWitness.combine (h₁ h₂ : HerbrandWitness)
    (_ : h₁.property = h₂.property)
    (_ : h₁.challenge = h₂.challenge) :
    HerbrandWitness where
  challenge := h₁.challenge
  witnesses := h₁.witnesses ++ h₂.witnesses
  property := h₁.property
  valid := by
    obtain ⟨w, hw, hp⟩ := h₁.valid
    exact ⟨w, List.mem_append_left _ hw, hp⟩

/-! ## RwEq Coherences -/

/-- RwEq: Dialectica soundness. -/
noncomputable def dialectica_sound_rweq {A B : DialecticaFormula}
    (wA : DialecticaWitness A) (wB : DialecticaWitness B)
    (c : (dialectica_conj A B).challengeType) :
    RwEq ((dialectica_conj_sound A B wA wB).correct c)
         ((dialectica_conj_sound A B wA wB).correct c) :=
  RwEq.refl _

/-- RwEq: compose_assoc via Path.refl. -/
noncomputable def compose_assoc_rweq (f g h : MonotoneFunctional) :
    RwEq (compose_assoc_path f g h) (Path.refl _) :=
  RwEq.refl _

/-- RwEq: symm(symm(bound_path)). -/
noncomputable def bound_symm_rweq (b : ProofTheoreticBound) (k n : Nat) (hn : n ≥ b.bound k) :
    RwEq (Path.symm (Path.symm (bound_path b k n hn)))
         (bound_path b k n hn) :=
  RwEq.step (Step.symm_symm _)

/-- RwEq: trans(bound_path, refl). -/
noncomputable def bound_trans_refl_rweq (b : ProofTheoreticBound) (k n : Nat) (hn : n ≥ b.bound k) :
    RwEq (Path.trans (bound_path b k n hn) (Path.refl _))
         (bound_path b k n hn) :=
  RwEq.step (Step.trans_refl_right _)

/-- Multi-step RwEq chain. -/
noncomputable def multi_step_rweq (b : ProofTheoreticBound) (k n : Nat) (hn : n ≥ b.bound k) :
    RwEq (Path.trans (Path.refl _) (bound_path b k n hn))
         (bound_path b k n hn) :=
  RwEq.step (Step.trans_refl_left _)

end ProofMining
end Logic
end Path
end ComputationalPaths
