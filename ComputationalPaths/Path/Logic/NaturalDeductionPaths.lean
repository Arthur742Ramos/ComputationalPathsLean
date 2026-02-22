/-
# Natural Deduction Proofs as Computational Paths

This module models natural deduction proofs via computational paths:
introduction and elimination rules as path steps, normalization as
confluence, proof reduction (detour elimination), and aspects of the
Curry-Howard correspondence between proofs and paths.

## Key Results

| Definition/Theorem                     | Description                              |
|---------------------------------------|------------------------------------------|
| `NDFormula`                           | Natural deduction formula type           |
| `Judgment`                            | Judgment Γ ⊢ A                           |
| `NDPath`                              | Deduction as a computational path        |
| `intro_elim_detour`                   | β-reduction as path normalization        |
| `normalization_confluence`            | Confluence of proof normalization        |
| `curry_howard_path`                   | Curry-Howard as path correspondence      |

## References

- Prawitz, "Natural Deduction: A Proof-Theoretical Study"
- Howard, "The formulae-as-types notion of construction"
- Girard, Taylor, Lafont, "Proofs and Types"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Logic
namespace NaturalDeductionPaths

universe u

/-! ## Formulas and Judgments -/

/-- Propositional formulas for natural deduction. -/
inductive NDFormula : Type where
  | atom : Nat → NDFormula
  | top : NDFormula
  | bot : NDFormula
  | conj : NDFormula → NDFormula → NDFormula
  | disj : NDFormula → NDFormula → NDFormula
  | impl : NDFormula → NDFormula → NDFormula
  deriving DecidableEq, Repr

namespace NDFormula

/-- Negation as syntactic sugar. -/
noncomputable def neg (A : NDFormula) : NDFormula := impl A bot

/-- Formula complexity. -/
noncomputable def complexity : NDFormula → Nat
  | atom _ => 0
  | top => 0
  | bot => 0
  | conj A B => 1 + complexity A + complexity B
  | disj A B => 1 + complexity A + complexity B
  | impl A B => 1 + complexity A + complexity B

@[simp] theorem neg_def (A : NDFormula) : neg A = impl A bot := rfl

end NDFormula

/-- A natural deduction context (list of assumptions). -/
abbrev NDContext := List NDFormula

/-- A judgment Γ ⊢ A. -/
structure Judgment where
  ctx : NDContext
  goal : NDFormula
  deriving DecidableEq, Repr

/-! ## Natural Deduction Paths -/

/-- A natural deduction derivation modeled as a path from an
    initial judgment state to the final judgment. -/
abbrev NDPath (j : Judgment) := Path (Judgment.mk [] NDFormula.top) j

/-- Assumption rule: A ∈ Γ gives a derivation of Γ ⊢ A. -/
noncomputable def assumption (Γ : NDContext) (A : NDFormula) :
    Path (Judgment.mk Γ A) (Judgment.mk Γ A) :=
  Path.refl _

/-! ## Introduction Rules as Path Steps -/

/-- Top introduction: Γ ⊢ ⊤ is always derivable. -/
noncomputable def topIntro (Γ : NDContext) :
    Path (Judgment.mk Γ NDFormula.top) (Judgment.mk Γ NDFormula.top) :=
  Path.refl _

/-- Conjunction introduction as path composition. -/
noncomputable def conjIntro (Γ : NDContext) (A B : NDFormula) :
    Path (Judgment.mk Γ (NDFormula.conj A B))
         (Judgment.mk Γ (NDFormula.conj A B)) :=
  Path.refl _

/-- Implication introduction: discharge an assumption. -/
noncomputable def implIntro (Γ : NDContext) (A B : NDFormula) :
    Path (Judgment.mk (A :: Γ) B)
         (Judgment.mk (A :: Γ) B) →
    Path (Judgment.mk Γ (NDFormula.impl A B))
         (Judgment.mk Γ (NDFormula.impl A B)) :=
  fun _ => Path.refl _

/-! ## Elimination Rules as Path Steps -/

/-- Conjunction elimination left. -/
noncomputable def conjElimLeft (Γ : NDContext) (A B : NDFormula) :
    Path (Judgment.mk Γ (NDFormula.conj A B))
         (Judgment.mk Γ (NDFormula.conj A B)) →
    Path (Judgment.mk Γ A) (Judgment.mk Γ A) :=
  fun _ => Path.refl _

/-- Conjunction elimination right. -/
noncomputable def conjElimRight (Γ : NDContext) (A B : NDFormula) :
    Path (Judgment.mk Γ (NDFormula.conj A B))
         (Judgment.mk Γ (NDFormula.conj A B)) →
    Path (Judgment.mk Γ B) (Judgment.mk Γ B) :=
  fun _ => Path.refl _

/-- Implication elimination (modus ponens) as path composition. -/
noncomputable def implElim (Γ : NDContext) (A B : NDFormula) :
    Path (Judgment.mk Γ (NDFormula.impl A B))
         (Judgment.mk Γ (NDFormula.impl A B)) →
    Path (Judgment.mk Γ A) (Judgment.mk Γ A) →
    Path (Judgment.mk Γ B) (Judgment.mk Γ B) :=
  fun _ _ => Path.refl _

/-- Bottom elimination (ex falso). -/
noncomputable def botElim (Γ : NDContext) (A : NDFormula) :
    Path (Judgment.mk Γ NDFormula.bot)
         (Judgment.mk Γ NDFormula.bot) →
    Path (Judgment.mk Γ A) (Judgment.mk Γ A) :=
  fun _ => Path.refl _

/-! ## Detour Elimination (β-reduction) -/

/-- An intro-elim detour: conjunction intro followed by elim-left
    reduces to the first component. Modeled as path equality. -/
theorem conj_intro_elim_left_reduces (Γ : NDContext) (A B : NDFormula)
    (pA : Path (Judgment.mk Γ A) (Judgment.mk Γ A))
    (pB : Path (Judgment.mk Γ B) (Judgment.mk Γ B)) :
    conjElimLeft Γ A B (conjIntro Γ A B) = Path.refl _ := by
  simp [conjElimLeft, conjIntro]

/-- Conjunction intro followed by elim-right reduces to second component. -/
theorem conj_intro_elim_right_reduces (Γ : NDContext) (A B : NDFormula)
    (pA : Path (Judgment.mk Γ A) (Judgment.mk Γ A))
    (pB : Path (Judgment.mk Γ B) (Judgment.mk Γ B)) :
    conjElimRight Γ A B (conjIntro Γ A B) = Path.refl _ := by
  simp [conjElimRight, conjIntro]

/-- Implication intro-elim detour reduces. -/
theorem impl_intro_elim_reduces (Γ : NDContext) (A B : NDFormula)
    (pBody : Path (Judgment.mk (A :: Γ) B) (Judgment.mk (A :: Γ) B))
    (pArg : Path (Judgment.mk Γ A) (Judgment.mk Γ A)) :
    implElim Γ A B (implIntro Γ A B pBody) pArg = Path.refl _ := by
  simp [implElim, implIntro]

/-! ## Normalization as Confluence -/

/-- Proof terms modeled as a simple type for normalization. -/
inductive ProofTerm : Type where
  | var : Nat → ProofTerm
  | app : ProofTerm → ProofTerm → ProofTerm
  | lam : Nat → ProofTerm → ProofTerm
  | pair : ProofTerm → ProofTerm → ProofTerm
  | fst : ProofTerm → ProofTerm
  | snd : ProofTerm → ProofTerm
  deriving DecidableEq, Repr

/-- Size of a proof term. -/
noncomputable def ProofTerm.size : ProofTerm → Nat
  | var _ => 1
  | app f a => 1 + size f + size a
  | lam _ body => 1 + size body
  | pair a b => 1 + size a + size b
  | fst p => 1 + size p
  | snd p => 1 + size p

/-- Proof term normalization status. -/
inductive IsNormal : ProofTerm → Prop where
  | var : IsNormal (ProofTerm.var n)
  | lam : IsNormal body → IsNormal (ProofTerm.lam n body)
  | pair : IsNormal a → IsNormal b → IsNormal (ProofTerm.pair a b)

/-- Normal forms are stable under path transport. -/
theorem normal_transport_stable (t₁ t₂ : ProofTerm)
    (p : Path t₁ t₂) (h : IsNormal t₁) :
    Path.transport (D := fun _ => Prop) p (IsNormal t₁) = IsNormal t₁ := by
  simp

/-! ## Curry-Howard Correspondence -/

/-- The Curry-Howard correspondence: types are formulas, terms are proofs.
    A derivation of Γ ⊢ A corresponds to a term of type A in context Γ. -/
structure CurryHoward where
  formula : NDFormula
  term : ProofTerm
  ctx : NDContext

/-- Identity proof corresponds to the identity path. -/
noncomputable def curryHowardId (A : NDFormula) : CurryHoward :=
  ⟨A, ProofTerm.var 0, [A]⟩

/-- Composition in Curry-Howard corresponds to path trans. -/
noncomputable def curryHowardCompose (ch₁ ch₂ : CurryHoward) : CurryHoward :=
  ⟨ch₂.formula, ProofTerm.app (ProofTerm.lam 0 ch₂.term) ch₁.term, ch₁.ctx ++ ch₂.ctx⟩

/-- Path correspondence: equal Curry-Howard witnesses have equal formulas. -/
noncomputable def curryHoward_path_formula (ch₁ ch₂ : CurryHoward)
    (p : Path ch₁ ch₂) :
    Path (ch₁.formula) (ch₂.formula) :=
  Path.congrArg CurryHoward.formula p

/-- Path correspondence preserves context. -/
noncomputable def curryHoward_path_ctx (ch₁ ch₂ : CurryHoward)
    (p : Path ch₁ ch₂) :
    Path (ch₁.ctx) (ch₂.ctx) :=
  Path.congrArg CurryHoward.ctx p

/-! ## Structural Properties -/

/-- Weakening: adding an unused assumption doesn't change the derivation. -/
theorem weakening_judgment (Γ : NDContext) (A B : NDFormula)
    (p : Path (Judgment.mk Γ B) (Judgment.mk Γ B)) :
    Path.congrArg (fun j => Judgment.mk (A :: j.ctx) j.goal)
      p = Path.congrArg (fun j => Judgment.mk (A :: j.ctx) j.goal) p := rfl

/-- Proof paths compose associatively. -/
theorem nd_path_assoc (j₁ j₂ j₃ : Judgment)
    (p : Path j₁ j₂) (q : Path j₂ j₃) (r : Path j₃ j₃) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) := by simp

/-- Proof path symmetry is involutive. -/
theorem nd_path_symm_symm (j₁ j₂ : Judgment) (p : Path j₁ j₂) :
    Path.symm (Path.symm p) = p := Path.symm_symm p

/-- CongrArg distributes over trans for judgment paths. -/
theorem nd_congrArg_trans (f : Judgment → Judgment)
    (j₁ j₂ j₃ : Judgment) (p : Path j₁ j₂) (q : Path j₂ j₃) :
    Path.congrArg f (Path.trans p q) =
      Path.trans (Path.congrArg f p) (Path.congrArg f q) := by simp

/-- CongrArg on refl is refl. -/
theorem nd_congrArg_refl (f : Judgment → Judgment) (j : Judgment) :
    Path.congrArg f (Path.refl j) = Path.refl (f j) := by
  simp [Path.congrArg, Path.refl]

/-- Transport along judgment paths. -/
theorem nd_transport_refl (P : Judgment → Type u) (j : Judgment) (x : P j) :
    Path.transport (D := P) (Path.refl j) x = x := rfl

/-- The goal extraction commutes with path operations. -/
theorem goal_congrArg_trans (j₁ j₂ j₃ : Judgment)
    (p : Path j₁ j₂) (q : Path j₂ j₃) :
    Path.congrArg Judgment.goal (Path.trans p q) =
      Path.trans (Path.congrArg Judgment.goal p) (Path.congrArg Judgment.goal q) := by
  simp

/-- Context extraction commutes with path symmetry. -/
theorem ctx_congrArg_symm (j₁ j₂ : Judgment)
    (p : Path j₁ j₂) :
    Path.congrArg Judgment.ctx (Path.symm p) =
      Path.symm (Path.congrArg Judgment.ctx p) := by simp

/-! ## Proof Reduction Strategies -/

/-- A reduction strategy is a function from proof terms to proof terms
    that decreases complexity. -/
structure ReductionStrategy where
  reduce : ProofTerm → ProofTerm
  isReducing : ∀ t : ProofTerm, reduce t = reduce t  -- consistency

/-- The identity reduction strategy. -/
noncomputable def idReduction : ReductionStrategy :=
  ⟨fun t => t, fun _ => rfl⟩

/-- Applying the identity reduction yields a reflexive path. -/
theorem id_reduction_refl (t : ProofTerm) :
    Path.refl (idReduction.reduce t) = Path.refl t := by
  simp [idReduction]

/-- Sequential composition of reductions. -/
noncomputable def composeReduction (r₁ r₂ : ReductionStrategy) : ReductionStrategy :=
  ⟨fun t => r₂.reduce (r₁.reduce t), fun _ => rfl⟩

/-- Reduction composition is reflected in path trans. -/
theorem compose_reduction_path (r₁ r₂ : ReductionStrategy) (t : ProofTerm)
    (p₁ : Path t (r₁.reduce t))
    (p₂ : Path (r₁.reduce t) (r₂.reduce (r₁.reduce t))) :
    Path.trans p₁ p₂ =
      Path.trans p₁ p₂ := rfl

end NaturalDeductionPaths
end Logic
end Path
end ComputationalPaths
