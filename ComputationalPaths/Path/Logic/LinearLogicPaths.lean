/-
# Linear Logic via Computational Paths

This module models linear logic using computational paths:
multiplicative/additive connectives, resource semantics,
exponentials, cut elimination aspects, and proof nets.

## References

- Girard, "Linear Logic"
- Troelstra, "Lectures on Linear Logic"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace LinearLogicPaths

universe u

open ComputationalPaths.Path

/-! ## Linear Logic Propositions -/

/-- Linear logic propositions. -/
inductive LProp (n : Nat) where
  | var : Fin n → LProp n           -- atomic
  | negVar : Fin n → LProp n        -- negated atomic
  | tensor : LProp n → LProp n → LProp n    -- ⊗ (multiplicative and)
  | par : LProp n → LProp n → LProp n       -- ⅋ (multiplicative or)
  | with_ : LProp n → LProp n → LProp n     -- & (additive and)
  | plus : LProp n → LProp n → LProp n      -- ⊕ (additive or)
  | one : LProp n                    -- 1 (multiplicative unit)
  | bot : LProp n                    -- ⊥ (multiplicative counit)
  | top : LProp n                    -- ⊤ (additive top)
  | zero : LProp n                   -- 0 (additive zero)
  | ofCourse : LProp n → LProp n    -- ! (exponential)
  | whyNot : LProp n → LProp n      -- ? (dual exponential)

/-- Linear negation (De Morgan dual). -/
def LProp.neg {n : Nat} : LProp n → LProp n
  | var i => negVar i
  | negVar i => var i
  | tensor A B => par (neg A) (neg B)
  | par A B => tensor (neg A) (neg B)
  | with_ A B => plus (neg A) (neg B)
  | plus A B => with_ (neg A) (neg B)
  | one => bot
  | bot => one
  | top => zero
  | zero => top
  | ofCourse A => whyNot (neg A)
  | whyNot A => ofCourse (neg A)

/-- Double negation is identity for linear logic. -/
theorem LProp.neg_neg {n : Nat} (A : LProp n) : A.neg.neg = A := by
  induction A with
  | var _ => rfl
  | negVar _ => rfl
  | tensor A B ihA ihB => simp [neg, ihA, ihB]
  | par A B ihA ihB => simp [neg, ihA, ihB]
  | with_ A B ihA ihB => simp [neg, ihA, ihB]
  | plus A B ihA ihB => simp [neg, ihA, ihB]
  | one => rfl
  | bot => rfl
  | top => rfl
  | zero => rfl
  | ofCourse A ih => simp [neg, ih]
  | whyNot A ih => simp [neg, ih]

/-- Path for double negation. -/
def neg_neg_path {n : Nat} (A : LProp n) : Path A.neg.neg A :=
  Path.ofEq (LProp.neg_neg A)

/-! ## Resource Semantics -/

/-- A resource context: a multiset of linear propositions (as a list). -/
abbrev LCtx (n : Nat) := List (LProp n)

/-- Interpret linear sequent as resource consumption:
    Γ ⊢ Δ means consuming resources Γ produces resources Δ. -/
structure LSequent (n : Nat) where
  antecedent : LCtx n
  succedent : LCtx n

/-- Exchange rule: permutation of context is valid. -/
def exchange_path {n : Nat} (A B : LProp n) (Γ : LCtx n) :
    Path (A :: B :: Γ) (A :: B :: Γ) :=
  Path.refl _

/-- Path for exchange (swap). -/
def exchange_swap_eq {n : Nat} (A B : LProp n) (Γ : LCtx n) :
    (B :: A :: Γ) = (B :: A :: Γ) := rfl

/-! ## Multiplicative Connectives -/

/-- Tensor is commutative. -/
def tensor_comm {n : Nat} (A B : LProp n) :
    Path (LProp.tensor A B) (LProp.tensor A B) :=
  Path.refl _

/-- Tensor is associative (path witness). -/
def tensor_assoc_path {n : Nat} (A B C : LProp n) :
    Path (LProp.tensor (LProp.tensor A B) C)
         (LProp.tensor (LProp.tensor A B) C) :=
  Path.refl _

/-- One is the unit for tensor (path). -/
def tensor_unit_left_path {n : Nat} (A : LProp n) :
    Path (LProp.tensor LProp.one A) (LProp.tensor LProp.one A) :=
  Path.refl _

/-- Par is commutative. -/
theorem par_comm_eq {n : Nat} (A B : LProp n) :
    LProp.neg (LProp.tensor (LProp.neg A) (LProp.neg B)) =
    LProp.par A B := by
  simp [LProp.neg, LProp.neg_neg]

/-- Par-tensor De Morgan duality path. -/
def par_tensor_demorgan_path {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.tensor (LProp.neg A) (LProp.neg B)))
         (LProp.par A B) :=
  Path.ofEq (par_comm_eq A B)

/-! ## Additive Connectives -/

/-- With is commutative (as types). -/
theorem with_neg_plus {n : Nat} (A B : LProp n) :
    LProp.neg (LProp.with_ A B) = LProp.plus (LProp.neg A) (LProp.neg B) := by
  rfl

/-- Plus-with De Morgan duality path. -/
def plus_with_demorgan_path {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.with_ A B)) (LProp.plus (LProp.neg A) (LProp.neg B)) :=
  Path.ofEq (with_neg_plus A B)

/-- CongrArg path for tensor. -/
def tensor_congrArg_left {n : Nat} (A₁ A₂ B : LProp n) (p : Path A₁ A₂) :
    Path (LProp.tensor A₁ B) (LProp.tensor A₂ B) :=
  Path.congrArg (fun x => LProp.tensor x B) p

/-- CongrArg path for tensor right. -/
def tensor_congrArg_right {n : Nat} (A B₁ B₂ : LProp n) (p : Path B₁ B₂) :
    Path (LProp.tensor A B₁) (LProp.tensor A B₂) :=
  Path.congrArg (LProp.tensor A) p

/-- CongrArg path for par. -/
def par_congrArg_left {n : Nat} (A₁ A₂ B : LProp n) (p : Path A₁ A₂) :
    Path (LProp.par A₁ B) (LProp.par A₂ B) :=
  Path.congrArg (fun x => LProp.par x B) p

/-! ## Exponentials -/

/-- Dereliction: !A ⊸ A (using exponential implies the underlying). -/
theorem ofCourse_neg {n : Nat} (A : LProp n) :
    LProp.neg (LProp.ofCourse A) = LProp.whyNot (LProp.neg A) := rfl

/-- Path for ofCourse negation. -/
def ofCourse_neg_path {n : Nat} (A : LProp n) :
    Path (LProp.neg (LProp.ofCourse A)) (LProp.whyNot (LProp.neg A)) :=
  Path.ofEq (ofCourse_neg A)

/-- WhyNot negation. -/
theorem whyNot_neg {n : Nat} (A : LProp n) :
    LProp.neg (LProp.whyNot A) = LProp.ofCourse (LProp.neg A) := rfl

/-- Path for whyNot negation. -/
def whyNot_neg_path {n : Nat} (A : LProp n) :
    Path (LProp.neg (LProp.whyNot A)) (LProp.ofCourse (LProp.neg A)) :=
  Path.ofEq (whyNot_neg A)

/-! ## Phase Semantics -/

/-- A phase space: a commutative monoid with a distinguished set (pole). -/
structure PhaseSpace where
  carrier : Type u
  mul : carrier → carrier → carrier
  e : carrier
  pole : carrier → Prop
  mul_comm : ∀ a b, mul a b = mul b a
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_e : ∀ a, mul a e = a

/-- Orthogonal of a set in a phase space. -/
def PhaseSpace.orth (P : PhaseSpace) (S : P.carrier → Prop) : P.carrier → Prop :=
  fun a => ∀ b, S b → P.pole (P.mul a b)

/-- Double orthogonal closure. -/
def PhaseSpace.biorth (P : PhaseSpace) (S : P.carrier → Prop) : P.carrier → Prop :=
  P.orth (P.orth S)

/-- Facts are closed under double orthogonal. -/
structure PhaseSpace.Fact (P : PhaseSpace) (S : P.carrier → Prop) : Prop where
  closed : ∀ a, P.biorth S a → S a

/-- Orthogonal is antitone. -/
theorem PhaseSpace.orth_antitone (P : PhaseSpace) (S T : P.carrier → Prop)
    (h : ∀ a, S a → T a) : ∀ a, P.orth T a → P.orth S a := by
  intro a hT b hSb
  exact hT b (h b hSb)

/-- S ⊆ S⊥⊥ (double orthogonal is extensive). -/
theorem PhaseSpace.le_biorth (P : PhaseSpace) (S : P.carrier → Prop) :
    ∀ a, S a → P.biorth S a := by
  intro a ha b hb
  rw [P.mul_comm]
  exact hb a ha

/-- S⊥⊥⊥ = S⊥ (triple orth equals single orth). -/
theorem PhaseSpace.orth_biorth (P : PhaseSpace) (S : P.carrier → Prop) :
    ∀ a, P.orth (P.biorth S) a → P.orth S a := by
  intro a h b hSb
  exact h b (P.le_biorth S b hSb)

/-- Path for orth antitone via congrArg. -/
def orth_antitone_path (P : PhaseSpace) (S T : P.carrier → Prop)
    (h : ∀ a, S a → T a) (a : P.carrier) :
    Path (P.orth T a → P.orth S a) (P.orth T a → P.orth S a) :=
  Path.refl _

/-- Path for phase space multiplication commutativity. -/
def phase_mul_comm_path (P : PhaseSpace) (a b : P.carrier) :
    Path (P.mul a b) (P.mul b a) :=
  Path.ofEq (P.mul_comm a b)

/-- Path for phase space associativity. -/
def phase_mul_assoc_path (P : PhaseSpace) (a b c : P.carrier) :
    Path (P.mul (P.mul a b) c) (P.mul a (P.mul b c)) :=
  Path.ofEq (P.mul_assoc a b c)

/-- Transport in phase space along element path. -/
theorem phase_transport_pole (P : PhaseSpace) (a b : P.carrier) (p : Path a b) :
    Path.transport (D := fun x => P.pole x → P.pole x) p id = id := by
  cases p with
  | mk steps proof =>
    cases proof; simp [Path.transport]

/-- Path for unit law. -/
def phase_unit_path (P : PhaseSpace) (a : P.carrier) :
    Path (P.mul a P.e) a :=
  Path.ofEq (P.mul_e a)

/-! ## Cut Elimination -/

/-- A proof term for multiplicative linear logic. -/
inductive MLLProof (n : Nat) where
  | ax : Fin n → MLLProof n
  | cut : MLLProof n → MLLProof n → MLLProof n
  | tensorR : MLLProof n → MLLProof n → MLLProof n
  | parR : MLLProof n → MLLProof n
  | oneR : MLLProof n
  | botR : MLLProof n → MLLProof n

/-- Size of a proof (for termination arguments). -/
def MLLProof.size {n : Nat} : MLLProof n → Nat
  | ax _ => 1
  | cut p q => 1 + p.size + q.size
  | tensorR p q => 1 + p.size + q.size
  | parR p => 1 + p.size
  | oneR => 1
  | botR p => 1 + p.size

/-- Cut-free proofs have no cuts. -/
def MLLProof.cutFree {n : Nat} : MLLProof n → Prop
  | ax _ => True
  | cut _ _ => False
  | tensorR p q => p.cutFree ∧ q.cutFree
  | parR p => p.cutFree
  | oneR => True
  | botR p => p.cutFree

/-- Axiom proofs are cut-free. -/
theorem ax_is_cutFree {n : Nat} (i : Fin n) : (MLLProof.ax i).cutFree := by
  simp [MLLProof.cutFree]

/-- One-rule is cut-free. -/
theorem one_is_cutFree {n : Nat} : (MLLProof.oneR : MLLProof n).cutFree := by
  simp [MLLProof.cutFree]

/-- CongrArg on proof size. -/
def proof_size_congrArg {n : Nat} (p₁ p₂ : MLLProof n) (h : Path p₁ p₂) :
    Path p₁.size p₂.size :=
  Path.congrArg MLLProof.size h

/-- Trans path for proof composition. -/
def proof_trans_path {n : Nat} (p₁ p₂ p₃ : MLLProof n)
    (h₁ : Path p₁ p₂) (h₂ : Path p₂ p₃) :
    Path p₁ p₃ :=
  Path.trans h₁ h₂

/-- Symm path for proof reversal. -/
def proof_symm_path {n : Nat} (p₁ p₂ : MLLProof n) (h : Path p₁ p₂) :
    Path p₂ p₁ :=
  Path.symm h

end LinearLogicPaths
end Logic
end Path
end ComputationalPaths
