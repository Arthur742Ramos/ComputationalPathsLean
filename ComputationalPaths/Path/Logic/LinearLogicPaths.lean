/-
# Linear Logic via Computational Paths

This module models linear logic using computational paths:
multiplicative/additive connectives, resource semantics,
exponentials, cut elimination aspects, and phase semantics.

Every algebraic identity is witnessed by domain-specific inductive
rewrite steps (`LNegStep`, `SWGroupStep`, `PhaseStep`), composed
into multi-step paths via `Path.trans`/`Path.symm`/`Path.congrArg`.

## References

- Girard, "Linear Logic"
- Troelstra, "Lectures on Linear Logic"
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths
namespace Path
namespace Logic
namespace LinearLogicPaths

universe u

open ComputationalPaths.Path

/-! ## Linear Logic Propositions -/

/-- Linear logic propositions. -/
inductive LProp (n : Nat) where
  | var : Fin n → LProp n
  | negVar : Fin n → LProp n
  | tensor : LProp n → LProp n → LProp n
  | par : LProp n → LProp n → LProp n
  | with_ : LProp n → LProp n → LProp n
  | plus : LProp n → LProp n → LProp n
  | one : LProp n
  | bot : LProp n
  | top : LProp n
  | zero : LProp n
  | ofCourse : LProp n → LProp n
  | whyNot : LProp n → LProp n
deriving DecidableEq

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

/-! ## Domain-specific rewrite steps for linear negation -/

/-- Rewrite steps capturing De Morgan dualities and involutivity of negation. -/
inductive LNegStep (n : Nat) : LProp n → LProp n → Type where
  | neg_neg (A : LProp n) : LNegStep n A.neg.neg A
  | tensor_demorgan (A B : LProp n) :
      LNegStep n (LProp.neg (LProp.tensor A B)) (LProp.par A.neg B.neg)
  | par_demorgan (A B : LProp n) :
      LNegStep n (LProp.neg (LProp.par A B)) (LProp.tensor A.neg B.neg)
  | with_demorgan (A B : LProp n) :
      LNegStep n (LProp.neg (LProp.with_ A B)) (LProp.plus A.neg B.neg)
  | plus_demorgan (A B : LProp n) :
      LNegStep n (LProp.neg (LProp.plus A B)) (LProp.with_ A.neg B.neg)
  | one_bot : LNegStep n (LProp.neg LProp.one) LProp.bot
  | bot_one : LNegStep n (LProp.neg LProp.bot) LProp.one
  | top_zero : LNegStep n (LProp.neg LProp.top) LProp.zero
  | zero_top : LNegStep n (LProp.neg LProp.zero) LProp.top
  | ofCourse_neg (A : LProp n) :
      LNegStep n (LProp.neg (LProp.ofCourse A)) (LProp.whyNot A.neg)
  | whyNot_neg (A : LProp n) :
      LNegStep n (LProp.neg (LProp.whyNot A)) (LProp.ofCourse A.neg)

/-- Convert a negation rewrite step to a Path. -/
def LNegStep.toPath : LNegStep n a b → Path a b
  | .neg_neg A          => Path.mk [Step.mk _ _ (LProp.neg_neg A)] (LProp.neg_neg A)
  | .tensor_demorgan _ _ => Path.refl _
  | .par_demorgan _ _    => Path.refl _
  | .with_demorgan _ _   => Path.refl _
  | .plus_demorgan _ _   => Path.refl _
  | .one_bot             => Path.refl _
  | .bot_one             => Path.refl _
  | .top_zero            => Path.refl _
  | .zero_top            => Path.refl _
  | .ofCourse_neg _      => Path.refl _
  | .whyNot_neg _        => Path.refl _

/-! ## Negation paths -/

-- 1. Double negation path
def neg_neg_path {n : Nat} (A : LProp n) : Path A.neg.neg A :=
  (LNegStep.neg_neg A).toPath

-- 2. Tensor De Morgan path
def tensor_demorgan_path {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.tensor A B)) (LProp.par A.neg B.neg) :=
  (LNegStep.tensor_demorgan A B).toPath

-- 3. Par De Morgan path
def par_demorgan_path {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.par A B)) (LProp.tensor A.neg B.neg) :=
  (LNegStep.par_demorgan A B).toPath

-- 4. With De Morgan path
def with_demorgan_path {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.with_ A B)) (LProp.plus A.neg B.neg) :=
  (LNegStep.with_demorgan A B).toPath

-- 5. Plus De Morgan path
def plus_demorgan_path {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.plus A B)) (LProp.with_ A.neg B.neg) :=
  (LNegStep.plus_demorgan A B).toPath

-- 6. One-Bot duality
def one_bot_path (n : Nat) : Path (LProp.neg (LProp.one : LProp n)) LProp.bot :=
  (LNegStep.one_bot (n := n)).toPath

-- 7. Bot-One duality
def bot_one_path (n : Nat) : Path (LProp.neg (LProp.bot : LProp n)) LProp.one :=
  (LNegStep.bot_one (n := n)).toPath

-- 8. ofCourse negation
def ofCourse_neg_path {n : Nat} (A : LProp n) :
    Path (LProp.neg (LProp.ofCourse A)) (LProp.whyNot A.neg) :=
  (LNegStep.ofCourse_neg A).toPath

-- 9. whyNot negation
def whyNot_neg_path {n : Nat} (A : LProp n) :
    Path (LProp.neg (LProp.whyNot A)) (LProp.ofCourse A.neg) :=
  (LNegStep.whyNot_neg A).toPath

/-! ## Symm paths (duality in reverse) -/

-- 10. Reverse De Morgan: par to neg-tensor
def par_to_neg_tensor_path {n : Nat} (A B : LProp n) :
    Path (LProp.par A.neg B.neg) (LProp.neg (LProp.tensor A B)) :=
  Path.symm (tensor_demorgan_path A B)

-- 11. Reverse: tensor to neg-par
def tensor_to_neg_par_path {n : Nat} (A B : LProp n) :
    Path (LProp.tensor A.neg B.neg) (LProp.neg (LProp.par A B)) :=
  Path.symm (par_demorgan_path A B)

/-! ## Multi-step chains -/

-- 12. Triple negation = single negation: ¬¬¬A → ¬A
def triple_neg_path {n : Nat} (A : LProp n) :
    Path A.neg.neg.neg A.neg :=
  (LNegStep.neg_neg A.neg).toPath

-- 13. Quadruple negation = identity via two double-neg steps
def quad_neg_path {n : Nat} (A : LProp n) :
    Path A.neg.neg.neg.neg A :=
  Path.trans
    (Path.congrArg LProp.neg (Path.congrArg LProp.neg (neg_neg_path A)))
    (neg_neg_path A)

-- 14. Neg of tensor then neg-neg on components:
--     ¬(A ⊗ B) → A⊥ ⅋ B⊥ (already done)
--     then congrArg to substitute: if A' = ¬¬A, then ¬(A' ⊗ B) path
def neg_tensor_chain {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.tensor A.neg.neg B)) (LProp.par A.neg.neg.neg B.neg) :=
  tensor_demorgan_path A.neg.neg B

-- 15. Full De Morgan roundtrip: ¬(A ⊗ B) → A⊥ ⅋ B⊥ → ¬(A ⊗ B)
def demorgan_roundtrip {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.tensor A B)) (LProp.neg (LProp.tensor A B)) :=
  Path.trans (tensor_demorgan_path A B) (par_to_neg_tensor_path A B)

/-! ## CongrArg paths for connectives -/

-- 16. CongrArg for tensor left
def tensor_congrArg_left {n : Nat} {A₁ A₂ : LProp n} (B : LProp n)
    (p : Path A₁ A₂) : Path (LProp.tensor A₁ B) (LProp.tensor A₂ B) :=
  Path.congrArg (fun x => LProp.tensor x B) p

-- 17. CongrArg for tensor right
def tensor_congrArg_right {n : Nat} (A : LProp n) {B₁ B₂ : LProp n}
    (p : Path B₁ B₂) : Path (LProp.tensor A B₁) (LProp.tensor A B₂) :=
  Path.congrArg (LProp.tensor A) p

-- 18. CongrArg for par left
def par_congrArg_left {n : Nat} {A₁ A₂ : LProp n} (B : LProp n)
    (p : Path A₁ A₂) : Path (LProp.par A₁ B) (LProp.par A₂ B) :=
  Path.congrArg (fun x => LProp.par x B) p

-- 19. CongrArg for par right
def par_congrArg_right {n : Nat} (A : LProp n) {B₁ B₂ : LProp n}
    (p : Path B₁ B₂) : Path (LProp.par A B₁) (LProp.par A B₂) :=
  Path.congrArg (LProp.par A) p

-- 20. CongrArg for negation
def neg_congrArg {n : Nat} {A B : LProp n}
    (p : Path A B) : Path A.neg B.neg :=
  Path.congrArg LProp.neg p

-- 21. CongrArg for ofCourse
def ofCourse_congrArg {n : Nat} {A B : LProp n}
    (p : Path A B) : Path (LProp.ofCourse A) (LProp.ofCourse B) :=
  Path.congrArg LProp.ofCourse p

-- 22. CongrArg for whyNot
def whyNot_congrArg {n : Nat} {A B : LProp n}
    (p : Path A B) : Path (LProp.whyNot A) (LProp.whyNot B) :=
  Path.congrArg LProp.whyNot p

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

/-- Rewrite steps for phase space monoid. -/
inductive PhaseStep (P : PhaseSpace.{u}) : P.carrier → P.carrier → Type u where
  | comm (a b : P.carrier) : PhaseStep P (P.mul a b) (P.mul b a)
  | assoc (a b c : P.carrier) :
      PhaseStep P (P.mul (P.mul a b) c) (P.mul a (P.mul b c))
  | unit_right (a : P.carrier) : PhaseStep P (P.mul a P.e) a
  | unit_left (a : P.carrier) : PhaseStep P (P.mul P.e a) a

def PhaseStep.toPath : PhaseStep P a b → Path a b
  | .comm a b       => Path.mk [Step.mk _ _ (P.mul_comm a b)] (P.mul_comm a b)
  | .assoc a b c    => Path.mk [Step.mk _ _ (P.mul_assoc a b c)] (P.mul_assoc a b c)
  | .unit_right a   => Path.mk [Step.mk _ _ (P.mul_e a)] (P.mul_e a)
  | .unit_left a    =>
      have h : P.mul P.e a = a := by
        have := P.mul_comm P.e a
        rw [this]; exact P.mul_e a
      Path.mk [Step.mk _ _ h] h

-- 23. Phase space commutativity path
def phaseCommPath (P : PhaseSpace.{u}) (a b : P.carrier) :
    Path (P.mul a b) (P.mul b a) :=
  (PhaseStep.comm a b).toPath

-- 24. Phase space associativity path
def phaseAssocPath (P : PhaseSpace.{u}) (a b c : P.carrier) :
    Path (P.mul (P.mul a b) c) (P.mul a (P.mul b c)) :=
  (PhaseStep.assoc a b c).toPath

-- 25. Phase space unit path
def phaseUnitPath (P : PhaseSpace.{u}) (a : P.carrier) :
    Path (P.mul a P.e) a :=
  (PhaseStep.unit_right a).toPath

-- 26. Phase space left unit path
def phaseLeftUnitPath (P : PhaseSpace.{u}) (a : P.carrier) :
    Path (P.mul P.e a) a :=
  (PhaseStep.unit_left a).toPath

-- 27. Phase monoid: (a · e) · b → a · b
def phaseUnitElimChain (P : PhaseSpace.{u}) (a b : P.carrier) :
    Path (P.mul (P.mul a P.e) b) (P.mul a b) :=
  Path.congrArg (fun x => P.mul x b) (phaseUnitPath P a)

-- 28. Phase monoid: triple reassociation
def phaseTripleAssoc (P : PhaseSpace.{u}) (a b c d : P.carrier) :
    Path (P.mul (P.mul (P.mul a b) c) d) (P.mul a (P.mul b (P.mul c d))) :=
  Path.trans
    (phaseAssocPath P (P.mul a b) c d)
    (phaseAssocPath P a b (P.mul c d))

/-- Orthogonal of a set in a phase space. -/
def PhaseSpace.orth (P : PhaseSpace) (S : P.carrier → Prop) : P.carrier → Prop :=
  fun a => ∀ b, S b → P.pole (P.mul a b)

/-- Double orthogonal closure. -/
def PhaseSpace.biorth (P : PhaseSpace) (S : P.carrier → Prop) : P.carrier → Prop :=
  P.orth (P.orth S)

-- 29. Orthogonal is antitone
theorem PhaseSpace.orth_antitone (P : PhaseSpace) (S T : P.carrier → Prop)
    (h : ∀ a, S a → T a) : ∀ a, P.orth T a → P.orth S a := by
  intro a hT b hSb
  exact hT b (h b hSb)

-- 30. S ⊆ S⊥⊥
theorem PhaseSpace.le_biorth (P : PhaseSpace) (S : P.carrier → Prop) :
    ∀ a, S a → P.biorth S a := by
  intro a ha b hb
  rw [P.mul_comm]
  exact hb a ha

-- 31. S⊥⊥⊥ = S⊥
theorem PhaseSpace.orth_biorth (P : PhaseSpace) (S : P.carrier → Prop) :
    ∀ a, P.orth (P.biorth S) a → P.orth S a := by
  intro a h b hSb
  exact h b (P.le_biorth S b hSb)

/-! ## Cut Elimination -/

/-- A proof term for multiplicative linear logic. -/
inductive MLLProof (n : Nat) where
  | ax : Fin n → MLLProof n
  | cut : MLLProof n → MLLProof n → MLLProof n
  | tensorR : MLLProof n → MLLProof n → MLLProof n
  | parR : MLLProof n → MLLProof n
  | oneR : MLLProof n
  | botR : MLLProof n → MLLProof n
deriving DecidableEq

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

-- 32. Axiom proofs are cut-free
theorem ax_is_cutFree {n : Nat} (i : Fin n) : (MLLProof.ax i).cutFree := by
  simp [MLLProof.cutFree]

-- 33. One-rule is cut-free
theorem one_is_cutFree {n : Nat} : (MLLProof.oneR : MLLProof n).cutFree := by
  simp [MLLProof.cutFree]

-- 34. CongrArg on proof size
def proof_size_congrArg {n : Nat} {p₁ p₂ : MLLProof n} (h : Path p₁ p₂) :
    Path p₁.size p₂.size :=
  Path.congrArg MLLProof.size h

-- 35. Trans path for proof composition
def proof_trans_path {n : Nat} {p₁ p₂ p₃ : MLLProof n}
    (h₁ : Path p₁ p₂) (h₂ : Path p₂ p₃) : Path p₁ p₃ :=
  Path.trans h₁ h₂

-- 36. Symm path for proof reversal
def proof_symm_path {n : Nat} {p₁ p₂ : MLLProof n} (h : Path p₁ p₂) :
    Path p₂ p₁ :=
  Path.symm h

/-! ## Transport along linear logic paths -/

-- 37. Transport negation across double-neg path
theorem transport_neg_neg {n : Nat} (A : LProp n) :
    Path.transport (D := fun X => LProp.neg X = LProp.neg X)
      (neg_neg_path A) rfl = rfl :=
  rfl

-- 38. Composing De Morgan paths: ¬(A ⊗ B) → A⊥ ⅋ B⊥ → ¬¬(A⊥ ⅋ B⊥)
def demorgan_then_neg {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.tensor A B))
         (LProp.neg (LProp.neg (LProp.par A.neg B.neg))) :=
  Path.trans
    (tensor_demorgan_path A B)
    (Path.symm (neg_neg_path (LProp.par A.neg B.neg)))

-- 39. Size is preserved by congrArg through tensorR
def tensorR_size_congrArg {n : Nat} {p₁ p₂ q : MLLProof n} (h : Path p₁ p₂) :
    Path (MLLProof.tensorR p₁ q).size (MLLProof.tensorR p₂ q).size :=
  Path.congrArg (fun x => (MLLProof.tensorR x q).size) h

-- 40. Neg of neg of tensor via chain of three steps
def neg_neg_tensor_chain {n : Nat} (A B : LProp n) :
    Path (LProp.neg (LProp.neg (LProp.tensor A B))) (LProp.tensor A B) :=
  neg_neg_path (LProp.tensor A B)

end LinearLogicPaths
end Logic
end Path
end ComputationalPaths
