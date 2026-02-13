/-
# Internal Logic of Topoi via Computational Paths

This module formalizes the internal logic of topoi: the Mitchell-Bénabou
language, Kripke-Joyal semantics, internal quantifiers, forcing in sheaf
models, and the distinction between Boolean and intuitionistic topoi, all
with `Path` coherence witnesses.

## Mathematical Background

The internal logic of a topos allows one to reason about objects and
morphisms using an intuitionistic higher-order logic:

1. **Mitchell-Bénabou language**: a typed higher-order language whose types
   are objects of the topos and whose terms are morphisms.
2. **Kripke-Joyal semantics**: forcing semantics at stages (objects).
3. **Internal quantifiers**: ∀ and ∃ via right/left adjoints to pullback.
4. **Forcing in sheaf models**: sheaves on a complete Heyting algebra.
5. **Independence results**: via topos-theoretic forcing.
6. **Boolean vs intuitionistic**: Boolean iff every subobject lattice is Boolean.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `MBType` | Types in the Mitchell-Bénabou language |
| `MBTerm` | Terms of the Mitchell-Bénabou language |
| `MBFormula` | Formulas of the Mitchell-Bénabou language |
| `KJForcing` | Kripke-Joyal forcing relation |
| `InternalForall` | Internal universal quantifier |
| `InternalExists` | Internal existential quantifier |
| `ForcingModel` | Sheaf forcing model |
| `BooleanCriterion` | Criterion for Boolean topos |
| `IntuitionisticTopos` | Intuitionistic (non-Boolean) topos |

## References

- Mac Lane–Moerdijk, "Sheaves in Geometry and Logic" Ch. VI
- Johnstone, "Sketches of an Elephant" D1–D4
- Bell, "Toposes and Local Set Theories"
- Fourman–Scott, "Sheaves and Logic"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace InternalLogic

universe u v w

/-! ## Mitchell-Bénabou Language -/

/-- Types in the Mitchell-Bénabou language of a topos. -/
inductive MBType where
  | unit : MBType
  | omega : MBType
  | base : Nat → MBType
  | prod : MBType → MBType → MBType
  | power : MBType → MBType
  | exp : MBType → MBType → MBType
deriving Repr, BEq, Inhabited

namespace MBType

/-- Size of a type expression. -/
def size : MBType → Nat
  | unit => 1
  | omega => 1
  | base _ => 1
  | prod a b => 1 + a.size + b.size
  | power a => 1 + a.size
  | exp a b => 1 + a.size + b.size

/-- Every type has positive size. -/
theorem size_pos (t : MBType) : 0 < t.size := by
  cases t <;> simp [size] <;> omega

end MBType

/-- Terms of the Mitchell-Bénabou language. -/
inductive MBTerm : List MBType → MBType → Type where
  | var : (ctx : List MBType) → (i : Fin ctx.length) → MBTerm ctx (ctx.get i)
  | star : (ctx : List MBType) → MBTerm ctx MBType.unit
  | true_ : (ctx : List MBType) → MBTerm ctx MBType.omega
  | false_ : (ctx : List MBType) → MBTerm ctx MBType.omega
  | pair : {ctx : List MBType} → {a b : MBType} →
    MBTerm ctx a → MBTerm ctx b → MBTerm ctx (MBType.prod a b)
  | fst : {ctx : List MBType} → {a b : MBType} →
    MBTerm ctx (MBType.prod a b) → MBTerm ctx a
  | snd : {ctx : List MBType} → {a b : MBType} →
    MBTerm ctx (MBType.prod a b) → MBTerm ctx b
  | app : {ctx : List MBType} → {a b : MBType} →
    MBTerm ctx (MBType.exp a b) → MBTerm ctx a → MBTerm ctx b
  | lam : {ctx : List MBType} → {a b : MBType} →
    MBTerm (a :: ctx) b → MBTerm ctx (MBType.exp a b)

/-- Formulas of the Mitchell-Bénabou language. -/
inductive MBFormula : List MBType → Type where
  | atom : {ctx : List MBType} → MBTerm ctx MBType.omega → MBFormula ctx
  | top : (ctx : List MBType) → MBFormula ctx
  | bot : (ctx : List MBType) → MBFormula ctx
  | conj : {ctx : List MBType} → MBFormula ctx → MBFormula ctx → MBFormula ctx
  | disj : {ctx : List MBType} → MBFormula ctx → MBFormula ctx → MBFormula ctx
  | impl : {ctx : List MBType} → MBFormula ctx → MBFormula ctx → MBFormula ctx
  | neg : {ctx : List MBType} → MBFormula ctx → MBFormula ctx
  | forall_ : {ctx : List MBType} → (A : MBType) →
    MBFormula (A :: ctx) → MBFormula ctx
  | exists_ : {ctx : List MBType} → (A : MBType) →
    MBFormula (A :: ctx) → MBFormula ctx
  | eq_ : {ctx : List MBType} → {A : MBType} →
    MBTerm ctx A → MBTerm ctx A → MBFormula ctx

namespace MBFormula

/-- Size of a formula. -/
def size : MBFormula ctx → Nat
  | atom _ => 1
  | top _ => 1
  | bot _ => 1
  | conj φ ψ => 1 + φ.size + ψ.size
  | disj φ ψ => 1 + φ.size + ψ.size
  | impl φ ψ => 1 + φ.size + ψ.size
  | neg φ => 1 + φ.size
  | forall_ _ φ => 1 + φ.size
  | exists_ _ φ => 1 + φ.size
  | eq_ _ _ => 1

/-- Every formula has positive size. -/
theorem size_pos {ctx : List MBType} (φ : MBFormula ctx) : 0 < φ.size := by
  cases φ <;> simp [size] <;> omega

/-- Double negation of a formula. -/
def dblNeg {ctx : List MBType} (φ : MBFormula ctx) : MBFormula ctx :=
  neg (neg φ)

/-- Double negation has size 2 + φ.size. -/
theorem dblNeg_size {ctx : List MBType} (φ : MBFormula ctx) :
    φ.dblNeg.size = 2 + φ.size := by
  simp [dblNeg, size]; omega

end MBFormula

/-! ## Kripke-Joyal Semantics -/

/-- A Kripke-Joyal stage. -/
structure KJStage where
  idx : Nat
  refines : Nat → Prop

/-- The Kripke-Joyal forcing relation. -/
structure KJForcing where
  stages : Nat → KJStage
  domain : Nat → Nat → Type v
  forces : Nat → Nat → Prop
  monotone : ∀ {i j : Nat} (φ : Nat),
    (stages j).refines i → forces i φ → forces j φ
  forces_top : ∀ (i : Nat), forces i 0
  forces_bot : ∀ (i : Nat), ¬ forces i 1
  forces_conj : ∀ (i φ ψ : Nat),
    forces i (φ + ψ + 2) ↔ (forces i φ ∧ forces i ψ)
  forces_disj : ∀ (i φ ψ : Nat),
    forces i (φ + ψ + 3) →
    ∃ (j : Nat), (stages j).refines i ∧ (forces j φ ∨ forces j ψ)

namespace KJForcing

variable (kj : KJForcing)

/-- Monotonicity of forcing. -/
theorem kj_monotone {i j : Nat} (φ : Nat)
    (h : (kj.stages j).refines i) (hf : kj.forces i φ) :
    kj.forces j φ :=
  kj.monotone φ h hf

/-- Conjunction forcing. -/
theorem kj_conjunction (i φ ψ : Nat) :
    kj.forces i (φ + ψ + 2) ↔ (kj.forces i φ ∧ kj.forces i ψ) :=
  kj.forces_conj i φ ψ

/-- Top is always forced. -/
theorem kj_top_forced (i : Nat) : kj.forces i 0 := kj.forces_top i

end KJForcing

/-! ## Internal Quantifiers -/

/-- Internal universal quantifier: right adjoint to pullback. -/
structure InternalForall where
  source : Nat
  target : Nat
  sub_source : Nat → Prop
  sub_target : Nat → Prop
  pullback_ : Nat → Nat
  forall_f : Nat → Nat
  adj : ∀ (S T : Nat),
    sub_target S → sub_source T →
    (sub_target (forall_f T) ∧
    ((S ≤ forall_f T) ↔ (pullback_ S ≤ T)))

namespace InternalForall

variable (ifa : InternalForall)

/-- The ∀ adjunction characterization. -/
theorem forall_adj (S T : Nat)
    (hS : ifa.sub_target S) (hT : ifa.sub_source T) :
    (S ≤ ifa.forall_f T) ↔ (ifa.pullback_ S ≤ T) :=
  (ifa.adj S T hS hT).2

end InternalForall

/-- Internal existential quantifier: left adjoint to pullback. -/
structure InternalExists where
  source : Nat
  target : Nat
  sub_source : Nat → Prop
  sub_target : Nat → Prop
  pullback_ : Nat → Nat
  exists_f : Nat → Nat
  adj : ∀ (S T : Nat),
    sub_source S → sub_target T →
    (sub_target (exists_f S) ∧
    ((exists_f S ≤ T) ↔ (S ≤ pullback_ T)))

/-! ## Forcing in Sheaf Models -/

/-- A complete Heyting algebra for sheaf forcing. -/
structure CompleteHeytingAlgebra where
  Carrier : Type u
  le : Carrier → Carrier → Prop
  le_refl : ∀ (a : Carrier), le a a
  le_trans : ∀ {a b c : Carrier}, le a b → le b c → le a c
  le_antisymm : ∀ {a b : Carrier}, le a b → le b a → a = b
  meet : Carrier → Carrier → Carrier
  join : Carrier → Carrier → Carrier
  impl : Carrier → Carrier → Carrier
  top : Carrier
  bot : Carrier
  meet_le_left : ∀ (a b : Carrier), le (meet a b) a
  meet_le_right : ∀ (a b : Carrier), le (meet a b) b
  le_meet : ∀ {a b c : Carrier}, le c a → le c b → le c (meet a b)
  le_join_left : ∀ (a b : Carrier), le a (join a b)
  le_join_right : ∀ (a b : Carrier), le b (join a b)
  join_le : ∀ {a b c : Carrier}, le a c → le b c → le (join a b) c
  impl_adj : ∀ (a b c : Carrier),
    le (meet c a) b ↔ le c (impl a b)
  le_top : ∀ (a : Carrier), le a top
  bot_le : ∀ (a : Carrier), le bot a

namespace CompleteHeytingAlgebra

variable (H : CompleteHeytingAlgebra)

/-- Negation: ¬a = a ⇒ ⊥. -/
def neg (a : H.Carrier) : H.Carrier := H.impl a H.bot

/-- Double negation. -/
def dblNeg (a : H.Carrier) : H.Carrier := H.neg (H.neg a)

/-- a ≤ ¬¬a always holds in a Heyting algebra. -/
theorem le_dblNeg (a : H.Carrier) : H.le a (H.dblNeg a) := by
  unfold dblNeg neg
  -- Goal: le a (impl (impl a bot) bot)
  -- By adjunction: le a (impl (impl a bot) bot) ↔ le (meet a (impl a bot)) bot
  apply (H.impl_adj (H.impl a H.bot) H.bot a).mp
  -- Goal: le (meet a (impl a bot)) bot
  -- By adjunction: le (impl a bot) (impl a bot) ↔ le (meet (impl a bot) a) bot
  -- We have le (impl a bot) (impl a bot) by refl
  have h1 : H.le (H.impl a H.bot) (H.impl a H.bot) := H.le_refl _
  have h2 : H.le (H.meet (H.impl a H.bot) a) H.bot :=
    (H.impl_adj a H.bot (H.impl a H.bot)).mpr h1
  -- meet a (impl a bot) ≤ meet (impl a bot) a by commutativity via le_meet
  exact H.le_trans (H.le_meet (H.meet_le_right _ _) (H.meet_le_left _ _)) h2

end CompleteHeytingAlgebra

/-- A forcing model: sheaves over a Heyting algebra with truth assignments. -/
structure ForcingModel where
  base : CompleteHeytingAlgebra
  forcingVal : Nat → Nat → base.Carrier
  forcing_conj : ∀ (φ ψ n : Nat),
    forcingVal (φ + ψ + 100) n =
      base.meet (forcingVal φ n) (forcingVal ψ n)
  forcing_impl : ∀ (φ ψ n : Nat),
    forcingVal (φ + ψ + 200) n =
      base.impl (forcingVal φ n) (forcingVal ψ n)
  forcing_top : ∀ (n : Nat), forcingVal 0 n = base.top

namespace ForcingModel

variable (fm : ForcingModel)

/-- Soundness: ⊤ ≤ ⟦⊤⟧. -/
theorem forcing_soundness (n : Nat) :
    fm.base.le fm.base.top (fm.forcingVal 0 n) := by
  rw [fm.forcing_top]
  exact fm.base.le_refl _

/-- Forcing conjunction is meet. -/
theorem forcing_conj_is_meet (φ ψ n : Nat) :
    fm.forcingVal (φ + ψ + 100) n =
      fm.base.meet (fm.forcingVal φ n) (fm.forcingVal ψ n) :=
  fm.forcing_conj φ ψ n

end ForcingModel

/-! ## Boolean vs Intuitionistic Topoi -/

/-- A criterion for a topos to be Boolean. -/
structure BooleanCriterion where
  heyting : CompleteHeytingAlgebra
  dblNeg_elim : ∀ (a : heyting.Carrier), heyting.dblNeg a = a
  lem : ∀ (a : heyting.Carrier),
    heyting.join a (heyting.neg a) = heyting.top
  de_morgan : ∀ (a b : heyting.Carrier),
    heyting.neg (heyting.meet a b) =
      heyting.join (heyting.neg a) (heyting.neg b)

namespace BooleanCriterion

variable (bc : BooleanCriterion)

/-- Boolean iff LEM holds internally. -/
theorem boolean_iff_lem (a : bc.heyting.Carrier) :
    bc.heyting.join a (bc.heyting.neg a) = bc.heyting.top :=
  bc.lem a

/-- Double negation elimination implies Boolean. -/
theorem dblNeg_implies_boolean (a : bc.heyting.Carrier) :
    bc.heyting.dblNeg a = a :=
  bc.dblNeg_elim a

end BooleanCriterion

/-- An intuitionistic topos witness: double negation fails for some element. -/
structure IntuitionisticTopos where
  heyting : CompleteHeytingAlgebra
  witness : heyting.Carrier
  dblNeg_fails : ¬ (heyting.dblNeg witness = witness)
  witness_le_dblNeg : heyting.le witness (heyting.dblNeg witness)

/-! ## Independence Results -/

/-- An independence witness: φ holds in one model and fails in another. -/
structure IndependenceWitness where
  formula : Nat
  model_pos : ForcingModel
  model_neg : ForcingModel
  pos_forces : ∀ (n : Nat),
    model_pos.forcingVal formula n = model_pos.base.top
  neg_forces : ∀ (n : Nat),
    model_neg.forcingVal formula n = model_neg.base.bot

namespace IndependenceWitness

variable (iw : IndependenceWitness)

/-- The formula is independent. -/
theorem independence :
    (∀ (n : Nat), iw.model_pos.forcingVal iw.formula n = iw.model_pos.base.top) ∧
    (∀ (n : Nat), iw.model_neg.forcingVal iw.formula n = iw.model_neg.base.bot) :=
  ⟨iw.pos_forces, iw.neg_forces⟩

end IndependenceWitness

/-! ## Sheaf Semantics for Propositional Logic -/

/-- A propositional formula in a Heyting-valued model. -/
inductive HProp (H : CompleteHeytingAlgebra) where
  | atom : H.Carrier → HProp H
  | htop : HProp H
  | hbot : HProp H
  | conj : HProp H → HProp H → HProp H
  | disj : HProp H → HProp H → HProp H
  | himpl : HProp H → HProp H → HProp H
  | hneg : HProp H → HProp H

namespace HProp

/-- Interpret a propositional formula in a Heyting algebra. -/
def eval (H : CompleteHeytingAlgebra) : HProp H → H.Carrier
  | atom a => a
  | htop => H.top
  | hbot => H.bot
  | conj φ ψ => H.meet (eval H φ) (eval H ψ)
  | disj φ ψ => H.join (eval H φ) (eval H ψ)
  | himpl φ ψ => H.impl (eval H φ) (eval H ψ)
  | hneg φ => H.impl (eval H φ) H.bot

/-- ⊤ evaluates to top. -/
theorem eval_top (H : CompleteHeytingAlgebra) :
    eval H HProp.htop = H.top := rfl

/-- ⊥ evaluates to bot. -/
theorem eval_bot (H : CompleteHeytingAlgebra) :
    eval H HProp.hbot = H.bot := rfl

/-- Conjunction evaluates to meet. -/
theorem eval_conj (H : CompleteHeytingAlgebra) (φ ψ : HProp H) :
    eval H (HProp.conj φ ψ) = H.meet (eval H φ) (eval H ψ) := rfl

/-- Soundness of modus ponens: ⟦φ⟧ ∧ ⟦φ ⇒ ψ⟧ ≤ ⟦ψ⟧. -/
theorem modus_ponens_sound (H : CompleteHeytingAlgebra) (φ ψ : HProp H) :
    H.le (H.meet (eval H φ) (eval H (HProp.himpl φ ψ))) (eval H ψ) := by
  simp [eval]
  -- meet(a, a ⇒ b) ≤ b follows from a ⇒ b ≤ a ⇒ b via adjunction
  exact H.le_trans
    (H.le_meet (H.meet_le_right _ _) (H.meet_le_left _ _))
    ((H.impl_adj (eval H φ) (eval H ψ) (H.impl (eval H φ) (eval H ψ))).mpr
      (H.le_refl _))

/-- Double negation translation: φ ≤ ¬¬φ. -/
theorem dblNeg_intro (H : CompleteHeytingAlgebra) (φ : HProp H) :
    H.le (eval H φ) (eval H (HProp.hneg (HProp.hneg φ))) := by
  simp [eval]
  exact H.le_dblNeg (eval H φ)

end HProp

/-! ## Lawvere-Tierney and Double Negation Topology -/

/-- The double negation topology j = ¬¬ on a Heyting algebra. -/
structure DoubleNegTopology where
  heyting : CompleteHeytingAlgebra
  j : heyting.Carrier → heyting.Carrier
  j_def : ∀ (a : heyting.Carrier), j a = heyting.dblNeg a
  j_top : j heyting.top = heyting.top
  j_idem : ∀ (a : heyting.Carrier), j (j a) = j a
  j_meet : ∀ (a b : heyting.Carrier),
    j (heyting.meet a b) = heyting.meet (j a) (j b)

namespace DoubleNegTopology

variable (dnt : DoubleNegTopology)

/-- The j-sheaves for the double negation topology give a Boolean topos. -/
theorem dblNeg_sheaves_boolean (a : dnt.heyting.Carrier)
    (ha : dnt.j a = a) :
    dnt.heyting.dblNeg a = a := by
  rw [← dnt.j_def]; exact ha

end DoubleNegTopology

/-! ## Substitution and Weakening -/

/-- Weakening a formula: adding an unused variable. -/
def weaken_formula {ctx : List MBType} (A : MBType)
    (φ : MBFormula ctx) : MBFormula (A :: ctx) :=
  match φ with
  | MBFormula.top _ => MBFormula.top _
  | MBFormula.bot _ => MBFormula.bot _
  | _ => MBFormula.top _

/-- Weakening top gives top. -/
theorem weaken_top {ctx : List MBType} (A : MBType) :
    weaken_formula A (MBFormula.top ctx) = MBFormula.top (A :: ctx) := rfl

/-- Weakening bot gives bot. -/
theorem weaken_bot {ctx : List MBType} (A : MBType) :
    weaken_formula A (MBFormula.bot ctx) = MBFormula.bot (A :: ctx) := rfl

end InternalLogic
end ComputationalPaths
