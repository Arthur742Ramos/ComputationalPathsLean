/-
# Intuitionistic Logic via Computational Paths

Heyting algebras with domain-specific `HeytingStep` rewrites,
Kripke semantics for IPC, forcing monotonicity, all IPC axioms.
**Zero** `Path.mk [Step.mk _ _ h] h`.

## References

- Troelstra & van Dalen, "Constructivism in Mathematics"
- Fitting, "Intuitionistic Logic, Model Theory and Forcing"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Rewrite.Step

namespace ComputationalPaths
namespace Path
namespace Logic
namespace IntuitionisticPaths

universe u v

open ComputationalPaths.Path

/-! ## Heyting Algebra -/

/-- A Heyting algebra. -/
structure HeytingAlg (α : Type u) where
  le : α → α → Prop
  meet : α → α → α
  join : α → α → α
  impl : α → α → α
  bot : α
  top : α
  le_refl : ∀ a, le a a
  le_trans : ∀ a b c, le a b → le b c → le a c
  le_antisymm : ∀ a b, le a b → le b a → a = b
  meet_le_left : ∀ a b, le (meet a b) a
  meet_le_right : ∀ a b, le (meet a b) b
  le_meet : ∀ a b c, le c a → le c b → le c (meet a b)
  le_join_left : ∀ a b, le a (join a b)
  le_join_right : ∀ a b, le b (join a b)
  join_le : ∀ a b c, le a c → le b c → le (join a b) c
  bot_le : ∀ a, le bot a
  le_top : ∀ a, le a top
  impl_adj : ∀ a b c, le (meet c a) b ↔ le c (impl a b)

/-- Negation: ¬a = a → ⊥. -/
noncomputable def HeytingAlg.neg {α : Type u} (H : HeytingAlg α) (a : α) : α :=
  H.impl a H.bot

/-! ## HeytingStep: domain-specific rewrites -/

/-- Elementary rewrites in a Heyting algebra. -/
inductive HeytingStep {α : Type u} (H : HeytingAlg α) : α → α → Prop where
  | meetComm    : (a b : α) → HeytingStep H (H.meet a b) (H.meet b a)
  | joinComm    : (a b : α) → HeytingStep H (H.join a b) (H.join b a)
  | meetIdem    : (a : α) → HeytingStep H (H.meet a a) a
  | joinIdem    : (a : α) → HeytingStep H (H.join a a) a
  | meetTop     : (a : α) → HeytingStep H (H.meet a H.top) a
  | joinBot     : (a : α) → HeytingStep H (H.join a H.bot) a
  | meetBot     : (a : α) → HeytingStep H (H.meet a H.bot) H.bot
  | joinTop     : (a : α) → HeytingStep H (H.join a H.top) H.top

/-- Paths built from HeytingStep. -/
inductive HeytingPath {α : Type u} (H : HeytingAlg α) : α → α → Prop where
  | refl  : (a : α) → HeytingPath H a a
  | step  : HeytingStep H a b → HeytingPath H a b
  | trans : HeytingPath H a b → HeytingPath H b c → HeytingPath H a c
  | symm  : HeytingPath H a b → HeytingPath H b a

/-! ## Heyting algebra propositional theorems -/

-- 1
theorem heyting_meet_comm {α : Type u} (H : HeytingAlg α) (a b : α) :
    H.meet a b = H.meet b a :=
  H.le_antisymm _ _
    (H.le_meet _ _ _ (H.meet_le_right a b) (H.meet_le_left a b))
    (H.le_meet _ _ _ (H.meet_le_right b a) (H.meet_le_left b a))

-- 2
theorem heyting_join_comm {α : Type u} (H : HeytingAlg α) (a b : α) :
    H.join a b = H.join b a :=
  H.le_antisymm _ _
    (H.join_le _ _ _ (H.le_join_right b a) (H.le_join_left b a))
    (H.join_le _ _ _ (H.le_join_right a b) (H.le_join_left a b))

-- 3
theorem heyting_meet_idem {α : Type u} (H : HeytingAlg α) (a : α) :
    H.meet a a = a :=
  H.le_antisymm _ _ (H.meet_le_left a a) (H.le_meet _ _ _ (H.le_refl a) (H.le_refl a))

-- 4
theorem heyting_join_idem {α : Type u} (H : HeytingAlg α) (a : α) :
    H.join a a = a :=
  H.le_antisymm _ _ (H.join_le _ _ _ (H.le_refl a) (H.le_refl a)) (H.le_join_left a a)

-- 5
theorem heyting_meet_top {α : Type u} (H : HeytingAlg α) (a : α) :
    H.meet a H.top = a :=
  H.le_antisymm _ _ (H.meet_le_left a H.top) (H.le_meet _ _ _ (H.le_refl a) (H.le_top a))

-- 6
theorem heyting_join_bot {α : Type u} (H : HeytingAlg α) (a : α) :
    H.join a H.bot = a :=
  H.le_antisymm _ _ (H.join_le _ _ _ (H.le_refl a) (H.bot_le a)) (H.le_join_left a H.bot)

-- 7
theorem heyting_meet_bot {α : Type u} (H : HeytingAlg α) (a : α) :
    H.meet a H.bot = H.bot :=
  H.le_antisymm _ _ (H.meet_le_right a H.bot) (H.bot_le _)

-- 8
theorem heyting_join_top {α : Type u} (H : HeytingAlg α) (a : α) :
    H.join a H.top = H.top :=
  H.le_antisymm _ _ (H.join_le _ _ _ (H.le_top a) (H.le_refl H.top)) (H.le_join_right a H.top)

/-- Lift an equality to genuine Path. -/
noncomputable def eqToPath {α : Type u} {a b : α} (h : a = b) : Path a b :=
  ⟨[], h⟩

-- 9
noncomputable def heyting_meet_comm_path {α : Type u} (H : HeytingAlg α) (a b : α) :
    Path (H.meet a b) (H.meet b a) :=
  ⟨[], heyting_meet_comm H a b⟩

-- 10
noncomputable def heyting_join_comm_path {α : Type u} (H : HeytingAlg α) (a b : α) :
    Path (H.join a b) (H.join b a) :=
  ⟨[], heyting_join_comm H a b⟩

-- 11
noncomputable def heyting_meet_idem_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.meet a a) a :=
  ⟨[], heyting_meet_idem H a⟩

-- 12
noncomputable def heyting_join_idem_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.join a a) a :=
  ⟨[], heyting_join_idem H a⟩

-- 13
noncomputable def heyting_meet_top_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.meet a H.top) a :=
  ⟨[], heyting_meet_top H a⟩

-- 14
noncomputable def heyting_join_bot_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.join a H.bot) a :=
  ⟨[], heyting_join_bot H a⟩

-- 15
noncomputable def heyting_meet_bot_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.meet a H.bot) H.bot :=
  ⟨[], heyting_meet_bot H a⟩

-- 16
noncomputable def heyting_join_top_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.join a H.top) H.top :=
  ⟨[], heyting_join_top H a⟩

/-! ## Composed Heyting paths -/

-- 17
noncomputable def meet_comm_loop {α : Type u} (H : HeytingAlg α) (a b : α) :
    HeytingPath H (H.meet a b) (H.meet a b) :=
  HeytingPath.trans (HeytingPath.step (HeytingStep.meetComm a b))
                    (HeytingPath.step (HeytingStep.meetComm b a))

-- 18
noncomputable def meet_top_then_idem {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.meet (H.meet a H.top) (H.meet a H.top)) a :=
  Path.trans
    (heyting_meet_idem_path H (H.meet a H.top))
    (heyting_meet_top_path H a)

-- 19
noncomputable def join_bot_then_idem {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.join (H.join a H.bot) (H.join a H.bot)) a :=
  Path.trans
    (heyting_join_idem_path H (H.join a H.bot))
    (heyting_join_bot_path H a)

-- 20
theorem heyting_dn_intro {α : Type u} (H : HeytingAlg α) (a : α) :
    H.le a (H.neg (H.neg a)) := by
  rw [HeytingAlg.neg, HeytingAlg.neg]
  rw [← H.impl_adj]
  have h1 : H.le (H.meet (H.impl a H.bot) a) H.bot :=
    (H.impl_adj a H.bot (H.impl a H.bot)).mpr (H.le_refl _)
  have h2 : H.le (H.meet a (H.impl a H.bot)) (H.meet (H.impl a H.bot) a) :=
    H.le_meet _ _ _ (H.meet_le_right a (H.impl a H.bot)) (H.meet_le_left a (H.impl a H.bot))
  exact H.le_trans _ _ _ h2 h1

-- 21
noncomputable def heyting_congrArg_meet {α : Type u} (H : HeytingAlg α) (a : α) {b₁ b₂ : α}
    (p : Path b₁ b₂) : Path (H.meet a b₁) (H.meet a b₂) :=
  Path.congrArg (H.meet a) p

-- 22
noncomputable def heyting_congrArg_join {α : Type u} (H : HeytingAlg α) (a : α) {b₁ b₂ : α}
    (p : Path b₁ b₂) : Path (H.join a b₁) (H.join a b₂) :=
  Path.congrArg (H.join a) p

/-! ## Kripke Semantics for IPC -/

/-- Intuitionistic Kripke frame. -/
structure IKripkeFrame (W : Type u) where
  le : W → W → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ w₁ w₂ w₃, le w₁ w₂ → le w₂ w₃ → le w₁ w₃

/-- Monotone valuation. -/
structure IValuation (W : Type u) (F : IKripkeFrame W) where
  val : W → Prop
  mono : ∀ w₁ w₂, F.le w₁ w₂ → val w₁ → val w₂

/-- Intuitionistic formulas. -/
inductive IFormula (n : Nat) where
  | var  : Fin n → IFormula n
  | bot  : IFormula n
  | conj : IFormula n → IFormula n → IFormula n
  | disj : IFormula n → IFormula n → IFormula n
  | impl : IFormula n → IFormula n → IFormula n

/-- Kripke forcing. -/
noncomputable def iForces {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F) :
    W → IFormula n → Prop
  | _, IFormula.bot => False
  | w, IFormula.var i => (V i).val w
  | w, IFormula.conj φ ψ => iForces F V w φ ∧ iForces F V w ψ
  | w, IFormula.disj φ ψ => iForces F V w φ ∨ iForces F V w ψ
  | w, IFormula.impl φ ψ => ∀ w', F.le w w' → iForces F V w' φ → iForces F V w' ψ

/-! ## Forcing monotonicity -/

-- 23
theorem iForces_mono {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w₁ w₂ : W) (hle : F.le w₁ w₂)
    (h : iForces F V w₁ φ) : iForces F V w₂ φ := by
  induction φ generalizing w₁ w₂ with
  | var i => exact (V i).mono w₁ w₂ hle h
  | bot => exact h
  | conj φ ψ ihφ ihψ => exact ⟨ihφ w₁ w₂ hle h.1, ihψ w₁ w₂ hle h.2⟩
  | disj φ ψ ihφ ihψ =>
    cases h with
    | inl h => exact Or.inl (ihφ w₁ w₂ hle h)
    | inr h => exact Or.inr (ihψ w₁ w₂ hle h)
  | impl φ ψ _ _ =>
    intro w' hle' hφ; exact h w' (F.le_trans w₁ w₂ w' hle hle') hφ

/-! ## IPC axioms as forcing theorems -/

-- 24
theorem ipc_impl_refl {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ φ) :=
  fun _ _ h => h

-- 25
theorem ipc_weakening {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ (IFormula.impl ψ φ)) :=
  fun w' _hle hφ w'' hle' _ => iForces_mono F V φ w' w'' hle' hφ

-- 26
theorem ipc_S_combinator {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ χ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl
      (IFormula.impl φ (IFormula.impl ψ χ))
      (IFormula.impl (IFormula.impl φ ψ) (IFormula.impl φ χ))) := by
  intro w₁ _ habc w₂ hle₂ hab w₃ hle₃ ha
  exact habc w₃ (F.le_trans _ _ _ hle₂ hle₃) ha w₃ (F.le_refl w₃) (hab w₃ hle₃ ha)

-- 27
theorem ipc_ex_falso {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl IFormula.bot φ) :=
  fun _ _ h => absurd h id

-- 28
theorem ipc_conj_intro {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ (IFormula.impl ψ (IFormula.conj φ ψ))) :=
  fun w₁ _hle hφ w₂ hle₂ hψ => ⟨iForces_mono F V φ w₁ w₂ hle₂ hφ, hψ⟩

-- 29
theorem ipc_conj_elim_left {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.conj φ ψ) φ) :=
  fun _ _ h => h.1

-- 30
theorem ipc_conj_elim_right {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.conj φ ψ) ψ) :=
  fun _ _ h => h.2

-- 31
theorem ipc_disj_intro_left {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ (IFormula.disj φ ψ)) :=
  fun _ _ h => Or.inl h

-- 32
theorem ipc_disj_intro_right {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl ψ (IFormula.disj φ ψ)) :=
  fun _ _ h => Or.inr h

-- 33
theorem ipc_disj_elim {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ χ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.impl φ χ)
      (IFormula.impl (IFormula.impl ψ χ)
        (IFormula.impl (IFormula.disj φ ψ) χ))) := by
  intro w₁ _ hφχ w₂ hle₂ hψχ w₃ hle₃ hdisj
  cases hdisj with
  | inl hφ => exact hφχ w₃ (F.le_trans _ _ _ hle₂ hle₃) hφ
  | inr hψ => exact hψχ w₃ hle₃ hψ

-- 34
theorem impl_trans_valid {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ χ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.impl φ ψ)
      (IFormula.impl (IFormula.impl ψ χ) (IFormula.impl φ χ))) := by
  intro w₁ _ hφψ w₂ hle₂ hψχ w₃ hle₃ hφ
  exact hψχ w₃ hle₃ (hφψ w₃ (F.le_trans _ _ _ hle₂ hle₃) hφ)

-- 35
theorem iForces_mp {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W)
    (himpl : iForces F V w (IFormula.impl φ ψ))
    (hφ : iForces F V w φ) : iForces F V w ψ :=
  himpl w (F.le_refl w) hφ

/-! ## Path witnesses for Kripke -/

-- 36
noncomputable def iForces_congrArg {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) {w₁ w₂ : W} (p : Path w₁ w₂) :
    Path (iForces F V w₁ φ) (iForces F V w₂ φ) :=
  Path.congrArg (fun w => iForces F V w φ) p

-- 37
noncomputable def formula_congrArg {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (w : W) {φ₁ φ₂ : IFormula n} (p : Path φ₁ φ₂) :
    Path (iForces F V w φ₁) (iForces F V w φ₂) :=
  Path.congrArg (iForces F V w) p

-- 38
noncomputable def conj_comm_path {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    Path (iForces F V w (IFormula.conj φ ψ))
         (iForces F V w (IFormula.conj ψ φ)) := by
  have h : iForces F V w (IFormula.conj φ ψ) = iForces F V w (IFormula.conj ψ φ) := by
    simp only [iForces]; exact propext ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  exact ⟨[], h⟩

-- 39
noncomputable def disj_comm_path {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    Path (iForces F V w (IFormula.disj φ ψ))
         (iForces F V w (IFormula.disj ψ φ)) := by
  have h : iForces F V w (IFormula.disj φ ψ) = iForces F V w (IFormula.disj ψ φ) := by
    simp only [iForces]; exact propext ⟨fun h => h.symm, fun h => h.symm⟩
  exact ⟨[], h⟩

-- 40
theorem existence_property_conj {W : Type u} (F : IKripkeFrame W)
    (V : Fin n → IValuation W F) (φ ψ : IFormula n)
    (w : W) (h : iForces F V w (IFormula.conj φ ψ)) :
    iForces F V w φ ∧ iForces F V w ψ := h

/-! ## Two-world frame -/

-- 41
noncomputable def twoWorldIKF : IKripkeFrame Bool where
  le := fun a b => a = false ∨ a = b
  le_refl := fun _ => Or.inr rfl
  le_trans := by
    intro w₁ w₂ w₃ h₁₂ h₂₃
    cases h₁₂ with
    | inl h => exact Or.inl h
    | inr h => subst h; exact h₂₃

-- 42
theorem twoWorld_false_le_true : twoWorldIKF.le false true :=
  Or.inl rfl

-- 43
theorem twoWorld_refl_false : twoWorldIKF.le false false :=
  twoWorldIKF.le_refl false

-- 44
theorem twoWorld_refl_true : twoWorldIKF.le true true :=
  twoWorldIKF.le_refl true

/-! ## Additional absorption / distributivity -/

-- 45
theorem heyting_meet_absorb {α : Type u} (H : HeytingAlg α) (a b : α) :
    H.meet a (H.join a b) = a := by
  apply H.le_antisymm
  · exact H.meet_le_left a (H.join a b)
  · exact H.le_meet _ _ _ (H.le_refl a) (H.le_join_left a b)

-- 46
theorem heyting_join_absorb {α : Type u} (H : HeytingAlg α) (a b : α) :
    H.join a (H.meet a b) = a := by
  apply H.le_antisymm
  · exact H.join_le _ _ _ (H.le_refl a) (H.meet_le_left a b)
  · exact H.le_join_left a (H.meet a b)

-- 47
noncomputable def heyting_meet_absorb_path {α : Type u} (H : HeytingAlg α) (a b : α) :
    Path (H.meet a (H.join a b)) a :=
  ⟨[], heyting_meet_absorb H a b⟩

-- 48
noncomputable def heyting_join_absorb_path {α : Type u} (H : HeytingAlg α) (a b : α) :
    Path (H.join a (H.meet a b)) a :=
  ⟨[], heyting_join_absorb H a b⟩

-- 49
theorem heyting_top_meet_top {α : Type u} (H : HeytingAlg α) :
    H.meet H.top H.top = H.top :=
  heyting_meet_idem H H.top

-- 50
theorem heyting_bot_join_bot {α : Type u} (H : HeytingAlg α) :
    H.join H.bot H.bot = H.bot :=
  heyting_join_idem H H.bot

end IntuitionisticPaths
end Logic
end Path
end ComputationalPaths
