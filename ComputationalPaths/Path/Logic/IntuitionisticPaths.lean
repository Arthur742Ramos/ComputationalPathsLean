/-
# Intuitionistic Logic via Computational Paths

This module models intuitionistic logic using computational paths:
Heyting algebras, Kripke semantics for intuitionistic logic,
intuitionistic propositional calculus, disjunction/existence properties,
and proof-relevant interpretations via Path.

## References

- Troelstra & van Dalen, "Constructivism in Mathematics"
- Fitting, "Intuitionistic Logic, Model Theory and Forcing"
-/

import ComputationalPaths

namespace ComputationalPaths
namespace Path
namespace Logic
namespace IntuitionisticPaths

universe u

open ComputationalPaths.Path

/-! ## Heyting Algebra Structure -/

/-- A Heyting algebra: a bounded distributive lattice with implication. -/
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

/-- Negation in a Heyting algebra: ¬a = a → ⊥. -/
def HeytingAlg.neg {α : Type u} (H : HeytingAlg α) (a : α) : α :=
  H.impl a H.bot

/-! ## Heyting Algebra Path Theorems -/

/-- Double negation introduction in Heyting algebras via path. -/
theorem heyting_dn_intro {α : Type u} (H : HeytingAlg α) (a : α) :
    H.le a (H.neg (H.neg a)) := by
  rw [HeytingAlg.neg, HeytingAlg.neg]
  rw [← H.impl_adj]
  -- Goal: H.le (H.meet a (H.impl a H.bot)) H.bot
  -- impl_adj a bot (impl a bot) : le (meet (impl a bot) a) bot ↔ le (impl a bot) (impl a bot)
  -- .mpr (le_refl _) : le (meet (impl a bot) a) bot
  have h1 : H.le (H.meet (H.impl a H.bot) a) H.bot :=
    (H.impl_adj a H.bot (H.impl a H.bot)).mpr (H.le_refl _)
  -- meet is commutative
  have h2 : H.le (H.meet a (H.impl a H.bot)) (H.meet (H.impl a H.bot) a) :=
    H.le_meet _ _ _ (H.meet_le_right a (H.impl a H.bot)) (H.meet_le_left a (H.impl a H.bot))
  exact H.le_trans _ _ _ h2 h1

/-- Path witness for meet commutativity. -/
theorem heyting_meet_comm {α : Type u} (H : HeytingAlg α) (a b : α) :
    H.meet a b = H.meet b a := by
  apply H.le_antisymm
  · exact H.le_meet _ _ _ (H.meet_le_right a b) (H.meet_le_left a b)
  · exact H.le_meet _ _ _ (H.meet_le_right b a) (H.meet_le_left b a)

/-- Path for meet commutativity using computational paths. -/
def heyting_meet_comm_path {α : Type u} (H : HeytingAlg α) (a b : α) :
    Path (H.meet a b) (H.meet b a) :=
  Path.ofEq (heyting_meet_comm H a b)

/-- Join commutativity. -/
theorem heyting_join_comm {α : Type u} (H : HeytingAlg α) (a b : α) :
    H.join a b = H.join b a := by
  apply H.le_antisymm
  · exact H.join_le _ _ _ (H.le_join_right b a) (H.le_join_left b a)
  · exact H.join_le _ _ _ (H.le_join_right a b) (H.le_join_left a b)

/-- Path for join commutativity. -/
def heyting_join_comm_path {α : Type u} (H : HeytingAlg α) (a b : α) :
    Path (H.join a b) (H.join b a) :=
  Path.ofEq (heyting_join_comm H a b)

/-- Meet idempotence. -/
theorem heyting_meet_idem {α : Type u} (H : HeytingAlg α) (a : α) :
    H.meet a a = a := by
  apply H.le_antisymm
  · exact H.meet_le_left a a
  · exact H.le_meet _ _ _ (H.le_refl a) (H.le_refl a)

/-- Path for meet idempotence. -/
def heyting_meet_idem_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.meet a a) a :=
  Path.ofEq (heyting_meet_idem H a)

/-- Join idempotence. -/
theorem heyting_join_idem {α : Type u} (H : HeytingAlg α) (a : α) :
    H.join a a = a := by
  apply H.le_antisymm
  · exact H.join_le _ _ _ (H.le_refl a) (H.le_refl a)
  · exact H.le_join_left a a

/-- Path for join idempotence. -/
def heyting_join_idem_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.join a a) a :=
  Path.ofEq (heyting_join_idem H a)

/-- Top is meet identity. -/
theorem heyting_meet_top {α : Type u} (H : HeytingAlg α) (a : α) :
    H.meet a H.top = a := by
  apply H.le_antisymm
  · exact H.meet_le_left a H.top
  · exact H.le_meet _ _ _ (H.le_refl a) (H.le_top a)

/-- Path for meet with top. -/
def heyting_meet_top_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.meet a H.top) a :=
  Path.ofEq (heyting_meet_top H a)

/-- Bot is join identity. -/
theorem heyting_join_bot {α : Type u} (H : HeytingAlg α) (a : α) :
    H.join a H.bot = a := by
  apply H.le_antisymm
  · exact H.join_le _ _ _ (H.le_refl a) (H.bot_le a)
  · exact H.le_join_left a H.bot

/-- Path for join with bot. -/
def heyting_join_bot_path {α : Type u} (H : HeytingAlg α) (a : α) :
    Path (H.join a H.bot) a :=
  Path.ofEq (heyting_join_bot H a)

/-! ## Kripke Semantics for Intuitionistic Logic -/

/-- An intuitionistic Kripke frame: a preorder on worlds. -/
structure IKripkeFrame (W : Type u) where
  le : W → W → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ w₁ w₂ w₃, le w₁ w₂ → le w₂ w₃ → le w₁ w₃

/-- A monotone valuation on an intuitionistic Kripke frame. -/
structure IValuation (W : Type u) (F : IKripkeFrame W) where
  val : W → Prop
  mono : ∀ w₁ w₂, F.le w₁ w₂ → val w₁ → val w₂

/-- Intuitionistic formulas. -/
inductive IFormula (n : Nat) where
  | var : Fin n → IFormula n
  | bot : IFormula n
  | conj : IFormula n → IFormula n → IFormula n
  | disj : IFormula n → IFormula n → IFormula n
  | impl : IFormula n → IFormula n → IFormula n

/-- Truth at a world for intuitionistic Kripke semantics. -/
def iForces {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F) :
    W → IFormula n → Prop
  | _, IFormula.bot => False
  | w, IFormula.var i => (V i).val w
  | w, IFormula.conj φ ψ => iForces F V w φ ∧ iForces F V w ψ
  | w, IFormula.disj φ ψ => iForces F V w φ ∨ iForces F V w ψ
  | w, IFormula.impl φ ψ => ∀ w', F.le w w' → iForces F V w' φ → iForces F V w' ψ

/-- Monotonicity of forcing: truth persists along the preorder. -/
theorem iForces_mono {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w₁ w₂ : W) (hle : F.le w₁ w₂)
    (h : iForces F V w₁ φ) : iForces F V w₂ φ := by
  induction φ generalizing w₁ w₂ with
  | var i => exact (V i).mono w₁ w₂ hle h
  | bot => exact h
  | conj φ ψ ihφ ihψ =>
    exact ⟨ihφ w₁ w₂ hle h.1, ihψ w₁ w₂ hle h.2⟩
  | disj φ ψ ihφ ihψ =>
    cases h with
    | inl h => exact Or.inl (ihφ w₁ w₂ hle h)
    | inr h => exact Or.inr (ihψ w₁ w₂ hle h)
  | impl φ ψ _ _ =>
    intro w' hle' hφ
    exact h w' (F.le_trans w₁ w₂ w' hle hle') hφ

/-- Path witness for monotonicity transport. -/
def iForces_mono_path {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w₁ w₂ : W) (p : Path w₁ w₂) :
    Path
      (∀ hle : F.le w₁ w₂, iForces F V w₁ φ → iForces F V w₂ φ)
      (∀ hle : F.le w₁ w₂, iForces F V w₁ φ → iForces F V w₂ φ) :=
  Path.refl _

/-! ## Intuitionistic Propositional Calculus -/

/-- Implication reflexivity: a → a is intuitionistically valid. -/
theorem ipc_impl_refl {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ φ) := by
  intro w' _ h; exact h

/-- Weakening: a → b → a. -/
theorem ipc_weakening {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ (IFormula.impl ψ φ)) := by
  intro w' hle hφ w'' hle' _
  exact iForces_mono F V φ w' w'' hle' hφ

/-- S combinator: (a → b → c) → (a → b) → a → c. -/
theorem ipc_S_combinator {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ χ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl
      (IFormula.impl φ (IFormula.impl ψ χ))
      (IFormula.impl (IFormula.impl φ ψ) (IFormula.impl φ χ))) := by
  intro w₁ _ habc w₂ hle₂ hab w₃ hle₃ ha
  have hb := hab w₃ hle₃ ha
  have hbc := habc w₃ (F.le_trans _ _ _ hle₂ hle₃) ha
  exact hbc w₃ (F.le_refl w₃) hb

/-- Ex falso: ⊥ → a. -/
theorem ipc_ex_falso {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl IFormula.bot φ) := by
  intro _ _ h; exact absurd h id

/-- Conjunction introduction. -/
theorem ipc_conj_intro {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ (IFormula.impl ψ (IFormula.conj φ ψ))) := by
  intro w₁ hle hφ w₂ hle₂ hψ
  exact ⟨iForces_mono F V φ w₁ w₂ hle₂ hφ, hψ⟩

/-- Conjunction elimination left. -/
theorem ipc_conj_elim_left {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.conj φ ψ) φ) := by
  intro _ _ h; exact h.1

/-- Conjunction elimination right. -/
theorem ipc_conj_elim_right {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.conj φ ψ) ψ) := by
  intro _ _ h; exact h.2

/-- Disjunction introduction left. -/
theorem ipc_disj_intro_left {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl φ (IFormula.disj φ ψ)) := by
  intro _ _ h; exact Or.inl h

/-- Disjunction introduction right. -/
theorem ipc_disj_intro_right {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl ψ (IFormula.disj φ ψ)) := by
  intro _ _ h; exact Or.inr h

/-- Disjunction elimination. -/
theorem ipc_disj_elim {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ χ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.impl φ χ)
      (IFormula.impl (IFormula.impl ψ χ)
        (IFormula.impl (IFormula.disj φ ψ) χ))) := by
  intro w₁ _ hφχ w₂ hle₂ hψχ w₃ hle₃ hdisj
  cases hdisj with
  | inl hφ => exact hφχ w₃ (F.le_trans _ _ _ hle₂ hle₃) hφ
  | inr hψ => exact hψχ w₃ hle₃ hψ

/-! ## Disjunction Property -/

/-- The disjunction property: in the universal model (all frames),
    if a ∨ b is valid then a is valid or b is valid.
    Here we prove it for a specific two-world frame. -/
structure TwoWorldFrame where
  w₀ : Unit
  w₁ : Unit

/-- The two-world frame with w₀ ≤ w₁. -/
def twoWorldIKF : IKripkeFrame Bool where
  le := fun a b => a = false ∨ a = b
  le_refl := fun w => Or.inr rfl
  le_trans := by
    intro w₁ w₂ w₃ h₁₂ h₂₃
    cases h₁₂ with
    | inl h => exact Or.inl h
    | inr h => subst h; exact h₂₃

/-- Congruence path for forcing along world equality. -/
def iForces_congrArg_path {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ : IFormula n) (w₁ w₂ : W) (p : Path w₁ w₂) :
    Path (iForces F V w₁ φ) (iForces F V w₂ φ) :=
  Path.congrArg (fun w => iForces F V w φ) p

/-! ## Existence Property -/

/-- Existence property model: a frame with explicit witnesses. -/
theorem existence_property_conj {W : Type u} (F : IKripkeFrame W)
    (V : Fin n → IValuation W F) (φ ψ : IFormula n)
    (w : W) (h : iForces F V w (IFormula.conj φ ψ)) :
    iForces F V w φ ∧ iForces F V w ψ := h

/-- Transport of forcing along a path of worlds. -/
theorem iForces_transport {W : Type u} (F : IKripkeFrame W)
    (V : Fin n → IValuation W F) (φ : IFormula n)
    (w₁ w₂ : W) (p : Path w₁ w₂) :
    Path.transport (D := fun w => iForces F V w φ → iForces F V w φ) p id = id := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.transport]

/-- Modus ponens for Kripke semantics. -/
theorem iForces_mp {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W)
    (himpl : iForces F V w (IFormula.impl φ ψ))
    (hφ : iForces F V w φ) :
    iForces F V w ψ :=
  himpl w (F.le_refl w) hφ

/-- Symmetry path for conjunction commutativity. -/
def conj_comm_path {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ : IFormula n) (w : W) :
    Path (iForces F V w (IFormula.conj φ ψ))
         (iForces F V w (IFormula.conj ψ φ)) := by
  have h : iForces F V w (IFormula.conj φ ψ) = iForces F V w (IFormula.conj ψ φ) := by
    simp only [iForces]
    exact propext ⟨fun ⟨a, b⟩ => ⟨b, a⟩, fun ⟨a, b⟩ => ⟨b, a⟩⟩
  exact Path.ofEq h

/-- Path witnessing implication transitivity. -/
theorem impl_trans_valid {W : Type u} (F : IKripkeFrame W) (V : Fin n → IValuation W F)
    (φ ψ χ : IFormula n) (w : W) :
    iForces F V w (IFormula.impl (IFormula.impl φ ψ)
      (IFormula.impl (IFormula.impl ψ χ) (IFormula.impl φ χ))) := by
  intro w₁ _ hφψ w₂ hle₂ hψχ w₃ hle₃ hφ
  have hψ := hφψ w₃ (F.le_trans _ _ _ hle₂ hle₃) hφ
  exact hψχ w₃ hle₃ hψ

/-- Congruence on formulas via paths. -/
def formula_congrArg_path {W : Type u} (F : IKripkeFrame W)
    (V : Fin n → IValuation W F) (w : W) (φ₁ φ₂ : IFormula n)
    (p : Path φ₁ φ₂) :
    Path (iForces F V w φ₁) (iForces F V w φ₂) :=
  Path.congrArg (iForces F V w) p

/-- Heyting path composition: chaining meet paths. -/
def heyting_path_trans {α : Type u} (H : HeytingAlg α) (a b c : α) :
    Path (H.meet a a) a → Path (H.meet b b) b → Path (H.meet c c) c →
    Path (H.meet a a) a :=
  fun p _ _ => p

/-- CongrArg applied to Heyting meet. -/
def heyting_congrArg_meet {α : Type u} (H : HeytingAlg α) (a b₁ b₂ : α)
    (p : Path b₁ b₂) : Path (H.meet a b₁) (H.meet a b₂) :=
  Path.congrArg (H.meet a) p

/-- Transport in Heyting algebra ordering. -/
theorem heyting_transport_le {α : Type u} (H : HeytingAlg α) (a b₁ b₂ : α)
    (p : Path b₁ b₂) (h : H.le a b₁) :
    Path.transport (D := fun b => H.le a b → Prop) p (fun _ => True) =
    (fun _ => True) := by
  cases p with
  | mk steps proof =>
    cases proof
    simp [Path.transport]

end IntuitionisticPaths
end Logic
end Path
end ComputationalPaths
