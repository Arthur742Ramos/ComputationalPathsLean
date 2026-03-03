/-
# Modal Logic via Computational Paths

This module models modal logic using computational paths:
Kripke frames as path graphs, accessibility as steps, modal operators
(□ and ◇) as path quantifiers, frame conditions as path properties,
and bisimulation as path equivalence.

## Key Results

| Definition/Theorem                    | Description                              |
|--------------------------------------|------------------------------------------|
| `KripkeFrame`                        | Kripke frame as accessibility structure  |
| `boxOp` / `diamondOp`               | Modal operators via paths                |
| `reflexive_frame_T`                  | T axiom from reflexive frames            |
| `transitive_frame_4`                 | Axiom 4 from transitive frames           |
| `symmetric_frame_B`                  | Axiom B from symmetric frames            |
| `bisimulation`                       | Bisimulation as path equivalence         |

## References

- Blackburn, de Rijke, Venema, "Modal Logic"
- Hughes & Cresswell, "A New Introduction to Modal Logic"
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace Logic
namespace ModalPaths

universe u

/-! ## Kripke Frames -/

/-- A Kripke frame: a set of worlds with an accessibility relation,
    modeled using computational paths. -/
structure KripkeFrame (W : Type u) where
  /-- Accessibility relation between worlds. -/
  acc : W → W → Prop
  /-- Decidable accessibility (for computation). -/
  decAcc : DecidableRel acc := by infer_instance

/-- A reflexive Kripke frame (every world accesses itself). -/
structure ReflexiveFrame (W : Type u) extends KripkeFrame W where
  refl : ∀ w : W, acc w w

/-- A transitive Kripke frame. -/
structure TransitiveFrame (W : Type u) extends KripkeFrame W where
  trans : ∀ w₁ w₂ w₃ : W, acc w₁ w₂ → acc w₂ w₃ → acc w₁ w₃

/-- A symmetric Kripke frame. -/
structure SymmetricFrame (W : Type u) extends KripkeFrame W where
  symm : ∀ w₁ w₂ : W, acc w₁ w₂ → acc w₂ w₁

/-- An equivalence frame (S5): reflexive, transitive, symmetric. -/
structure EquivalenceFrame (W : Type u) extends KripkeFrame W where
  refl : ∀ w : W, acc w w
  trans : ∀ w₁ w₂ w₃ : W, acc w₁ w₂ → acc w₂ w₃ → acc w₁ w₃
  symm : ∀ w₁ w₂ : W, acc w₁ w₂ → acc w₂ w₁

/-! ## Accessibility as Paths -/

/-- An accessibility path: a chain of accessible worlds. -/
inductive AccPath {W : Type u} (F : KripkeFrame W) : W → W → Type u where
  | single : F.acc w₁ w₂ → AccPath F w₁ w₂
  | refl : AccPath F w w
  | chain : AccPath F w₁ w₂ → AccPath F w₂ w₃ → AccPath F w₁ w₃

/-- Length of an accessibility path. -/
noncomputable def AccPath.length {W : Type u} {F : KripkeFrame W} {w₁ w₂ : W} :
    AccPath F w₁ w₂ → Nat
  | single _ => 1
  | refl => 0
  | chain p q => p.length + q.length

/-- Reverse an accessibility path (requires symmetry). -/
noncomputable def AccPath.reverse {W : Type u} {F : SymmetricFrame W} {w₁ w₂ : W} :
    AccPath F.toKripkeFrame w₁ w₂ → AccPath F.toKripkeFrame w₂ w₁
  | single h => single (F.symm _ _ h)
  | refl => refl
  | chain p q => chain (reverse q) (reverse p)

/-! ## Modal Operators as Path Quantifiers -/

/-- A valuation assigns truth values at worlds. -/
abbrev Valuation (W : Type u) := W → Prop

/-- Box operator: □φ holds at w iff φ holds at all accessible worlds. -/
noncomputable def boxOp {W : Type u} (F : KripkeFrame W) (φ : Valuation W) : Valuation W :=
  fun w => ∀ w' : W, F.acc w w' → φ w'

/-- Diamond operator: ◇φ holds at w iff φ holds at some accessible world. -/
noncomputable def diamondOp {W : Type u} (F : KripkeFrame W) (φ : Valuation W) : Valuation W :=
  fun w => ∃ w' : W, F.acc w w' ∧ φ w'

/-- Box-diamond duality: □φ ↔ ¬◇¬φ. -/
theorem box_diamond_dual {W : Type u} (F : KripkeFrame W) (φ : Valuation W)
    (w : W) :
    boxOp F φ w ↔ ¬ diamondOp F (fun w' => ¬ φ w') w := by
  constructor
  · intro hbox ⟨w', hacc, hneg⟩
    exact hneg (hbox w' hacc)
  · intro hndiam w' hacc
    exact Classical.byContradiction fun h => hndiam ⟨w', hacc, h⟩

/-- Diamond-box duality: ◇φ ↔ ¬□¬φ. -/
theorem diamond_box_dual {W : Type u} (F : KripkeFrame W) (φ : Valuation W)
    (w : W) :
    diamondOp F φ w ↔ ¬ boxOp F (fun w' => ¬ φ w') w := by
  constructor
  · intro ⟨w', hacc, hphi⟩ hbox
    exact hbox w' hacc hphi
  · intro hnbox
    exact Classical.byContradiction fun hndiam =>
      hnbox fun w' hacc hphi => hndiam ⟨w', hacc, hphi⟩

/-! ## Frame Conditions as Path Properties -/

/-- T axiom: □φ → φ (from reflexive frames). -/
theorem reflexive_frame_T {W : Type u} (F : ReflexiveFrame W)
    (φ : Valuation W) (w : W) :
    boxOp F.toKripkeFrame φ w → φ w := by
  intro hbox
  exact hbox w (F.refl w)

/-- Axiom 4: □φ → □□φ (from transitive frames). -/
theorem transitive_frame_4 {W : Type u} (F : TransitiveFrame W)
    (φ : Valuation W) (w : W) :
    boxOp F.toKripkeFrame φ w → boxOp F.toKripkeFrame (boxOp F.toKripkeFrame φ) w := by
  intro hbox w₁ h₁ w₂ h₂
  exact hbox w₂ (F.trans w w₁ w₂ h₁ h₂)

/-- Axiom B: φ → □◇φ (from symmetric frames). -/
theorem symmetric_frame_B {W : Type u} (F : SymmetricFrame W)
    (φ : Valuation W) (w : W) :
    φ w → boxOp F.toKripkeFrame (diamondOp F.toKripkeFrame φ) w := by
  intro hphi w' hacc
  exact ⟨w, F.symm w w' hacc, hphi⟩

/-- Axiom 5: ◇φ → □◇φ (from euclidean frames). -/
theorem euclidean_frame_5 {W : Type u} (F : EquivalenceFrame W)
    (φ : Valuation W) (w : W) :
    diamondOp F.toKripkeFrame φ w → boxOp F.toKripkeFrame (diamondOp F.toKripkeFrame φ) w := by
  intro ⟨w', hacc, hphi⟩ w'' hacc'
  exact ⟨w', F.trans w'' w w' (F.symm w w'' hacc') hacc, hphi⟩

/-- K axiom: □(φ → ψ) → □φ → □ψ (for all frames). -/
theorem K_axiom {W : Type u} (F : KripkeFrame W)
    (φ ψ : Valuation W) (w : W) :
    boxOp F (fun w' => φ w' → ψ w') w → boxOp F φ w → boxOp F ψ w := by
  intro himpl hphi w' hacc
  exact himpl w' hacc (hphi w' hacc)

/-- Necessitation: if φ is valid, then □φ is valid. -/
theorem necessitation {W : Type u} (F : KripkeFrame W)
    (φ : Valuation W) (hvalid : ∀ w, φ w) :
    ∀ w, boxOp F φ w := by
  intro w w' _
  exact hvalid w'

/-! ## Box is Monotone -/

/-- Box preserves implication. -/
theorem box_monotone {W : Type u} (F : KripkeFrame W) (φ ψ : Valuation W)
    (h : ∀ w, φ w → ψ w) (w : W) :
    boxOp F φ w → boxOp F ψ w := by
  intro hbox w' hacc
  exact h w' (hbox w' hacc)

/-- Diamond preserves implication. -/
theorem diamond_monotone {W : Type u} (F : KripkeFrame W) (φ ψ : Valuation W)
    (h : ∀ w, φ w → ψ w) (w : W) :
    diamondOp F φ w → diamondOp F ψ w := by
  intro ⟨w', hacc, hphi⟩
  exact ⟨w', hacc, h w' hphi⟩

/-! ## Bisimulation as Path Equivalence -/

/-- A bisimulation between two Kripke frames. -/
structure Bisimulation {W₁ W₂ : Type u}
    (F₁ : KripkeFrame W₁) (F₂ : KripkeFrame W₂) where
  /-- The bisimulation relation. -/
  rel : W₁ → W₂ → Prop
  /-- Forward condition (zig): if related and w₁ accesses w₁',
      then w₂ accesses some w₂' related to w₁'. -/
  zig : ∀ w₁ w₂ w₁', rel w₁ w₂ → F₁.acc w₁ w₁' →
    ∃ w₂', F₂.acc w₂ w₂' ∧ rel w₁' w₂'
  /-- Backward condition (zag): if related and w₂ accesses w₂',
      then w₁ accesses some w₁' related to w₂'. -/
  zag : ∀ w₁ w₂ w₂', rel w₁ w₂ → F₂.acc w₂ w₂' →
    ∃ w₁', F₁.acc w₁ w₁' ∧ rel w₁' w₂'

/-- Identity bisimulation. -/
noncomputable def idBisimulation {W : Type u} (F : KripkeFrame W) :
    Bisimulation F F where
  rel := fun w₁ w₂ => w₁ = w₂
  zig := by
    intro w₁ w₂ w₁' heq hacc
    subst heq
    exact ⟨w₁', hacc, rfl⟩
  zag := by
    intro w₁ w₂ w₂' heq hacc
    subst heq
    exact ⟨w₂', hacc, rfl⟩

/-- Bisimulation preserves box truth. -/
theorem bisimulation_preserves_box {W₁ W₂ : Type u}
    {F₁ : KripkeFrame W₁} {F₂ : KripkeFrame W₂}
    (B : Bisimulation F₁ F₂)
    (φ₁ : Valuation W₁) (φ₂ : Valuation W₂)
    (hphi : ∀ w₁ w₂, B.rel w₁ w₂ → (φ₁ w₁ ↔ φ₂ w₂))
    (w₁ : W₁) (w₂ : W₂) (hrel : B.rel w₁ w₂) :
    boxOp F₁ φ₁ w₁ ↔ boxOp F₂ φ₂ w₂ := by
  constructor
  · intro hbox w₂' hacc₂
    obtain ⟨w₁', hacc₁, hrel'⟩ := B.zag w₁ w₂ w₂' hrel hacc₂
    exact (hphi w₁' w₂' hrel').mp (hbox w₁' hacc₁)
  · intro hbox w₁' hacc₁
    obtain ⟨w₂', hacc₂, hrel'⟩ := B.zig w₁ w₂ w₁' hrel hacc₁
    exact (hphi w₁' w₂' hrel').mpr (hbox w₂' hacc₂)

/-- Bisimulation preserves diamond truth. -/
theorem bisimulation_preserves_diamond {W₁ W₂ : Type u}
    {F₁ : KripkeFrame W₁} {F₂ : KripkeFrame W₂}
    (B : Bisimulation F₁ F₂)
    (φ₁ : Valuation W₁) (φ₂ : Valuation W₂)
    (hphi : ∀ w₁ w₂, B.rel w₁ w₂ → (φ₁ w₁ ↔ φ₂ w₂))
    (w₁ : W₁) (w₂ : W₂) (hrel : B.rel w₁ w₂) :
    diamondOp F₁ φ₁ w₁ ↔ diamondOp F₂ φ₂ w₂ := by
  constructor
  · intro ⟨w₁', hacc₁, hphi₁⟩
    obtain ⟨w₂', hacc₂, hrel'⟩ := B.zig w₁ w₂ w₁' hrel hacc₁
    exact ⟨w₂', hacc₂, (hphi w₁' w₂' hrel').mp hphi₁⟩
  · intro ⟨w₂', hacc₂, hphi₂⟩
    obtain ⟨w₁', hacc₁, hrel'⟩ := B.zag w₁ w₂ w₂' hrel hacc₂
    exact ⟨w₁', hacc₁, (hphi w₁' w₂' hrel').mpr hphi₂⟩

/-! ## Path-based Frame Properties -/

/-- In a reflexive frame, accessibility paths include self-loops. -/
noncomputable def refl_frame_self_path {W : Type u} (F : ReflexiveFrame W) (w : W) :
    AccPath F.toKripkeFrame w w := AccPath.refl

/-- Accessibility paths compose. -/
noncomputable def acc_path_compose {W : Type u} (F : KripkeFrame W)
    (w₁ w₂ w₃ : W) (p : AccPath F w₁ w₂) (q : AccPath F w₂ w₃) :
    AccPath F w₁ w₃ := AccPath.chain p q

/-- In a transitive frame, single-step accessibility implies path existence. -/
noncomputable def trans_frame_path {W : Type u} (F : TransitiveFrame W)
    (w₁ w₂ : W) (h : F.toKripkeFrame.acc w₁ w₂) :
    AccPath F.toKripkeFrame w₁ w₂ := AccPath.single h

/-- CongrArg on valuations along paths. -/
theorem valuation_congrArg {W : Type u} (φ : Valuation W)
    (w₁ w₂ : W) (p : Path w₁ w₂) :
    Path.congrArg φ p = Path.congrArg φ p := rfl

/-- Transport of modal truth along world paths. -/
theorem transport_box {W : Type u} (F : KripkeFrame W)
    (φ : Valuation W) (w₁ w₂ : W) (p : Path w₁ w₂) :
    Path.transport (D := fun w => boxOp F φ w → boxOp F φ w) p id = id := by
  cases p with
  | mk steps proof =>
    cases proof
    simp

/-- Box of conjunction distributes. -/
theorem box_conj_distrib {W : Type u} (F : KripkeFrame W)
    (φ ψ : Valuation W) (w : W) :
    boxOp F (fun w' => φ w' ∧ ψ w') w ↔ (boxOp F φ w ∧ boxOp F ψ w) := by
  constructor
  · intro h
    exact ⟨fun w' hw => (h w' hw).1, fun w' hw => (h w' hw).2⟩
  · intro ⟨h₁, h₂⟩ w' hw
    exact ⟨h₁ w' hw, h₂ w' hw⟩

/-- Diamond of disjunction distributes. -/
theorem diamond_disj_distrib {W : Type u} (F : KripkeFrame W)
    (φ ψ : Valuation W) (w : W) :
    diamondOp F (fun w' => φ w' ∨ ψ w') w ↔
      (diamondOp F φ w ∨ diamondOp F ψ w) := by
  constructor
  · intro ⟨w', hacc, hor⟩
    cases hor with
    | inl h => exact Or.inl ⟨w', hacc, h⟩
    | inr h => exact Or.inr ⟨w', hacc, h⟩
  · intro hor
    cases hor with
    | inl h =>
      obtain ⟨w', hacc, hphi⟩ := h
      exact ⟨w', hacc, Or.inl hphi⟩
    | inr h =>
      obtain ⟨w', hacc, hpsi⟩ := h
      exact ⟨w', hacc, Or.inr hpsi⟩

end ModalPaths
end Logic
end Path
end ComputationalPaths
