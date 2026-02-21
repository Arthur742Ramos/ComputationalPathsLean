/-
# Postnikov Tower via Computational Paths

This module develops the Postnikov tower for computational paths:

1. **n-truncation via quotient** – `τ n A a` identifies loops by `RwEq`-level
   truncation; at level 0 everything collapses, at level ≥ 1 we quotient by
   `RwEqProp`.
2. **Postnikov tower** – a sequence of stages `τ n A a` connected by bonding
   maps `τ (n+1) A a → τ n A a`.
3. **τ₁ recovers π₁** – `τ 1 A a ≃ π₁(A,a)` by `SimpleEquiv`, since both
   are `LoopQuot A a`.
4. **k-invariants** – `RwEq`-invariant loop data descends to coherent maps on
   truncation stages.

All proofs use `Path`/`Step`/`RwEq`. No `sorry`/`admit`.
-/

import CompPaths.Core
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.Quot
import ComputationalPaths.Path.Rewrite.SimpleEquiv

namespace CompPaths.Homotopy.PostnikovTower

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Section 1 – n-truncation via quotient -/

/-- Based loops as computational paths. -/
abbrev Loop (A : Type u) (a : A) : Type u :=
  Path a a

/-- Quotient relation for the `n`-truncation of based loops.
    At level 0 everything is identified; at level ≥ 1 we use `RwEqProp`. -/
def truncRel (A : Type u) (a : A) : Nat → Loop A a → Loop A a → Prop
  | 0, _, _ => True
  | _ + 1, p, q => RwEqProp p q

/-- `truncRel n` is an equivalence relation for every `n`. -/
noncomputable def truncSetoid (A : Type u) (a : A) (n : Nat) :
    Setoid (Loop A a) where
  r := truncRel A a n
  iseqv := by
    constructor
    · intro p
      cases n with
      | zero => trivial
      | succ n => exact ⟨rweq_refl p⟩
    · intro p q hpq
      cases n with
      | zero => trivial
      | succ n =>
        obtain ⟨h⟩ := hpq
        exact ⟨rweq_symm h⟩
    · intro p q r hpq hqr
      cases n with
      | zero => trivial
      | succ n =>
        obtain ⟨h₁⟩ := hpq
        obtain ⟨h₂⟩ := hqr
        exact ⟨rweq_trans h₁ h₂⟩

/-- `τ n A a` – the `n`-truncation of loops at `a` via quotient. -/
abbrev τ (n : Nat) (A : Type u) (a : A) : Type u :=
  Quot (truncSetoid A a n).r

/-- Class of a loop in the `n`-truncation quotient. -/
def truncClass (n : Nat) {A : Type u} {a : A} (p : Loop A a) : τ n A a :=
  Quot.mk _ p

/-- At positive levels, `RwEq`-related loops have equal classes. -/
theorem truncClass_sound {A : Type u} {a : A} {n : Nat} {p q : Loop A a}
    (h : RwEq p q) :
    truncClass (n + 1) p = truncClass (n + 1) q :=
  Quot.sound (⟨h⟩ : RwEqProp p q)

/-- In every positive stage, `p · refl` and `p` define the same class
    (witnessed by `Step.trans_refl_right`). -/
theorem truncClass_right_unit {A : Type u} {a : A}
    (n : Nat) (p : Loop A a) :
    truncClass (n + 1) (Path.trans p (Path.refl a)) = truncClass (n + 1) p :=
  truncClass_sound (rweq_of_step (Step.trans_refl_right p))

/-- Symmetrically, `refl · p = p` in every positive stage. -/
theorem truncClass_left_unit {A : Type u} {a : A}
    (n : Nat) (p : Loop A a) :
    truncClass (n + 1) (Path.trans (Path.refl a) p) = truncClass (n + 1) p :=
  truncClass_sound (rweq_of_step (Step.trans_refl_left p))

/-! ## Section 2 – Postnikov tower -/

/-- Bonding map `τ (n+1) A a → τ n A a` for the Postnikov tower.
    At every level the canonical quotient map coarsens the relation. -/
noncomputable def postnikovProjection (A : Type u) (a : A) :
    (n : Nat) → τ (n + 1) A a → τ n A a
  | 0 =>
      Quot.lift (fun p => truncClass 0 p) (by
        intro _ _ _
        exact Quot.sound trivial)
  | n + 1 =>
      Quot.lift (fun p => truncClass (n + 1) p) (by
        intro _ _ hpq
        exact Quot.sound hpq)

/-- The Postnikov tower bundled as stages with bonding maps. -/
structure PostnikovTower (A : Type u) (a : A) where
  /-- Stage `n` of the tower. -/
  stage : Nat → Type u
  /-- Projection from stage `n + 1` to stage `n`. -/
  proj : (n : Nat) → stage (n + 1) → stage n

/-- Canonical Postnikov tower from quotient truncations. -/
noncomputable def postnikovTower (A : Type u) (a : A) : PostnikovTower A a where
  stage := fun n => τ n A a
  proj := postnikovProjection A a

/-- Projections transport the right-unit rewrite. -/
theorem projection_right_unit {A : Type u} {a : A}
    (n : Nat) (p : Loop A a) :
    postnikovProjection A a (n + 1)
        (truncClass (n + 2) (Path.trans p (Path.refl a))) =
      postnikovProjection A a (n + 1)
        (truncClass (n + 2) p) := by
  simp only [postnikovProjection]
  exact truncClass_right_unit (n + 1) p

/-! ## Section 3 – τ₁(A) recovers π₁ -/

/-- First truncation stage. -/
abbrev τ₁ (A : Type u) (a : A) : Type u := τ 1 A a

/-- Map from `τ₁(A,a)` to the fundamental group `π₁(A,a)`.
    Both are `Quot (RwEqProp · ·)`, so the map lifts the identity on loops. -/
noncomputable def tau1ToPiOne (A : Type u) (a : A) :
    τ₁ A a → PiOne A a :=
  Quot.lift (fun p => (Quot.mk _ p : PiOne A a)) (by
    intro _ _ hpq
    exact Quot.sound hpq)

/-- Map from `π₁(A,a)` to `τ₁(A,a)`. -/
noncomputable def piOneToTau1 (A : Type u) (a : A) :
    PiOne A a → τ₁ A a :=
  Quot.lift (fun p => (Quot.mk _ p : τ₁ A a)) (by
    intro _ _ hpq
    exact Quot.sound hpq)

/-- Left inverse witness. -/
theorem tau1_pi1_left_inv {A : Type u} (a : A) (x : τ₁ A a) :
    piOneToTau1 A a (tau1ToPiOne A a x) = x := by
  exact Quot.inductionOn x (fun _ => rfl)

/-- Right inverse witness. -/
theorem tau1_pi1_right_inv {A : Type u} (a : A) (x : PiOne A a) :
    tau1ToPiOne A a (piOneToTau1 A a x) = x := by
  exact Quot.inductionOn x (fun _ => rfl)

/-- `τ₁(A,a) ≃ π₁(A,a)` as a `SimpleEquiv`. -/
noncomputable def tau1RecoversPiOne (A : Type u) (a : A) :
    SimpleEquiv (τ₁ A a) (PiOne A a) where
  toFun := tau1ToPiOne A a
  invFun := piOneToTau1 A a
  left_inv := fun x => tau1_pi1_left_inv a x
  right_inv := fun x => tau1_pi1_right_inv a x

/-- Stage 1 of the canonical Postnikov tower is `π₁`. -/
noncomputable def postnikovStageOneEquivPiOne (A : Type u) (a : A) :
    SimpleEquiv ((postnikovTower A a).stage 1) (PiOne A a) :=
  tau1RecoversPiOne A a

/-! ## Section 4 – k-invariants -/

/-- Data for a k-invariant: an `RwEq`-invariant function on loops. -/
structure KInvariantData (A : Type u) (a : A) (n : Nat) where
  /-- Coefficient type. -/
  coeff : Type u
  /-- The raw map on loops. -/
  onLoop : Loop A a → coeff
  /-- `onLoop` respects rewrite equality. -/
  respects_rweq : ∀ {p q : Loop A a}, RwEq p q → onLoop p = onLoop q

/-- A k-invariant on stage `n+1`: a map from the quotient together with
    right-unit coherence expressed as a `Path`. -/
structure KInvariant (A : Type u) (a : A) (n : Nat) where
  /-- Coefficient type. -/
  coeff : Type u
  /-- The descended map on the quotient stage. -/
  classMap : τ (n + 1) A a → coeff
  /-- Right-unit coherence: `classMap [p · refl] = classMap [p]`. -/
  rightUnitCompat :
    ∀ p : Loop A a,
      Path
        (classMap (truncClass (n + 1) (Path.trans p (Path.refl a))))
        (classMap (truncClass (n + 1) p))

/-- Any `RwEq`-invariant loop recipe descends to a k-invariant on `τ_{n+1}`. -/
noncomputable def KInvariantData.toKInvariant {A : Type u} {a : A} {n : Nat}
    (K : KInvariantData A a n) : KInvariant A a n where
  coeff := K.coeff
  classMap := Quot.lift K.onLoop (by
    intro p q hpq
    exact K.respects_rweq (Classical.choice hpq))
  rightUnitCompat := by
    intro p
    exact Path.stepChain (K.respects_rweq (rweq_of_step (Step.trans_refl_right p)))

/-- Canonical k-invariant data: the identity quotient map on stage `n+1`. -/
noncomputable def canonicalKInvariantData (A : Type u) (a : A) (n : Nat) :
    KInvariantData A a n where
  coeff := τ (n + 1) A a
  onLoop := fun p => truncClass (n + 1) p
  respects_rweq := by
    intro p q hpq
    exact Quot.sound (⟨hpq⟩ : RwEqProp p q)

/-- Canonical k-invariant on stage `n+1`. -/
noncomputable def canonicalKInvariant (A : Type u) (a : A) (n : Nat) :
    KInvariant A a n :=
  (canonicalKInvariantData A a n).toKInvariant

/-- The bonding map itself is a k-invariant (the projection from `n+2` to `n+1`). -/
noncomputable def bondingKInvariant (A : Type u) (a : A) (n : Nat) :
    KInvariant A a (n + 1) where
  coeff := τ (n + 1) A a
  classMap := postnikovProjection A a (n + 1)
  rightUnitCompat := by
    intro p
    exact Path.stepChain (projection_right_unit (n + 1) p)

end CompPaths.Homotopy.PostnikovTower
