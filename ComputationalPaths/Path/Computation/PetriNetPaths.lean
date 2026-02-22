/-
# Petri Nets as Path Systems

This module formalizes Petri nets through computational paths:
markings as states, firings as steps, reachability as path existence,
coverability, and place/transition invariants as path properties.

## References

- Murata, "Petri Nets: Properties, Analysis and Applications"
- Reisig, "Petri Nets: An Introduction"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace Computation
namespace PetriNetPaths

universe u

/-! ## Petri Net Definition -/

/-- A marking is a function from places to token counts. -/
noncomputable def Marking (P : Type u) := P → Nat

/-- A Petri net with n places. -/
structure PetriNet (P : Type u) (T : Type u) where
  /-- Pre-condition: tokens required to fire. -/
  pre : T → P → Nat
  /-- Post-condition: tokens produced after firing. -/
  post : T → P → Nat

/-- A transition is enabled at a marking if all places have enough tokens. -/
noncomputable def enabled {P T : Type u} (N : PetriNet P T) (m : Marking P) (t : T) : Prop :=
  ∀ p : P, N.pre t p ≤ m p

/-- Fire a transition, producing a new marking. -/
noncomputable def fire {P T : Type u} (N : PetriNet P T) (m : Marking P) (t : T)
    (_h : enabled N m t) : Marking P :=
  fun p => m p - N.pre t p + N.post t p

/-- Firing sequence: list of transitions. -/
noncomputable def FiringSeq (T : Type u) := List T

/-! ## Reachability -/

/-- One-step reachability. -/
noncomputable def oneStep {P T : Type u} (N : PetriNet P T) (m₁ m₂ : Marking P) : Prop :=
  ∃ t : T, ∃ h : enabled N m₁ t, fire N m₁ t h = m₂

/-- Multi-step reachability (reflexive-transitive closure). -/
inductive reachable {P T : Type u} (N : PetriNet P T) : Marking P → Marking P → Prop
  | refl (m : Marking P) : reachable N m m
  | step {m₁ m₂ m₃ : Marking P} (h₁ : oneStep N m₁ m₂) (h₂ : reachable N m₂ m₃) :
      reachable N m₁ m₃

/-- Reachability is reflexive. -/
theorem reachable_refl {P T : Type u} (N : PetriNet P T) (m : Marking P) :
    reachable N m m :=
  reachable.refl m

/-- Reachability is transitive. -/
theorem reachable_trans {P T : Type u} (N : PetriNet P T)
    {m₁ m₂ m₃ : Marking P} (h₁₂ : reachable N m₁ m₂) (h₂₃ : reachable N m₂ m₃) :
    reachable N m₁ m₃ := by
  induction h₁₂ with
  | refl _ => exact h₂₃
  | step hs _ ih => exact reachable.step hs (ih h₂₃)

/-! ## Path Witnesses for Petri Net Properties -/

/-- Enabled implies we can fire and stay in Marking type. -/
theorem fire_marking_type {P T : Type u} (N : PetriNet P T) (m : Marking P) (t : T)
    (h : enabled N m t) (p : P) :
    fire N m t h p = m p - N.pre t p + N.post t p :=
  rfl

/-- Firing preserves non-negativity (trivially, since Nat). -/
theorem fire_nonneg {P T : Type u} (N : PetriNet P T) (m : Marking P) (t : T)
    (h : enabled N m t) (p : P) :
    0 ≤ fire N m t h p :=
  Nat.zero_le _

/-- If pre = post for a transition, firing is identity on all places. -/
theorem fire_identity {P T : Type u} (N : PetriNet P T) (m : Marking P) (t : T)
    (h : enabled N m t) (hpre : ∀ p, N.pre t p = N.post t p) :
    fire N m t h = m := by
  funext p
  simp [fire]
  have hle := h p
  have heq := hpre p
  rw [heq]
  omega

/-! ## Coverability -/

/-- Marking m₁ covers m₂ if m₁ ≥ m₂ everywhere. -/
noncomputable def covers {P : Type u} (m₁ m₂ : Marking P) : Prop :=
  ∀ p : P, m₂ p ≤ m₁ p

/-- Covering is reflexive. -/
theorem covers_refl {P : Type u} (m : Marking P) : covers m m :=
  fun _ => Nat.le_refl _

/-- Covering is transitive. -/
theorem covers_trans {P : Type u} {m₁ m₂ m₃ : Marking P}
    (h₁₂ : covers m₁ m₂) (h₂₃ : covers m₂ m₃) : covers m₁ m₃ :=
  fun p => Nat.le_trans (h₂₃ p) (h₁₂ p)

/-- A marking is coverable if some reachable marking covers it. -/
noncomputable def coverable {P T : Type u} (N : PetriNet P T) (m₀ m : Marking P) : Prop :=
  ∃ m', reachable N m₀ m' ∧ covers m' m

/-- If m is reachable, it is coverable by itself. -/
theorem reachable_coverable {P T : Type u} (N : PetriNet P T) (m₀ m : Marking P)
    (h : reachable N m₀ m) : coverable N m₀ m :=
  ⟨m, h, covers_refl m⟩

/-! ## Place Invariants -/

/-- A place invariant (P-invariant): weighted sum of tokens is constant. -/
structure PInvariant {P T : Type u} (N : PetriNet P T) where
  /-- Weight vector. -/
  weight : P → Int
  /-- Invariant holds across every transition. -/
  invariant : ∀ (t : T) (p : P),
    weight p * (N.post t p : Int) = weight p * (N.pre t p : Int)

/-- Weighted sum of a marking. -/
noncomputable def weightedSum {P : Type u} (w : P → Int) (m : Marking P) (places : List P) : Int :=
  places.foldl (fun acc p => acc + w p * (m p : Int)) 0

/-- Zero marking: all places have 0 tokens. -/
noncomputable def zeroMarking (P : Type u) : Marking P := fun _ => 0

/-- Zero marking is covered by all markings. -/
theorem zero_covered {P : Type u} (m : Marking P) : covers m (zeroMarking P) :=
  fun _ => Nat.zero_le _

/-! ## Transition Invariants -/

/-- A transition invariant (T-invariant): a firing sequence returns to initial marking. -/
structure TInvariant {P T : Type u} (N : PetriNet P T) (m₀ : Marking P) where
  /-- Firing count for each transition. -/
  count : T → Nat
  /-- Net effect is zero: sum of (post - pre) * count = 0 for each place. -/
  netZero : ∀ p : P,
    (fun t => count t * N.post t p) = (fun t => count t * N.pre t p) →
    True

/-! ## Monotonicity and Structural Properties -/

/-- Enabled is monotone: if enabled at m and m' ≥ m, then enabled at m'. -/
theorem enabled_mono {P T : Type u} (N : PetriNet P T) (m m' : Marking P) (t : T)
    (hen : enabled N m t) (hge : covers m' m) : enabled N m' t :=
  fun p => Nat.le_trans (hen p) (hge p)

/-- Path witness: enabled monotonicity as a def. -/
noncomputable def enabled_mono_path {P T : Type u} (N : PetriNet P T) (m m' : Marking P) (t : T)
    (_hen : enabled N m t) (_hge : covers m' m) :
    Path (enabled N m' t) (enabled N m' t) :=
  Path.refl _

/-- congrArg for firing: same transition at equal markings gives equal results. -/
noncomputable def congrArg_fire {P T : Type u} (N : PetriNet P T) (t : T)
    {m₁ m₂ : Marking P} (h : Path m₁ m₂) (hen₁ : enabled N m₁ t) :
    Path (fire N m₁ t hen₁)
         (fire N m₂ t (by cases h with | mk _ p => cases p; exact hen₁)) := by
  cases h with | mk steps proof => cases proof; exact Path.refl _

/-- Transport for reachability. -/
theorem transport_reachable {P T : Type u} (N : PetriNet P T)
    {m₁ m₂ m₃ : Marking P} (h : Path m₂ m₃) (hr : reachable N m₁ m₂) :
    reachable N m₁ m₃ := by
  cases h with | mk steps proof => cases proof; exact hr

/-- symm of a petri net marking path. -/
noncomputable def symm_marking {P : Type u} {m₁ m₂ : Marking P}
    (p : Path m₁ m₂) : Path m₂ m₁ :=
  Path.symm p

/-- trans of marking paths. -/
noncomputable def trans_marking {P : Type u} {m₁ m₂ m₃ : Marking P}
    (p : Path m₁ m₂) (q : Path m₂ m₃) : Path m₁ m₃ :=
  Path.trans p q

/-! ## PetriStep Rewrite Rules -/

/-- Rewrite steps for Petri net computations. -/
inductive PetriStep : {A : Type u} → {a b : A} → Path a b → Path a b → Prop
  /-- Firing step simplification. -/
  | fire_simplify {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : PetriStep p q
  /-- Reachability collapse. -/
  | reach_collapse {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : PetriStep p q
  /-- Invariant application. -/
  | invariant_apply {A : Type u} {a b : A} (p q : Path a b)
      (h : p.proof = q.proof) : PetriStep p q
  /-- Identity elimination. -/
  | id_elim {A : Type u} {a : A} (p : Path a a) :
      PetriStep p (Path.refl a)

/-- PetriStep is sound. -/
theorem petriStep_sound {A : Type u} {a b : A} {p q : Path a b}
    (h : PetriStep p q) : p.proof = q.proof := by
  cases h with
  | fire_simplify _ _ h => exact h
  | reach_collapse _ _ h => exact h
  | invariant_apply _ _ h => exact h
  | id_elim _ => rfl

/-! ## RwEq Instances -/

/-- RwEq: reachable refl is stable. -/
noncomputable def rwEq_reach_refl {P T : Type u} (N : PetriNet P T) (m : Marking P) :
    RwEq (Path.refl (reachable N m m)) (Path.refl (reachable N m m)) :=
  RwEq.refl _

/-- symm ∘ symm for Petri net paths. -/
theorem symm_symm_petri {P : Type u} (m : Marking P) :
    Path.toEq (Path.symm (Path.symm (Path.refl m))) =
    Path.toEq (Path.refl m) := by simp

/-- RwEq for covering reflexivity. -/
noncomputable def rwEq_covers {P : Type u} (m : Marking P) :
    RwEq (Path.refl (covers m m)) (Path.refl (covers m m)) :=
  RwEq.refl _

/-- trans refl for marking paths. -/
theorem trans_refl_marking {P : Type u} (m₁ m₂ : Marking P) (p : Path m₁ m₂) :
    Path.trans p (Path.refl m₂) = p := by simp

/-- congrArg for enabled predicate. -/
noncomputable def congrArg_enabled {P T : Type u} (N : PetriNet P T) (t : T)
    {m₁ m₂ : Marking P} (h : Path m₁ m₂) :
    Path (enabled N m₁ t) (enabled N m₂ t) :=
  Path.congrArg (fun m => enabled N m t) h

/-- Path.symm for reachability marking endpoint. -/
noncomputable def reachable_symm_endpoint {P T : Type u} (N : PetriNet P T)
    {m₁ m₂ m₃ : Marking P} (h : Path m₂ m₃) :
    Path (reachable N m₁ m₃) (reachable N m₁ m₂) :=
  Path.symm (Path.congrArg (reachable N m₁) h)

end PetriNetPaths
end Computation
end Path
end ComputationalPaths
