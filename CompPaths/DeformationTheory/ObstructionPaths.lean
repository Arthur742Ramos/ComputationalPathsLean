import CompPaths.Core
import CompPaths.Rewriting.CriticalPairs

namespace CompPaths
namespace DeformationTheory

open ComputationalPaths
open ComputationalPaths.Path
open CompPaths.Rewriting

universe u

/-- Partial deformation tower up to level `n` with explicit `RwEq` links. -/
structure PartialDeformation {A : Type u} {a b : A} (p₀ : Path a b) (n : Nat) where
  pathAt : Nat → Path a b
  start : p₀ = pathAt 0
  adjacent : ∀ t, t < n → RwEq (pathAt t) (pathAt (t + 1))

namespace PartialDeformation

variable {A : Type u} {a b : A} {p₀ : Path a b} {n : Nat}

@[simp] def terminal (D : PartialDeformation p₀ n) : Path a b :=
  D.pathAt n

noncomputable def prefixRwEq (D : PartialDeformation p₀ n) :
    ∀ t, t ≤ n → RwEq (D.pathAt 0) (D.pathAt t)
  | 0, _ => rweq_refl (D.pathAt 0)
  | Nat.succ t, h =>
      have ht : t < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self t) h
      have hprev : RwEq (D.pathAt 0) (D.pathAt t) := prefixRwEq D t (Nat.le_of_lt ht)
      rweq_trans hprev (D.adjacent t ht)

noncomputable def totalRwEq (D : PartialDeformation p₀ n) :
    RwEq p₀ D.terminal :=
  rweq_trans (rweq_of_eq D.start) (D.prefixRwEq n (Nat.le_refl n))

end PartialDeformation

/-- Quotient of paths by rewrite equivalence. -/
abbrev RwEqClass {A : Type u} {x y : A} : Type u :=
  Quot (fun p q : Path x y => RwEqProp p q)

noncomputable def rweqClassOf {A : Type u} {x y : A}
    (p : Path x y) : RwEqClass (A := A) (x := x) (y := y) :=
  Quot.mk _ p

noncomputable def rweq_symm_congr_from_rweq
    {A : Type u} {a b : A} {p q : Path a b}
    (h : RwEq p q) : RwEq (Path.symm p) (Path.symm q) := by
  induction h with
  | refl p =>
      exact rweq_refl (Path.symm p)
  | step hs =>
      exact rweq_of_step (ComputationalPaths.Path.Step.symm_congr hs)
  | symm _ ih =>
      exact rweq_symm ih
  | trans _ _ ih₁ ih₂ =>
      exact rweq_trans ih₁ ih₂

noncomputable def rweq_of_rw
    {A : Type u} {a b : A} {p q : Path a b}
    (h : Rw p q) : RwEq p q := by
  induction h with
  | refl p =>
      exact rweq_refl p
  | tail h step ih =>
      exact rweq_trans ih (rweq_of_step step)

/-- Obstruction cocycle at level `n`: two competing one-step extensions
from the terminal path of a partial deformation. -/
structure ObstructionCocycle
    {A : Type u} {a b : A} {p₀ : Path a b} {n : Nat}
    (D : PartialDeformation p₀ n) where
  caseTag : CriticalPairCase
  left : Path a b
  right : Path a b
  leftStep : ComputationalPaths.Path.Step D.terminal left
  rightStep : ComputationalPaths.Path.Step D.terminal right

namespace ObstructionCocycle

variable {A : Type u} {a b : A} {p₀ : Path a b} {n : Nat}
variable {D : PartialDeformation p₀ n}

/-- Primary obstruction loop at the target endpoint. -/
@[simp] def obstructionLoop (oc : ObstructionCocycle D) : Path b b :=
  Path.trans (Path.symm oc.left) oc.right

/-- Obstruction cocycle represented as an `RwEq` class. -/
noncomputable def obstructionClass (oc : ObstructionCocycle D) :
    RwEqClass (A := A) (x := b) (y := b) :=
  rweqClassOf oc.obstructionLoop

/-- Joinability phrased at the `RwEq` level. -/
def Joinable (oc : ObstructionCocycle D) : Prop :=
  ∃ r : Path a b, RwEq oc.left r ∧ RwEq oc.right r

/-- Joinability in the `Rw` sense, as used in `CriticalPairs.lean`. -/
def RwJoinable (oc : ObstructionCocycle D) : Prop :=
  JoinableRw oc.left oc.right

/-- Vanishing of the primary obstruction class. -/
def Vanishes (oc : ObstructionCocycle D) : Prop :=
  RwEqProp oc.obstructionLoop (Path.refl b)

/-- Two choices of extension data with `RwEq`-equivalent branches. -/
structure SameChoice (oc₁ oc₂ : ObstructionCocycle D) where
  leftEq : RwEq oc₁.left oc₂.left
  rightEq : RwEq oc₁.right oc₂.right

theorem obstructionLoop_respects_rweq
    {oc₁ oc₂ : ObstructionCocycle D}
    (h : SameChoice oc₁ oc₂) :
    RwEq oc₁.obstructionLoop oc₂.obstructionLoop := by
  exact rweq_trans_congr
    (rweq_symm_congr_from_rweq h.leftEq)
    h.rightEq

/-- Well-definedness: equivalent extension choices define the same obstruction class. -/
theorem obstructionClass_well_defined
    {oc₁ oc₂ : ObstructionCocycle D}
    (h : SameChoice oc₁ oc₂) :
    oc₁.obstructionClass = oc₂.obstructionClass := by
  exact Quot.sound (rweqProp_of_rweq (obstructionLoop_respects_rweq h))

theorem joinable_of_rwJoinable
    (oc : ObstructionCocycle D) (h : oc.RwJoinable) :
    oc.Joinable := by
  rcases h with ⟨r, hl, hr⟩
  exact ⟨r, rweq_of_rw hl, rweq_of_rw hr⟩

theorem vanishes_of_joinable
    (oc : ObstructionCocycle D) (h : oc.Joinable) :
    oc.Vanishes := by
  rcases h with ⟨r, hleft, hright⟩
  have hright_left : RwEq oc.right oc.left :=
    rweq_trans hright (rweq_symm hleft)
  have h₁ :
      RwEq
        (Path.trans (Path.symm oc.left) oc.right)
        (Path.trans (Path.symm oc.left) oc.left) :=
    rweq_trans_congr_right (Path.symm oc.left) hright_left
  have h₂ :
      RwEq (Path.trans (Path.symm oc.left) oc.left) (Path.refl b) :=
    rweq_cmpA_inv_left oc.left
  exact rweqProp_of_rweq (rweq_trans h₁ h₂)

theorem joinable_of_vanishes
    (oc : ObstructionCocycle D) (h : oc.Vanishes) :
    oc.Joinable := by
  rcases h with ⟨hloop⟩
  have hcongr :
      RwEq
        (Path.trans oc.left oc.obstructionLoop)
        (Path.trans oc.left (Path.refl b)) :=
    rweq_trans_congr_left oc.left hloop
  have hToLeft :
      RwEq (Path.trans oc.left oc.obstructionLoop) oc.left :=
    rweq_trans hcongr (rweq_cmpA_refl_right oc.left)
  have hToRight :
      RwEq (Path.trans oc.left oc.obstructionLoop) oc.right := by
    simpa [obstructionLoop] using
      (rweq_of_step (ComputationalPaths.Path.Step.trans_cancel_left oc.left oc.right))
  have hright_left : RwEq oc.right oc.left :=
    rweq_trans (rweq_symm hToRight) hToLeft
  exact ⟨oc.left, rweq_refl oc.left, hright_left⟩

/-- Vanishing criterion: the primary obstruction vanishes exactly when the
critical pair at that level is joinable. -/
theorem vanishing_iff_joinable (oc : ObstructionCocycle D) :
    oc.Vanishes ↔ oc.Joinable := by
  constructor
  · intro h
    exact joinable_of_vanishes oc h
  · intro h
    exact vanishes_of_joinable oc h

theorem vanishing_of_criticalPairJoinable
    (oc : ObstructionCocycle D) (h : oc.RwJoinable) :
    oc.Vanishes :=
  vanishes_of_joinable oc (joinable_of_rwJoinable oc h)

/-- Secondary (Toda) representative, defined only after primary vanishing. -/
structure TodaRepresentative (oc : ObstructionCocycle D) where
  primaryVanishes : oc.Vanishes
  mediator : Path a b
  leftJoin : RwEq oc.left mediator
  rightJoin : RwEq oc.right mediator
  secondary : Path b b

namespace TodaRepresentative

variable {oc : ObstructionCocycle D}

noncomputable def secondaryClass (τ : TodaRepresentative oc) :
    RwEqClass (A := A) (x := b) (y := b) :=
  rweqClassOf τ.secondary

def GaugeEquivalent (τ₁ τ₂ : TodaRepresentative oc) : Prop :=
  RwEq τ₁.secondary τ₂.secondary

theorem secondaryClass_eq_of_gauge
    {τ₁ τ₂ : TodaRepresentative oc}
    (h : GaugeEquivalent τ₁ τ₂) :
    τ₁.secondaryClass = τ₂.secondaryClass := by
  exact Quot.sound (rweqProp_of_rweq h)

/-- Toda bracket as a right coset in the space of `RwEq` classes. -/
def todaCoset (τ : TodaRepresentative oc) :
    Set (RwEqClass (A := A) (x := b) (y := b)) :=
  fun cls => ∃ γ : Path b b, cls = rweqClassOf (Path.trans τ.secondary γ)

abbrev TodaBracket (oc : ObstructionCocycle D) :=
  Set (RwEqClass (A := A) (x := b) (y := b))

noncomputable def todaBracket (τ : TodaRepresentative oc) : TodaBracket oc :=
  τ.todaCoset

theorem baseClass_mem_todaBracket (τ : TodaRepresentative oc) :
    τ.secondaryClass ∈ τ.todaBracket := by
  refine ⟨Path.refl b, ?_⟩
  exact Quot.sound (rweqProp_of_rweq (rweq_symm (rweq_cmpA_refl_right τ.secondary)))

theorem todaBracket_eq_of_gauge
    {τ₁ τ₂ : TodaRepresentative oc}
    (h : GaugeEquivalent τ₁ τ₂) :
    τ₁.todaBracket = τ₂.todaBracket := by
  funext cls
  apply propext
  constructor
  · intro hmem
    rcases hmem with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    calc
      cls = rweqClassOf (Path.trans τ₁.secondary γ) := hγ
      _ = rweqClassOf (Path.trans τ₂.secondary γ) := by
        exact Quot.sound (rweqProp_of_rweq (rweq_trans_congr_left γ h))
  · intro hmem
    rcases hmem with ⟨γ, hγ⟩
    refine ⟨γ, ?_⟩
    calc
      cls = rweqClassOf (Path.trans τ₂.secondary γ) := hγ
      _ = rweqClassOf (Path.trans τ₁.secondary γ) := by
        exact Quot.sound (rweqProp_of_rweq
          (rweq_trans_congr_left γ (rweq_symm h)))

end TodaRepresentative

end ObstructionCocycle

end DeformationTheory
end CompPaths
