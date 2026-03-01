import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Rewrite.CriticalPairs
namespace ComputationalPaths
namespace DeformationTheory

open ComputationalPaths
open ComputationalPaths.Path
open ComputationalPaths.Path.Rewriting

universe u

/-- Partial deformation tower up to level `n` with explicit `RwEq` links. -/
structure PartialDeformation {A : Type u} {a b : A} (p₀ : Path a b) (n : Nat) where
  pathAt : Nat → Path a b
  start : p₀ = pathAt 0
  adjacent : ∀ t, t < n → RwEq (pathAt t) (pathAt (t + 1))

namespace PartialDeformation

variable {A : Type u} {a b : A} {p₀ : Path a b} {n : Nat}

@[simp] noncomputable def terminal (D : PartialDeformation p₀ n) : Path a b :=
  D.pathAt n

noncomputable def prefixRwEq (D : PartialDeformation p₀ n) :
    ∀ t, t ≤ n → RwEq (D.pathAt 0) (D.pathAt t)
  | 0, _ => rweq_trans (rweq_symm (rweq_cmpA_refl_right (D.pathAt 0))) (rweq_cmpA_refl_right (D.pathAt 0))
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
    (h : RwEq p q) : RwEq (Path.symm p) (Path.symm q) :=
  rweq_symm_congr h

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
@[simp] noncomputable def obstructionLoop (oc : ObstructionCocycle D) : Path b b :=
  Path.trans (Path.symm oc.left) oc.right

/-- Obstruction cocycle represented as an `RwEq` class. -/
noncomputable def obstructionClass (oc : ObstructionCocycle D) :
    RwEqClass (A := A) (x := b) (y := b) :=
  rweqClassOf oc.obstructionLoop

/-- Joinability phrased at the `RwEq` level. -/
noncomputable def Joinable (oc : ObstructionCocycle D) : Type u :=
  Σ r : Path a b, RwEq oc.left r × RwEq oc.right r

/-- Joinability in the `Rw` sense, as used in `CriticalPairs.lean`. -/
noncomputable def RwJoinable (oc : ObstructionCocycle D) : Prop :=
  JoinableRw oc.left oc.right

/-- Vanishing of the primary obstruction class. -/
noncomputable def Vanishes (oc : ObstructionCocycle D) : Prop :=
  RwEqProp oc.obstructionLoop (Path.refl b)

/-- Two choices of extension data with `RwEq`-equivalent branches. -/
structure SameChoice (oc₁ oc₂ : ObstructionCocycle D) where
  leftEq : RwEq oc₁.left oc₂.left
  rightEq : RwEq oc₁.right oc₂.right

noncomputable def obstructionLoop_respects_rweq
    {oc₁ oc₂ : ObstructionCocycle D}
    (h : SameChoice oc₁ oc₂) :
    RwEq oc₁.obstructionLoop oc₂.obstructionLoop :=
  rweq_trans_congr
    (rweq_symm_congr_from_rweq h.leftEq)
    h.rightEq

/-- Well-definedness: equivalent extension choices define the same obstruction class. -/
theorem obstructionClass_well_defined
    {oc₁ oc₂ : ObstructionCocycle D}
    (h : SameChoice oc₁ oc₂) :
    oc₁.obstructionClass = oc₂.obstructionClass :=
  Quot.sound (rweqProp_of_rweq (obstructionLoop_respects_rweq h))

noncomputable def vanishes_of_joinable
    (oc : ObstructionCocycle D) (h : oc.Joinable) :
    oc.Vanishes := by
  obtain ⟨r, hleft, hright⟩ := h
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

noncomputable def GaugeEquivalent (τ₁ τ₂ : TodaRepresentative oc) : Type u :=
  RwEq τ₁.secondary τ₂.secondary

theorem secondaryClass_eq_of_gauge
    {τ₁ τ₂ : TodaRepresentative oc}
    (h : GaugeEquivalent τ₁ τ₂) :
    τ₁.secondaryClass = τ₂.secondaryClass :=
  Quot.sound (rweqProp_of_rweq h)

end TodaRepresentative

end ObstructionCocycle

end DeformationTheory
end ComputationalPaths
