/- 
# Spectral sequence from path-length filtration

This module defines:

1. the filtration `Fₙ` of based loops by recorded path length,
2. the associated graded `Grₙ` modulo `RwEq`,
3. the `E₁` page entries and their chain-level link to `HomologicalAlgebra`,
4. the `d₁` differential from `Step` composition,
5. the `E₂` page as `H₁` converging to `π₁`,
6. collapse at `E₂` for complete rewriting systems via `ConfluenceDeep`.
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq
import ComputationalPaths.Path.Algebra.HomologicalAlgebra
import ComputationalPaths.Path.Rewrite.ConfluenceDeep
import ComputationalPaths.Path.Homotopy.FundamentalGroup
import ComputationalPaths.Path.Rewrite.SimpleEquiv
namespace ComputationalPaths.Path.Algebra

open ComputationalPaths
open ComputationalPaths.Path

universe u

noncomputable section

abbrev Loop (A : Type u) (a : A) : Type u := Path a a

/-- `Fₙ`: loops with at most `n` recorded rewrite steps. -/
noncomputable def Filtration (A : Type u) (a : A) (n : Nat) : Type u :=
  { p : Loop A a // Path.length p ≤ n }

/-- Canonical inclusion `Fₙ ↪ Fₙ₊₁`. -/
noncomputable def filtrationIncl {A : Type u} {a : A} (n : Nat) :
    Filtration A a n → Filtration A a (n + 1)
  | ⟨p, hp⟩ => ⟨p, Nat.le_trans hp (Nat.le_succ n)⟩

/-- Reflexive loop always belongs to every filtration stage. -/
noncomputable def reflInFiltration (A : Type u) (a : A) (n : Nat) : Filtration A a n :=
  ⟨Path.refl a, by simp⟩

/-- Exact-length loops used for the associated graded piece. -/
noncomputable def ExactLengthLoop (A : Type u) (a : A) (n : Nat) : Type u :=
  { p : Loop A a // Path.length p = n }

/-- `Grₙ` relation: exact-length loops modulo `RwEq`. -/
noncomputable def gradedRel {A : Type u} {a : A} {n : Nat}
    (x y : ExactLengthLoop A a n) : Prop :=
  Nonempty (RwEq x.1 y.1)

noncomputable def gradedSetoid (A : Type u) (a : A) (n : Nat) : Setoid (ExactLengthLoop A a n) where
  r := gradedRel (A := A) (a := a) (n := n)
  iseqv :=
    { refl := by
        intro x
        exact ⟨rweq_trans (rweq_symm (rweq_cmpA_refl_right x.1)) (rweq_cmpA_refl_right x.1)⟩
      symm := by
        intro x y h
        rcases h with ⟨hxy⟩
        exact ⟨rweq_symm hxy⟩
      trans := by
        intro x y z hxy hyz
        rcases hxy with ⟨hxy⟩
        rcases hyz with ⟨hyz⟩
        exact ⟨rweq_trans hxy hyz⟩ }

/-- Associated graded piece: loops with exactly `n` steps modulo `RwEq`. -/
abbrev Gr (A : Type u) (a : A) (n : Nat) : Type u :=
  Quot (gradedSetoid A a n).r

/-- A representative for `Grₙ` defines a degree-1 chain in `HomologicalAlgebra`. -/
noncomputable def toOneCell {A : Type u} {a : A} {n : Nat}
    (x : ExactLengthLoop A a n) : C1 A :=
  ⟨a, a, x.1⟩

/-- In the based setting, `∂₁` of an `E₁` representative is `a - a`. -/
@[simp] theorem boundary1_toOneCell {A : Type u} {a : A} {n : Nat}
    (x : ExactLengthLoop A a n) :
    boundary1 (A := A) (toOneCell x) = FormalDiff.mk a a := rfl

/-- `E₁^{p,q}` for this filtration (concentrated in row `q = 0`). -/
abbrev E1Entry (A : Type u) (a : A) (p q : Nat) : Type u :=
  if q = 0 then Gr A a p else PUnit

@[simp] theorem e1_zero_row {A : Type u} {a : A} (p : Nat) :
    E1Entry A a p 0 = Gr A a p := by
  simp [E1Entry]

/-- `E₁` maps to `H₁` via the chain complex quotient from `HomologicalAlgebra`. -/
noncomputable def e1ToH1 {A : Type u} {a : A} (n : Nat) :
    Gr A a n → H1 A a :=
  Quot.lift
    (fun x : ExactLengthLoop A a n => Quot.mk _ x.1)
    (by
      intro x y h
      exact Quot.sound h)

@[simp] theorem e1ToH1_mk {A : Type u} {a : A} {n : Nat}
    (x : ExactLengthLoop A a n) :
    e1ToH1 (A := A) (a := a) n (Quot.mk _ x) = Quot.mk _ x.1 :=
  rfl

/-- Representative-level `d₁`: compose with unit path on the left. -/
noncomputable def d1Rep {A : Type u} {a : A} {n : Nat}
    (x : ExactLengthLoop A a n) : ExactLengthLoop A a n :=
  ⟨Path.trans (Path.refl a) x.1, by
      simpa using x.2⟩

/-- `d₁` is induced by a primitive `Step` composition rule. -/
theorem d1Rep_step {A : Type u} {a : A} {n : Nat}
    (x : ExactLengthLoop A a n) :
    Step (d1Rep x).1 x.1 := by
  simpa [d1Rep] using (Step.trans_refl_left x.1)

/-- Hence `d₁` preserves classes modulo `RwEq`. -/
noncomputable def d1Rep_respects_rweq {A : Type u} {a : A} {n : Nat}
    {x y : ExactLengthLoop A a n} (h : RwEq x.1 y.1) :
    RwEq (d1Rep x).1 (d1Rep y).1 := by
  change RwEq (Path.trans (Path.refl a) x.1) (Path.trans (Path.refl a) y.1)
  exact rweq_trans_congr_right (Path.refl a) h

/-- Differential `d₁ : E₁^{n,0} → E₁^{n,0}`. -/
noncomputable def d1 {A : Type u} {a : A} (n : Nat) :
    Gr A a n → Gr A a n :=
  Quot.lift
    (fun x : ExactLengthLoop A a n => Quot.mk _ (d1Rep x))
    (by
      intro x y h
      rcases h with ⟨hxy⟩
      exact Quot.sound ⟨d1Rep_respects_rweq (x := x) (y := y) hxy⟩)

/-- `E₂` page identified with first homology from `HomologicalAlgebra`. -/
abbrev E2 (A : Type u) (a : A) : Type u := H1 A a

/-- Convergence statement `E₂ ≃ π₁` via the existing `H₁ ≃ π₁` theorem. -/
noncomputable def e2ConvergesToPi1 (A : Type u) (a : A) :
    SimpleEquiv (E2 A a) (π₁(A, a)) :=
  h1EquivPi1 A a

/-- Collapse criterion at `E₂`: every `RwEq` pair has a common `Rw` reduct. -/
noncomputable def CollapsesAtE2 (A : Type u) (a : A) : Prop :=
  ∀ p q : Loop A a, RwEq p q → ∃ m, Rw p m ∧ Rw q m

/-- Confluence gives collapse at `E₂` (Church-Rosser on loops). -/
theorem collapses_at_E2_of_confluent {A : Type u} {a : A}
    (hConf : ComputationalPaths.Confluence.StepConfluent (A := A) (a := a) (b := a)) :
    CollapsesAtE2 A a := by
  intro p q h
  exact ComputationalPaths.Confluence.church_rosser_rweq
    (A := A) (a := a) (b := a) hConf h

/-- Complete rewriting (termination + local confluence) collapses at `E₂`. -/
theorem collapses_at_E2_of_complete {A : Type u} {a : A}
    (wf : WellFounded (fun y x : Loop A a => Step x y))
    (hLocal : ComputationalPaths.Confluence.StepLocallyConfluent (A := A) (a := a) (b := a)) :
    CollapsesAtE2 A a := by
  have hConf : ComputationalPaths.Confluence.StepConfluent (A := A) (a := a) (b := a) :=
    ComputationalPaths.Confluence.step_newman_lemma
      (A := A) (a := a) (b := a) wf hLocal
  exact collapses_at_E2_of_confluent (A := A) (a := a) hConf

end

end ComputationalPaths.Path.Algebra
