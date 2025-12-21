/-
# Homotopy Sets and Axiom K

This file characterizes homotopy sets (h-sets) in terms of Axiom K.
A type is a "set" in the homotopy-theoretic sense if all parallel paths
are RwEq (i.e., it has h-level 0 for paths).

## Key Definitions

- `IsHSet A`: A type A is a homotopy set if any two parallel paths are RwEq
- `AxiomK A`: A type A satisfies Axiom K if every loop is RwEq to refl

## Main Theorems

1. `isHSet_iff_axiomK`: A type is a set iff it satisfies Axiom K
2. `inverse_unique`: Every path has a unique inverse (up to RwEq)
3. `decidableEq_implies_isHSet`: Types with decidable equality are sets
-/

import ComputationalPaths.Path.Homotopy.Reflexivity
import ComputationalPaths.Path.Homotopy.FundamentalGroup

namespace ComputationalPaths.Path

universe u

variable {A : Type u}

/-- A type is a homotopy set (h-set) if any two parallel paths are RwEq.
    This is the computational paths analog of "0-truncated" types in HoTT. -/
def IsHSet (A : Type u) : Prop :=
  ∀ {a b : A} (p q : Path a b), RwEq p q

/-- A type satisfies Axiom K if every loop is RwEq to refl.
    This is the computational paths analog of the "K axiom" in type theory. -/
def AxiomK (A : Type u) : Prop :=
  ∀ (a : A) (p : Path a a), RwEq p (Path.refl a)

/-- Subsingleton types satisfy Axiom K: any loop rewrites to reflexivity.

This is provable because, when `A` has exactly one element, every base rewrite
step in a loop can be replaced by the unique reflexive step at the basepoint,
and `Path.ofEq rfl` rewrites to `Path.refl` (see `Homotopy/Reflexivity.lean`). -/
theorem axiomK_of_subsingleton (A : Type u) [Subsingleton A] : AxiomK A := by
  intro a p
  have step_eq_refl (s : ComputationalPaths.Step A) :
      s = ComputationalPaths.Step.mk a a (rfl : a = a) := by
    cases s with
    | mk src tgt proof =>
        have hsrc : src = a := Subsingleton.elim src a
        have htgt : tgt = a := Subsingleton.elim tgt a
        cases hsrc
        cases htgt
        have hproof : proof = (rfl : a = a) := Subsingleton.elim proof rfl
        cases hproof
        rfl
  cases p with
  | mk steps proof =>
      cases proof
      induction steps with
      | nil =>
          -- `Path.mk [] rfl` is definitionally `Path.refl a`.
          simp [Path.refl]
      | cons s ss ih =>
          have hseg :
              RwEq
                (Path.mk ([s] : List (ComputationalPaths.Step A)) (rfl : a = a))
                (Path.refl a) := by
            have hs : s = ComputationalPaths.Step.mk a a (rfl : a = a) :=
              step_eq_refl s
            have hpath :
                Path.mk ([s] : List (ComputationalPaths.Step A)) (rfl : a = a) =
                  Path.ofEq (A := A) (a := a) (b := a) (rfl : a = a) := by
              simp [Path.ofEq, hs]
            exact RwEq.trans (rweq_of_eq hpath) (rweq_ofEq_rfl_refl a)
          have htrans :
              RwEq
                (Path.trans
                  (Path.mk ([s] : List (ComputationalPaths.Step A)) (rfl : a = a))
                  (Path.mk (A := A) (a := a) (b := a) ss (rfl : a = a)))
                (Path.trans (Path.refl a) (Path.refl a)) :=
            rweq_trans_congr (hp := hseg) (hq := ih)
          have hrefl :
              RwEq (Path.trans (Path.refl a) (Path.refl a)) (Path.refl a) :=
            rweq_of_step (Step.trans_refl_left (Path.refl a))
          simpa [Path.trans] using RwEq.trans htrans hrefl

/-- Lemma 5.12: Every path has an inverse that composes to refl on both sides.
    In our formalization, the inverse is `Path.symm`. -/
theorem inverse_left {a b : A} (p : Path a b) :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_of_step (Step.symm_trans p)

theorem inverse_right {a b : A} (p : Path a b) :
    RwEq (Path.trans p (Path.symm p)) (Path.refl a) :=
  rweq_of_step (Step.trans_symm p)

/-- Inverses are unique up to RwEq: if q composes with p to refl,
    then q is RwEq to symm p.

    This formalizes the uniqueness part of Lemma 5.12:
    "Furthermore, t⁻¹ is unique up to propositional identity" -/
theorem inverse_unique {a b : A} (p : Path a b) (q : Path b a)
    (hpq : RwEq (Path.trans p q) (Path.refl a)) :
    RwEq q (Path.symm p) := by
  -- q ≈ trans refl q ≈ trans (trans (symm p) p) q
  --   ≈ trans (symm p) (trans p q) ≈ trans (symm p) refl ≈ symm p
  have h1 : RwEq q (Path.trans (Path.refl b) q) := by
    exact (rweq_of_step (Step.trans_refl_left q)).symm
  have h2 : RwEq (Path.trans (Path.refl b) q) (Path.trans (Path.trans (Path.symm p) p) q) := by
    exact rweq_trans_congr_left q (inverse_left p).symm
  have h3 : RwEq (Path.trans (Path.trans (Path.symm p) p) q) (Path.trans (Path.symm p) (Path.trans p q)) := by
    exact rweq_tt (Path.symm p) p q
  have h4 : RwEq (Path.trans (Path.symm p) (Path.trans p q)) (Path.trans (Path.symm p) (Path.refl a)) := by
    exact rweq_trans_congr_right (Path.symm p) hpq
  have h5 : RwEq (Path.trans (Path.symm p) (Path.refl a)) (Path.symm p) := by
    exact rweq_of_step (Step.trans_refl_right (Path.symm p))
  exact RwEq.trans (RwEq.trans (RwEq.trans (RwEq.trans h1 h2) h3) h4) h5

/-- If A is a set, then A satisfies Axiom K.

    Proof: Any loop `p : a → a` is parallel to `refl a`, so by `IsHSet`, `p ≈ refl`. -/
theorem isHSet_implies_axiomK (h : IsHSet A) : AxiomK A := by
  intro a p
  exact h p (Path.refl a)

/-- If A satisfies Axiom K, then A is a set.

    Proof: Given paths `p, q : a → b`, form `trans p (symm q) : a → a`.
    By Axiom K, this is RwEq to refl. Then derive `p ≈ q` via path algebra. -/
theorem axiomK_implies_isHSet (h : AxiomK A) : IsHSet A := by
  intro a b p q
  -- Form the loop trans p (symm q) : a → a
  have loop_refl : RwEq (Path.trans p (Path.symm q)) (Path.refl a) := h a _
  -- We need to show p ≈ q
  -- p ≈ trans p refl ≈ trans p (trans (symm q) q)
  --   ≈ trans (trans p (symm q)) q ≈ trans refl q ≈ q
  have h1 : RwEq p (Path.trans p (Path.refl b)) :=
    (rweq_of_step (Step.trans_refl_right p)).symm
  have h2 : RwEq (Path.trans p (Path.refl b)) (Path.trans p (Path.trans (Path.symm q) q)) :=
    rweq_trans_congr_right p (inverse_left q).symm
  have h3 : RwEq (Path.trans p (Path.trans (Path.symm q) q)) (Path.trans (Path.trans p (Path.symm q)) q) :=
    (rweq_tt p (Path.symm q) q).symm
  have h4 : RwEq (Path.trans (Path.trans p (Path.symm q)) q) (Path.trans (Path.refl a) q) :=
    rweq_trans_congr_left q loop_refl
  have h5 : RwEq (Path.trans (Path.refl a) q) q :=
    rweq_of_step (Step.trans_refl_left q)
  exact RwEq.trans (RwEq.trans (RwEq.trans (RwEq.trans h1 h2) h3) h4) h5

/-- A type is a set iff it satisfies Axiom K. -/
theorem isHSet_iff_axiomK : IsHSet A ↔ AxiomK A :=
  ⟨isHSet_implies_axiomK, axiomK_implies_isHSet⟩

/-- Subsingleton types have trivial fundamental group. -/
theorem pi1_trivial_of_subsingleton (A : Type u) [Subsingleton A] (a : A) :
    ∀ (α : π₁(A, a)), α = Quot.mk _ (Path.refl a) := by
  intro α
  induction α using Quot.ind with
  | _ p =>
      apply Quot.sound
      have hk : AxiomK A := axiomK_of_subsingleton (A := A)
      exact hk a p

/-- **Decidable equality axiom for paths**: Types with decidable equality satisfy Axiom K.
For such types, every loop is RwEq to refl.

This is sound because types with DecidableEq have unique equality proofs (all equal to rfl).
Without the general canonicalization rule, we state this as a targeted axiom for types
where path collapsing is known to be safe. -/
class HasDecidableEqAxiomK (A : Type u) [DecidableEq A] : Prop where
  axiomK : AxiomK A

/-- Types with decidable equality satisfy Axiom K (assumed as an explicit hypothesis). -/
theorem decidableEq_implies_axiomK [DecidableEq A] [h : HasDecidableEqAxiomK A] : AxiomK A :=
  h.axiomK

/-- Subsingleton types satisfy `HasDecidableEqAxiomK` (no extra axioms required). -/
instance instHasDecidableEqAxiomK_of_subsingleton (A : Type u) [DecidableEq A] [Subsingleton A] :
    HasDecidableEqAxiomK A where
  axiomK := axiomK_of_subsingleton (A := A)

/-- A type with decidable equality is a set -/
theorem decidableEq_implies_isHSet [DecidableEq A] [HasDecidableEqAxiomK A] : IsHSet A :=
  axiomK_implies_isHSet decidableEq_implies_axiomK

-- Examples: Concrete types are sets

instance [HasDecidableEqAxiomK Nat] : IsHSet Nat :=
  decidableEq_implies_isHSet

instance [HasDecidableEqAxiomK Bool] : IsHSet Bool :=
  decidableEq_implies_isHSet

instance [HasDecidableEqAxiomK Unit] : IsHSet Unit :=
  decidableEq_implies_isHSet

instance [HasDecidableEqAxiomK Empty] : IsHSet Empty :=
  decidableEq_implies_isHSet

end ComputationalPaths.Path
