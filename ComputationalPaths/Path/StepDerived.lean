/-
# Derived Rewrite-Step Lemmas

This module provides derived lemmas about the rewrite-step system (`Step`),
building composite rewriting strategies from the primitive step constructors.
We prove that the step relation respects various algebraic compositions,
and record useful derived reduction sequences.
-/

import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace Path
namespace StepDerived

universe u v

variable {A : Type u}
variable {a b c d : A}

/-! ## Derived single-step identities -/

/-- Symmetry of a reflexivity path built via `ofEq rfl` reduces to `ofEq rfl`. -/
theorem symm_ofEq_rfl (a : A) :
    Path.symm (Path.stepChain (rfl : a = a)) = Path.stepChain rfl := by
  simp [Path.symm, Path.stepChain]

/-- Double symmetry of `ofEq` recovers the original `ofEq`. -/
theorem symm_symm_ofEq (h : a = b) :
    Path.symm (Path.symm (Path.stepChain h)) = Path.stepChain h := by
  simp

/-- Composing a path with its own inverse produces a path whose `toEq` is `rfl`. -/
theorem trans_symm_toEq (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = rfl := by
  simp

/-- Composing the inverse with the original path also yields `rfl`. -/
theorem symm_trans_toEq (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = rfl := by
  simp

/-! ## Multi-step reduction sequences -/

/-- The path `trans (trans (refl a) p) (refl b)` reduces to `p` in two steps. -/
theorem rw_trans_refl_both (p : Path a b) :
    Rw (Path.trans (Path.trans (Path.refl a) p) (Path.refl b)) p := by
  apply rw_trans
  · exact Rw.tail (Rw.refl _) (Step.trans_refl_right _)
  · exact Rw.tail (Rw.refl _) (Step.trans_refl_left _)

/-- Triple left identity: `refl ∘ (refl ∘ p) ▷* p`. -/
theorem rw_trans_refl_left_twice (p : Path a b) :
    Rw (Path.trans (Path.refl a) (Path.trans (Path.refl a) p)) p := by
  apply rw_trans
  · exact Rw.tail (Rw.refl _) (Step.trans_refl_left _)
  · exact Rw.tail (Rw.refl _) (Step.trans_refl_left _)

/-- Symmetry of `symm p` rewrites to `p`. -/
theorem rw_symm_symm (p : Path a b) :
    Rw (Path.symm (Path.symm p)) p :=
  rw_of_step (Step.symm_symm p)

/-- `(refl ∘ p) ∘ q ▷* p ∘ q` via associativity and left identity. -/
theorem rw_assoc_then_left_id (p : Path a b) (q : Path b c) :
    Rw (Path.trans (Path.trans (Path.refl a) p) q)
       (Path.trans p q) := by
  have h1 : Rw (Path.trans (Path.trans (Path.refl a) p) q)
                (Path.trans (Path.refl a) (Path.trans p q)) :=
    rw_of_step (Step.trans_assoc (Path.refl a) p q)
  have h2 : Rw (Path.trans (Path.refl a) (Path.trans p q))
                (Path.trans p q) :=
    rw_of_step (Step.trans_refl_left (Path.trans p q))
  exact rw_trans h1 h2

/-- Right identity after reassociation:
    `(p ∘ q) ∘ refl ▷* p ∘ q`. -/
theorem rw_trans_refl_right_outer (p : Path a b) (q : Path b c) :
    Rw (Path.trans (Path.trans p q) (Path.refl c))
       (Path.trans p q) :=
  rw_of_step (Step.trans_refl_right _)

/-! ## Congruence-step interactions -/

/-- Applying `congrArg f` to `refl a` is rewrite-equal to `refl (f a)`. -/
theorem rweq_congrArg_refl_eq {B : Type u} (f : A → B) (a : A) :
    RwEq (Path.congrArg f (Path.refl a)) (Path.refl (f a)) := by
  simp

/-- `congrArg f (symm p)` is rewrite-equal to `symm (congrArg f p)`. -/
theorem rweq_congrArg_symm_eq {B : Type u} (f : A → B) (p : Path a b) :
    RwEq (Path.congrArg f (Path.symm p))
         (Path.symm (Path.congrArg f p)) := by
  simp

/-- `congrArg f (trans p q)` is rewrite-equal to
    `trans (congrArg f p) (congrArg f q)`. -/
theorem rweq_congrArg_trans_eq {B : Type u} (f : A → B)
    (p : Path a b) (q : Path b c) :
    RwEq (Path.congrArg f (Path.trans p q))
         (Path.trans (Path.congrArg f p) (Path.congrArg f q)) := by
  simp

/-- `congrArg id p` is rewrite-equal to `p`. -/
theorem rweq_congrArg_id_eq (p : Path a b) :
    RwEq (Path.congrArg (fun x : A => x) p) p := by
  simp

/-- Composition of congruences: `congrArg (g ∘ f) p` equals
    `congrArg g (congrArg f p)`. -/
theorem rweq_congrArg_comp_eq {B C : Type u}
    (f : A → B) (g : B → C)
    (p : Path a b) :
    RwEq (Path.congrArg (fun x => g (f x)) p)
         (Path.congrArg g (Path.congrArg f p)) := by
  simp

/-! ## Inverse-law derived sequences -/

/-- `symm p ∘ p ▷ refl` — left inverse law. -/
theorem rw_symm_trans_cancel (p : Path a b) :
    Rw (Path.trans (Path.symm p) p) (Path.refl b) :=
  rw_of_step (Step.symm_trans p)

/-- `p ∘ symm p ▷ refl` — right inverse law. -/
theorem rw_trans_symm_cancel (p : Path a b) :
    Rw (Path.trans p (Path.symm p)) (Path.refl a) :=
  rw_of_step (Step.trans_symm p)

/-! ## Symmetry distribution -/

/-- `symm (p ∘ q)` rewrites to `symm q ∘ symm p` (contravariance). -/
theorem rw_symm_trans (p : Path a b) (q : Path b c) :
    Rw (Path.symm (Path.trans p q))
       (Path.trans (Path.symm q) (Path.symm p)) :=
  rw_of_step (Step.symm_trans_congr p q)

/-- `symm (symm q ∘ symm p)` rewrites back to `p ∘ q`. -/
theorem rw_symm_symm_trans (p : Path a b) (q : Path b c) :
    Rw (Path.symm (Path.trans (Path.symm q) (Path.symm p)))
       (Path.trans p q) := by
  apply rw_trans
  · exact rw_of_step (Step.symm_trans_congr (Path.symm q) (Path.symm p))
  · apply rw_trans
    · apply Rw.tail (Rw.refl _)
      exact Step.trans_congr_left (Path.symm (Path.symm q))
        (Step.symm_symm p)
    · apply Rw.tail (Rw.refl _)
      exact Step.trans_congr_right p (Step.symm_symm q)

/-! ## Path algebra coherence -/

/-- The Mac Lane pentagon: the two ways to reassociate `((p ∘ q) ∘ r) ∘ s`
    into `p ∘ (q ∘ (r ∘ s))` yield the same result (up to `RwEq`). -/
theorem rweq_pentagon (p : Path a b) (q : Path b c) (r : Path c d)
    {e : A} (s : Path d e) :
    RwEq
      (Path.trans (Path.trans (Path.trans p q) r) s)
      (Path.trans p (Path.trans q (Path.trans r s))) := by
  apply RwEq.trans
  · exact rweq_of_step (Step.trans_assoc (Path.trans p q) r s)
  · exact rweq_of_step (Step.trans_assoc p q (Path.trans r s))

/-- Symmetry of reflexivity at any point is reflexivity at that point. -/
theorem rw_symm_refl (a : A) :
    Rw (Path.symm (Path.refl a)) (Path.refl a) :=
  rw_of_step (Step.symm_refl a)

/-- `ofEq h` for any `h : a = a` rewrites to `ofEq rfl`. -/
theorem rweq_ofEq_rfl_eq_refl (h : a = a) :
    RwEq (Path.stepChain h) (Path.stepChain rfl) := by
  have : h = rfl := rfl
  subst this
  exact RwEq.refl _

/-! ## Step preservation under congruence -/

/-- If `Step p q` then `Step (congrArg f p) (congrArg f q)` via context
    congruence. -/
theorem step_congrArg_of_step {B : Type u} (f : A → B) {p q : Path a b}
    (h : Step p q) :
    Step (Path.congrArg f p) (Path.congrArg f q) :=
  Step.context_congr ⟨f⟩ h

/-- If `Rw p q` then `Rw (congrArg f p) (congrArg f q)`. -/
theorem rw_congrArg_of_rw {B : Type u} (f : A → B) {p q : Path a b}
    (h : Rw p q) :
    Rw (Path.congrArg f p) (Path.congrArg f q) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih (step_congrArg_of_step f step)

/-- If `RwEq p q` then `RwEq (congrArg f p) (congrArg f q)`. -/
theorem rweq_congrArg_of_rweq' {B : Type u} (f : A → B) {p q : Path a b}
    (h : RwEq p q) :
    RwEq (Path.congrArg f p) (Path.congrArg f q) :=
  rweq_congrArg_of_rweq f h

/-! ## Derived transport-step identities -/

/-- Transport along `ofEq rfl` is the identity. -/
theorem transport_ofEq_rfl {D : A → Sort v} (x : D a) :
    Path.transport (Path.stepChain (rfl : a = a)) x = x := by
  simp [Path.transport]

/-- Transport along `trans (ofEq h₁) (ofEq h₂)` equals sequential transport. -/
theorem transport_ofEq_trans {D : A → Sort v}
    (h₁ : a = b) (h₂ : b = c) (x : D a) :
    Path.transport (Path.trans (Path.stepChain h₁) (Path.stepChain h₂)) x =
      Path.transport (Path.stepChain h₂) (Path.transport (Path.stepChain h₁) x) := by
  cases h₁; cases h₂; rfl

/-! ## Rw interaction with symmetry congruence -/

/-- If `Step p q` then `Step (symm p) (symm q)`. -/
theorem step_symm_of_step {p q : Path a b}
    (h : Step p q) : Step (Path.symm p) (Path.symm q) :=
  Step.symm_congr h

/-- If `Rw p q` then `Rw (symm p) (symm q)`. -/
theorem rw_symm_of_rw {p q : Path a b}
    (h : Rw p q) : Rw (Path.symm p) (Path.symm q) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih => exact Rw.tail ih (Step.symm_congr step)

/-- If `Step p q` then `Step (trans p r) (trans q r)` (left congruence). -/
theorem step_trans_left_of_step {p q : Path a b} (r : Path b c)
    (h : Step p q) : Step (Path.trans p r) (Path.trans q r) :=
  Step.trans_congr_left r h

/-- If `Step p q` then `Step (trans r p) (trans r q)` (right congruence). -/
theorem step_trans_right_of_step (r : Path a b) {p q : Path b c}
    (h : Step p q) : Step (Path.trans r p) (Path.trans r q) :=
  Step.trans_congr_right r h

/-- If `Rw p q` then `Rw (trans p r) (trans q r)` (left congruence). -/
theorem rw_trans_left_of_rw {p q : Path a b} (r : Path b c)
    (h : Rw p q) : Rw (Path.trans p r) (Path.trans q r) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih =>
      exact Rw.tail ih (Step.trans_congr_left r step)

/-- If `Rw p q` then `Rw (trans r p) (trans r q)` (right congruence). -/
theorem rw_trans_right_of_rw (r : Path a b) {p q : Path b c}
    (h : Rw p q) : Rw (Path.trans r p) (Path.trans r q) := by
  induction h with
  | refl => exact Rw.refl _
  | tail _ step ih =>
      exact Rw.tail ih (Step.trans_congr_right r step)

/-! ## Concrete examples -/

/-- A concrete path on natural numbers: `0 = 0` witnessed by `refl`. -/
example : Path (0 : Nat) 0 := Path.refl 0

/-- The path `ofEq (Nat.add_zero 0)` from `0 + 0` to `0`. -/
example : Path (0 + 0) 0 := Path.stepChain (Nat.add_zero 0)

/-- Symmetry of a concrete arithmetic identity. -/
example : Path 0 (0 + 0) := Path.symm (Path.stepChain (Nat.add_zero 0))

/-- Composing two concrete arithmetic identities. -/
example : Path (0 + 0 + 0) 0 :=
  Path.trans
    (Path.stepChain (Nat.add_zero (0 + 0)))
    (Path.stepChain (Nat.add_zero 0))

/-- The groupoid inverse law holds concretely for any `ofEq`. -/
example (h : a = b) :
    (Path.trans (Path.stepChain h) (Path.symm (Path.stepChain h))).toEq = rfl := by
  simp

/-- Double symmetry toEq at the concrete level. -/
example (p : Path (0 : Nat) 0) :
    (Path.symm (Path.symm p)).toEq = p.toEq := by
  simp

end StepDerived
end Path
end ComputationalPaths
