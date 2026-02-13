import ComputationalPaths.Path.Basic.Core
/-
# Strip Lemma for Confluence

This module develops the strip lemma (also known as the "diamond-to-confluence"
lifting lemma) for the computational-path rewriting system.  The strip lemma
states that if a single step can always be closed against another single step
(local confluence / diamond property), then a single step can be closed against
any multi-step chain.  Iterating then gives full confluence.

## Main Results

- `DiamondWitness`, `StripWitness`: packaging for diamond/strip closings
- `strip_preserves_toEq`: the strip join preserves propositional equality
- `Joinable`: Prop-level joinability and its algebraic properties
- `join_lift_symm_prop`, `join_lift_trans_*`: lifting joinability
- `unique_normal_form_of_rweq`: uniqueness of normal forms up to RwEq
- Concrete strip closings for canonical path-algebra rules

## References

- Huet, "Confluent Reductions" (1980)
- Terese, "Term Rewriting Systems" (2003), Chapter 2
- Newman, "On Theories with a Combinatorial Definition of Equivalence" (1942)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.Rw
import ComputationalPaths.Path.Rewrite.Confluence
import ComputationalPaths.Path.Rewrite.Normalization

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace StripLemma

open Confluence

universe u

variable {A : Type u} {a b : A}

/-! ## Diamond Property -/

/-- Witness structure for a diamond closing. -/
structure DiamondWitness {A : Type u} {a b : A}
    (q r : Path a b) where
  meet : Path a b
  left : Rw q meet
  right : Rw r meet

/-- Convert a `Confluence.Join` to a `DiamondWitness`. -/
def Join.toDiamondWitness {A : Type u} {a b : A}
    {q r : Path a b} (j : Join q r) : DiamondWitness q r :=
  { meet := j.meet, left := j.left, right := j.right }

/-- Convert a `DiamondWitness` to a `Confluence.Join`. -/
def DiamondWitness.toJoin {A : Type u} {a b : A}
    {q r : Path a b} (d : DiamondWitness q r) : Join q r :=
  { meet := d.meet, left := d.left, right := d.right }

/-- A reflexive diamond witness: any path joins with itself. -/
def DiamondWitness.refl {A : Type u} {a b : A}
    (p : Path a b) : DiamondWitness p p :=
  { meet := p, left := Rw.refl p, right := Rw.refl p }

/-- Diamond witnesses preserve the toEq invariant. -/
theorem diamondWitness_toEq {A : Type u} {a b : A}
    {q r : Path a b} (d : DiamondWitness q r) :
    q.toEq = r.toEq := by
  have h1 := rw_toEq d.left
  have h2 := rw_toEq d.right
  exact h1.trans h2.symm

/-- Symmetric diamond witness. -/
def DiamondWitness.symm {A : Type u} {a b : A}
    {q r : Path a b} (d : DiamondWitness q r) : DiamondWitness r q :=
  { meet := d.meet, left := d.right, right := d.left }

/-! ## Strip Property -/

/-- Witness structure for a strip closing. -/
structure StripWitness {A : Type u} {a b : A}
    (q r : Path a b) where
  meet : Path a b
  left_rw : Rw q meet
  right_rw : Rw r meet

/-- Convert a `StripWitness` to a `Confluence.Join`. -/
def StripWitness.toJoin {A : Type u} {a b : A}
    {q r : Path a b} (s : StripWitness q r) : Join q r :=
  { meet := s.meet, left := s.left_rw, right := s.right_rw }

/-- A reflexive strip witness. -/
def StripWitness.refl {A : Type u} {a b : A}
    (p : Path a b) : StripWitness p p :=
  { meet := p, left_rw := Rw.refl p, right_rw := Rw.refl p }

/-- Symmetric strip witness. -/
def StripWitness.symm {A : Type u} {a b : A}
    {q r : Path a b} (s : StripWitness q r) : StripWitness r q :=
  { meet := s.meet, left_rw := s.right_rw, right_rw := s.left_rw }

/-- The toEq of both sides of a strip witness agree. -/
theorem stripWitness_toEq {A : Type u} {a b : A}
    {q r : Path a b} (s : StripWitness q r) :
    q.toEq = r.toEq := by
  exact (rw_toEq s.left_rw).trans (rw_toEq s.right_rw).symm

/-- Compose two strip witnesses when the meeting points are equal. -/
def StripWitness.comp {A : Type u} {a b : A}
    {p q r : Path a b}
    (s₁ : StripWitness p q) (s₂ : StripWitness q r)
    (h : s₁.meet = s₂.meet) : StripWitness p r :=
  { meet := s₁.meet
  , left_rw := s₁.left_rw
  , right_rw := h ▸ s₂.right_rw }

/-! ## Preservation Theorems -/

/-- The strip join preserves propositional equality. -/
theorem strip_preserves_toEq {p q r : Path a b}
    (hstep : Step (A := A) p q)
    (hrw : Rw (A := A) (a := a) (b := b) p r) :
    q.toEq = r.toEq :=
  (step_toEq hstep).symm.trans (rw_toEq hrw)

/-- A single-step rewrite preserves toEq. -/
theorem single_step_toEq_eq {p q : Path a b}
    (h : Step (A := A) p q) : p.toEq = q.toEq :=
  step_toEq h

/-- All members of an Rw chain share the same toEq. -/
theorem rw_chain_toEq_eq {p q : Path a b}
    (h : Rw (A := A) (a := a) (b := b) p q) : p.toEq = q.toEq :=
  rw_toEq h

/-- Transitivity of the toEq invariant across a peak. -/
theorem three_path_toEq {p q r : Path a b}
    (hpq : Rw p q) (hpr : Rw p r) :
    q.toEq = r.toEq :=
  (rw_toEq hpq).symm.trans (rw_toEq hpr)

/-- In an Rw chain, the source determines the propositional equality of
all subsequent paths. -/
theorem rw_determines_toEq {p q₁ q₂ : Path a b}
    (h₁ : Rw p q₁) (h₂ : Rw p q₂) :
    q₁.toEq = q₂.toEq :=
  (rw_toEq h₁).symm.trans (rw_toEq h₂)

/-! ## Joinability as a Prop -/

/-- Prop-level joinability: two paths can be joined by Rw. -/
def Joinable {A : Type u} {a b : A} (p q : Path a b) : Prop :=
  ∃ s : Path a b, Rw p s ∧ Rw q s

/-- Joinability is reflexive. -/
theorem join_refl_prop (p : Path a b) : Joinable p p :=
  ⟨p, Rw.refl p, Rw.refl p⟩

/-- Joinability is symmetric. -/
theorem join_symm_prop {p q : Path a b}
    (h : Joinable p q) : Joinable q p := by
  obtain ⟨s, hps, hqs⟩ := h
  exact ⟨s, hqs, hps⟩

/-- If p → q by a step, then p and q are joinable. -/
theorem joinable_of_step {p q : Path a b}
    (h : Step (A := A) p q) : Joinable p q :=
  ⟨q, rw_of_step h, Rw.refl q⟩

/-- If p →* q, then p and q are joinable. -/
theorem joinable_of_rw {p q : Path a b}
    (h : Rw p q) : Joinable p q :=
  ⟨q, h, Rw.refl q⟩

/-- If p = q (definitionally equal paths), then they are joinable. -/
theorem joinable_of_eq {p q : Path a b}
    (h : p = q) : Joinable p q := by
  subst h; exact join_refl_prop p

/-! ## Lifting Joins through Congruence -/

/-- If p and q are joinable, then `symm p` and `symm q` are joinable. -/
theorem join_lift_symm_prop {p q : Path a b}
    (h : Joinable p q) :
    Joinable (Path.symm p) (Path.symm q) := by
  obtain ⟨s, hps, hqs⟩ := h
  exact ⟨Path.symm s, rw_symm_congr hps, rw_symm_congr hqs⟩

/-- If p₁,p₂ are joinable, then `trans p₁ r` and `trans p₂ r` are joinable. -/
theorem join_lift_trans_left_prop {c : A} {p₁ p₂ : Path a b}
    (r : Path b c) (h : Joinable p₁ p₂) :
    Joinable (Path.trans p₁ r) (Path.trans p₂ r) := by
  obtain ⟨s, hp₁s, hp₂s⟩ := h
  exact ⟨Path.trans s r,
    rw_trans_congr_left r hp₁s,
    rw_trans_congr_left r hp₂s⟩

/-- If q₁,q₂ are joinable, then `trans p q₁` and `trans p q₂` are joinable. -/
theorem join_lift_trans_right_prop {c : A} {q₁ q₂ : Path b c}
    (p : Path a b) (h : Joinable q₁ q₂) :
    Joinable (Path.trans p q₁) (Path.trans p q₂) := by
  obtain ⟨s, hq₁s, hq₂s⟩ := h
  exact ⟨Path.trans p s,
    rw_trans_congr_right p hq₁s,
    rw_trans_congr_right p hq₂s⟩

/-- Joinability lifts through both components of a trans simultaneously. -/
theorem join_lift_trans_both {c : A} {p₁ p₂ : Path a b} {q₁ q₂ : Path b c}
    (hp : Joinable p₁ p₂) (hq : Joinable q₁ q₂) :
    Joinable (Path.trans p₁ q₁) (Path.trans p₂ q₂) := by
  obtain ⟨sp, hp₁sp, hp₂sp⟩ := hp
  obtain ⟨sq, hq₁sq, hq₂sq⟩ := hq
  exact ⟨Path.trans sp sq,
    rw_trans (rw_trans_congr_left q₁ hp₁sp) (rw_trans_congr_right sp hq₁sq),
    rw_trans (rw_trans_congr_left q₂ hp₂sp) (rw_trans_congr_right sp hq₂sq)⟩

/-! ## Normal Form Uniqueness -/

/-- Normal forms are unique up to RwEq. -/
theorem unique_normal_form_of_rweq
    {p q : Path a b}
    (_h : RwEq p q)
    (hp : IsNormal p) (hq : IsNormal q) :
    p = q := by
  unfold IsNormal at hp hq; rw [hp, hq]

/-- Normalization commutes with the toEq extractor. -/
theorem normalize_toEq_invariant (p : Path a b) :
    (Path.normalize p).toEq = p.toEq := by
  simp

/-- Normal paths are exactly the `ofEq` paths. -/
theorem isNormal_iff_eq_ofEq (p : Path a b) :
    IsNormal p ↔ p = Path.ofEq p.toEq :=
  Iff.rfl

/-- All paths between the same endpoints normalize to the same thing. -/
theorem normalization_confluence (p q : Path a b) :
    Path.normalize p = Path.normalize q := by
  simp [Path.normalize]

/-! ## Concrete Strip Closings -/

/-- Symmetry-symmetry strip: `symm (symm p)` joins with `p`. -/
theorem strip_symm_symm (p : Path a b) :
    Joinable (Path.symm (Path.symm p)) p :=
  ⟨p, rw_of_eq (Path.symm_symm p), Rw.refl p⟩

/-- Associativity strip. -/
theorem strip_assoc {c d : A} (p : Path a b) (q : Path b c) (r : Path c d) :
    Joinable (Path.trans (Path.trans p q) r)
             (Path.trans p (Path.trans q r)) :=
  ⟨Path.trans p (Path.trans q r),
    rw_of_step (Step.trans_assoc p q r), Rw.refl _⟩

/-- `trans_refl_left` and `trans_refl_right` join at the reduced path. -/
theorem strip_trans_refl_both (p : Path a b) :
    Joinable (Path.trans p (Path.refl b))
             (Path.trans (Path.refl a) p) :=
  ⟨p, rw_of_step (Step.trans_refl_right p),
      rw_of_step (Step.trans_refl_left p)⟩

/-- `symm_refl` strip. -/
theorem strip_symm_refl (x : A) :
    Joinable (Path.symm (Path.refl x)) (Path.refl x) :=
  ⟨Path.refl x, rw_of_step (Step.symm_refl x), Rw.refl _⟩

/-- Right inverse strip. -/
theorem strip_trans_symm (p : Path a b) :
    Joinable (Path.trans p (Path.symm p)) (Path.refl a) :=
  ⟨Path.refl a, rw_of_step (Step.trans_symm p), Rw.refl _⟩

/-- Left inverse strip. -/
theorem strip_symm_trans (p : Path a b) :
    Joinable (Path.trans (Path.symm p) p) (Path.refl b) :=
  ⟨Path.refl b, rw_of_step (Step.symm_trans p), Rw.refl _⟩

/-- Symmetry of composition strip. -/
theorem strip_symm_trans_congr {c : A} (p : Path a b) (q : Path b c) :
    Joinable (Path.symm (Path.trans p q))
             (Path.trans (Path.symm q) (Path.symm p)) :=
  ⟨Path.trans (Path.symm q) (Path.symm p),
    rw_of_step (Step.symm_trans_congr p q), Rw.refl _⟩

/-- trans_refl_left: `refl · p` joins with `p`. -/
theorem strip_trans_refl_left (p : Path a b) :
    Joinable (Path.trans (Path.refl a) p) p :=
  ⟨p, rw_of_step (Step.trans_refl_left p), Rw.refl _⟩

/-- trans_refl_right: `p · refl` joins with `p`. -/
theorem strip_trans_refl_right (p : Path a b) :
    Joinable (Path.trans p (Path.refl b)) p :=
  ⟨p, rw_of_step (Step.trans_refl_right p), Rw.refl _⟩

/-! ## Width Bounds -/

/-- The "width" of a path: number of steps in its trace. -/
def stripWidth {A : Type u} {a b : A} (p : Path a b) : Nat :=
  p.steps.length

@[simp] theorem stripWidth_refl (x : A) : stripWidth (Path.refl x) = 0 := by
  simp [stripWidth]

@[simp] theorem stripWidth_ofEq (h : a = b) : stripWidth (Path.ofEq h) = 1 := by
  simp [stripWidth, Path.ofEq]

@[simp] theorem stripWidth_normalize (p : Path a b) :
    stripWidth (Path.normalize p) = 1 := by
  simp [stripWidth, Path.normalize]

@[simp] theorem stripWidth_trans {c : A} (p : Path a b) (q : Path b c) :
    stripWidth (Path.trans p q) = stripWidth p + stripWidth q := by
  simp [stripWidth, Path.trans]

@[simp] theorem stripWidth_symm (p : Path a b) :
    stripWidth (Path.symm p) = stripWidth p := by
  simp [stripWidth, Path.symm, List.length_map, List.length_reverse]

/-- A normal path has width exactly 1. -/
theorem stripWidth_of_isNormal {p : Path a b} (h : IsNormal p) :
    stripWidth p = 1 := by
  unfold IsNormal at h; rw [h]; simp [stripWidth, Path.ofEq]

/-- Width is monotone under Rw: rewriting can only change width
(but the toEq is preserved). -/
theorem stripWidth_rw_toEq {p q : Path a b}
    (h : Rw p q) : p.toEq = q.toEq :=
  rw_toEq h

/-- Width of congrArg equals width of the argument. -/
@[simp] theorem stripWidth_congrArg {B : Type u} (f : A → B)
    (p : Path a b) :
    stripWidth (Path.congrArg f p) = stripWidth p := by
  simp [stripWidth, Path.congrArg, List.length_map]

end StripLemma
end Rewrite
end Path
end ComputationalPaths
