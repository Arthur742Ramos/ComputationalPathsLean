/-
# Confluence witnesses for LNDEQ rewrites

This module repackages the `rw_confluent` theorem from `Rw.lean` so that
critical-pair style arguments can cite explicit join objects.  The API mirrors
the presentation in the SAJL paper: given two reductions out of the same source
we produce a common successor together with the necessary `Rw` certificates.
-/

import ComputationalPaths.Path.Rewrite.LNDEQ
import ComputationalPaths.Path.Rewrite.Termination

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace Confluence

open LNDEQ

universe u

/-- Join data for two reductions. -/
structure Join {A : Type u} {a b : A}
    (p q : Path a b) where
  meet : Path a b
  left : Rw (A := A) (a := a) (b := b) p meet
  right : Rw (A := A) (a := a) (b := b) q meet

@[simp] def Join.rweq {A : Type u} {a b : A}
    {p q : Path a b} (J : Join (A := A) (a := a) (b := b) p q) :
    RwEq (A := A) (a := a) (b := b) p q :=
  rweq_trans (rweq_of_rw J.left) (rweq_symm (rweq_of_rw J.right))

@[simp] def Join.quot_eq {A : Type u} {a b : A}
    {p q : Path a b} (J : Join (A := A) (a := a) (b := b) p q) :
    (Quot.mk _ p : PathRwQuot A a b) = Quot.mk _ q :=
  Quot.sound J.rweq

@[simp] theorem join_refl {A : Type u} {a b : A} (p : Path a b) :
    Join (A := A) (a := a) (b := b) p p :=
  { meet := p, left := Rw.refl p, right := Rw.refl p }

/-- Join witnesses built from the canonical normal form. -/
@[simp] def of_rw {A : Type u} {a b : A}
    {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
    Join (A := A) (a := a) (b := b) q r :=
  { meet := Path.ofEq (A := A) (a := a) (b := b) p.toEq
    left := rw_to_canonical_of_rw (A := A) (a := a) (b := b)
      (p := p) (q := q) hq
    right := rw_to_canonical_of_rw (A := A) (a := a) (b := b)
      (p := p) (q := r) hr }

/-- Joining the targets of two single-step reductions. -/
@[simp] def of_steps {A : Type u} {a b : A}
    {p q r : Path a b} (hq : Step (A := A) (a := a) (b := b) p q)
    (hr : Step (A := A) (a := a) (b := b) p r) :
    Join (A := A) (a := a) (b := b) q r :=
  of_rw (A := A) (a := a) (b := b)
    (p := p) (q := q) (r := r)
    (Rw.step (A := A) (p := p) (q := q) hq)
    (Rw.step (A := A) (p := p) (q := r) hr)

namespace LNDEQ

/-- LNDEQ instantiations produce concrete join witnesses whenever their sources
agree. -/
@[simp] def Instantiation.join
    (i j : Instantiation)
    (h : i.p = j.p) :
    Join (A := _) (a := _) (b := _) i.q j.q := by
  subst h
  exact Confluence.of_steps (A := _) (a := _) (b := _)
    (p := i.p) (q := i.q) (r := j.q) i.step j.step

@[simp] theorem Instantiation.join_rweq
    (i j : Instantiation) (h : i.p = j.p) :
    RwEq (A := _) (a := _) (b := _) i.q j.q :=
  (Instantiation.join (i := i) (j := j) (h := h)).rweq

@[simp] theorem Instantiation.join_quot_eq
    (i j : Instantiation) (h : i.p = j.p) :
    (Quot.mk _ i.q : PathRwQuot _ _ _) = Quot.mk _ j.q :=
  (Instantiation.join (i := i) (j := j) (h := h)).quot_eq

end LNDEQ

namespace CriticalPairs

open LNDEQ.Builder

universe u

section ProdFst

variable {A : Type u} {B : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

/-- Critical pair between the two `fst` β-rules. -/
@[simp] def mx2_fst (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Join (A := A) (a := a₁) (b := a₂)
      (Builder.instMx2l1 (A := A) (B := B) (p := p) (q := q)).q
      (Builder.instMx2l2 (A := A) (B := B) (p := p) (q := q)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instMx2l1 (A := A) (B := B) (p := p) (q := q))
    (j := Builder.instMx2l2 (A := A) (B := B) (p := p) (q := q))
    rfl

end ProdFst

section ProdSnd

variable {A : Type u} {B : Type u}
variable {a : A} {b₁ b₂ : B}

/-- Critical pair witnessing that both `snd` β-rules agree when the left path is reflexive. -/
@[simp] def mx2_snd (q : Path b₁ b₂) :
    Join (A := B) (a := b₁) (b := b₂)
      (Builder.instMx2r1 (A := A) (B := B)
        (p := Path.refl (A := A) a) (q := q)).q
      (Builder.instMx2r2 (A := A) (B := B) (a := a) (q := q)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instMx2r1 (A := A) (B := B)
      (p := Path.refl (A := A) a) (q := q))
    (j := Builder.instMx2r2 (A := A) (B := B) (a := a) (q := q))
    rfl

end ProdSnd

section AssocUnits

variable {A : Type u} {a b c : A}

/-- Associativity overlaps with right-unit when the tail is reflexive. -/
@[simp] def tt_rrr (p : Path a b) (q : Path b c) :
    Join (A := A) (a := a) (b := c)
      (Builder.instTt (A := A) (p := p) (q := q) (r := Path.refl c)).q
      (Builder.instRrr (A := A)
        (p := Path.trans (A := A) (p := p) (q := q))).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instTt (A := A) (p := p) (q := q) (r := Path.refl c))
    (j := Builder.instRrr (A := A)
      (p := Path.trans (A := A) (p := p) (q := q)))
    rfl

/-- Associativity overlaps with left-unit when the head is reflexive. -/
@[simp] def tt_lrr (q : Path a b) (r : Path b c) :
    Join (A := A) (a := a) (b := c)
      (Builder.instTt (A := A) (p := Path.refl a) (q := q) (r := r)).q
      (Builder.instLrr (A := A)
        (p := Path.trans (A := A) (p := q) (q := r))).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instTt (A := A) (p := Path.refl a) (q := q) (r := r))
    (j := Builder.instLrr (A := A)
      (p := Path.trans (A := A) (p := q) (q := r)))
    rfl

end AssocUnits

section ContextCancellation

variable {A : Type u} {B : Type u}
variable (C : Context A B)
variable {a₁ a₂ : A}
variable {x y : B}

/-- Associativity overlaps with the left cancellation rule `ttsv`. -/
@[simp] def tt_ttsv
    (p : Path a₁ a₂) (v : Path (C.fill a₁) y) :
    Join (A := B) (a := C.fill a₁) (b := y)
      (Builder.instTt (A := B)
        (p := Context.map (A := A) (B := B) C p)
        (q := Context.map (A := A) (B := B) C (Path.symm p))
        (r := v)).q
      (Builder.instTtsv (A := A) (B := B)
        (C := C) (p := p) (v := v)).q := by
  classical
  let i₁ := Builder.instTt (A := B)
      (p := Context.map (A := A) (B := B) C p)
      (q := Context.map (A := A) (B := B) C (Path.symm p))
      (r := v)
  let i₂ := Builder.instTtsv (A := A) (B := B)
      (C := C) (p := p) (v := v)
  let shared :=
    Path.trans
      (Path.trans
        (Context.map (A := A) (B := B) C p)
        (Context.map (A := A) (B := B) C (Path.symm p)))
      v
  have h_assoc :
      Step (A := B) (a := C.fill a₁) (b := y)
        shared i₂.p := by
    simpa [shared, i₂, Builder.instTtsv]
      using Step.trans_assoc (A := B)
        (p := Context.map (A := A) (B := B) C p)
        (q := Context.map (A := A) (B := B) C (Path.symm p))
        (r := v)
  have h_left :
      Rw (A := B) (a := C.fill a₁) (b := y)
        shared i₁.q := by
    change Rw (A := B) (a := C.fill a₁) (b := y) i₁.p i₁.q
    exact Rw.step (A := B) (p := i₁.p) (q := i₁.q) i₁.step
  have h_right :
      Rw (A := B) (a := C.fill a₁) (b := y)
        shared i₂.q := by
    refine Rw.tail ?_ i₂.step
    refine Rw.tail (Rw.refl shared) ?_
    simpa using h_assoc
  exact of_rw (A := B) (a := C.fill a₁) (b := y)
    (p := shared) (q := i₁.q) (r := i₂.q) h_left h_right

/-- Associativity overlaps with the right cancellation rule `tstu`. -/
@[simp] def tt_tstu
    (p : Path a₁ a₂) (v : Path x (C.fill a₁)) :
    Join (A := B) (a := x) (b := C.fill a₂)
      (Builder.instTt (A := B)
        (p := v)
        (q := Context.map (A := A) (B := B) C p)
        (r := Context.map (A := A) (B := B) C (Path.symm p))).q
      (Builder.instTstu (A := A) (B := B)
        (C := C) (p := p) (v := v)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instTt (A := B)
      (p := v)
      (q := Context.map (A := A) (B := B) C p)
      (r := Context.map (A := A) (B := B) C (Path.symm p)))
    (j := Builder.instTstu (A := A) (B := B)
      (C := C) (p := p) (v := v))
    rfl

end ContextCancellation

section ContextSubstitution

variable {A : Type u} {B : Type u}
variable (C : Context A B)
variable {a₁ a₂ : A}

/-- `tsbll` overlaps with the reflexive `slr` rule when the left proof is
reflexive, yielding identical sources and hence a direct join witness. -/
@[simp] def tsbll_slr (p : Path a₁ a₂) :
    Join (A := B) (a := C.fill a₁) (b := C.fill a₂)
      (Builder.instTsbll (A := A) (B := B) (C := C)
        (r := Path.refl (C.fill a₁)) (p := p)).q
      (Builder.instSlr (A := A) (B := B) (C := C) (p := p)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instTsbll (A := A) (B := B) (C := C)
      (r := Path.refl (C.fill a₁)) (p := p))
    (j := Builder.instSlr (A := A) (B := B) (C := C) (p := p))
    rfl

/-- The right-sided counterparts `tsbrl` and `srr` also overlap when the
trailing witness is reflexive, so they admit the same canonical join. -/
@[simp] def tsbrl_srr (p : Path a₁ a₂) :
    Join (A := B) (a := C.fill a₁) (b := C.fill a₂)
      (Builder.instTsbrl (A := A) (B := B) (C := C)
        (p := p) (t := Path.refl (C.fill a₂))).q
      (Builder.instSrr (A := A) (B := B) (C := C) (p := p)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instTsbrl (A := A) (B := B) (C := C)
      (p := p) (t := Path.refl (C.fill a₂)))
    (j := Builder.instSrr (A := A) (B := B) (C := C) (p := p))
    rfl

/-- Reflexive witnesses trigger both `srsr` and `srrrr` reductions from the same source. -/
@[simp] def srsr_srrrr {a : A} {y : B}
    (t : Path (C.fill a) y) :
    Join (A := B) (a := y) (b := C.fill a)
      (Builder.instSrsr (A := A) (B := B) (C := C)
        (a₁ := a) (a₂ := a)
        (p := Path.refl a) (t := t)).q
      (Builder.instSrrrr (A := A) (B := B) (C := C)
        (a₁ := a) (a₂ := a)
        (p := Path.refl a) (t := t)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instSrsr (A := A) (B := B) (C := C)
      (a₁ := a) (a₂ := a)
      (p := Path.refl a) (t := t))
    (j := Builder.instSrrrr (A := A) (B := B) (C := C)
      (a₁ := a) (a₂ := a)
      (p := Path.refl a) (t := t))
    rfl

end ContextSubstitution

section SymmetricCancellation

variable {A : Type u} {B : Type u}
variable (C : Context A B)
variable {x : B} {a₁ a₂ : A}
variable (r : Path x (C.fill a₁)) (p : Path a₁ a₂)

/-- Symmetry distributes over both the associativity rule (`stss`) and the
contexted substitution rule (`ssbl`).  When instantiated with matching
arguments the two reductions share a source, giving a critical-pair join. -/
@[simp] def stss_ssbl :
    Join (A := B) (a := C.fill a₂) (b := x)
      (Builder.instStss (A := B)
        (p := r)
        (q := Context.map (A := A) (B := B) C p)).q
      (Builder.instSsbl (A := A) (B := B) (C := C)
        (r := r) (p := p)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instStss (A := B)
      (p := r)
      (q := Context.map (A := A) (B := B) C p))
    (j := Builder.instSsbl (A := A) (B := B) (C := C)
      (r := r) (p := p))
    rfl

@[simp] def stss_ssbr
    {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
    Join (A := B) (a := y) (b := C.fill a₁)
      (Builder.instStss (A := B)
        (p := Context.map (A := A) (B := B) C p)
        (q := t)).q
      (Builder.instSsbr (A := A) (B := B) (C := C)
        (p := p) (t := t)).q := by
  refine LNDEQ.Instantiation.join
    (i := Builder.instStss (A := B)
      (p := Context.map (A := A) (B := B) C p)
      (q := t))
    (j := Builder.instSsbr (A := A) (B := B) (C := C)
      (p := p) (t := t))
    rfl

end SymmetricCancellation

end CriticalPairs

end Confluence
end Rewrite
end Path
end ComputationalPaths
