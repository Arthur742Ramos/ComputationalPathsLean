/-
# Confluence witnesses for LNDEQ rewrites

This module packages join data for multi-step rewrites on computational `Path`s.
Concrete join witnesses are provided in `ConfluenceProof.lean`, which derives
`HasJoinOfRw` from termination and local confluence assumptions. The API mirrors
the presentation in the SAJL paper: given two reductions out of the same source
we produce a common successor together with the necessary `Rw` certificates.
-/

import ComputationalPaths.Path.Rewrite.LNDEQ
import ComputationalPaths.Path.Rewrite.Quot

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

@[simp] def join_refl {A : Type u} {a b : A} (p : Path a b) :
    Join (A := A) (a := a) (b := b) p p :=
  { meet := p, left := Rw.refl p, right := Rw.refl p }

/-- **Confluence interface**: Given two rewrites from a common source, their
targets can be joined. This is parameterized as a typeclass. At the `Path`
level, it is NOT globally instantiated (since `Path` has distinct normal
forms with different step lists). For the genuine algebraic confluence on
abstract `Expr` syntax, see `GroupoidConfluence.confluence`. -/
class HasJoinOfRw : Type (u + 1) where
  join_of_rw {A : Type u} {a b : A}
      {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
      Join (A := A) (a := a) (b := b) q r

@[simp] def join_of_rw [h : HasJoinOfRw.{u}]
    {A : Type u} {a b : A} {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
    Join (A := A) (a := a) (b := b) q r :=
  h.join_of_rw (hq := hq) (hr := hr)

noncomputable section

variable [HasJoinOfRw.{u}]

/-- Join witnesses built from confluence of rewrites. -/
@[simp] def of_rw {A : Type u} {a b : A}
    {p q r : Path a b} (hq : Rw p q) (hr : Rw p r) :
    Join (A := A) (a := a) (b := b) q r :=
  join_of_rw hq hr

/-- Joining the targets of two single-step reductions. -/
@[simp] def of_steps {A : Type u} {a b : A}
    {p q r : Path a b} (hq : Step (A := A) (a := a) (b := b) p q)
    (hr : Step (A := A) (a := a) (b := b) p r) :
    Join (A := A) (a := a) (b := b) q r :=
  of_rw (A := A) (a := a) (b := b)
    (p := p) (q := q) (r := r)
    (rw_of_step (A := A) hq)
    (rw_of_step (A := A) hr)

namespace LNDEQ

/-- LNDEQ instantiations produce concrete join witnesses whenever their sources
agree.  This version takes explicit type parameters to avoid heterogeneous equality issues. -/
@[simp] def Instantiation.join
    {A : Type u} {a b : A}
    {p q r : Path a b}
    (step₁ : Step (A := A) p q)
    (step₂ : Step (A := A) p r) :
    Join (A := A) (a := a) (b := b) q r :=
  Confluence.of_steps (A := A) (a := a) (b := b)
    (p := p) (q := q) (r := r) step₁ step₂

@[simp] theorem Instantiation.join_rweq
    {A : Type u} {a b : A}
    {p q r : Path a b}
    (step₁ : Step (A := A) p q)
    (step₂ : Step (A := A) p r) :
    RwEq (A := A) (a := a) (b := b) q r :=
  (Instantiation.join (A := A) (a := a) (b := b)
    (p := p) (q := q) (r := r)
    step₁ step₂).rweq

@[simp] theorem Instantiation.join_quot_eq
    {A : Type u} {a b : A}
    {p q r : Path a b}
    (step₁ : Step (A := A) p q)
    (step₂ : Step (A := A) p r) :
    (Quot.mk _ q : PathRwQuot A a b) = Quot.mk _ r :=
  (Instantiation.join (A := A) (a := a) (b := b)
    (p := p) (q := q) (r := r)
    step₁ step₂).quot_eq

end LNDEQ

namespace CriticalPairs

open LNDEQ.Builder

section ProdFst

variable {A : Type u} {B : Type u}
variable {a₁ a₂ : A} {b₁ b₂ : B}

/-- Critical pair between the two `fst` β-rules. -/
@[simp] def mx2_fst (p : Path a₁ a₂) (q : Path b₁ b₂) :
    Join (A := A) (a := a₁) (b := a₂)
      (Builder.instMx2l1 (A := A) (B := B) (p := p) (q := q)).q
      (Builder.instMx2l2 (A := A) (B := B) (p := p) (q := q)).q :=
  LNDEQ.Instantiation.join
    (Builder.instMx2l1 (A := A) (B := B) (p := p) (q := q)).step
    (Builder.instMx2l2 (A := A) (B := B) (p := p) (q := q)).step

end ProdFst

section ProdSnd

variable {A : Type u} {B : Type u}
variable {a : A} {b₁ b₂ : B}

/-- Critical pair witnessing that both `snd` β-rules agree when the left path is reflexive. -/
@[simp] def mx2_snd (q : Path b₁ b₂) :
    Join (A := B) (a := b₁) (b := b₂)
      (Builder.instMx2r1 (A := A) (B := B)
        (p := Path.refl (A := A) a) (q := q)).q
      (Builder.instMx2r2 (A := A) (B := B) (a := a) (q := q)).q :=
  LNDEQ.Instantiation.join
    (Builder.instMx2r1 (A := A) (B := B) (p := Path.refl (A := A) a) (q := q)).step
    (Builder.instMx2r2 (A := A) (B := B) (a := a) (q := q)).step

end ProdSnd

section AssocUnits

variable {A : Type u} {a b c : A}

/-- Associativity overlaps with right-unit when the tail is reflexive. -/
@[simp] def tt_rrr (p : Path a b) (q : Path b c) :
    Join (A := A) (a := a) (b := c)
      (Builder.instTt (A := A) (p := p) (q := q) (r := Path.refl c)).q
      (Builder.instRrr (A := A)
        (p := Path.trans (A := A) (p := p) (q := q))).q :=
  LNDEQ.Instantiation.join
    (Builder.instTt (A := A) (p := p) (q := q) (r := Path.refl c)).step
    (Builder.instRrr (A := A) (p := Path.trans (A := A) (p := p) (q := q))).step

/-- Associativity overlaps with left-unit when the head is reflexive. -/
@[simp] def tt_lrr (q : Path a b) (r : Path b c) :
    Join (A := A) (a := a) (b := c)
      (Builder.instTt (A := A) (p := Path.refl a) (q := q) (r := r)).q
      (Builder.instLrr (A := A)
        (p := Path.trans (A := A) (p := q) (q := r))).q :=
  LNDEQ.Instantiation.join
    (Builder.instTt (A := A) (p := Path.refl a) (q := q) (r := r)).step
    (Builder.instLrr (A := A) (p := Path.trans (A := A) (p := q) (q := r))).step

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
    exact rw_of_step (A := B) i₁.step
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
    Join (A := B) (a := x) (b := C.fill a₁)
      (Builder.instTt (A := B)
        (p := v)
        (q := Context.map (A := A) (B := B) C p)
        (r := Context.map (A := A) (B := B) C (Path.symm p))).q
      (Builder.instTstu (A := A) (B := B)
        (C := C) (p := p) (v := v)).q :=
  LNDEQ.Instantiation.join
    (Builder.instTt (A := B)
      (p := v)
      (q := Context.map (A := A) (B := B) C p)
      (r := Context.map (A := A) (B := B) C (Path.symm p))).step
    (Builder.instTstu (A := A) (B := B) (C := C) (p := p) (v := v)).step

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
      (Builder.instSlr (A := A) (B := B) (C := C) (p := p)).q :=
  LNDEQ.Instantiation.join
    (Builder.instTsbll (A := A) (B := B) (C := C)
      (r := Path.refl (C.fill a₁)) (p := p)).step
    (Builder.instSlr (A := A) (B := B) (C := C) (p := p)).step

/-- The right-sided counterparts `tsbrl` and `srr` also overlap when the
trailing witness is reflexive, so they admit the same canonical join. -/
@[simp] def tsbrl_srr (p : Path a₁ a₂) :
    Join (A := B) (a := C.fill a₁) (b := C.fill a₂)
      (Builder.instTsbrl (A := A) (B := B) (C := C)
        (p := p) (t := Path.refl (C.fill a₂))).q
      (Builder.instSrr (A := A) (B := B) (C := C) (p := p)).q :=
  LNDEQ.Instantiation.join
    (Builder.instTsbrl (A := A) (B := B) (C := C)
      (p := p) (t := Path.refl (C.fill a₂))).step
    (Builder.instSrr (A := A) (B := B) (C := C) (p := p)).step

/-- Reflexive witnesses trigger both `srsr` and `srrrr` reductions from the same source. -/
@[simp] def srsr_srrrr {a : A} {y : B}
    (t : Path (C.fill a) y) :
    Join (A := B) (a := C.fill a) (b := y)
      (Builder.instSrsr (A := A) (B := B) (C := C)
        (a₁ := a) (a₂ := a)
        (p := Path.refl a) (t := t)).q
      (Builder.instSrrrr (A := A) (B := B) (C := C)
        (a₁ := a) (a₂ := a)
        (p := Path.refl a) (t := t)).q :=
  LNDEQ.Instantiation.join
    (Builder.instSrsr (A := A) (B := B) (C := C)
      (a₁ := a) (a₂ := a)
      (p := Path.refl a) (t := t)).step
    (Builder.instSrrrr (A := A) (B := B) (C := C)
      (a₁ := a) (a₂ := a)
      (p := Path.refl a) (t := t)).step

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
        (r := r) (p := p)).q :=
  LNDEQ.Instantiation.join
    (Builder.instStss (A := B) (p := r)
      (q := Context.map (A := A) (B := B) C p)).step
    (Builder.instSsbl (A := A) (B := B) (C := C) (r := r) (p := p)).step

@[simp] def stss_ssbr
    {a₁ a₂ : A} {y : B}
    (p : Path a₁ a₂) (t : Path (C.fill a₂) y) :
    Join (A := B) (a := y) (b := C.fill a₁)
      (Builder.instStss (A := B)
        (p := Context.map (A := A) (B := B) C p)
        (q := t)).q
      (Builder.instSsbr (A := A) (B := B) (C := C)
        (p := p) (t := t)).q :=
  LNDEQ.Instantiation.join
    (Builder.instStss (A := B)
      (p := Context.map (A := A) (B := B) C p)
      (q := t)).step
    (Builder.instSsbr (A := A) (B := B) (C := C) (p := p) (t := t)).step

end SymmetricCancellation

section Sigma

variable {A : Type u}

variable {B : A → Type u}

variable {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}

@[simp] def mxsigma_fst_eta
    (p : Path (Sigma.mk a₁ b₁) (Sigma.mk a₂ b₂)) :
    Join (A := A) (a := a₁) (b := a₂)
      (Builder.instMxsigmaFst (A := A) (B := B)
        (p := Path.sigmaFst (B := B) p)
        (q := Path.sigmaSnd (B := B) p)).q
      (Path.congrArg Sigma.fst p) := by
  classical
  let i := Builder.instMxsigmaFst (A := A) (B := B)
      (p := Path.sigmaFst (B := B) p)
      (q := Path.sigmaSnd (B := B) p)
  have hbeta : Step (A := A)
      i.p i.q := i.step
  let C : Context (Sigma B) A := ⟨Sigma.fst⟩
  have heta : Step (A := A)
      i.p (Path.congrArg Sigma.fst p) := by
    simpa [i]
      using Step.context_congr (A := Sigma B) (B := A) (C := C)
        (p := Path.sigmaMk (B := B)
          (Path.sigmaFst (B := B) p) (Path.sigmaSnd (B := B) p))
        (q := p)
        (Step.sigma_eta (A := A) (B := B) (p := p))
  exact of_steps (A := A) (a := a₁) (b := a₂)
    (p := i.p) (q := i.q) (r := Path.congrArg Sigma.fst p)
    hbeta heta

end Sigma

end CriticalPairs

/-! ## Structural properties of Join -/

/-- Join is symmetric: if p and q join, then q and p join. -/
@[simp] def Join.symm {A : Type u} {a b : A}
    {p q : Path a b} (J : Join (A := A) (a := a) (b := b) p q) :
    Join (A := A) (a := a) (b := b) q p :=
  { meet := J.meet, left := J.right, right := J.left }

/-- Join.symm is an involution. -/
theorem Join.symm_symm {A : Type u} {a b : A}
    {p q : Path a b} (J : Join (A := A) (a := a) (b := b) p q) :
    J.symm.symm = J := by
  sorry

/-- Join of identical paths yields the same quot class. -/
theorem Join.refl_quot {A : Type u} {a b : A}
    (p : Path a b) :
    (join_refl p).quot_eq = rfl := by
  sorry

/-- Join is transitive: if p joins q and q joins r, then p joins r. -/
theorem Join.trans_join {A : Type u} {a b : A}
    {p q r : Path a b}
    (J₁ : Join (A := A) (a := a) (b := b) p q)
    (J₂ : Join (A := A) (a := a) (b := b) q r) :
    ∃ (s : Path a b), Rw (A := A) (a := a) (b := b) p s ∧ Rw (A := A) (a := a) (b := b) r s := by
  sorry

/-- The meet of a reflexive join is the path itself. -/
theorem join_refl_meet {A : Type u} {a b : A}
    (p : Path a b) :
    (join_refl p).meet = p := by
  sorry

/-- Symmetric join induces the symmetric RwEq. -/
theorem Join.symm_rweq {A : Type u} {a b : A}
    {p q : Path a b} (J : Join (A := A) (a := a) (b := b) p q) :
    J.symm.rweq = rweq_symm J.rweq := by
  sorry

/-- of_rw with Rw.refl produces a join with the original as meet. -/
theorem of_rw_refl_left {A : Type u} {a b : A}
    {p q : Path a b} (hr : Rw (A := A) (a := a) (b := b) p q) :
    (of_rw (Rw.refl p) hr).meet = q := by
  sorry

/-- of_rw with Rw.refl on right produces a join with the original as meet. -/
theorem of_rw_refl_right {A : Type u} {a b : A}
    {p q : Path a b} (hq : Rw (A := A) (a := a) (b := b) p q) :
    (of_rw hq (Rw.refl p)).meet = q := by
  sorry

/-- Join quot_eq is transitive via Eq.trans. -/
theorem Join.quot_eq_trans {A : Type u} {a b : A}
    {p q r : Path a b}
    (J₁ : Join (A := A) (a := a) (b := b) p q)
    (J₂ : Join (A := A) (a := a) (b := b) q r) :
    (Quot.mk _ p : PathRwQuot A a b) = Quot.mk _ r := by
  sorry

/-- Join rweq is sound for the quotient: rweq implies quotient equality. -/
theorem Join.rweq_sound {A : Type u} {a b : A}
    {p q : Path a b} (J : Join (A := A) (a := a) (b := b) p q) :
    ∀ (f : Path a b → Path a b → Prop),
      (∀ x y, RwEq x y → f x y) → f p q := by
  sorry

/-- Two joins from the same source have equivalent meets up to Rw. -/
theorem Join.meets_rweq {A : Type u} {a b : A}
    {p q r : Path a b}
    (J₁ : Join (A := A) (a := a) (b := b) p q)
    (J₂ : Join (A := A) (a := a) (b := b) p r) :
    RwEq (A := A) (a := a) (b := b) J₁.meet J₂.meet := by
  sorry

end

end Confluence
end Rewrite
end Path
end ComputationalPaths
