/-
# The essential image of derivation erasure

`RawErasure` proves that evaluation factors through erasure and that atoms round
trip.  Neither statement says which label-free programs are *reached*.  The
target grammar `QuotProgram` is deliberately permissive: its `congr` constructor
quantifies over every endofunction of the term model, whereas erasure only ever
supplies a function induced by a source frame.  Erasure is therefore not
surjective onto `QuotProgram`, and claims of the form "erasure identifies the two
program languages" are too strong.

This module pins the image down exactly.  `FramedAt t u q` is the sub-syntax of
label-free programs whose atoms are quotient soundness applied to a source
definitional equality and whose congruences are frame-induced.  Then

* `erase_framedAt` — every erased program is framed;
* `framedAt_surjective` — every framed program is an erased program;
* `erase_congr_frame_induced` — every congruence in the image is `Frame.map C` for an
  actual source frame, so erasure invents no congruence outside that family.

Together these characterize the essential image, which is the statement the
factorization theorem needs in order to be about a genuine target language.
-/

import ComputationalPaths.Path.TypeTheory.RawErasure

namespace ComputationalPaths
namespace Path
namespace TypeTheory
namespace RawMLTT

/-- Label-free programs in the essential image of erasure, indexed by the source
expressions they connect.  Atoms come from source definitional equalities and
congruences from source frames; no other quotient program is framed. -/
inductive FramedAt {n : Nat} :
    (t u : Expr n) → QuotProgram (denote t) (denote u) → Prop where
  | atom {t u : Expr n} (h : DefEq t u) :
      FramedAt t u (QuotProgram.atom (Quotient.sound h))
  | refl (t : Expr n) :
      FramedAt t t (QuotProgram.refl (denote t))
  | symm {t u : Expr n} {p : QuotProgram (denote t) (denote u)} :
      FramedAt t u p → FramedAt u t p.symm
  | trans {t u v : Expr n} {p : QuotProgram (denote t) (denote u)}
      {q : QuotProgram (denote u) (denote v)} :
      FramedAt t u p → FramedAt u v q → FramedAt t v (p.trans q)
  | congr (C : Frame n) {t u : Expr n}
      {p : QuotProgram (denote t) (denote u)} :
      FramedAt t u p →
      FramedAt (C.plug t) (C.plug u) (p.congr (Frame.map C))

/-- **Erasure lands in the framed fragment.**  In particular it never produces a
congruence by an endofunction that is not induced by a source frame. -/
theorem erase_framedAt {n : Nat} {t u : Expr n} (p : IdentityExpr t u) :
    FramedAt t u (erase p) := by
  induction p with
  | atom h => exact FramedAt.atom h
  | refl t => exact FramedAt.refl t
  | symm _ ih => exact FramedAt.symm ih
  | trans _ _ ih₁ ih₂ => exact FramedAt.trans ih₁ ih₂
  | congr C _ ih => exact FramedAt.congr C ih

/-- **Erasure is surjective onto the framed fragment.**  Every framed label-free
program is the erasure of a source identity program. -/
theorem framedAt_surjective {n : Nat} {t u : Expr n}
    {q : QuotProgram (denote t) (denote u)} (hq : FramedAt t u q) :
    ∃ p : IdentityExpr t u, erase p = q := by
  induction hq with
  | atom h => exact ⟨IdentityExpr.atom h, rfl⟩
  | refl t => exact ⟨IdentityExpr.refl t, rfl⟩
  | symm _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨IdentityExpr.symm p, by simp [erase, hp]⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨p, hp⟩ := ih₁
      obtain ⟨r, hr⟩ := ih₂
      exact ⟨IdentityExpr.trans p r, by simp [erase, hp, hr]⟩
  | congr C _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨IdentityExpr.congr C p, by simp [erase, hp]⟩

/-- **The image is exactly the framed fragment.** -/
theorem erase_image_eq_framedAt {n : Nat} {t u : Expr n}
    (q : QuotProgram (denote t) (denote u)) :
    (∃ p : IdentityExpr t u, erase p = q) ↔ FramedAt t u q := by
  constructor
  · rintro ⟨p, rfl⟩
    exact erase_framedAt p
  · exact framedAt_surjective

/-- Erasure only ever applies frame-induced congruences: this is the precise
sense in which it "invents nothing".  The permissive endofunction argument of
`QuotProgram.congr` is never exercised outside the family `Frame.map C`, so the
image is a proper sub-syntax of the target grammar. -/
theorem erase_congr_frame_induced {n : Nat} {t u : Expr n} (C : Frame n)
    (p : IdentityExpr t u) :
    erase (IdentityExpr.congr C p) = (erase p).congr (Frame.map C) := rfl

/-- Likewise every erased atom is quotient soundness applied to a source
definitional equality, so no atom of the image records anything else. -/
theorem erase_atom_is_sound {n : Nat} {t u : Expr n} (h : DefEq t u) :
    erase (IdentityExpr.atom h) = QuotProgram.atom (Quotient.sound h) := rfl

end RawMLTT
end TypeTheory
end Path
end ComputationalPaths
