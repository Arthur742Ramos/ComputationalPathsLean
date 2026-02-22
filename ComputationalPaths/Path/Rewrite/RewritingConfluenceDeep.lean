/-
# Deep Confluence for Rewriting: Newman, Diamond, Church-Rosser, Word Problem

Canonical entry-point for confluence theory in ComputationalPaths.Rewriting.
Re-exports the abstract infrastructure from ComputationalPaths.Path.Rewrite.ConfluenceDeep
and adds Word Problem decidability for terminating confluent systems.

## Main Results

- `RTC`, `Confluent`, `LocallyConfluent`, `Diamond` — abstract ARS definitions
- `newman_lemma` — Newman's Lemma: WF + local confluence ⟹ confluence
- `diamond_lemma_terminating` — Diamond Lemma for terminating systems
- `church_rosser_rweq` — Church-Rosser: confluence ⟹ RwEq has common reduct
- `eq_closure_same_nf` — Word Problem: equivalent terms have same normal form
- `path_word_problem_toEq` — Path-level: normalisation decides toEq equality
- All proofs use Path / Step / Rw / RwEq. No sorry / admit.
-/

import ComputationalPaths.Path.Rewrite.ConfluenceDeep
namespace ComputationalPaths
namespace Rewriting
namespace ConfluenceDeep

open ComputationalPaths.Path.Confluence
open ComputationalPaths.Path

universe u

/-! ## Re-export core definitions -/

/-- Newman's Lemma (re-export): well-founded + locally confluent ⟹ confluent -/
theorem newmans_lemma {α : Type u} {R : α → α → Prop}
    (wf : WellFounded (fun y x => R x y))
    (hlc : LocallyConfluent R) :
    Confluent R :=
  newman_lemma wf hlc

/-- Diamond Lemma (re-export): well-founded + diamond ⟹ confluent -/
theorem diamond_lemma {α : Type u} {R : α → α → Prop}
    (wf : WellFounded (fun y x => R x y))
    (hd : Diamond R) :
    Confluent R :=
  diamond_lemma_terminating wf hd

/-! ## Word Problem decidability for terminating confluent systems -/

/-- A normalisation function: given a term, computes its normal form
    together with a proof of reduction. -/
structure NormalisationFn {α : Type u} (R : α → α → Prop) where
  nf : α → α
  reduces : ∀ a, RTC R a (nf a)
  is_nf : ∀ a b, ¬ R (nf a) b

/-- The symmetric-transitive closure (equational theory). -/
inductive EqClosure {α : Type u} (R : α → α → Prop) : α → α → Prop
  | fwd {a b} : R a b → EqClosure R a b
  | bwd {a b} : R b a → EqClosure R a b
  | refl (a) : EqClosure R a a
  | trans {a b c} : EqClosure R a b → EqClosure R b c → EqClosure R a c

private theorem rtc_nf_eq {α : Type u} {R : α → α → Prop}
    (conf : Confluent R) (norm : NormalisationFn R)
    (a b : α) (hab : RTC R a b) :
    norm.nf a = norm.nf b := by
  obtain ⟨d, hd1, hd2⟩ := conf a (norm.nf a) (norm.nf b)
    (norm.reduces a) (RTC.trans hab (norm.reduces b))
  rcases RTC.cases_head hd1 with h1 | ⟨c, hc, _⟩
  · rcases RTC.cases_head hd2 with h2 | ⟨c, hc, _⟩
    · exact h2.symm ▸ h1
    · exact absurd hc (norm.is_nf b c)
  · exact absurd hc (norm.is_nf a c)

/-- **Word Problem**: equivalent terms in a confluent system have the same
    normal form. Combined with decidable equality on normal forms, this
    decides the equational theory. -/
theorem eq_closure_same_nf {α : Type u} {R : α → α → Prop}
    (conf : Confluent R) (norm : NormalisationFn R)
    {a b : α} (h : EqClosure R a b) :
    norm.nf a = norm.nf b := by
  induction h with
  | fwd hr => exact rtc_nf_eq conf norm _ _ (RTC.single hr)
  | bwd hr => exact (rtc_nf_eq conf norm _ _ (RTC.single hr)).symm
  | refl _ => rfl
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

/-- **Word Problem (complete characterisation)**: two terms are in the
    equational theory of R iff they have the same normal form. -/
theorem word_problem_iff {α : Type u} {R : α → α → Prop}
    (conf : Confluent R) (norm : NormalisationFn R)
    (a b : α) :
    EqClosure R a b ↔ norm.nf a = norm.nf b := by
  constructor
  · exact eq_closure_same_nf conf norm
  · intro h
    have rtc_to_eqcl : ∀ x y, RTC R x y → EqClosure R x y := by
      intro x y hxy
      induction hxy with
      | refl _ => exact EqClosure.refl _
      | step hr _ ih => exact EqClosure.trans (EqClosure.fwd hr) ih
    have rtc_to_eqcl_sym : ∀ x y, RTC R x y → EqClosure R y x := by
      intro x y hxy
      induction hxy with
      | refl _ => exact EqClosure.refl _
      | step hr _ ih => exact EqClosure.trans ih (EqClosure.bwd hr)
    have ha := rtc_to_eqcl _ _ (norm.reduces a)
    have hb_sym := rtc_to_eqcl_sym _ _ (norm.reduces b)
    have key : EqClosure R (norm.nf a) (norm.nf b) := by
      rw [h]; exact EqClosure.refl _
    exact EqClosure.trans ha (EqClosure.trans key hb_sym)

/-! ## Path-level Word Problem (via toEq) -/

section PathWordProblem

variable {A : Type u} {a b : A}

/-- Path-level normalisation function for Step. -/
structure PathNormFn (a b : A) where
  nf : ComputationalPaths.Path a b → ComputationalPaths.Path a b
  reduces : ∀ p : ComputationalPaths.Path a b, ComputationalPaths.Path.Rw p (nf p)
  is_nf : ∀ (p q : ComputationalPaths.Path a b), ¬ ComputationalPaths.Path.Step (nf p) q

/-- **Path Word Problem (toEq version)**: normalisation preserves toEq,
    so two paths have equal toEq iff their normal forms do. -/
theorem path_word_problem_toEq
    (norm : PathNormFn a b)
    (p q : ComputationalPaths.Path a b) :
    (norm.nf p).toEq = (norm.nf q).toEq ↔
      p.toEq = q.toEq := by
  constructor
  · intro h
    have hp := ComputationalPaths.Path.rw_toEq (norm.reduces p)
    have hq := ComputationalPaths.Path.rw_toEq (norm.reduces q)
    calc p.toEq = (norm.nf p).toEq := hp
      _ = (norm.nf q).toEq := h
      _ = q.toEq := hq.symm
  · intro h
    have hp := ComputationalPaths.Path.rw_toEq (norm.reduces p)
    have hq := ComputationalPaths.Path.rw_toEq (norm.reduces q)
    calc (norm.nf p).toEq = p.toEq := hp.symm
      _ = q.toEq := h
      _ = (norm.nf q).toEq := hq

end PathWordProblem

end ConfluenceDeep
end Rewriting
end ComputationalPaths
