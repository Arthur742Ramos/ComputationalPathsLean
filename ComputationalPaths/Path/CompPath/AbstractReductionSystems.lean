/-
# Abstract Reduction Systems via Computational Paths

Formalizes Abstract Reduction Systems (ARS): multi-step reductions,
confluence, Church-Rosser, termination, Newman's lemma, parallel reduction.

## References

- Baader & Nipkow, "Term Rewriting and All That" (1998)
- Terese, "Term Rewriting Systems" (2003)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.CompPath.ARS

open ComputationalPaths.Path

universe u

variable {A : Type u}

/-! ## Multi-step (reflexive-transitive closure) -/

inductive Star (step : A → A → Prop) : A → A → Prop where
  | refl : Star step a a
  | cons : step a b → Star step b c → Star step a c

namespace Star
variable {step : A → A → Prop}

theorem single {a b : A} (s : step a b) : Star step a b := .cons s .refl

theorem append {a b c : A} (h1 : Star step a b) (h2 : Star step b c) :
    Star step a c := by
  induction h1 with
  | refl => exact h2
  | cons s _ ih => exact .cons s (ih h2)
end Star

/-! ## Conversion -/

inductive Conv (step : A → A → Prop) : A → A → Prop where
  | refl : Conv step a a
  | fwd : step a b → Conv step b c → Conv step a c
  | bwd : step b a → Conv step b c → Conv step a c

namespace Conv
variable {step : A → A → Prop}

theorem append {a b c : A} (h1 : Conv step a b) (h2 : Conv step b c) :
    Conv step a c := by
  induction h1 with
  | refl => exact h2
  | fwd s _ ih => exact .fwd s (ih h2)
  | bwd s _ ih => exact .bwd s (ih h2)

theorem flip {a b : A} (h : Conv step a b) : Conv step b a := by
  induction h with
  | refl => exact .refl
  | fwd s _ ih => exact ih.append (.bwd s .refl)
  | bwd s _ ih => exact ih.append (.fwd s .refl)

theorem ofStar {a b : A} (h : Star step a b) : Conv step a b := by
  induction h with
  | refl => exact .refl
  | cons s _ ih => exact .fwd s ih
end Conv

/-! ## Properties -/

noncomputable def Diamond (step : A → A → Prop) :=
  ∀ {a b c : A}, step a b → step a c → ∃ d, step b d ∧ step c d

noncomputable def WCR (step : A → A → Prop) :=
  ∀ {a b c : A}, step a b → step a c → ∃ d, Star step b d ∧ Star step c d

noncomputable def CR (step : A → A → Prop) :=
  ∀ {a b c : A}, Star step a b → Star step a c → ∃ d, Star step b d ∧ Star step c d

noncomputable def ChurchRosser (step : A → A → Prop) :=
  ∀ {a b : A}, Conv step a b → ∃ c, Star step a c ∧ Star step b c

noncomputable def SemiCR (step : A → A → Prop) :=
  ∀ {a b c : A}, step a b → Star step a c → ∃ d, Star step b d ∧ Star step c d

noncomputable def NF (step : A → A → Prop) (a : A) := ∀ b, ¬step a b

noncomputable def SN (step : A → A → Prop) := WellFounded (fun b a => step a b)

/-! ## Strip Lemma -/

theorem strip {step : A → A → Prop} (hD : Diamond step)
    {a b c : A} (sab : step a b) (hac : Star step a c) :
    ∃ d, Star step b d ∧ Star step c d := by
  revert b
  induction hac with
  | refl =>
    intro b sab
    exact ⟨b, .refl, Star.single sab⟩
  | cons sac _hcc ih =>
    intro b sab
    obtain ⟨d', hbd', hmidd'⟩ := hD sab sac
    obtain ⟨e, hd'e, hce⟩ := ih hmidd'
    exact ⟨e, Star.cons hbd' hd'e, hce⟩

/-! ## Diamond ⟹ Confluence -/

theorem diamond_cr {step : A → A → Prop} (hD : Diamond step) :
    CR step := by
  intro a b c hab hac
  revert c
  induction hab with
  | refl => intro c hac; exact ⟨c, hac, .refl⟩
  | cons sab' _hbc ih =>
    intro c hac
    obtain ⟨d, hbd, hacd⟩ := strip hD sab' hac
    obtain ⟨e, hbe, hde⟩ := ih hbd
    exact ⟨e, hbe, Star.append hacd hde⟩

/-! ## Confluence ↔ Church-Rosser -/

theorem cr_church_rosser {step : A → A → Prop} (hC : CR step) :
    ChurchRosser step := by
  intro a b hab
  induction hab with
  | refl => exact ⟨_, Star.refl, Star.refl⟩
  | fwd s _ ih =>
    obtain ⟨d, hd1, hd2⟩ := ih
    exact ⟨d, Star.cons s hd1, hd2⟩
  | bwd s _ ih =>
    obtain ⟨d, hd1, hd2⟩ := ih
    obtain ⟨e, he1, he2⟩ := hC (Star.single s) hd1
    exact ⟨e, he1, Star.append hd2 he2⟩

theorem church_rosser_cr {step : A → A → Prop} (hCR : ChurchRosser step) :
    CR step := by
  intro a b c hab hac
  exact hCR (Conv.append (Conv.flip (Conv.ofStar hab)) (Conv.ofStar hac))

theorem diamond_church_rosser {step : A → A → Prop} (hD : Diamond step) :
    ChurchRosser step := cr_church_rosser (diamond_cr hD)

theorem diamond_wcr {step : A → A → Prop} (hD : Diamond step) : WCR step := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hD hab hac
  exact ⟨d, Star.single hbd, Star.single hcd⟩

/-! ## Semi-Confluence ↔ Confluence -/

theorem semi_to_cr {step : A → A → Prop} (hSC : SemiCR step) : CR step := by
  intro a b c hab hac
  revert c
  induction hab with
  | refl => intro c hac; exact ⟨c, hac, .refl⟩
  | cons sab' _hbc ih =>
    intro c hac
    obtain ⟨d, hbd, hcd⟩ := hSC sab' hac
    obtain ⟨e, hbe, hde⟩ := ih hbd
    exact ⟨e, hbe, Star.append hcd hde⟩

theorem cr_to_semi {step : A → A → Prop} (hC : CR step) : SemiCR step :=
  fun sab hac => hC (Star.single sab) hac

theorem semi_iff_cr {step : A → A → Prop} : SemiCR step ↔ CR step :=
  ⟨semi_to_cr, cr_to_semi⟩

/-! ## Termination and Normal Forms -/

theorem sn_has_nf {step : A → A → Prop} (hT : SN step) (a : A) :
    ∃ nf, Star step a nf ∧ NF step nf := by
  induction a using hT.induction with
  | _ a ih =>
    by_cases h : ∃ b, step a b
    · obtain ⟨b, hab⟩ := h
      obtain ⟨nf, hnf, hnfnf⟩ := ih b hab
      exact ⟨nf, Star.cons hab hnf, hnfnf⟩
    · simp only [not_exists] at h
      exact ⟨a, .refl, h⟩

theorem nf_unique {step : A → A → Prop} (hC : CR step)
    {a nf1 nf2 : A}
    (h1 : Star step a nf1) (hn1 : NF step nf1)
    (h2 : Star step a nf2) (hn2 : NF step nf2) : nf1 = nf2 := by
  obtain ⟨d, hd1, hd2⟩ := hC h1 h2
  cases hd1 with
  | refl =>
    cases hd2 with
    | refl => rfl
    | cons s _ => exact absurd s (hn2 _)
  | cons s _ => exact absurd s (hn1 _)

theorem cr_nf_reduces {step : A → A → Prop} (hC : CR step)
    {a nf : A} (hconv : Conv step a nf) (hnf : NF step nf) :
    Star step a nf := by
  obtain ⟨d, had, hnfd⟩ := cr_church_rosser hC hconv
  cases hnfd with
  | refl => exact had
  | cons s _ => exact absurd s (hnf _)

/-! ## Newman's Lemma -/

theorem newman {step : A → A → Prop} (hT : SN step) (hLC : WCR step) :
    CR step := by
  suffices ∀ a, ∀ b c : A, Star step a b → Star step a c →
      ∃ d, Star step b d ∧ Star step c d by
    intro a b c hab hac; exact this a b c hab hac
  intro a; induction a using hT.induction with
  | _ a ih =>
    intro b c hab hac
    cases hab with
    | refl => exact ⟨c, hac, .refl⟩
    | cons sab1 h1b =>
      cases hac with
      | refl => exact ⟨b, .refl, .cons sab1 h1b⟩
      | cons sac1 h1c =>
        obtain ⟨d0, hb1d0, hc1d0⟩ := hLC sab1 sac1
        obtain ⟨d1, hbd1, hd0d1⟩ := ih _ sab1 _ _ h1b hb1d0
        obtain ⟨d2, hcd2, hd0d2⟩ := ih _ sac1 _ _ h1c hc1d0
        obtain ⟨e, hd1e, hd2e⟩ := ih _ sab1 _ _
          (Star.append hb1d0 hd0d1) (Star.append hb1d0 hd0d2)
        exact ⟨e, Star.append hbd1 hd1e, Star.append hcd2 hd2e⟩

/-! ## Parallel Reduction -/

inductive ParStep (step : A → A → Prop) : A → A → Prop where
  | refl : ParStep step a a
  | lift : step a b → ParStep step a b

namespace ParStep
variable {step : A → A → Prop}

theorem toStar {a b : A} (h : ParStep step a b) : Star step a b := by
  cases h with | refl => exact .refl | lift s => exact Star.single s

theorem par_strip
    (hPD : ∀ {a b c : A}, ParStep step a b → ParStep step a c →
      ∃ d, ParStep step b d ∧ ParStep step c d)
    {a b c : A} (hab : Star step a b) (hac : ParStep step a c) :
    ∃ d, Star step b d ∧ Star step c d := by
  revert c
  induction hab with
  | refl => intro c hac; exact ⟨c, hac.toStar, .refl⟩
  | cons sab' _hbc ih =>
    intro c hac
    obtain ⟨d1, hbd1, hcd1⟩ := hPD (.lift sab') hac
    obtain ⟨d2, hbd2, hd1d2⟩ := ih hbd1
    exact ⟨d2, hbd2, Star.append hcd1.toStar hd1d2⟩

theorem par_diamond_cr
    (hPD : ∀ {a b c : A}, ParStep step a b → ParStep step a c →
      ∃ d, ParStep step b d ∧ ParStep step c d) :
    CR step := by
  intro a b c hab hac
  revert b
  induction hac with
  | refl => intro b hab; exact ⟨b, .refl, hab⟩
  | cons sac' _hcc ih =>
    intro b hab
    obtain ⟨d1, hbd1, hcd1⟩ := par_strip hPD hab (.lift sac')
    obtain ⟨d2, hd1d2, hcd2⟩ := ih hcd1
    exact ⟨d2, Star.append hbd1 hd1d2, hcd2⟩
end ParStep

/-! ## Subcommutative Diamond -/

noncomputable def SubDiamond (step : A → A → Prop) :=
  ∀ {a b c : A}, step a b → step a c →
    ∃ d, (b = d ∨ step b d) ∧ (c = d ∨ step c d)

theorem sub_diamond_cr {step : A → A → Prop} (hSD : SubDiamond step) :
    CR step := by
  apply ParStep.par_diamond_cr
  intro a b c hab hac
  cases hab with
  | refl => exact ⟨c, hac, .refl⟩
  | lift sab =>
    cases hac with
    | refl => exact ⟨b, .refl, .lift sab⟩
    | lift sac =>
      obtain ⟨d, hbd, hcd⟩ := hSD sab sac
      exact ⟨d, hbd.elim (· ▸ .refl) .lift, hcd.elim (· ▸ .refl) .lift⟩

theorem diamond_sub {step : A → A → Prop} (hD : Diamond step) :
    SubDiamond step := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := hD hab hac
  exact ⟨d, .inr hbd, .inr hcd⟩

/-! ## Normal form choice -/

noncomputable def nfOf {step : A → A → Prop} (hT : SN step) (a : A) : A :=
  (sn_has_nf hT a).choose

theorem nfOf_reduces {step : A → A → Prop} (hT : SN step) (a : A) :
    Star step a (nfOf hT a) := (sn_has_nf hT a).choose_spec.1

theorem nfOf_is_nf {step : A → A → Prop} (hT : SN step) (a : A) :
    NF step (nfOf hT a) := (sn_has_nf hT a).choose_spec.2

theorem nfOf_fixed {step : A → A → Prop} (hT : SN step) {a : A}
    (h : NF step a) : nfOf hT a = a := by
  have hred := nfOf_reduces hT a
  match hred with
  | .refl => rfl
  | .cons s _ => exact absurd s (h _)

/-! ## Commutation -/

noncomputable def Commute (s1 s2 : A → A → Prop) :=
  ∀ {a b c : A}, Star s1 a b → Star s2 a c → ∃ d, Star s2 b d ∧ Star s1 c d

/-! ## Connection to computational Path -/

/-- Lift an equality to a single-step computational path. -/
noncomputable def toPath {a b : A} (h : a = b) : Path a b := Path.mk [Step.mk _ _ h] h

/-- Path-first transitivity bridge for `toPath`. -/
noncomputable def toPath_trans_rweq {a b c : A} (h1 : a = b) (h2 : b = c) :
    RwEq
      (Path.stepChain ((Path.trans (toPath h1) (toPath h2)).toEq))
      (Path.stepChain ((toPath (h1.trans h2)).toEq)) := by
  exact rweq_of_eq (by subst h1; subst h2; rfl)

/-- The underlying equality of composed paths is the composition of equalities. -/
theorem toPath_toEq_trans {a b c : A} (h1 : a = b) (h2 : b = c) :
    (Path.trans (toPath h1) (toPath h2)).toEq = (toPath (h1.trans h2)).toEq := by
  simpa using rweq_toEq (toPath_trans_rweq h1 h2)

/-- Path-first symmetry bridge for `toPath`. -/
noncomputable def toPath_symm_rweq {a b : A} (h : a = b) :
    RwEq
      (Path.stepChain ((Path.symm (toPath h)).toEq))
      (Path.stepChain ((toPath h.symm).toEq)) := by
  exact rweq_of_eq (by subst h; rfl)

/-- Symmetry of path equalities. -/
theorem toPath_toEq_symm {a b : A} (h : a = b) :
    (Path.symm (toPath h)).toEq = (toPath h.symm).toEq := by
  simpa using rweq_toEq (toPath_symm_rweq h)

/-- Reflexive path from `rfl`. -/
theorem toPath_refl (a : A) : toPath (rfl : a = a) = Path.mk [Step.mk a a rfl] rfl := rfl

/-- RwEq form of transport along `toPath`. -/
noncomputable def transport_via_toPath_rweq {a b : A} {D : A → Type u} (h : a = b) (x : D a) :
    RwEq
      (Path.stepChain (A := D b)
        (a := Path.transport (toPath h) x)
        (b := h ▸ x)
        (by
          subst h
          simpa using (Path.transport_refl (A := A) (D := D) (a := a) x)))
      (Path.refl (h ▸ x)) := by
  subst h
  simpa [toPath] using
    (rweq_of_step (Step.transport_refl_beta (A := A) (B := D) (a := a) x))

/-- Transport along a toPath is the same as Eq-substitution. -/
theorem transport_via_path {a b : A} {D : A → Type u} (h : a = b) (x : D a) :
    Path.transport (toPath h) x = h ▸ x := by subst h; rfl

/-- Two paths with the same underlying equality have the same transport behavior. -/
theorem transport_eq_of_toEq {a b : A} {D : A → Type u}
    (p q : Path a b) (x : D a) :
    Path.transport p x = Path.transport q x := by
  cases p with | mk _ hp => cases q with | mk _ hq => cases hp; cases hq; rfl

/-! ## Reflexive closure -/

theorem star_refl_step {step : A → A → Prop} {a b : A}
    (h : Star step a b) : Star (fun x y => x = y ∨ step x y) a b := by
  induction h with
  | refl => exact .refl
  | cons s _ ih => exact .cons (.inr s) ih

theorem refl_step_to_star {step : A → A → Prop} {a b : A}
    (h : Star (fun x y => x = y ∨ step x y) a b) : Star step a b := by
  induction h with
  | refl => exact .refl
  | cons s _ ih =>
    match s with
    | .inl heq => exact heq ▸ ih
    | .inr s => exact .cons s ih

/-! ## Development -/

structure MarkedRedex (step : A → A → Prop) where
  src : A
  tgt : A
  red : step src tgt
  marked : Bool

structure Dev (step : A → A → Prop) where
  redexes : List (MarkedRedex step)

noncomputable def Dev.len {step : A → A → Prop} (d : Dev step) : Nat := d.redexes.length

theorem dev_empty_len {step : A → A → Prop} :
    (Dev.mk (step := step) []).len = 0 := rfl

noncomputable def Dev.cat {step : A → A → Prop} (d1 d2 : Dev step) : Dev step :=
  ⟨d1.redexes ++ d2.redexes⟩

theorem dev_cat_len {step : A → A → Prop} (d1 d2 : Dev step) :
    (d1.cat d2).len = d1.len + d2.len := by
  simp [Dev.cat, Dev.len, List.length_append]

/-! ## Cofinal -/

noncomputable def Cofinal (step : A → A → Prop) (f : Nat → A) :=
  (∀ n, step (f n) (f (n + 1))) ∧
  ∀ b, Star step (f 0) b → ∃ m, Star step b (f m)

theorem cofinal_join {step : A → A → Prop} (hC : CR step)
    {a b c : A} (hab : Star step a b) (hac : Star step a c) :
    ∃ d, Star step b d ∧ Star step c d := hC hab hac

end ComputationalPaths.Path.CompPath.ARS
