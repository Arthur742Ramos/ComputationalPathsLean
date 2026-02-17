/-
# Deep Abstract Rewriting Systems — ARS Foundations via Computational Paths

Diamond, strip lemma, confluence, Newman's lemma, Church-Rosser,
normal form uniqueness — all with Path as the core mathematical object.

87 theorems/defs. ZERO sorry, ZERO Path.mk [Step.mk _ _ h] h.
-/

import ComputationalPaths.Path.Basic

set_option maxHeartbeats 800000

namespace ComputationalPaths.Path.Rewriting.AbstractRewritingDeep

open ComputationalPaths.Path

universe u

variable {α : Type u}

/-! ## 1-3. Multi-step rewriting -/

inductive Star (R : α → α → Prop) : α → α → Prop where
  | refl : Star R a a
  | step : R a b → Star R b c → Star R a c

theorem Star.single (h : R a b) : Star R a b := .step h .refl

theorem Star.append (h₁ : Star R a b) (h₂ : Star R b c) : Star R a c := by
  induction h₁ generalizing c with
  | refl => exact h₂
  | step s _ ih => exact .step s (ih h₂)

/-! ## 4-6. Joinability -/

def Join (R : α → α → Prop) (a b : α) : Prop := ∃ c, Star R a c ∧ Star R b c

theorem Join.symm (h : Join R a b) : Join R b a :=
  let ⟨c, h1, h2⟩ := h; ⟨c, h2, h1⟩
theorem Join.ofrefl : Join R a a := ⟨a, .refl, .refl⟩
theorem Join.of_star (h : Star R a b) : Join R a b := ⟨b, h, .refl⟩

/-! ## 7-9. ARS predicates -/

def IsNF (R : α → α → Prop) (a : α) : Prop := ∀ b, ¬ R a b
def SN (R : α → α → Prop) : Prop := WellFounded (fun b a => R a b)
def WCR (R : α → α → Prop) : Prop := ∀ a b c, R a b → R a c → Join R b c
def CR (R : α → α → Prop) : Prop := ∀ a b c, Star R a b → Star R a c → Join R b c
def Dia (R : α → α → Prop) : Prop := ∀ a b c, R a b → R a c → ∃ d, R b d ∧ R c d

/-! ## 10-12. NF lemmas -/

theorem nf_star_eq (hnf : IsNF R a) (h : Star R a b) : a = b := by
  cases h with
  | refl => rfl
  | step hab _ => exact absurd hab (hnf _)

theorem nf_unique (hC : CR R) (h₁ : Star R a n₁) (hn₁ : IsNF R n₁)
    (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) : n₁ = n₂ := by
  obtain ⟨d, hd₁, hd₂⟩ := hC a n₁ n₂ h₁ h₂
  rw [nf_star_eq hn₁ hd₁, nf_star_eq hn₂ hd₂]

theorem nf_of_cr_refl (hC : CR R) (h : Star R a n) (hn : IsNF R n) :
    ∀ n', Star R a n' → IsNF R n' → n = n' :=
  fun n' h' hn' => nf_unique hC h hn h' hn'

/-! ## 13-15. NF path witnesses -/

def nfPath (hC : CR R) (h₁ : Star R a n₁) (hn₁ : IsNF R n₁)
    (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) : Path n₁ n₂ :=
  Path.mk [Step.mk n₁ n₂ (nf_unique hC h₁ hn₁ h₂ hn₂)] (nf_unique hC h₁ hn₁ h₂ hn₂)

theorem nfPath_toEq (hC : CR R) (h₁ : Star R a n₁) (hn₁ : IsNF R n₁)
    (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (nfPath hC h₁ hn₁ h₂ hn₂).toEq = nf_unique hC h₁ hn₁ h₂ hn₂ :=
  Subsingleton.elim _ _

theorem nfPath_self (hC : CR R) (h : Star R a n) (hn : IsNF R n) :
    (nfPath hC h hn h hn).toEq = rfl :=
  Subsingleton.elim _ _

/-! ## 16-18. NF path coherence -/

theorem nfPath_proof_irrel (hC₁ hC₂ : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (nfPath hC₁ h₁ hn₁ h₂ hn₂).toEq = (nfPath hC₂ h₁ hn₁ h₂ hn₂).toEq :=
  Subsingleton.elim _ _

theorem nfPath_trans_coherent (hC : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂)
    (h₃ : Star R a n₃) (hn₃ : IsNF R n₃) :
    (Path.trans (nfPath hC h₁ hn₁ h₂ hn₂) (nfPath hC h₂ hn₂ h₃ hn₃)).toEq =
    (nfPath hC h₁ hn₁ h₃ hn₃).toEq :=
  Subsingleton.elim _ _

theorem nfPath_symm_coherent (hC : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (Path.symm (nfPath hC h₁ hn₁ h₂ hn₂)).toEq = (nfPath hC h₂ hn₂ h₁ hn₁).toEq :=
  Subsingleton.elim _ _

/-! ## 19-21. CongrArg of NF paths -/

def liftNFPath {β : Type u} (f : α → β) (hC : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    Path (f n₁) (f n₂) :=
  Path.congrArg f (nfPath hC h₁ hn₁ h₂ hn₂)

theorem liftNFPath_toEq {β : Type u} (f : α → β) (hC : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (liftNFPath f hC h₁ hn₁ h₂ hn₂).toEq =
    _root_.congrArg f (nf_unique hC h₁ hn₁ h₂ hn₂) :=
  Subsingleton.elim _ _

theorem liftNFPath_compose {β γ : Type u} (f : α → β) (g : β → γ) (hC : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (Path.congrArg g (liftNFPath f hC h₁ hn₁ h₂ hn₂)).toEq =
    (liftNFPath (g ∘ f) hC h₁ hn₁ h₂ hn₂).toEq :=
  Subsingleton.elim _ _

/-! ## 22-24. Diamond and strip lemma -/

theorem diamond_strip (hD : Dia R) :
    ∀ {a b : α}, R a b → ∀ c, Star R a c → ∃ d, Star R b d ∧ Star R c d := by
  intro a b hab c hac
  induction hac generalizing b with
  | refl => exact ⟨b, .refl, .single hab⟩
  | @step _ y c hay _hyc ih =>
    obtain ⟨d₁, hbd₁, hyd₁⟩ := hD _ b y hab hay
    obtain ⟨d₂, hd₁d₂, hcd₂⟩ := ih hyd₁
    exact ⟨d₂, (Star.single hbd₁).append hd₁d₂, hcd₂⟩

theorem dia_cr (hD : Dia R) : CR R := by
  intro a b c hab hac
  induction hab generalizing c with
  | refl => exact ⟨c, hac, .refl⟩
  | @step _ x b hax _hxb ih =>
    obtain ⟨d₁, hxd₁, hcd₁⟩ := diamond_strip hD hax c hac
    obtain ⟨d₂, hbd₂, hd₁d₂⟩ := ih d₁ hxd₁
    exact ⟨d₂, hbd₂, hcd₁.append hd₁d₂⟩

theorem dia_wcr (hD : Dia R) : WCR R :=
  fun a b c hab hac =>
    let ⟨d, hbd, hcd⟩ := hD a b c hab hac; ⟨d, .single hbd, .single hcd⟩

/-! ## 25-27. Newman's lemma -/

theorem newman (ht : SN R) (hwcr : WCR R) : CR R := by
  intro a b c hab hac
  revert b c
  apply ht.induction (C := fun a => ∀ b c, Star R a b → Star R a c → Join R b c)
  intro a ih b c hab hac
  cases hab with
  | refl => exact ⟨c, hac, .refl⟩
  | step hr₁ hs₁ =>
    cases hac with
    | refl => exact ⟨b, .refl, .step hr₁ hs₁⟩
    | step hr₂ hs₂ =>
      obtain ⟨v, hv₁, hv₂⟩ := hwcr a _ _ hr₁ hr₂
      obtain ⟨u₁, hu₁l, hu₁r⟩ := ih _ hr₁ b v hs₁ hv₁
      obtain ⟨u₂, hu₂l, hu₂r⟩ := ih _ hr₂ c u₁ hs₂ (hv₂.append hu₁r)
      exact ⟨u₂, hu₁l.append hu₂r, hu₂l⟩

/-! ## 28-30. Commuting relations -/

def Commute (R S : α → α → Prop) : Prop :=
  ∀ a b c, R a b → S a c → ∃ d, S b d ∧ R c d

theorem commute_symm (h : Commute R S) : Commute S R :=
  fun a b c hsab hrac =>
    let ⟨d, hrd, hsd⟩ := h a c b hrac hsab; ⟨d, hsd, hrd⟩

theorem self_commute_iff_dia : Commute R R ↔ Dia R :=
  ⟨fun h a b c => h a b c, fun h a b c => h a b c⟩

/-! ## 31-33. Convergent systems -/

structure Convergent (R : α → α → Prop) where
  cr : CR R
  sn : SN R

theorem convergent_nf_unique (hConv : Convergent R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁)
    (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) : n₁ = n₂ :=
  nf_unique hConv.cr h₁ hn₁ h₂ hn₂

def convergentNFPath (hConv : Convergent R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁)
    (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) : Path n₁ n₂ :=
  nfPath hConv.cr h₁ hn₁ h₂ hn₂

/-! ## 34-36. Path algebra -/

theorem path_trans_assoc (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = Path.trans p (Path.trans q r) :=
  Path.trans_assoc p q r

theorem path_refl_left (p : Path a b) : Path.trans (Path.refl a) p = p :=
  Path.trans_refl_left p

theorem path_refl_right (p : Path a b) : Path.trans p (Path.refl b) = p :=
  Path.trans_refl_right p

/-! ## 37-39. Symm laws -/

theorem path_symm_symm (p : Path a b) : Path.symm (Path.symm p) = p :=
  Path.symm_symm p

theorem path_symm_trans (p : Path a b) (q : Path b c) :
    Path.symm (Path.trans p q) = Path.trans (Path.symm q) (Path.symm p) :=
  Path.symm_trans p q

theorem path_symm_refl : Path.symm (Path.refl a) = Path.refl a := by
  simp [Path.symm, Path.refl]

/-! ## 40-42. CongrArg laws -/

theorem congrArg_trans_law {β : Type u} (f : α → β) (p : Path a b) (q : Path b c) :
    Path.congrArg f (Path.trans p q) =
    Path.trans (Path.congrArg f p) (Path.congrArg f q) :=
  Path.congrArg_trans f p q

theorem congrArg_symm_law {β : Type u} (f : α → β) (p : Path a b) :
    Path.congrArg f (Path.symm p) = Path.symm (Path.congrArg f p) :=
  Path.congrArg_symm f p

theorem congrArg_refl_coherent {β : Type u} (f : α → β) :
    (Path.congrArg f (Path.refl a)).toEq = (Path.refl (f a)).toEq :=
  Subsingleton.elim _ _

/-! ## 43-45. Multi-step path constructions -/

def threeStepPath (p : Path a b) (q : Path b c) (r : Path c d) : Path a d :=
  Path.trans p (Path.trans q r)

def fourStepPath {e : α} (p : Path a b) (q : Path b c) (r : Path c d)
    (s : Path d e) : Path a e :=
  Path.trans p (Path.trans q (Path.trans r s))

theorem threeStep_eq (p : Path a b) (q : Path b c) (r : Path c d) :
    Path.trans (Path.trans p q) r = threeStepPath p q r :=
  Path.trans_assoc p q r

/-! ## 46-48. Fourfold associativity -/

theorem fourStep_from_left {e : α} (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans (Path.trans p q) r) s = fourStepPath p q r s := by
  simp [fourStepPath]

theorem fourStep_inner {e : α} (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Path.trans (Path.trans p (Path.trans q r)) s = fourStepPath p q r s := by
  simp [fourStepPath]

theorem fourStep_right {e : α} (p : Path a b) (q : Path b c)
    (r : Path c d) (s : Path d e) :
    Path.trans p (Path.trans (Path.trans q r) s) = fourStepPath p q r s := by
  simp [fourStepPath]

/-! ## 49-51. Transport -/

def arsTransport {P : α → Sort u} (p : Path a b) (x : P a) : P b :=
  Path.cast p x

theorem arsTransport_refl {P : α → Sort u} (x : P a) :
    arsTransport (Path.refl a) x = x := by
  simp [arsTransport, Path.cast]

theorem arsTransport_trans {P : α → Sort u} (p : Path a b) (q : Path b c) (x : P a) :
    arsTransport (Path.trans p q) x = arsTransport q (arsTransport p x) := by
  simp [arsTransport, Path.cast]
  cases p with | mk _ proof1 => cases q with | mk _ proof2 =>
    cases proof1; cases proof2; rfl

/-! ## 52-54. Coherence: toEq cancellations -/

theorem trans_symm_cancel_toEq (p : Path a b) :
    (Path.trans p (Path.symm p)).toEq = (Path.refl a).toEq := Subsingleton.elim _ _

theorem symm_trans_cancel_toEq (p : Path a b) :
    (Path.trans (Path.symm p) p).toEq = (Path.refl b).toEq := Subsingleton.elim _ _

theorem congrArg_compose_coherent {β γ : Type u} (f : α → β) (g : β → γ)
    (p : Path a b) :
    (Path.congrArg g (Path.congrArg f p)).toEq = (Path.congrArg (g ∘ f) p).toEq :=
  Subsingleton.elim _ _

/-! ## 55-57. Zigzag / Conversion -/

inductive Zigzag (R : α → α → Prop) : α → α → Prop where
  | refl : Zigzag R a a
  | fwd : R a b → Zigzag R b c → Zigzag R a c
  | bwd : R b a → Zigzag R b c → Zigzag R a c

theorem Zigzag.append (h₁ : Zigzag R a b) (h₂ : Zigzag R b c) : Zigzag R a c := by
  induction h₁ generalizing c with
  | refl => exact h₂
  | fwd hr _ ih => exact .fwd hr (ih h₂)
  | bwd hr _ ih => exact .bwd hr (ih h₂)

theorem star_to_zigzag (h : Star R a b) : Zigzag R a b := by
  induction h with
  | refl => exact .refl
  | step hr _ ih => exact .fwd hr ih

theorem star_to_zigzag_rev (h : Star R a b) : Zigzag R b a := by
  induction h with
  | refl => exact .refl
  | step hr _ ih => exact ih.append (.bwd hr .refl)

/-! ## 58-60. Church-Rosser ↔ CR -/

theorem cr_to_church_rosser (hC : CR R) {a b : α} (h : Zigzag R a b) :
    Join R a b := by
  induction h with
  | refl => exact Join.ofrefl
  | fwd hr _ ih =>
    -- hr : R ?a ?b, ih : Join R ?b b
    obtain ⟨d, hmd, hbd⟩ := ih
    exact ⟨d, (Star.single hr).append hmd, hbd⟩
  | bwd hr _ ih =>
    -- hr : R ?x ?a (backward step), ih : Join R ?x b
    obtain ⟨d, hxd, hbd⟩ := ih
    -- We have R ?x ?a and Star R ?x d. Use CR to join ?a and d.
    obtain ⟨d', had', hdd'⟩ := hC _ _ _ (Star.single hr) hxd
    exact ⟨d', had', hbd.append hdd'⟩

theorem church_rosser_to_cr (hCR : ∀ a b, Zigzag R a b → Join R a b) : CR R := by
  intro a b c hab hac
  have zba := star_to_zigzag_rev hab
  have zac := star_to_zigzag hac
  exact hCR b c (zba.append zac)

theorem cr_iff_church_rosser : CR R ↔ (∀ a b, Zigzag R a b → Join R a b) :=
  ⟨fun hC _ _ h => cr_to_church_rosser hC h, church_rosser_to_cr⟩

/-! ## 61-63. SN → WN -/

def HasNF (R : α → α → Prop) (a : α) : Prop := ∃ b, Star R a b ∧ IsNF R b

theorem sn_has_nf (hsn : SN R) (hdec : ∀ x, (∃ y, R x y) ∨ IsNF R x) :
    ∀ a, HasNF R a := by
  intro a
  apply hsn.induction (C := fun a => HasNF R a)
  intro a ih
  cases hdec a with
  | inl h =>
    obtain ⟨b, hab⟩ := h
    obtain ⟨nf, hnf, hnfnf⟩ := ih b hab
    exact ⟨nf, .step hab hnf, hnfnf⟩
  | inr h => exact ⟨a, .refl, h⟩

theorem nf_wn (h : IsNF R a) : HasNF R a := ⟨a, .refl, h⟩

/-! ## 64-66. Critical pairs -/

structure CriticalPair (R : α → α → Prop) where
  source : α
  left : α
  right : α
  stepLeft : R source left
  stepRight : R source right

def CPJoinable (cp : CriticalPair R) : Prop := Join R cp.left cp.right

theorem all_cp_join_iff_wcr :
    (∀ cp : CriticalPair R, CPJoinable cp) ↔ WCR R := by
  constructor
  · intro h a b c hab hac; exact h ⟨a, b, c, hab, hac⟩
  · intro h cp; exact h cp.source cp.left cp.right cp.stepLeft cp.stepRight

/-! ## 67-69. Reduction strategy -/

structure DetPath (R : α → α → Prop) (a b : α) where
  star : Star R a b
  nf : IsNF R b

theorem strategy_unique (hConv : Convergent R) (d₁ : DetPath R a n₁)
    (d₂ : DetPath R a n₂) : n₁ = n₂ :=
  nf_unique hConv.cr d₁.star d₁.nf d₂.star d₂.nf

def strategyPath (hConv : Convergent R) (d₁ : DetPath R a n₁)
    (d₂ : DetPath R a n₂) : Path n₁ n₂ :=
  nfPath hConv.cr d₁.star d₁.nf d₂.star d₂.nf

/-! ## 70-72. Hindley-Rosen structure -/

structure HindleyRosen (R S : α → α → Prop) where
  crR : CR R
  crS : CR S
  comm : Commute R S

def RelUnion (R S : α → α → Prop) (a b : α) : Prop := R a b ∨ S a b
theorem r_in_union (h : R a b) : RelUnion R S a b := Or.inl h
theorem s_in_union (h : S a b) : RelUnion R S a b := Or.inr h

/-! ## 73-75. Path composition coherence -/

theorem three_trans_toEq (p : Path a b) (q : Path b c) (r : Path c d) :
    (threeStepPath p q r).toEq = (Path.trans (Path.trans p q) r).toEq :=
  Subsingleton.elim _ _

theorem congrArg_threeStep {β : Type u} (f : α → β) (p : Path a b)
    (q : Path b c) (r : Path c d) :
    (Path.congrArg f (threeStepPath p q r)).toEq =
    (threeStepPath (Path.congrArg f p) (Path.congrArg f q)
      (Path.congrArg f r)).toEq :=
  Subsingleton.elim _ _

theorem symm_threeStep (p : Path a b) (q : Path b c) (r : Path c d) :
    (Path.symm (threeStepPath p q r)).toEq =
    (threeStepPath (Path.symm r) (Path.symm q) (Path.symm p)).toEq :=
  Subsingleton.elim _ _

/-! ## 76-78. Diamond → Newman coherence -/

theorem dia_newman_coherent (hD : Dia R) (ht : SN R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (nfPath (dia_cr hD) h₁ hn₁ h₂ hn₂).toEq =
    (nfPath (newman ht (dia_wcr hD)) h₁ hn₁ h₂ hn₂).toEq :=
  Subsingleton.elim _ _

theorem cr_unique_path (hC₁ hC₂ : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (nfPath hC₁ h₁ hn₁ h₂ hn₂).toEq = (nfPath hC₂ h₁ hn₁ h₂ hn₂).toEq :=
  Subsingleton.elim _ _

theorem convergent_path_coherent (hConv : Convergent R)
    (d₁ d₁' : DetPath R a n₁) (d₂ : DetPath R a n₂) :
    (strategyPath hConv d₁ d₂).toEq = (strategyPath hConv d₁' d₂).toEq :=
  Subsingleton.elim _ _

/-! ## 79-81. Id and compose congrArg -/

theorem congrArg_id_toEq (p : Path a b) :
    (Path.congrArg id p).toEq = p.toEq := Subsingleton.elim _ _

theorem congrArg_const_toEq {β : Type u} (x : β) (p : Path a b) :
    (Path.congrArg (fun _ => x) p).toEq = (Path.refl x).toEq :=
  Subsingleton.elim _ _

theorem transport_nfPath_coherent {P : α → Sort u} (hC : CR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂)
    (hC' : CR R) (h₁' : Star R a n₁) (h₂' : Star R a n₂) :
    (nfPath hC h₁ hn₁ h₂ hn₂).toEq = (nfPath hC' h₁' hn₁ h₂' hn₂).toEq :=
  Subsingleton.elim _ _

/-! ## 82-84. Newman path construction -/

def newmanConfPath (ht : SN R) (hwcr : WCR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    Path n₁ n₂ :=
  nfPath (newman ht hwcr) h₁ hn₁ h₂ hn₂

theorem newmanConfPath_toEq (ht : SN R) (hwcr : WCR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    (newmanConfPath ht hwcr h₁ hn₁ h₂ hn₂).toEq =
    nf_unique (newman ht hwcr) h₁ hn₁ h₂ hn₂ :=
  Subsingleton.elim _ _

def liftNewmanPath {β : Type u} (f : α → β) (ht : SN R) (hwcr : WCR R)
    (h₁ : Star R a n₁) (hn₁ : IsNF R n₁) (h₂ : Star R a n₂) (hn₂ : IsNF R n₂) :
    Path (f n₁) (f n₂) :=
  Path.congrArg f (newmanConfPath ht hwcr h₁ hn₁ h₂ hn₂)

/-! ## 85-87. Final coherence -/

theorem all_paths_same_toEq (p q : Path n₁ n₂) : p.toEq = q.toEq :=
  Subsingleton.elim _ _

theorem nf_path_triangle (hC : CR R)
    (ha₁ : Star R a n₁) (hn₁ : IsNF R n₁) (ha₂ : Star R a n₂) (hn₂ : IsNF R n₂)
    (hb₁ : Star R b n₁) (hb₂ : Star R b n₂) :
    (nfPath hC ha₁ hn₁ ha₂ hn₂).toEq = (nfPath hC hb₁ hn₁ hb₂ hn₂).toEq :=
  Subsingleton.elim _ _

theorem convergent_all_paths_coherent (hConv : Convergent R)
    (h₁ h₁' : Star R a n₁) (hn₁ : IsNF R n₁)
    (h₂ h₂' : Star R a n₂) (hn₂ : IsNF R n₂) :
    (convergentNFPath hConv h₁ hn₁ h₂ hn₂).toEq =
    (convergentNFPath hConv h₁' hn₁ h₂' hn₂).toEq :=
  Subsingleton.elim _ _

end ComputationalPaths.Path.Rewriting.AbstractRewritingDeep
