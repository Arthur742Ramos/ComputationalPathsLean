import ComputationalPaths.Path.Rewrite.Step
import ComputationalPaths.Path.Rewrite.RwEq

/-!
# Type-Valued Confluence Theory for Computational Paths

This module develops confluence theory in the **Type-valued** setting,
matching the Type-valued `Step` and `RwEq` infrastructure. All results
produce genuine computational witnesses (Sigma types) rather than mere
existence proofs (∃).

## Main results

- `RwT`: Type-valued reflexive-transitive closure of `Step`
- `ARTC`: Abstract Type-valued reflexive-transitive closure
- `DiamondT`, `ConfluentT`, `LocallyConfluentT`, `SemiConfluentT`
- `diamond_strip_T`, `diamond_confluence_T`: diamond → strip → confluence
- `newman_T`: Newman's Lemma (Type-valued)
- `church_rosser_T`: Church-Rosser from Type-valued confluence
- `IsNormalFormT`, `normal_form_unique_T`: normal form characterization
-/

namespace ComputationalPaths
namespace Path
namespace Rewrite
namespace ConfluenceDeepType

universe u v

variable {A : Type u}

/-! ## Type-valued reflexive-transitive closure of Step -/

/-- Type-valued multi-step rewriting. -/
inductive RwT {a b : A} : Path a b → Path a b → Type (u + 1) where
  | refl : (p : Path a b) → RwT p p
  | tail : {p q r : Path a b} → RwT p q → Step q r → RwT p r

namespace RwT

variable {a b : A}

noncomputable def single {p q : Path a b} (h : Step p q) : RwT p q :=
  RwT.tail (RwT.refl p) h

noncomputable def append {p q r : Path a b}
    (h₁ : RwT p q) (h₂ : RwT q r) : RwT p r := by
  match h₂ with
  | .refl _ => exact h₁
  | .tail h₂' step => exact RwT.tail (append h₁ h₂') step

noncomputable def cons {p q r : Path a b}
    (h : Step p q) (h₂ : RwT q r) : RwT p r :=
  RwT.append (RwT.single h) h₂

theorem rwT_toEq {p q : Path a b} (h : RwT p q) :
    p.toEq = q.toEq := by
  match h with
  | .refl _ => rfl
  | .tail h' step => exact (rwT_toEq h').trans (step_toEq step)

noncomputable def toRw {p q : Path a b} (h : RwT p q) : Rw p q := by
  match h with
  | .refl _ => exact Rw.refl _
  | .tail h' step => exact Rw.tail (toRw h') step

end RwT

noncomputable def rweq_of_rwT {a b : A} {p q : Path a b}
    (h : RwT p q) : RwEq p q := by
  match h with
  | .refl _ => exact RwEq.refl _
  | .tail h' step => exact RwEq.trans (rweq_of_rwT h') (RwEq.step step)

/-! ## Abstract Type-valued ARS -/

/-- Type-valued reflexive-transitive closure for an abstract relation. -/
inductive ARTC {α : Type u} (R : α → α → Type v) : α → α → Type (max u v) where
  | refl : (a : α) → ARTC R a a
  | step : {a b c : α} → R a b → ARTC R b c → ARTC R a c

namespace ARTC

variable {α : Type u} {R : α → α → Type v}

noncomputable def single {a b : α} (h : R a b) : ARTC R a b :=
  ARTC.step h (ARTC.refl b)

noncomputable def trans {a b c : α}
    (h₁ : ARTC R a b) (h₂ : ARTC R b c) : ARTC R a c := by
  match h₁ with
  | .refl _ => exact h₂
  | .step r rest => exact ARTC.step r (trans rest h₂)

noncomputable def snoc {a b c : α}
    (h₁ : ARTC R a b) (h₂ : R b c) : ARTC R a c :=
  ARTC.trans h₁ (ARTC.single h₂)

end ARTC

/-! ## Type-valued confluence properties -/

/-- Type-valued local confluence. -/
def LocallyConfluentT {α : Type u} (R : α → α → Type v) : Type (max u v) :=
  ∀ {a b c : α}, R a b → R a c → Σ d : α, ARTC R b d × ARTC R c d

/-- Type-valued confluence. -/
def ConfluentT {α : Type u} (R : α → α → Type v) : Type (max u v) :=
  ∀ {a b c : α}, ARTC R a b → ARTC R a c → Σ d : α, ARTC R b d × ARTC R c d

/-- Type-valued diamond property. -/
def DiamondT {α : Type u} (R : α → α → Type v) : Type (max u v) :=
  ∀ {a b c : α}, R a b → R a c → Σ d : α, R b d × R c d

/-- Type-valued semi-confluence. -/
def SemiConfluentT {α : Type u} (R : α → α → Type v) : Type (max u v) :=
  ∀ {a b c : α}, R a b → ARTC R a c → Σ d : α, ARTC R b d × ARTC R c d

/-! ## Diamond → Strip → Confluence -/

/-- **Strip Lemma** (Type-valued): diamond property lets us close one step
    against a multi-step chain. -/
noncomputable def diamond_strip_T {α : Type u} {R : α → α → Type v}
    (hD : DiamondT R)
    {a b c : α} (hab : R a b) (hac : ARTC R a c) :
    Σ d : α, ARTC R b d × R c d := by
  match hac with
  | .refl _ => exact ⟨b, ARTC.refl b, hab⟩
  | .step hax hxc =>
    obtain ⟨d₁, hbd₁, hxd₁⟩ := hD hab hax
    obtain ⟨d₂, hd₁d₂, hcd₂⟩ := diamond_strip_T hD hxd₁ hxc
    exact ⟨d₂, ARTC.step hbd₁ hd₁d₂, hcd₂⟩

/-- **Diamond → Confluence** (Type-valued). -/
noncomputable def diamond_confluence_T {α : Type u} {R : α → α → Type v}
    (hD : DiamondT R) :
    ConfluentT R := by
  intro a b c hab hac
  match hab with
  | .refl _ => exact ⟨c, hac, ARTC.refl c⟩
  | .step hax hxb =>
    obtain ⟨d₁, hcd₁, hxd₁⟩ := diamond_strip_T hD hax hac
    obtain ⟨d₂, hbd₂, hd₁d₂⟩ := diamond_confluence_T hD hxb hcd₁
    exact ⟨d₂, hbd₂, ARTC.step hxd₁ hd₁d₂⟩

/-- Diamond implies local confluence (Type-valued). -/
noncomputable def diamond_local_T {α : Type u} {R : α → α → Type v}
    (hD : DiamondT R) :
    LocallyConfluentT R :=
  fun hab hac =>
    let ⟨d, hbd, hcd⟩ := hD hab hac
    ⟨d, ARTC.single hbd, ARTC.single hcd⟩

/-- Diamond implies semi-confluence (Type-valued). -/
noncomputable def diamond_semi_T {α : Type u} {R : α → α → Type v}
    (hD : DiamondT R) :
    SemiConfluentT R := by
  intro a b c hab hac
  obtain ⟨d, hbd, hcd⟩ := diamond_strip_T hD hab hac
  exact ⟨d, hbd, ARTC.single hcd⟩

/-- Confluence implies semi-confluence (Type-valued). -/
noncomputable def confluent_semi_T {α : Type u} {R : α → α → Type v}
    (hC : ConfluentT R) :
    SemiConfluentT R :=
  fun hab hac => hC (ARTC.single hab) hac

/-- Semi-confluence implies confluence (Type-valued). -/
noncomputable def semi_confluent_T {α : Type u} {R : α → α → Type v}
    (hS : SemiConfluentT R) :
    ConfluentT R := by
  intro a b c hab hac
  match hab with
  | .refl _ => exact ⟨c, hac, ARTC.refl c⟩
  | .step hax hxb =>
    obtain ⟨d₁, hcd₁, hxd₁⟩ := hS hax hac
    obtain ⟨d₂, hbd₂, hd₁d₂⟩ := semi_confluent_T hS hxb hcd₁
    exact ⟨d₂, hbd₂, ARTC.trans hxd₁ hd₁d₂⟩

/-! ## Newman's Lemma (Type-valued) -/

/-- **Newman's Lemma** (Type-valued, parametric): well-founded + locally confluent → confluent.
    This wraps the abstract statement; the WF recursion is delegated to `WellFounded.fix`. -/
noncomputable def newman_T {α : Type u} {R : α → α → Type v}
    (wf : WellFounded (fun y x => Nonempty (R x y)))
    (hLocal : LocallyConfluentT R) :
    ConfluentT R :=
  newman_core wf hLocal
  where
    /-- Core recursive helper for Newman's lemma using WellFounded.fix. -/
    newman_core {α : Type u} {R : α → α → Type v}
        (wf : WellFounded (fun y x => Nonempty (R x y)))
        (hLocal : LocallyConfluentT R) :
        ConfluentT R :=
      fun {a b c} hab hac =>
        wf.fix (C := fun a => ∀ {b c : α}, ARTC R a b → ARTC R a c →
            Σ d : α, ARTC R b d × ARTC R c d)
          (fun a ih {b c} hab hac =>
            match hab, hac with
            | ARTC.refl _, hac' => ⟨_, hac', ARTC.refl _⟩
            | hab', ARTC.refl _ => ⟨_, ARTC.refl _, hab'⟩
            | ARTC.step ha₁ h₁b, ARTC.step ha₂ h₂c =>
              let ⟨d₀, h₁d₀, h₂d₀⟩ := hLocal ha₁ ha₂
              let ⟨d₁, hbd₁, hd₀d₁⟩ := ih _ ⟨ha₁⟩ h₁b h₁d₀
              let ⟨d₂, hcd₂, hd₁d₂⟩ := ih _ ⟨ha₂⟩ h₂c (ARTC.trans h₂d₀ hd₀d₁)
              ⟨d₂, ARTC.trans hbd₁ hd₁d₂, hcd₂⟩) a hab hac

/-! ## Church-Rosser (Type-valued) -/

/-- Symmetric closure of ARTC. -/
inductive EqClosure {α : Type u} (R : α → α → Type v) : α → α → Type (max u v) where
  | fwd : {a b : α} → ARTC R a b → EqClosure R a b
  | bwd : {a b : α} → ARTC R b a → EqClosure R a b
  | refl : (a : α) → EqClosure R a a
  | trans : {a b c : α} → EqClosure R a b → EqClosure R b c → EqClosure R a c

/-- **Church-Rosser** (Type-valued): if `ARTC R` is confluent, then the
    equivalence closure has common reducts. -/
noncomputable def church_rosser_T {α : Type u} {R : α → α → Type v}
    (hConf : ConfluentT R)
    {a b : α} (h : EqClosure R a b) :
    Σ c : α, ARTC R a c × ARTC R b c := by
  match h with
  | .fwd hab => exact ⟨b, hab, ARTC.refl b⟩
  | .bwd hba => exact ⟨a, ARTC.refl a, hba⟩
  | .refl a => exact ⟨a, ARTC.refl a, ARTC.refl a⟩
  | .trans h₁ h₂ =>
    obtain ⟨c₁, hac₁, hbc₁⟩ := church_rosser_T hConf h₁
    obtain ⟨c₂, hbc₂, hcc₂⟩ := church_rosser_T hConf h₂
    obtain ⟨d, hc₁d, hc₂d⟩ := hConf hbc₁ hbc₂
    exact ⟨d, ARTC.trans hac₁ hc₁d, ARTC.trans hcc₂ hc₂d⟩

/-! ## Path-level Type-valued confluence -/

section PathLevel

variable {a b : A}

/-- Church-Rosser for `RwEq` from Type-valued confluence of `Step`. -/
noncomputable def church_rosser_rweq_T
    (hConf : ∀ {p q r : Path a b}, RwT p q → RwT p r →
      Σ m : Path a b, RwT q m × RwT r m)
    {p q : Path a b} (h : RwEq p q) :
    Σ m : Path a b, RwT p m × RwT q m := by
  match h with
  | .refl p => exact ⟨p, RwT.refl p, RwT.refl p⟩
  | .step s => exact ⟨_, RwT.single s, RwT.refl _⟩
  | .symm h' =>
    obtain ⟨m, hpm, hqm⟩ := church_rosser_rweq_T hConf h'
    exact ⟨m, hqm, hpm⟩
  | .trans h₁ h₂ =>
    obtain ⟨m₁, hpm₁, hqm₁⟩ := church_rosser_rweq_T hConf h₁
    obtain ⟨m₂, hqm₂, hrm₂⟩ := church_rosser_rweq_T hConf h₂
    obtain ⟨m, hm₁m, hm₂m⟩ := hConf hqm₁ hqm₂
    exact ⟨m, RwT.append hpm₁ hm₁m, RwT.append hrm₂ hm₂m⟩

/-- Normal form: no Step applies. -/
def IsNormalFormT (p : Path a b) : Prop :=
  ∀ q : Path a b, Step p q → False

/-- If two paths both reduce to normal forms and are RwEq-equivalent,
    their normal forms are RwEq-equivalent. -/
noncomputable def normal_form_rweq {p q np nq : Path a b}
    (hp : RwT p np) (hq : RwT q nq)
    (heq : RwEq p q) : RwEq np nq :=
  RwEq.trans (RwEq.symm (rweq_of_rwT hp)) (RwEq.trans heq (rweq_of_rwT hq))

/-- A normal form cannot be rewritten further. -/
noncomputable def rwT_from_nf_is_refl {p q : Path a b}
    (hnf : IsNormalFormT p) (h : RwT p q) : p = q := by
  match h with
  | .refl _ => rfl
  | .tail h' step =>
    have := rwT_from_nf_is_refl hnf h'
    subst this
    exact (hnf _ step).elim

/-- Normal forms are unique under confluence (Type-valued). -/
noncomputable def normal_form_unique_T
    (hConf : ∀ {p q r : Path a b}, RwT p q → RwT p r →
      Σ m : Path a b, RwT q m × RwT r m)
    {p np nq : Path a b}
    (hnp : IsNormalFormT np) (hnq : IsNormalFormT nq)
    (hp : RwT p np) (hq : RwT p nq) : RwEq np nq := by
  obtain ⟨m, hnpm, hnqm⟩ := hConf hp hq
  have h1 : np = m := rwT_from_nf_is_refl hnp hnpm
  have h2 : nq = m := rwT_from_nf_is_refl hnq hnqm
  subst h1
  subst h2
  exact RwEq.refl _

end PathLevel

/-! ## Commutation -/

section Commutation

variable {α : Type u} {R S : α → α → Type v}

/-- Two relations commute if diverging steps can be joined. -/
def CommuteT (R S : α → α → Type v) : Type (max u v) :=
  ∀ {a b c : α}, R a b → S a c → Σ d : α, S b d × R c d

/-- Commutation is symmetric. -/
noncomputable def commute_symm (h : CommuteT R S) : CommuteT S R :=
  fun hab hac =>
    let ⟨d, hbd, hcd⟩ := h hac hab
    ⟨d, hcd, hbd⟩

/-- Self-commutation → diamond property. -/
noncomputable def self_commute_to_diamond (h : CommuteT R R) : DiamondT R :=
  fun hab hac =>
    let ⟨d, hbd, hcd⟩ := h hab hac
    ⟨d, hbd, hcd⟩

/-- Diamond property → self-commutation. -/
noncomputable def diamond_to_self_commute (h : DiamondT R) : CommuteT R R :=
  fun hab hac =>
    let ⟨d, hbd, hcd⟩ := h hab hac
    ⟨d, hbd, hcd⟩

end Commutation

end ConfluenceDeepType
end Rewrite
end Path
end ComputationalPaths
