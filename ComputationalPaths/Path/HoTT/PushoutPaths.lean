/-
# Higher inductive types: pushouts, coequalizers, suspensions

This module develops higher inductive type constructions using computational
paths: pushouts, coequalizers, suspensions as pushouts, and basic
Seifert–van Kampen aspects.  We use `Quot` to construct quotient types and
`Path` to capture the glue/identification maps as computational paths.
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace Path
namespace HoTT
namespace Pushouts

open ComputationalPaths.Path

universe u v w

variable {A : Type u}

/-! ## Span -/

/-- A span is the basic data for a pushout: A ← C → B. -/
structure Span (A : Type u) (B : Type u) (C : Type u) where
  left  : C → A
  right : C → B

/-! ## Pushout type (via Quot) -/

/-- Raw glue relation on A ⊕ B: identify `inl (f c)` with `inr (g c)`. -/
inductive PushoutRel {A B C : Type u} (s : Span A B C) :
    A ⊕ B → A ⊕ B → Prop where
  | glue (c : C) : PushoutRel s (Sum.inl (s.left c)) (Sum.inr (s.right c))

/-- The pushout type, quotienting A ⊕ B by the glue relation. -/
def Pushout {A B C : Type u} (s : Span A B C) : Type u :=
  Quot (PushoutRel s)

/-- Left inclusion into the pushout. -/
def Pushout.inl {A B C : Type u} {s : Span A B C} (a : A) : Pushout s :=
  Quot.mk _ (Sum.inl a)

/-- Right inclusion into the pushout. -/
def Pushout.inr {A B C : Type u} {s : Span A B C} (b : B) : Pushout s :=
  Quot.mk _ (Sum.inr b)

/-- The glue identification: inl(f c) = inr(g c) in the pushout. -/
theorem Pushout.glue {A B C : Type u} {s : Span A B C} (c : C) :
    @Pushout.inl A B C s (s.left c) = @Pushout.inr A B C s (s.right c) :=
  Quot.sound (PushoutRel.glue c)

/-- The glue identification as a computational path. -/
def Pushout.gluePath {A B C : Type u} {s : Span A B C} (c : C) :
    Path (@Pushout.inl A B C s (s.left c)) (@Pushout.inr A B C s (s.right c)) :=
  Path.mk [Step.mk _ _ (Pushout.glue c)] (Pushout.glue c)

/-- Elimination from the pushout into a type family (non-dependent). -/
def Pushout.lift {A B C : Type u} {s : Span A B C} {D : Type v}
    (fA : A → D) (fB : B → D)
    (hglue : ∀ c, fA (s.left c) = fB (s.right c)) :
    Pushout s → D :=
  Quot.lift (fun x => match x with | Sum.inl a => fA a | Sum.inr b => fB b)
    (fun x y r => by cases r with | glue c => exact hglue c)

/-- Lift computes on inl. -/
theorem Pushout.lift_inl {A B C : Type u} {s : Span A B C} {D : Type v}
    (fA : A → D) (fB : B → D)
    (hglue : ∀ c, fA (s.left c) = fB (s.right c)) (a : A) :
    Pushout.lift fA fB hglue (Pushout.inl a) = fA a := rfl

/-- Lift computes on inr. -/
theorem Pushout.lift_inr {A B C : Type u} {s : Span A B C} {D : Type v}
    (fA : A → D) (fB : B → D)
    (hglue : ∀ c, fA (s.left c) = fB (s.right c)) (b : B) :
    Pushout.lift fA fB hglue (Pushout.inr b) = fB b := rfl

/-! ## Coequalizer -/

/-- Raw coequalizer relation: identify f(a) with g(a). -/
inductive CoequalizerRel {X Y : Type u} (f g : X → Y) : Y → Y → Prop where
  | coeq (x : X) : CoequalizerRel f g (f x) (g x)

/-- The coequalizer type. -/
def Coequalizer {X Y : Type u} (f g : X → Y) : Type u :=
  Quot (CoequalizerRel f g)

/-- Inclusion into the coequalizer. -/
def Coequalizer.inc {X Y : Type u} {f g : X → Y} (y : Y) : Coequalizer f g :=
  Quot.mk _ y

/-- The coequalizer identification: inc(f x) = inc(g x). -/
theorem Coequalizer.coeq {X Y : Type u} {f g : X → Y} (x : X) :
    @Coequalizer.inc X Y f g (f x) = @Coequalizer.inc X Y f g (g x) :=
  Quot.sound (CoequalizerRel.coeq x)

/-- The coequalizer identification as a computational path. -/
def Coequalizer.coeqPath {X Y : Type u} {f g : X → Y} (x : X) :
    Path (@Coequalizer.inc X Y f g (f x)) (@Coequalizer.inc X Y f g (g x)) :=
  Path.mk [Step.mk _ _ (Coequalizer.coeq x)] (Coequalizer.coeq x)

/-- Elimination from the coequalizer. -/
def Coequalizer.lift {X Y : Type u} {f g : X → Y} {D : Type v}
    (h : Y → D) (hcoeq : ∀ x, h (f x) = h (g x)) :
    Coequalizer f g → D :=
  Quot.lift h (fun a b r => by cases r with | coeq x => exact hcoeq x)

/-- Lift computes on inc. -/
theorem Coequalizer.lift_inc {X Y : Type u} {f g : X → Y} {D : Type v}
    (h : Y → D) (hcoeq : ∀ x, h (f x) = h (g x)) (y : Y) :
    Coequalizer.lift h hcoeq (Coequalizer.inc y) = h y := rfl

/-! ## Suspension -/

/-- The suspension span: PUnit ← A → PUnit. -/
def suspSpan (A : Type u) : Span PUnit PUnit A where
  left  := fun _ => PUnit.unit
  right := fun _ => PUnit.unit

/-- The suspension type Σ(A). -/
def Susp (A : Type u) : Type u := Pushout (suspSpan A)

/-- North pole. -/
def Susp.north {A : Type u} : Susp A := Pushout.inl PUnit.unit

/-- South pole. -/
def Susp.south {A : Type u} : Susp A := Pushout.inr PUnit.unit

/-- Meridian: a path from north to south for each a : A. -/
def Susp.merid {A : Type u} (a : A) :
    Path (@Susp.north A) (@Susp.south A) :=
  Pushout.gluePath a

/-- A loop at the north pole, formed from two meridians. -/
def Susp.loop {A : Type u} (a₁ a₂ : A) :
    Path (@Susp.north A) (@Susp.north A) :=
  Path.trans (Susp.merid a₁) (Path.symm (Susp.merid a₂))

/-- The loop from a point and itself is trivial at the toEq level. -/
theorem Susp.loop_same_toEq {A : Type u} (a : A) :
    (Susp.loop a a).toEq = rfl := by
  simp

/-- Meridian steps capture the single glue step. -/
theorem Susp.merid_steps {A : Type u} (a : A) :
    (Susp.merid a).steps.length = 1 := by
  simp [Susp.merid, Pushout.gluePath]

/-! ## Circle as suspension of Bool -/

/-- The circle S¹, defined as the suspension of Bool. -/
def Circle : Type := Susp Bool

/-- Base point of the circle. -/
def Circle.base : Circle := Susp.north

/-- The loop on the circle from the two Bool-meridians. -/
def Circle.loop : Path Circle.base Circle.base :=
  Susp.loop true false

/-- Circle loop has the right step structure (via trans). -/
theorem Circle.loop_steps :
    Circle.loop.steps =
      (Susp.merid true).steps ++ (Path.symm (Susp.merid false)).steps := by
  apply proof_irrel

/-! ## Wedge sum -/

/-- Wedge relation: identify the two basepoints. -/
inductive WedgeRel {A B : Type u} (a₀ : A) (b₀ : B) :
    A ⊕ B → A ⊕ B → Prop where
  | wedge : WedgeRel a₀ b₀ (Sum.inl a₀) (Sum.inr b₀)

/-- The wedge sum A ∨ B (with chosen basepoints). -/
def Wedge {A B : Type u} (a₀ : A) (b₀ : B) : Type u :=
  Quot (WedgeRel a₀ b₀)

/-- Left inclusion into the wedge. -/
def Wedge.inl {A B : Type u} {a₀ : A} {b₀ : B} (a : A) : Wedge a₀ b₀ :=
  Quot.mk _ (Sum.inl a)

/-- Right inclusion into the wedge. -/
def Wedge.inr {A B : Type u} {a₀ : A} {b₀ : B} (b : B) : Wedge a₀ b₀ :=
  Quot.mk _ (Sum.inr b)

/-- The wedge identification as propositional equality. -/
theorem Wedge.glue {A B : Type u} {a₀ : A} {b₀ : B} :
    @Wedge.inl A B a₀ b₀ a₀ = @Wedge.inr A B a₀ b₀ b₀ :=
  Quot.sound WedgeRel.wedge

/-- The wedge identification as a computational path. -/
def Wedge.gluePath {A B : Type u} {a₀ : A} {b₀ : B} :
    Path (@Wedge.inl A B a₀ b₀ a₀) (@Wedge.inr A B a₀ b₀ b₀) :=
  Path.mk [Step.mk _ _ Wedge.glue] Wedge.glue

/-! ## Pushout properties via Path -/

/-- Composing the glue path with its inverse is trivial (toEq). -/
theorem gluePath_trans_symm_toEq {A B C : Type u} {s : Span A B C} (c : C) :
    (Path.trans (@Pushout.gluePath A B C s c)
      (Path.symm (@Pushout.gluePath A B C s c))).toEq = rfl := by
  simp

/-- The symmetric of the glue path links inr back to inl. -/
theorem gluePath_symm_proof {A B C : Type u} {s : Span A B C} (c : C) :
    (Path.symm (@Pushout.gluePath A B C s c)).proof =
      (Pushout.glue c).symm := rfl

/-- congrArg through the left pushout inclusion. -/
theorem congrArg_pushout_inl {A B C : Type u} {s : Span A B C}
    {a₁ a₂ : A} (p : Path a₁ a₂) :
    congrArg (Pushout.inl (s := s)) p =
      congrArg (@Pushout.inl A B C s) p := rfl

/-- congrArg through the right pushout inclusion. -/
theorem congrArg_pushout_inr {A B C : Type u} {s : Span A B C}
    {b₁ b₂ : B} (p : Path b₁ b₂) :
    congrArg (Pushout.inr (s := s)) p =
      congrArg (@Pushout.inr A B C s) p := rfl

/-- Transport along gluePath computes via the glue equality. -/
theorem transport_gluePath {A B C : Type u} {s : Span A B C}
    {D : Pushout s → Type v} (c : C)
    (x : D (Pushout.inl (s.left c))) :
    (Path.transport (D := D) (Pushout.gluePath c) x : D (Pushout.inr (s.right c))) =
      (Pushout.glue c ▸ x : D (Pushout.inr (s.right c))) := by
  simp [Path.transport]

/-- Naturality of the glue: applying a function over the pushout
respects the identification (at the propositional level). -/
theorem pushout_naturality {A B C : Type u} {s : Span A B C} {D : Type v}
    (fA : A → D) (fB : B → D)
    (hglue : ∀ c, fA (s.left c) = fB (s.right c))
    (c : C) :
    _root_.congrArg (Pushout.lift fA fB hglue) (Pushout.glue c) = hglue c := by
  rfl

/-- The coequalizer path composed with its inverse is trivial (toEq). -/
theorem coeqPath_trans_symm_toEq {X Y : Type u} {f g : X → Y} (x : X) :
    (Path.trans (@Coequalizer.coeqPath X Y f g x)
      (Path.symm (@Coequalizer.coeqPath X Y f g x))).toEq = rfl := by
  simp

/-- congrArg through coequalizer inclusion. -/
theorem congrArg_coeq_inc {X Y : Type u} {f g : X → Y}
    {y₁ y₂ : Y} (p : Path y₁ y₂) :
    congrArg (@Coequalizer.inc X Y f g) p =
      congrArg (Coequalizer.inc (f := f) (g := g)) p := rfl

/-- Transport along coeqPath computes via the coeq equality. -/
theorem transport_coeqPath {X Y : Type u} {f g : X → Y}
    {D : Coequalizer f g → Type v} (x : X)
    (d : D (Coequalizer.inc (f x))) :
    (Path.transport (D := D) (Coequalizer.coeqPath x) d : D (Coequalizer.inc (g x))) =
      (Coequalizer.coeq x ▸ d : D (Coequalizer.inc (g x))) := by
  simp [Path.transport]

/-- Pushout of the trivial span over PEmpty is just the coproduct. -/
theorem pushout_empty_span (A B : Type u) :
    ∀ (x : @Pushout A B PEmpty ⟨PEmpty.elim, PEmpty.elim⟩),
      (∃ a, x = Pushout.inl a) ∨ (∃ b, x = Pushout.inr b) := by
  intro x
  induction x using Quot.ind with
  | mk s =>
    match s with
    | Sum.inl a => exact Or.inl ⟨a, rfl⟩
    | Sum.inr b => exact Or.inr ⟨b, rfl⟩

/-- Functoriality: a map of spans induces a map of pushouts. -/
def Pushout.map {A₁ B₁ C₁ A₂ B₂ C₂ : Type u}
    {s₁ : Span A₁ B₁ C₁} {s₂ : Span A₂ B₂ C₂}
    (fA : A₁ → A₂) (fB : B₁ → B₂) (fC : C₁ → C₂)
    (hleft : ∀ c, fA (s₁.left c) = s₂.left (fC c))
    (hright : ∀ c, fB (s₁.right c) = s₂.right (fC c)) :
    Pushout s₁ → Pushout s₂ :=
  Quot.lift
    (fun x => match x with
      | Sum.inl a => Pushout.inl (fA a)
      | Sum.inr b => Pushout.inr (fB b))
    (fun x y r => by
      cases r with
      | glue c =>
        show Pushout.inl (fA (s₁.left c)) = Pushout.inr (fB (s₁.right c))
        calc Pushout.inl (fA (s₁.left c))
            = Pushout.inl (s₂.left (fC c)) := _root_.congrArg Pushout.inl (hleft c)
          _ = Pushout.inr (s₂.right (fC c)) := Pushout.glue (fC c)
          _ = Pushout.inr (fB (s₁.right c)) := _root_.congrArg Pushout.inr (hright c).symm)

/-- Pushout map respects inl. -/
theorem Pushout.map_inl {A₁ B₁ C₁ A₂ B₂ C₂ : Type u}
    {s₁ : Span A₁ B₁ C₁} {s₂ : Span A₂ B₂ C₂}
    (fA : A₁ → A₂) (fB : B₁ → B₂) (fC : C₁ → C₂)
    (hleft : ∀ c, fA (s₁.left c) = s₂.left (fC c))
    (hright : ∀ c, fB (s₁.right c) = s₂.right (fC c))
    (a : A₁) :
    Pushout.map fA fB fC hleft hright (Pushout.inl a) = Pushout.inl (fA a) := rfl

/-- Pushout map respects inr. -/
theorem Pushout.map_inr {A₁ B₁ C₁ A₂ B₂ C₂ : Type u}
    {s₁ : Span A₁ B₁ C₁} {s₂ : Span A₂ B₂ C₂}
    (fA : A₁ → A₂) (fB : B₁ → B₂) (fC : C₁ → C₂)
    (hleft : ∀ c, fA (s₁.left c) = s₂.left (fC c))
    (hright : ∀ c, fB (s₁.right c) = s₂.right (fC c))
    (b : B₁) :
    Pushout.map fA fB fC hleft hright (Pushout.inr b) = Pushout.inr (fB b) := rfl

end Pushouts
end HoTT
end Path
end ComputationalPaths
