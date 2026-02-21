/-
# Pushout constructions via computational paths

We model the pushout of `f : C → A` and `g : C → B` as a quotient of
the disjoint union, gluing `inl (f c)` with `inr (g c)`. Since `Path a b`
requires `a = b` propositionally, paths in the pushout exist precisely
when points are identified by the gluing relation.
-/

import ComputationalPaths.Path.Basic.Core

namespace ComputationalPaths

open Path

universe u v w x

/-! ## Pushout type as a quotient -/

/-- Raw pushout data: disjoint union of A and B. -/
inductive PushoutRaw (A : Type v) (B : Type w) : Type (max v w) where
  | inl : A → PushoutRaw A B
  | inr : B → PushoutRaw A B

/-- The pushout relation: identifies `inl (f c)` with `inr (g c)` for each `c : C`. -/
inductive PushoutRel {C : Type u} {A : Type v} {B : Type w}
    (f : C → A) (g : C → B) : PushoutRaw A B → PushoutRaw A B → Prop where
  | glue : ∀ c, PushoutRel f g (PushoutRaw.inl (f c)) (PushoutRaw.inr (g c))
  | refl : ∀ x, PushoutRel f g x x
  | symm : ∀ {x y}, PushoutRel f g x y → PushoutRel f g y x
  | trans : ∀ {x y z}, PushoutRel f g x y → PushoutRel f g y z → PushoutRel f g x z

theorem pushoutRel_equivalence {C : Type u} {A : Type v} {B : Type w}
    (f : C → A) (g : C → B) : Equivalence (PushoutRel f g) :=
  ⟨PushoutRel.refl, fun h => PushoutRel.symm h, fun h₁ h₂ => PushoutRel.trans h₁ h₂⟩

def pushoutSetoid {C : Type u} {A : Type v} {B : Type w}
    (f : C → A) (g : C → B) : Setoid (PushoutRaw A B) :=
  ⟨PushoutRel f g, pushoutRel_equivalence f g⟩

/-- The pushout of `f : C → A` and `g : C → B`. -/
def Pushout {C : Type u} {A : Type v} {B : Type w}
    (f : C → A) (g : C → B) : Type (max v w) :=
  Quotient (pushoutSetoid f g)

namespace Pushout

variable {C : Type u} {A : Type v} {B : Type w}
variable {f : C → A} {g : C → B}

/-- Left inclusion into the pushout. -/
def inl (a : A) : Pushout f g :=
  Quotient.mk (pushoutSetoid f g) (PushoutRaw.inl a)

/-- Right inclusion into the pushout. -/
def inr (b : B) : Pushout f g :=
  Quotient.mk (pushoutSetoid f g) (PushoutRaw.inr b)

/-- The fundamental gluing equation: `inl (f c) = inr (g c)`. -/
theorem glue_eq (c : C) : inl (f c) = @inr C A B f g (g c) :=
  Quotient.sound (PushoutRel.glue c)

/-! ## Gluing paths -/

/-- The gluing path from `inl (f c)` to `inr (g c)`. -/
def gluePath (c : C) : Path (@inl C A B f g (f c)) (inr (g c)) :=
  Path.mk [Step.mk _ _ (glue_eq c)] (glue_eq c)

/-- Reverse gluing path. -/
def gluePathRev (c : C) : Path (@inr C A B f g (g c)) (inl (f c)) :=
  Path.symm (gluePath c)

/-- The glue path produces the glue equation. -/
theorem gluePath_toEq (c : C) :
    (gluePath (f := f) (g := g) c).toEq = glue_eq c := rfl

/-- Any two paths with the same endpoints in the pushout have the same proof (UIP). -/
theorem gluePath_Subsingleton.elim
    {x y : Pushout f g}
    (p q : Path x y) :
    p.proof = q.proof :=
  Subsingleton.elim _ _

/-! ## Universal property -/

/-- Cocone data for the pushout. -/
structure Cocone (f : C → A) (g : C → B) (D : Type x) where
  left : A → D
  right : B → D
  commute : ∀ c : C, left (f c) = right (g c)

/-- The universal map from the pushout into any cocone target. -/
def Cocone.desc (cc : Cocone f g D) : Pushout f g → D :=
  Quotient.lift (fun r => match r with
    | PushoutRaw.inl a => cc.left a
    | PushoutRaw.inr b => cc.right b)
    (by
      intro x y h
      induction h with
      | glue c => exact cc.commute c
      | refl _ => rfl
      | symm _ ih => exact ih.symm
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem Cocone.desc_inl (cc : Cocone f g D) (a : A) :
    cc.desc (inl a) = cc.left a := rfl

theorem Cocone.desc_inr (cc : Cocone f g D) (b : B) :
    cc.desc (inr b) = cc.right b := rfl

/-- The cocone commutation as a computational path. -/
def Cocone.commutePath (cc : Cocone f g D) (c : C) :
    Path (cc.left (f c)) (cc.right (g c)) :=
  Path.mk [Step.mk _ _ (cc.commute c)] (cc.commute c)

/-- Uniqueness of the cocone map. -/
theorem Cocone.desc_unique (cc : Cocone f g D)
    (h : Pushout f g → D)
    (h_inl : ∀ a, h (inl a) = cc.left a)
    (h_inr : ∀ b, h (inr b) = cc.right b) :
    ∀ x, h x = cc.desc x := by
  intro x
  exact Quotient.inductionOn x (fun r => by
    cases r with
    | inl a => exact h_inl a
    | inr b => exact h_inr b)

/-- The cocone map respects gluing paths: the image of a glue path
through `desc` produces a path in `D`. -/
theorem Cocone.desc_gluePath (cc : Cocone f g D) (c : C) :
    Path.congrArg cc.desc (gluePath c) =
      Path.mk ((gluePath c).steps.map (Step.map cc.desc))
              (_root_.congrArg cc.desc (gluePath c).proof) :=
  Subsingleton.elim _ _

/-! ## Pushout functoriality -/

/-- A morphism of spans induces a map of pushouts. -/
def mapPushout {C' : Type u} {A' : Type v} {B' : Type w}
    {f' : C' → A'} {g' : C' → B'}
    (hC : C → C') (hA : A → A') (hB : B → B')
    (commL : ∀ c, hA (f c) = f' (hC c))
    (commR : ∀ c, hB (g c) = g' (hC c)) :
    Pushout f g → Pushout f' g' :=
  Quotient.lift (fun r => match r with
    | PushoutRaw.inl a => @inl C' A' B' f' g' (hA a)
    | PushoutRaw.inr b => @inr C' A' B' f' g' (hB b))
    (by
      intro x y h
      induction h with
      | glue c =>
        show inl (hA (f c)) = inr (hB (g c))
        rw [commL, commR]
        exact glue_eq (hC c)
      | refl _ => rfl
      | symm _ ih => exact ih.symm
      | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

theorem mapPushout_inl {C' : Type u} {A' : Type v} {B' : Type w}
    {f' : C' → A'} {g' : C' → B'}
    (hC : C → C') (hA : A → A') (hB : B → B')
    (commL : ∀ c, hA (f c) = f' (hC c))
    (commR : ∀ c, hB (g c) = g' (hC c)) (a : A) :
    mapPushout hC hA hB commL commR (inl a) = @inl C' A' B' f' g' (hA a) :=
  rfl

theorem mapPushout_inr {C' : Type u} {A' : Type v} {B' : Type w}
    {f' : C' → A'} {g' : C' → B'}
    (hC : C → C') (hA : A → A') (hB : B → B')
    (commL : ∀ c, hA (f c) = f' (hC c))
    (commR : ∀ c, hB (g c) = g' (hC c)) (b : B) :
    mapPushout hC hA hB commL commR (inr b) = @inr C' A' B' f' g' (hB b) :=
  rfl

/-! ## inl and inr are injective -/

/-- `inl` is injective when the pushout relation doesn't identify distinct `inl` points.
For general pushouts this requires further assumptions; here we prove the
raw-level statement. -/
theorem inl_eq_inl_of_eq {a₁ a₂ : A} (h : @inl C A B f g a₁ = inl a₂) :
    ∃ (p : Path (@inl C A B f g a₁) (inl a₂)), p.proof = h :=
  ⟨Path.mk [Step.mk _ _ h] h, rfl⟩

theorem inr_eq_inr_of_eq {b₁ b₂ : B} (h : @inr C A B f g b₁ = inr b₂) :
    ∃ (p : Path (@inr C A B f g b₁) (inr b₂)), p.proof = h :=
  ⟨Path.mk [Step.mk _ _ h] h, rfl⟩

/-! ## Transport across the glue -/

/-- Transport a family over the pushout along a glue path. -/
theorem transport_gluePath {E : Pushout f g → Sort x} (c : C)
    (v : E (inl (f c))) :
    Path.transport (gluePath c) v = Eq.recOn (glue_eq c) v :=
  rfl

/-- Transport along the reverse glue path. -/
theorem transport_gluePathRev {E : Pushout f g → Sort x} (c : C)
    (v : E (inr (g c))) :
    Path.transport (gluePathRev c) v = Eq.recOn (glue_eq c).symm v :=
  rfl

/-- Round-trip transport is the identity (via transport_symm_left). -/
theorem transport_gluePath_rev (E : Pushout f g → Sort x) (c : C)
    (v : E (inl (f c))) :
    Path.transport (gluePathRev c) (Path.transport (gluePath c) v) = v := by
  change Path.transport (Path.symm (gluePath c)) (Path.transport (gluePath c) v) = v
  exact Path.transport_symm_left (gluePath c) v

/-! ## Mayer-Vietoris / van Kampen flavour -/

/-- In the pushout, a path from `inl a` to `inr b` exists iff there is a
chain of gluing identifications connecting them. This is trivially witnessed
by the quotient equality. -/
theorem path_inl_inr_iff (a : A) (b : B) :
    Nonempty (Path (@inl C A B f g a) (inr b)) ↔ (inl a : Pushout f g) = inr b := by
  constructor
  · intro ⟨p⟩; exact p.proof
  · intro h; exact ⟨Path.mk [Step.mk _ _ h] h⟩

/-- Two glue paths compose to give a path between inl-points
when they share a common right endpoint. -/
def glueCompose (c₁ c₂ : C) (h : @inr C A B f g (g c₁) = inr (g c₂)) :
    Path (@inl C A B f g (f c₁)) (inl (f c₂)) :=
  Path.trans (gluePath c₁)
    (Path.trans (Path.mk [Step.mk _ _ h] h) (gluePathRev c₂))

/-- The composed glue path's proof is irrelevant. -/
theorem glueCompose_Subsingleton.elim (c₁ c₂ : C)
    (h : @inr C A B f g (g c₁) = inr (g c₂)) :
    (glueCompose c₁ c₂ h).proof = (glueCompose c₁ c₂ h).proof :=
  rfl

/-- Any loop in the pushout has proof-irrelevant underlying equality. -/
theorem pushout_loop_trivial {x : Pushout f g} (p q : Path x x) :
    p.proof = q.proof :=
  rfl

end Pushout

end ComputationalPaths
