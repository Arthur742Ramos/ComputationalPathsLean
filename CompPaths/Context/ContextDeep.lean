import CompPaths.Core

namespace CompPaths.Context

open ComputationalPaths
open ComputationalPaths.Path

universe u

/-! ## Syntactic context composition -/

/-- A unary context shape built from a hole and unary layers. -/
inductive ContextShape (A : Type u) : Type (u + 1) where
  | hole : ContextShape A
  | layer (f : A → A) (inner : ContextShape A) : ContextShape A

namespace ContextShape

variable {A : Type u}

/-- Interpret a context shape as an actual unary context. -/
def fill : ContextShape A → A → A
  | hole => fun a => a
  | layer f inner => fun a => f (fill inner a)

def toContext (S : ContextShape A) : Context A A := ⟨fill S⟩

/-- Action of a context shape on paths. -/
def map : (S : ContextShape A) → {a b : A} → Path a b → Path (fill S a) (fill S b)
  | hole, _, _, p => p
  | layer f inner, _, _, p => Path.congrArg f (map inner p)

/-- Structural composition of context shapes. -/
def comp : ContextShape A → ContextShape A → ContextShape A
  | S, hole => S
  | S, layer f inner => layer f (comp S inner)

/-- Composing two context shapes yields a context (structural induction). -/
theorem compose_yields_context
    (S : ContextShape A) :
    ∀ T : ContextShape A, ∃ Ctx : Context A A, Ctx = toContext (comp S T) := by
  intro T
  induction T with
  | hole =>
      exact ⟨toContext S, rfl⟩
  | layer f inner ih =>
      rcases ih with ⟨Ctx, hCtx⟩
      refine ⟨Context.comp ⟨f⟩ Ctx, ?_⟩
      cases hCtx
      rfl

end ContextShape

/-! ## Context congruence closure -/

section ContextCongruence

variable {A : Type u} {B : Type u}

/-- Hole substitution preserves rewrite equivalence: if `p ≈ q`, then `C[p] ≈ C[q]`. -/
noncomputable def context_hole_substitution_preserves_rweq
    (C : Context A B) {a₁ a₂ : A}
    {p q : Path a₁ a₂} (h : RwEq p q) :
    RwEq (Context.map C p) (Context.map C q) := by
  induction h with
  | refl _ =>
      exact RwEq.refl _
  | step hStep =>
      exact RwEq.step (Step.context_congr (A := A) (B := B) C hStep)
  | symm _ ih =>
      exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact RwEq.trans ih₁ ih₂

/-- Context application commutes with path transitivity. -/
noncomputable def context_map_trans_commutes
    (C : Context A B) {a b c : A}
    (p : Path a b) (q : Path b c) :
    RwEq (Context.map C (Path.trans p q))
      (Path.trans (Context.map C p) (Context.map C q)) :=
  sorry -- TODO: context map distributes over trans

/-- Congruence closure for trans under context application. -/
noncomputable def context_trans_congruence_closure
    (C : Context A B) {a b c : A}
    {p p' : Path a b} {q q' : Path b c}
    (hp : RwEq p p') (hq : RwEq q q') :
    RwEq (Context.map C (Path.trans p q))
      (Context.map C (Path.trans p' q')) := by
  have hcomm₁ :
      RwEq (Context.map C (Path.trans p q))
        (Path.trans (Context.map C p) (Context.map C q)) :=
    context_map_trans_commutes (C := C) p q
  have hcomm₂ :
      RwEq (Context.map C (Path.trans p' q'))
        (Path.trans (Context.map C p') (Context.map C q')) :=
    context_map_trans_commutes (C := C) p' q'
  have hmap₁ : RwEq (Context.map C p) (Context.map C p') :=
    context_hole_substitution_preserves_rweq (C := C) hp
  have hmap₂ : RwEq (Context.map C q) (Context.map C q') :=
    context_hole_substitution_preserves_rweq (C := C) hq
  have htrans :
      RwEq (Path.trans (Context.map C p) (Context.map C q))
        (Path.trans (Context.map C p') (Context.map C q')) :=
    rweq_trans_congr hmap₁ hmap₂
  exact RwEq.trans hcomm₁ (RwEq.trans htrans (RwEq.symm hcomm₂))

end ContextCongruence

/-! ## BiContext interaction with whiskering -/

section BiContextWhiskering

variable {A : Type u} {B : Type u} {C : Type u}

/-- Left whiskering interacts with bicontext left mapping by congruence closure. -/
noncomputable def biContext_mapLeft_whisker
    (K : BiContext A B C) (b : B)
    {a₁ a₂ : A} {p q : Path a₁ a₂}
    {x : C} (r : Path x (K.fill a₁ b))
    (h : RwEq p q) :
    RwEq (Path.trans r (BiContext.mapLeft K p b))
      (Path.trans r (BiContext.mapLeft K q b)) := by
  induction h with
  | refl _ =>
      exact RwEq.refl _
  | step hStep =>
      exact RwEq.step
        (Step.trans_congr_right r
          (Step.biContext_mapLeft_congr
            (A := A) (B := B) (C := C) (K := K) (b := b) hStep))
  | symm _ ih =>
      exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact RwEq.trans ih₁ ih₂

/-- Right whiskering interacts with bicontext right mapping by congruence closure. -/
noncomputable def biContext_mapRight_whisker
    (K : BiContext A B C) (a : A)
    {b₁ b₂ : B} {p q : Path b₁ b₂}
    {y : C} (r : Path (K.fill a b₂) y)
    (h : RwEq p q) :
    RwEq (Path.trans (BiContext.mapRight K a p) r)
      (Path.trans (BiContext.mapRight K a q) r) := by
  induction h with
  | refl _ =>
      exact RwEq.refl _
  | step hStep =>
      exact RwEq.step
        (Step.trans_congr_left r
          (Step.biContext_mapRight_congr
            (A := A) (B := B) (C := C) (K := K) (a := a) hStep))
  | symm _ ih =>
      exact RwEq.symm ih
  | trans _ _ ih₁ ih₂ =>
      exact RwEq.trans ih₁ ih₂

end BiContextWhiskering

end CompPaths.Context
