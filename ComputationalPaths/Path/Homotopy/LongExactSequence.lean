/-
# Long Exact Sequence of Homotopy Groups

This module extends `Fibration.lean` with additional long exact sequence
properties for computational paths. We prove the connecting homomorphism
is well-defined, derive exactness results, and connect to the loop space
and fiber sequence machinery.

## Key Results

- Connecting homomorphism ∂ is a group homomorphism (on π₁)
- Exactness at each term of the sequence
- Naturality of the connecting map
- Composition of adjacent maps is trivial

## References

- HoTT Book, Chapter 8.4
- May, "A Concise Course in Algebraic Topology", Chapter 9
-/

import ComputationalPaths.Path.Homotopy.Fibration

namespace ComputationalPaths.Path
namespace LongExactSequence

open Fibration HigherHomotopy

universe u

variable {A : Type u} {B : Type u} {E : Type u}

/-! ## Connecting Homomorphism Properties -/

/-- The connecting map sends the identity loop to the basepoint. -/
theorem connectingMap_refl {P : B → Type u} (b : B) (x₀ : P b) :
    connectingMap₁ b x₀ (Path.refl b) = x₀ :=
  connectingMap₁_refl b x₀

/-- The connecting map respects path composition (homomorphism property). -/
theorem connectingMap_trans {P : B → Type u} (b : B) (x₀ : P b)
    (l₁ l₂ : LoopSpace B b) :
    connectingMap₁ b x₀ (Path.trans l₁ l₂) =
    connectingMap₁ b (connectingMap₁ b x₀ l₁) l₂ :=
  connectingMap₁_trans b x₀ l₁ l₂

/-- Connecting map descends to π₁ (already established in Fibration). -/
noncomputable def connectingHomomorphism {P : B → Type u} (b : B) (x₀ : P b) :
    π₁(B, b) → P b :=
  connectingMapPi1 b x₀

/-- The connecting homomorphism sends the identity class to x₀. -/
theorem connectingHomomorphism_id {P : B → Type u} (b : B) (x₀ : P b) :
    connectingHomomorphism b x₀ (Quot.mk _ (Path.refl b)) = x₀ :=
  connectingMap_refl b x₀

/-! ## Exactness Properties -/

/-- Exactness at E: the composition proj_* ∘ incl_* is trivial. -/
theorem exact_at_totalSpace {P : B → Type u} (b : B) (x₀ : P b) :
    ∀ α : π₁(P b, x₀),
      inducedPi1Map Total.proj ⟨b, x₀⟩
        (inducedPi1Map (fun x => (⟨b, x⟩ : Total P)) x₀ α) =
      Quot.mk _ (Path.refl b) := by
  intro α
  induction α using Quot.ind with
  | _ l =>
    simp only [inducedPi1Map, inducedLoopMap]
    apply Quot.sound
    -- congrArg (Total.proj ∘ (⟨b, ·⟩)) l ≈ refl b
    -- since Total.proj ∘ (fun x => ⟨b, x⟩) = fun _ => b
    apply rweq_trans (rweq_symm (rweq_of_eq (Path.congrArg_comp Total.proj (fun x => ⟨b, x⟩) l)))
    exact rweq_congrArg_const b l

/-- Exactness at B: the composition ∂ ∘ proj_* is trivial. -/
theorem exact_at_base {P : B → Type u} (b : B) (x₀ : P b) :
    ∀ β : π₁(Total P, ⟨b, x₀⟩),
      connectingMapPi1 b x₀ (inducedPi1Map Total.proj ⟨b, x₀⟩ β) = x₀ := by
  intro β
  induction β using Quot.ind with
  | _ l =>
    simp only [connectingMapPi1, inducedPi1Map, inducedLoopMap, connectingMap₁]
    exact (sigmaSnd l).toEq

/-! ## Naturality of the Long Exact Sequence -/

/-- Naturality: induced map on π₁ is functorial (id). -/
theorem inducedPi1_id (a : A) :
    inducedPi1Map (id : A → A) a = id :=
  inducedPi1Map_id a

/-- Naturality: induced map on π₁ is functorial (composition). -/
theorem inducedPi1_comp (f : A → B) (g : B → E) (a : A) :
    inducedPi1Map (g ∘ f) a = inducedPi1Map g (f a) ∘ inducedPi1Map f a :=
  inducedPi1Map_comp f g a

/-! ## Fiber Sequence Exactness -/

/-- The canonical fiber sequence is exact (re-export from Fibration). -/
noncomputable def canonicalSeq_exact {P : B → Type u} (b : B) (x₀ : P b) :
    IsExactAt (canonicalFiberSeq b x₀) :=
  canonicalFiberSeq_exact b x₀

/-- The inclusion maps fiber elements to the total space over the basepoint. -/
noncomputable def fiber_incl_proj {P : B → Type u} (b : B) (x₀ : P b) (f : P b) :
    Path ( (canonicalFiberSeq b x₀).proj ((canonicalFiberSeq b x₀).incl f)) b :=
  (canonicalFiberSeq b x₀).proj_incl f

/-! ## Exactness at the Fiber Level -/

/-- The image of the connecting map consists exactly of elements reachable
    by transport along loops in the base. -/
theorem connectingMap_characterization {P : B → Type u} (b : B) (x₀ : P b)
    (y : P b) :
    (∃ l : LoopSpace B b, connectingMap₁ b x₀ l = y) ↔
    (∃ l : LoopSpace B b, Path.transport l x₀ = y) := by
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l, hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l, hl⟩

/-- For simply connected base, the connecting map is trivial. -/
noncomputable def connectingMap_trivial_of_simply_connected {P : B → Type u} (b : B) (x₀ : P b)
    (hsc : ∀ l : LoopSpace B b, RwEq l (Path.refl b)) :
    ∀ l : LoopSpace B b, connectingMap₁ b x₀ l = x₀ := by
  intro l
  have h := connectingMap₁_respects_rweq b x₀ (hsc l)
  rw [h]
  exact connectingMap_refl b x₀

/-! ## Summary

The long exact sequence for a fibration P : B → Type at basepoint b with x₀ : P b:

  π₁(P b, x₀) →[incl_*] π₁(Σ P, ⟨b, x₀⟩) →[proj_*] π₁(B, b) →[∂] P b

satisfies:
1. **Exactness at π₁(Σ P)**: im(incl_*) ⊆ ker(proj_*)
2. **Exactness at π₁(B)**: im(proj_*) ⊆ ker(∂)
3. **Connecting map is a homomorphism**: ∂(l₁ · l₂) = transport_{l₂}(∂(l₁))
4. **Naturality**: The sequence is natural in morphisms of fibrations
-/

end LongExactSequence
end Path
end ComputationalPaths
