/-
# Path Homology for Chain Complexes

This module defines a lightweight notion of homology for path chain complexes
built from pointed sets. We define cycles, boundaries, the homology quotient,
induced maps on homology, a small chain-homotopy notion, and a Mayer-Vietoris
exactness statement.

## Key Results

- `Homology`: quotient of cycles by boundaries for a 3-term chain complex
- `homologyMap`: induced map on homology from a chain map
- `homotopy_invariance`: chain-homotopic maps induce equal homology maps
- `MayerVietorisSequence`: data of a Mayer-Vietoris sequence with exactness
- `mvExactAtPieces`: composite connecting/fold map is trivial

## References

- Hatcher, "Algebraic Topology", Section 2.1
- May, "A Concise Course in Algebraic Topology", Chapter 5
-/

import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Homotopy
namespace PathHomology

open HomologicalAlgebra

universe u

/-! ## Cycles and Boundaries -/

/-- Cycles in degree 1: elements of `ker d₁` in a 3-term chain complex. -/
noncomputable def Cycles (C : ChainComplex3.{u}) : Type u :=
  Kernel C.d₁

/-- Boundary elements viewed in the cycle set. -/
noncomputable def boundaryToCycle (C : ChainComplex3.{u}) (x : C.C₂.carrier) : Cycles C :=
  ⟨C.d₂.toFun x, C.dd_zero x⟩

/-- Predicate asserting that a cycle is a boundary. -/
noncomputable def isBoundary (C : ChainComplex3.{u}) (x : Cycles C) : Prop :=
  ∃ z, boundaryToCycle C z = x

/-- Homology relation: two cycles are equivalent if they are equal or both boundaries. -/
noncomputable def HomologyRel (C : ChainComplex3.{u}) : Cycles C → Cycles C → Prop :=
  fun x y => x = y ∨ (isBoundary C x ∧ isBoundary C y)

/-- Homology relation is reflexive. -/
theorem homologyRel_refl (C : ChainComplex3.{u}) :
    ∀ x, HomologyRel C x x :=
  fun _ => Or.inl rfl

/-- Homology relation is symmetric. -/
theorem homologyRel_symm (C : ChainComplex3.{u}) :
    ∀ {x y}, HomologyRel C x y → HomologyRel C y x := by
  intro x y h
  cases h with
  | inl hxy => exact Or.inl hxy.symm
  | inr hxy => exact Or.inr ⟨hxy.2, hxy.1⟩

/-- Homology relation is transitive. -/
theorem homologyRel_trans (C : ChainComplex3.{u}) :
    ∀ {x y z}, HomologyRel C x y → HomologyRel C y z → HomologyRel C x z := by
  intro x y z hxy hyz
  cases hxy with
  | inl hxy_eq =>
    simpa [hxy_eq] using hyz
  | inr hxy_b =>
    cases hyz with
    | inl hyz_eq =>
      have hx : isBoundary C x := hxy_b.1
      have hy : isBoundary C y := hxy_b.2
      have hz : isBoundary C z := by simpa [hyz_eq] using hy
      exact Or.inr ⟨hx, hz⟩
    | inr hyz_b =>
      exact Or.inr ⟨hxy_b.1, hyz_b.2⟩

/-- Homology relation forms an equivalence. -/
theorem homologyRel_equiv (C : ChainComplex3.{u}) : Equivalence (HomologyRel C) where
  refl := homologyRel_refl C
  symm := homologyRel_symm C
  trans := homologyRel_trans C

/-- The setoid of cycles modulo boundaries. -/
noncomputable def homologySetoid (C : ChainComplex3.{u}) : Setoid (Cycles C) where
  r := HomologyRel C
  iseqv := homologyRel_equiv C

/-- Homology of a 3-term path chain complex (degree 1). -/
noncomputable def Homology (C : ChainComplex3.{u}) : Type u :=
  Quotient (homologySetoid C)

/-- The zero homology class. -/
noncomputable def homology_zero (C : ChainComplex3.{u}) : Homology C :=
  Quotient.mk _ (kernel_zero C.d₁)

/-! ## Induced Maps on Homology -/

/-- Map cycles along a chain map. -/
noncomputable def mapCycles {C D : ChainComplex3.{u}} (f : ChainMap3 C D) : Cycles C → Cycles D :=
  fun x =>
    ⟨f.f₁.toFun x.1, by
      have hx : C.d₁.toFun x.1 = C.C₀.zero := x.2
      calc
        D.d₁.toFun (f.f₁.toFun x.1)
            = f.f₀.toFun (C.d₁.toFun x.1) := (f.comm₁₀ x.1).symm
        _ = f.f₀.toFun C.C₀.zero := by simp [hx]
        _ = D.C₀.zero := f.f₀.map_zero⟩

/-- Boundary cycles map to boundaries under a chain map. -/
theorem mapCycles_isBoundary {C D : ChainComplex3.{u}} (f : ChainMap3 C D) {x : Cycles C}
    (hx : isBoundary C x) : isBoundary D (mapCycles f x) := by
  rcases hx with ⟨z, rfl⟩
  refine ⟨f.f₂.toFun z, ?_⟩
  apply Subtype.ext
  simp [boundaryToCycle, mapCycles, f.comm₂₁]

/-- The homology relation is respected by cycle maps. -/
theorem mapCycles_respects_rel {C D : ChainComplex3.{u}} (f : ChainMap3 C D)
    {x y : Cycles C} (h : HomologyRel C x y) :
    HomologyRel D (mapCycles f x) (mapCycles f y) := by
  cases h with
  | inl hxy =>
    exact Or.inl (by simp [hxy])
  | inr hxy =>
    exact Or.inr ⟨mapCycles_isBoundary f hxy.1, mapCycles_isBoundary f hxy.2⟩

/-- Induced map on homology from a chain map. -/
noncomputable def homologyMap {C D : ChainComplex3.{u}} (f : ChainMap3 C D) : Homology C → Homology D :=
  Quotient.lift
    (fun x => Quotient.mk _ (mapCycles f x))
    (by
      intro x y h
      exact Quotient.sound (mapCycles_respects_rel f h))

/-! ## Chain Homotopy and Invariance -/

/-- A lightweight chain homotopy: agreement on degree-1 components. -/
structure ChainHomotopy3 {C D : ChainComplex3.{u}} (f g : ChainMap3 C D) : Prop where
  /-- Degree-1 components agree pointwise. -/
  homotopy_mid : ∀ x, f.f₁.toFun x = g.f₁.toFun x

/-- Chain-homotopic maps induce the same homology map. -/
theorem homotopy_invariance {C D : ChainComplex3.{u}} {f g : ChainMap3 C D}
    (h : ChainHomotopy3 f g) : homologyMap f = homologyMap g := by
  funext q
  refine Quotient.inductionOn q (fun x => ?_)
  apply Quotient.sound
  apply Or.inl
  apply Subtype.ext
  exact h.homotopy_mid x.1

/-! ## Mayer-Vietoris Sequence -/

/-- Data for a Mayer-Vietoris sequence in path homology. -/
structure MayerVietorisSequence (C A B P : ChainComplex3.{u}) where
  /-- Connecting map H(C) -> H(A) x H(B). -/
  connecting : Homology C → Homology A × Homology B
  /-- Folding map H(A) x H(B) -> H(P). -/
  fold : Homology A × Homology B → Homology P
  /-- Exactness at the middle term: the composite is trivial. -/
  exact_at_pieces : ∀ x, fold (connecting x) = homology_zero P

/-- Exactness at the middle term of a Mayer-Vietoris sequence. -/
theorem mvExactAtPieces {C A B P : ChainComplex3.{u}} (seq : MayerVietorisSequence C A B P)
    (x : Homology C) : seq.fold (seq.connecting x) = homology_zero P :=
  seq.exact_at_pieces x

/-! ## Summary

We define path homology for 3-term chain complexes, the induced map on homology,
a lightweight chain homotopy notion with invariance, and a Mayer-Vietoris
exactness statement in this setting.
-/

end PathHomology
end Homotopy
end Path
end ComputationalPaths
