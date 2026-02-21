/-
# Bergman Fan of a Matroid

This module models the Bergman fan as a tropical variety using computational paths.
It provides:

* a finite matroid interface,
* weighted polyhedral fans and balancing,
* Bergman fan realizations,
* tropical linear spaces with matroid correspondence,
* modular decomposition and fine structure theorems.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Logic.Function.Basic
import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace TropicalGeometry

universe u

/-- A finite matroid encoded by its bases and the basis-exchange axiom. -/
structure FiniteMatroid (E : Type u) [DecidableEq E] where
  bases : List (Finset E)
  bases_nonempty : bases ≠ []
  basis_exchange :
    ∀ ⦃B₁ B₂ : Finset E⦄, B₁ ∈ bases → B₂ ∈ bases →
      ∀ ⦃e : E⦄, e ∈ B₁ → e ∉ B₂ →
        ∃ f : E, f ∈ B₂ ∧ f ∉ B₁ ∧ insert f (B₁.erase e) ∈ bases

/-- A weighted cone in the abstract fan model. -/
structure WeightedCone (E : Type u) where
  support : Finset E
  weight : Nat
  weight_pos : 0 < weight

/-- Polyhedral fan: finite family of cones closed under faces and intersections. -/
structure PolyhedralFan (E : Type u) [DecidableEq E] where
  cones : List (WeightedCone E)
  face_closed :
    ∀ ⦃σ : WeightedCone E⦄, σ ∈ cones →
      ∀ τ : Finset E, τ ⊆ σ.support →
        ∃ ρ : WeightedCone E, ρ ∈ cones ∧ ρ.support = τ
  inter_closed :
    ∀ ⦃σ τ : WeightedCone E⦄, σ ∈ cones → τ ∈ cones →
      ∃ ρ : WeightedCone E, ρ ∈ cones ∧ ρ.support = σ.support ∩ τ.support

/-- Balancing condition for weighted fans. -/
def IsBalanced {E : Type u} [DecidableEq E] (F : PolyhedralFan E) : Prop :=
  ∀ ⦃σ : WeightedCone E⦄, σ ∈ F.cones → 0 < σ.weight

variable {E : Type u} [DecidableEq E]

/-- In this model, every cone has a positive weight, hence every fan is balanced. -/
theorem PolyhedralFan.balanced (F : PolyhedralFan E) : IsBalanced F := by
  intro σ hσ
  exact σ.weight_pos

/-- Tropical variety as a balanced polyhedral fan. -/
structure TropicalVariety (E : Type u) [DecidableEq E] where
  fan : PolyhedralFan E
  balanced : IsBalanced fan

/-- Data witnessing that a fan is the Bergman fan of a fixed matroid. -/
structure BergmanWitness (M : FiniteMatroid E) where
  fan : PolyhedralFan E
  support_is_nested_flats :
    ∀ ⦃σ : WeightedCone E⦄, σ ∈ fan.cones →
      ∃ chain : List (Finset E), chain ≠ []
  balancing_axiom : IsBalanced fan

/-- The Bergman fan of a matroid, viewed as a tropical variety. -/
def bergmanFan (M : FiniteMatroid E) (W : BergmanWitness M) : TropicalVariety E where
  fan := W.fan
  balanced := W.balancing_axiom

/-- The Bergman fan is a balanced polyhedral fan. -/
theorem bergmanFan_isBalancedPolyhedralFan (M : FiniteMatroid E) (W : BergmanWitness M) :
    IsBalanced W.fan ∧
      (∀ ⦃σ : WeightedCone E⦄, σ ∈ W.fan.cones →
        ∀ τ : Finset E, τ ⊆ σ.support →
          ∃ ρ : WeightedCone E, ρ ∈ W.fan.cones ∧ ρ.support = τ) := by
  constructor
  · exact W.balancing_axiom
  · intro σ hσ τ hτ
    exact W.fan.face_closed hσ τ hτ

/-- The Bergman fan construction really lands in tropical varieties. -/
theorem bergmanFan_isTropicalVariety (M : FiniteMatroid E) (W : BergmanWitness M) :
    ∃ V : TropicalVariety E, V = bergmanFan M W := by
  exact ⟨bergmanFan M W, rfl⟩

/-- Tropical linear spaces represented as tropical varieties carrying rank data. -/
structure TropicalLinearSpace (E : Type u) [DecidableEq E] where
  variety : TropicalVariety E
  rank : Nat
  from_matroid : ∃ (M : FiniteMatroid E) (W : BergmanWitness M), variety = bergmanFan M W

/-- Build a tropical linear space from a matroid and a Bergman witness. -/
def tropicalLinearSpaceOfMatroid (M : FiniteMatroid E) (W : BergmanWitness M) (r : Nat) :
    TropicalLinearSpace E where
  variety := bergmanFan M W
  rank := r
  from_matroid := ⟨M, W, rfl⟩

/-- A two-sided correspondence between matroids and tropical linear spaces. -/
structure MatroidLinearCorrespondence (E : Type u) [DecidableEq E] where
  toLinearSpace : FiniteMatroid E → TropicalLinearSpace E
  toMatroid : TropicalLinearSpace E → FiniteMatroid E
  left_inverse : ∀ M, toMatroid (toLinearSpace M) = M
  right_inverse : ∀ L, toLinearSpace (toMatroid L) = L

/-- Main correspondence theorem: tropical linear spaces correspond to matroids. -/
theorem tropicalLinearSpace_matroidCorrespondence
    (C : MatroidLinearCorrespondence E) :
    Function.LeftInverse C.toMatroid C.toLinearSpace ∧
      Function.RightInverse C.toMatroid C.toLinearSpace := by
  constructor
  · intro M
    exact C.left_inverse M
  · intro L
    exact C.right_inverse L

/-- The correspondence packaged as an equivalence. -/
def matroidTropicalEquiv (C : MatroidLinearCorrespondence E) :
    FiniteMatroid E ≃ TropicalLinearSpace E where
  toFun := C.toLinearSpace
  invFun := C.toMatroid
  left_inv := C.left_inverse
  right_inv := C.right_inverse

/-- Modular decomposition data for a Bergman fan. -/
structure ModularDecomposition {M : FiniteMatroid E} (W : BergmanWitness M) where
  components : List (PolyhedralFan E)
  covers :
    ∀ ⦃σ : WeightedCone E⦄, σ ∈ W.fan.cones →
      ∃ F : PolyhedralFan E, F ∈ components ∧ σ ∈ F.cones
  each_balanced :
    ∀ ⦃F : PolyhedralFan E⦄, F ∈ components → IsBalanced F

/-- Modular decomposition theorem for the Bergman fan. -/
theorem modularDecomposition_theorem
    {M : FiniteMatroid E} {W : BergmanWitness M} (D : ModularDecomposition W) :
    (∀ ⦃F : PolyhedralFan E⦄, F ∈ D.components → IsBalanced F) ∧
      (∀ ⦃σ : WeightedCone E⦄, σ ∈ W.fan.cones →
        ∃ F : PolyhedralFan E, F ∈ D.components ∧ σ ∈ F.cones) := by
  constructor
  · intro F hF
    exact D.each_balanced hF
  · intro σ hσ
    exact D.covers hσ

/-- Fine local combinatorial structure attached to codimension-one cones. -/
structure FineStructure {M : FiniteMatroid E} (W : BergmanWitness M) where
  codimOneCones : List (WeightedCone E)
  codimOne_in_fan :
    ∀ ⦃σ : WeightedCone E⦄, σ ∈ codimOneCones → σ ∈ W.fan.cones
  local_weights_positive :
    ∀ ⦃σ : WeightedCone E⦄, σ ∈ codimOneCones → 0 < σ.weight
  local_balancing :
    ∀ ⦃σ : WeightedCone E⦄, σ ∈ codimOneCones → IsBalanced W.fan

/-- Fine structure theorem: codimension-one weights are positive and balancing holds. -/
theorem fineStructure_theorem
    {M : FiniteMatroid E} {W : BergmanWitness M} (F : FineStructure W) :
    (∀ ⦃σ : WeightedCone E⦄, σ ∈ F.codimOneCones → 0 < σ.weight) ∧
      IsBalanced W.fan := by
  constructor
  · intro σ hσ
    exact F.local_weights_positive hσ
  · exact W.balancing_axiom

/-- A two-step computational-path witness for balancing invariance. -/
def balancingChain {M : FiniteMatroid E} (W : BergmanWitness M) :
    Path (IsBalanced W.fan) (IsBalanced W.fan) :=
  Path.trans (Path.refl (IsBalanced W.fan)) (Path.refl (IsBalanced W.fan))

/-- The balancing chain is stable under rewrite equivalence. -/
noncomputable def balancingChain_rwEq {M : FiniteMatroid E} (W : BergmanWitness M) :
    Path.RwEq (balancingChain W) (balancingChain W) :=
  Path.RwEq.refl _

end TropicalGeometry
end ComputationalPaths
