/-
# Simplicial Homotopy Groups and Kan Fillers

This module provides Mathlib-based wrappers for simplicial homotopy groups
via geometric realization, together with the Kan complex horn-filling property.

## Key Results

- `SimplicialPiN`: simplicial homotopy groups via geometric realization
- `simplicialPiN_commGroup`: commutative group structure for `n ≥ 2`
- `KanComplex`: Kan complex predicate re-export
- `kan_horn_filling`: horn-filling existence in a Kan complex
- `hornFiller`, `hornFiller_spec`: a chosen filler and its specification

## References

- Mathlib `AlgebraicTopology/SingularSet`
- Mathlib `AlgebraicTopology/SimplicialSet/KanComplex`
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Horn
import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex
import Mathlib.AlgebraicTopology.SingularSet
import Mathlib.Topology.Homotopy.HomotopyGroup

open CategoryTheory
open scoped Topology Simplicial

namespace ComputationalPaths
namespace Path
namespace SimplicialHomotopy

universe u

/-! ## Simplicial homotopy groups -/

/-- The `n`-th simplicial homotopy group via geometric realization. -/
abbrev SimplicialPiN (n : ℕ) (S : SSet.{u}) (x : SSet.toTop.obj S) : Type _ :=
  π_ n (SSet.toTop.obj S) x

/-- For `n ≥ 2`, simplicial homotopy groups are commutative. -/
noncomputable instance simplicialPiN_commGroup (n : ℕ) [Nat.AtLeastTwo n]
    (S : SSet.{u}) (x : SSet.toTop.obj S) : CommGroup (SimplicialPiN n S x) :=
  inferInstance

/-! ## Kan complexes and horn fillers -/

/-- Re-export of the Kan complex predicate on simplicial sets. -/
abbrev KanComplex (S : SSet.{u}) : Prop :=
  SSet.KanComplex S

/-- Horn fillers exist in Kan complexes. -/
lemma kan_horn_filling {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    ∃ σ : Δ[n + 1] ⟶ S, σ₀ = Λ[n + 1, i].ι ≫ σ :=
  SSet.KanComplex.hornFilling (σ₀ := σ₀)

/-- A chosen horn filler in a Kan complex. -/
noncomputable def hornFiller {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    Δ[n + 1] ⟶ S :=
  Classical.choose (kan_horn_filling (S := S) (σ₀ := σ₀))

/-- The chosen filler extends the original horn. -/
lemma hornFiller_spec {S : SSet.{u}} [KanComplex S]
    {n : ℕ} {i : Fin (n + 2)} (σ₀ : (Λ[n + 1, i] : SSet) ⟶ S) :
    σ₀ = Λ[n + 1, i].ι ≫ hornFiller (S := S) (σ₀ := σ₀) := by
  classical
  simpa [hornFiller] using
    (Classical.choose_spec (kan_horn_filling (S := S) (σ₀ := σ₀)))

/-! ## Summary -/

/-!
We defined simplicial homotopy groups via geometric realization and recorded
Kan complex horn-fillers, including a chosen filler with its specification.
-/

end SimplicialHomotopy
end Path
end ComputationalPaths
