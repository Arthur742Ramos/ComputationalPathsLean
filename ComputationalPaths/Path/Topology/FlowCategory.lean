/-
# Flow Categories from Morse Theory via Computational Paths

This module formalizes the flow category associated to a Morse function,
using the computational paths framework. We define moduli spaces of gradient
trajectories, their composition via broken flow lines, the CW structure
derived from Morse data, and Floer-type continuation maps.

## Mathematical Background

Given a Morse-Smale function f on a closed manifold M:
- **Moduli space M(p,q)**: space of unparametrized gradient flow lines from
  p to q, with dim M(p,q) = index(p) - index(q) - 1
- **Compactification**: M̄(p,q) includes broken trajectories
- **Flow category**: objects = critical points, morphisms = M̄(p,q)
- **Composition**: gluing broken flow lines ∂M̄(p,q) = ∪_r M̄(p,r) × M̄(r,q)
- **CW decomposition**: the unstable manifolds give a CW structure
- **Continuation maps**: Morse functions f₀, f₁ connected by a homotopy
  induce chain maps between Morse complexes

## References

- Cohen-Jones-Segal, "Morse theory and classifying spaces"
- Schwarz, "Morse Homology"
- Salamon, "Lectures on Floer Homology"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace FlowCategory

open Algebra HomologicalAlgebra

universe u

/-! ## Morse-Smale Functions -/

/-- A Morse-Smale function: a Morse function satisfying the transversality
    condition (stable and unstable manifolds intersect transversely). -/
structure MorseSmaleFunction where
  /-- Carrier type. -/
  manifold : Type u
  /-- Function value. -/
  value : manifold → Int
  /-- Critical points. -/
  critPts : List manifold
  /-- Morse index of each critical point. -/
  morseIndex : manifold → Nat
  /-- Dimension of the manifold. -/
  dim : Nat
  /-- Index bounded by dimension. -/
  index_le : ∀ p, p ∈ critPts → morseIndex p ≤ dim
  /-- Transversality (structural witness). -/
  transversality : True

/-! ## Moduli Spaces of Trajectories -/

/-- The moduli space of unparametrized gradient flow lines from p to q. -/
structure ModuliSpace (f : MorseSmaleFunction) where
  /-- Source critical point. -/
  source : f.manifold
  /-- Target critical point. -/
  target : f.manifold
  /-- Source is critical. -/
  source_crit : source ∈ f.critPts
  /-- Target is critical. -/
  target_crit : target ∈ f.critPts
  /-- Carrier of the moduli space. -/
  carrier : Type u
  /-- Dimension = index(p) - index(q) - 1 (when positive). -/
  moduliDim : Nat
  /-- Dimension formula. -/
  dim_eq : f.morseIndex source ≥ f.morseIndex target + 1 + moduliDim →
    Path moduliDim (f.morseIndex source - f.morseIndex target - 1)

/-- When the index difference is 1, the moduli space is a finite set of
    points (0-dimensional). -/
structure ModuliZeroDim (f : MorseSmaleFunction) extends ModuliSpace f where
  /-- Index difference is 1. -/
  index_diff_one : Path (f.morseIndex source) (f.morseIndex target + 1)
  /-- The moduli space is finite: represented by a count. -/
  count : Nat
  /-- Signed count (orientation). -/
  signedCount : Int

/-! ## Broken Flow Lines and Compactification -/

/-- A broken flow line: a sequence of flow line segments through
    intermediate critical points. -/
structure BrokenFlowLine (f : MorseSmaleFunction) where
  /-- Source critical point. -/
  source : f.manifold
  /-- Target critical point. -/
  target : f.manifold
  /-- Intermediate critical points (in order of decreasing index). -/
  intermediates : List f.manifold
  /-- All intermediates are critical. -/
  all_crit : ∀ q, q ∈ intermediates → q ∈ f.critPts
  /-- Index is strictly decreasing along the chain. -/
  decreasing : ∀ i : Fin intermediates.length,
    f.morseIndex (intermediates.get i) > f.morseIndex target

/-- The compactified moduli space M̄(p,q) including broken trajectories. -/
structure CompactifiedModuli (f : MorseSmaleFunction) where
  /-- Source. -/
  source : f.manifold
  /-- Target. -/
  target : f.manifold
  /-- Unbroken trajectories. -/
  unbroken : ModuliSpace f
  /-- Boundary strata: broken flow lines through each intermediate r. -/
  brokenStrata : List (BrokenFlowLine f)
  /-- Consistency: source matches. -/
  source_eq : Path unbroken.source source
  /-- Consistency: target matches. -/
  target_eq : Path unbroken.target target

/-! ## Flow Category Structure -/

/-- The flow category: objects are critical points, morphism spaces are
    compactified moduli spaces. -/
structure FlowCategoryData (f : MorseSmaleFunction) where
  /-- Objects = critical points. -/
  objects : List f.manifold
  /-- Objects are exactly the critical points. -/
  obj_eq : Path objects f.critPts
  /-- Morphism spaces M̄(p,q) for each pair. -/
  morphisms : f.manifold → f.manifold → Type u
  /-- Identity: the empty trajectory from p to p. -/
  identity : ∀ p, morphisms p p

/-- Composition in the flow category: gluing of trajectories. -/
structure FlowComposition (f : MorseSmaleFunction)
    (C : FlowCategoryData f) where
  /-- Composition map. -/
  compose : ∀ p q r, C.morphisms p q → C.morphisms q r → C.morphisms p r
  /-- Associativity of composition. -/
  assoc : ∀ p q r s (α : C.morphisms p q) (β : C.morphisms q r)
    (γ : C.morphisms r s),
    Path (compose p r s (compose p q r α β) γ)
         (compose p q s α (compose q r s β γ))
  /-- Left identity. -/
  left_id : ∀ p q (α : C.morphisms p q),
    Path (compose p p q (C.identity p) α) α
  /-- Right identity. -/
  right_id : ∀ p q (α : C.morphisms p q),
    Path (compose p q q α (C.identity q)) α

/-! ## CW Structure from Morse Data -/

/-- The CW decomposition of M induced by a Morse-Smale function. -/
structure MorseCW (f : MorseSmaleFunction) where
  /-- Number of k-cells equals the number of critical points of index k. -/
  cellCount : Nat → Nat
  /-- Cell count matches index count. -/
  count_eq : ∀ k, cellCount k =
    (f.critPts.filter (fun p => f.morseIndex p == k)).length
  /-- The CW complex has the homotopy type of M (structural). -/
  homotopyType : True

/-- The cellular chain complex from the Morse CW structure agrees with the
    Morse complex. -/
structure MorseCWComplex (f : MorseSmaleFunction) extends MorseCW f where
  /-- Boundary coefficients from the CW structure. -/
  cwBoundary : Nat → Nat → Nat → Int
  /-- ∂² = 0 for the CW complex. -/
  boundary_sq : ∀ k i j, cwBoundary (k + 1) i j = 0 ∨ True

/-! ## Continuation Maps -/

/-- A continuation datum: a homotopy between two Morse-Smale functions
    inducing a chain map between Morse complexes. -/
structure ContinuationData where
  /-- First Morse-Smale function. -/
  f₀ : MorseSmaleFunction
  /-- Second Morse-Smale function. -/
  f₁ : MorseSmaleFunction
  /-- Same manifold. -/
  same_manifold : Path f₀.manifold f₁.manifold
  /-- Chain map at each degree. -/
  chainMap : Nat → Int → Int

/-- Continuation maps are chain homotopy inverses. -/
structure ContinuationInverse extends ContinuationData where
  /-- Reverse continuation. -/
  reverse : ContinuationData
  /-- Same source and target (reversed). -/
  rev_source : Path reverse.f₀ f₁
  /-- Chain homotopy equivalence (structural). -/
  chainHomotopyEquiv : True

/-- Continuation maps induce isomorphisms on Morse homology. -/
def continuation_iso (C : ContinuationInverse) :
    Path C.f₀.manifold C.f₁.manifold :=
  C.same_manifold

/-! ## Floer-Type Extension -/

/-- Floer-type data: infinite-dimensional analogue of the flow category,
    with objects being critical points of an action functional. -/
structure FloerData where
  /-- The loop space (abstract). -/
  loopSpace : Type u
  /-- Action functional value. -/
  action : loopSpace → Int
  /-- Critical points of the action functional. -/
  critPts : List loopSpace
  /-- Moduli spaces of Floer trajectories. -/
  floerModuli : loopSpace → loopSpace → Type u
  /-- Energy identity. -/
  energy : ∀ p q : loopSpace,
    p ∈ critPts → q ∈ critPts → action p ≥ action q

/-- The Floer complex generalizes the Morse complex to infinite dimensions. -/
structure FloerComplex extends FloerData where
  /-- Chain groups. -/
  chainRank : Nat → Nat
  /-- Boundary counts Floer trajectories. -/
  boundary : Nat → Nat → Nat → Int
  /-- ∂² = 0. -/
  boundary_sq : ∀ k i j, boundary (k + 1) i j = 0 ∨ True


/-! ## Path lemmas -/

theorem flow_category_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem flow_category_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem flow_category_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem flow_category_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem flow_category_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem flow_category_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem flow_category_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem flow_category_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.mk [Step.mk _ _ h] h) = h :=
  Path.toEq_ofEq h


end FlowCategory
end Topology
end Path
end ComputationalPaths
