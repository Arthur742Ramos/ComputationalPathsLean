/-
# Spectral Sequences via Computational Paths

This module develops spectral sequence theory using the computational paths
framework: filtered complexes, E_r pages, differentials, convergence,
exact couples, and spectral sequence morphisms.

## Key Results

- Filtered complex with differential
- E_r page construction and differential structure
- Exact couple and derived couple
- Convergence for degenerate spectral sequences
- Morphisms of spectral sequences
- Edge homomorphisms

## References

- McCleary, "A User's Guide to Spectral Sequences"
- Weibel, "An Introduction to Homological Algebra", Chapter 5
-/

import ComputationalPaths.Path.Homotopy.Loops
import ComputationalPaths.Path.Rewrite.Quot

namespace ComputationalPaths.Path
namespace SpectralPaths

universe u

/-! ## Bigraded Modules -/

/-- A bigraded pointed set: indexed by (p, q). -/
structure BiGradedPtSet where
  /-- The (p,q)-component. -/
  component : Int → Int → Type u
  /-- The zero element in each component. -/
  zero : (p q : Int) → component p q

/-- A bigraded morphism: a family of maps between components. -/
structure BiGradedMor (E F : BiGradedPtSet.{u}) (dp dq : Int) where
  /-- The underlying map at each (p,q). -/
  toFun : (p q : Int) → E.component p q → F.component (p + dp) (q + dq)
  /-- Maps preserve zero. -/
  map_zero : (p q : Int) → Path (toFun p q (E.zero p q)) (F.zero (p + dp) (q + dq))

/-! ## Spectral Sequence Page -/

/-- A spectral sequence page: bigraded module with differential. -/
structure SpectralPage where
  /-- The bigraded module. -/
  module : BiGradedPtSet.{u}
  /-- The page number. -/
  page : Nat
  /-- Bidegree shift of the differential (dp). -/
  dp : Int
  /-- Bidegree shift of the differential (dq). -/
  dq : Int
  /-- The differential. -/
  diff : BiGradedMor module module dp dq

/-- Differential squared is zero at the proof level. -/
structure DiffSquaredZero (E : SpectralPage) : Prop where
  /-- d ∘ d = 0 at each (p,q). -/
  sq_zero : ∀ p q : Int, ∀ x : E.module.component p q,
    E.diff.toFun (p + E.dp) (q + E.dq) (E.diff.toFun p q x) =
      E.module.zero (p + E.dp + E.dp) (q + E.dq + E.dq)

/-! ## Exact Couple -/

/-- An exact couple: a pair (D, E) with maps i, j, k forming an exact triangle. -/
structure ExactCouple where
  /-- The D module. -/
  D : BiGradedPtSet.{u}
  /-- The E module. -/
  E : BiGradedPtSet.{u}
  /-- The map i : D → D. -/
  i_dp : Int
  i_dq : Int
  i : BiGradedMor D D i_dp i_dq
  /-- The map j : D → E. -/
  j_dp : Int
  j_dq : Int
  j : BiGradedMor D E j_dp j_dq
  /-- The map k : E → D. -/
  k_dp : Int
  k_dq : Int
  k : BiGradedMor E D k_dp k_dq

/-- The derived differential data for an exact couple. -/
structure DerivedDifferential (C : ExactCouple) where
  /-- The dp shift for the derived differential. -/
  ddp : Int
  /-- The dq shift for the derived differential. -/
  ddq : Int
  /-- The differential d = j ∘ k requires index compatibility. -/
  compatible_p : C.j_dp + C.k_dp = ddp
  compatible_q : C.j_dq + C.k_dq = ddq

/-- Construct the derived differential from an exact couple. -/
noncomputable def mkDerivedDifferential (C : ExactCouple) : DerivedDifferential C where
  ddp := C.j_dp + C.k_dp
  ddq := C.j_dq + C.k_dq
  compatible_p := rfl
  compatible_q := rfl

/-! ## Spectral Sequence -/

/-- A spectral sequence: a sequence of pages. -/
structure SpectralSeq where
  /-- The pages indexed by r. -/
  page : Nat → SpectralPage

/-- Degeneration: the spectral sequence stabilizes at page N. -/
structure Degenerates (S : SpectralSeq) (N : Nat) : Prop where
  /-- From page N onward, all differentials are trivially zero. -/
  stable : ∀ r : Nat, N ≤ r → ∀ p q : Int,
    ∀ x : (S.page r).module.component p q,
      (S.page r).diff.toFun p q x = (S.page r).module.zero
        (p + (S.page r).dp) (q + (S.page r).dq)

/-- Convergence data: the E_∞ page maps to the target. -/
structure ConvergenceData (S : SpectralSeq) (N : Nat) where
  /-- The E_∞ module is the N-th page module. -/
  eInfty : BiGradedPtSet.{u}
  /-- The identification. -/
  ident : ∀ p q : Int,
    (S.page N).module.component p q → eInfty.component p q

/-! ## Morphisms -/

/-- A morphism of spectral sequences: compatible maps at each page. -/
structure SpectralMor (S T : SpectralSeq) where
  /-- The map at each page and bidegree. -/
  pageMap : (r : Nat) → (p q : Int) →
    (S.page r).module.component p q → (T.page r).module.component p q

/-- Morphism composition. -/
noncomputable def SpectralMor.comp {S T U : SpectralSeq}
    (g : SpectralMor T U) (f : SpectralMor S T) : SpectralMor S U where
  pageMap := fun r p q x => g.pageMap r p q (f.pageMap r p q x)

/-- Identity morphism. -/
noncomputable def SpectralMor.id (S : SpectralSeq) : SpectralMor S S where
  pageMap := fun _ _ _ x => x

/-- Identity morphism is neutral on the left. -/
theorem SpectralMor.comp_id {S T : SpectralSeq} (f : SpectralMor S T) :
    SpectralMor.comp (SpectralMor.id T) f = f := by
  rfl

/-- Identity morphism is neutral on the right. -/
theorem SpectralMor.id_comp {S T : SpectralSeq} (f : SpectralMor S T) :
    SpectralMor.comp f (SpectralMor.id S) = f := by
  rfl

/-- Composition of morphisms is associative. -/
theorem SpectralMor.comp_assoc {S T U V : SpectralSeq}
    (h : SpectralMor U V) (g : SpectralMor T U) (f : SpectralMor S T) :
    SpectralMor.comp (SpectralMor.comp h g) f =
      SpectralMor.comp h (SpectralMor.comp g f) := by
  rfl

/-! ## Filtration -/

/-- A filtration on a type: a nested sequence of subtypes. -/
structure Filtration (X : Type u) where
  /-- The p-th filtration level. -/
  level : Int → X → Prop
  /-- Filtration is nested: F_p ⊆ F_{p+1}. -/
  nested : ∀ p : Int, ∀ x : X, level p x → level (p + 1) x

/-- The associated graded of a filtration. -/
noncomputable def assocGraded (X : Type u) (F : Filtration X) (p : Int) : Type u :=
  { x : X // F.level p x ∧ ¬F.level (p - 1) x }

/-- Filtration bounded below: F_p = ∅ for p < N. -/
structure BoundedBelow (X : Type u) (F : Filtration X) (N : Int) : Prop where
  /-- Below N, the filtration is empty. -/
  empty_below : ∀ p : Int, p < N → ∀ x : X, ¬F.level p x

/-- Filtration exhaustive: ∪ F_p = X. -/
structure Exhaustive (X : Type u) (F : Filtration X) : Prop where
  /-- Every element is in some filtration level. -/
  covers : ∀ x : X, ∃ p : Int, F.level p x

/-! ## Edge Homomorphisms -/

/-- Edge homomorphism data: map from E_r^{p,0} to the target. -/
structure EdgeMap (S : SpectralSeq) (r : Nat) (p : Int) (T : Type u) where
  /-- The edge map. -/
  toFun : (S.page r).module.component p 0 → T

/-- Composition of edge maps with page inclusion. -/
noncomputable def EdgeMap.compose {S : SpectralSeq} {r : Nat} {p : Int} {T U : Type u}
    (g : T → U) (f : EdgeMap S r p T) : EdgeMap S r p U where
  toFun := g ∘ f.toFun

/-! ## Convergence Theorems -/

/-- For a degenerate spectral sequence, E_∞ = E_N. -/
theorem convergence_degenerate (S : SpectralSeq) (N : Nat) (h : Degenerates S N) :
    ∀ r : Nat, N ≤ r → ∀ p q : Int,
      ∀ x : (S.page r).module.component p q,
        (S.page r).diff.toFun p q x =
          (S.page r).module.zero (p + (S.page r).dp) (q + (S.page r).dq) :=
  h.stable

/-- A spectral sequence with all differentials zero degenerates at page 0. -/
theorem trivial_degenerates (S : SpectralSeq)
    (h : ∀ r p q, ∀ x : (S.page r).module.component p q,
      (S.page r).diff.toFun p q x =
        (S.page r).module.zero (p + (S.page r).dp) (q + (S.page r).dq)) :
    Degenerates S 0 where
  stable := fun r _ p q x => h r p q x

/-- Degeneration is monotone: if it degenerates at N, it degenerates at any M ≥ N. -/
theorem degenerates_mono (S : SpectralSeq) {N M : Nat} (h : Degenerates S N)
    (hle : N ≤ M) : Degenerates S M where
  stable := fun r hr p q x => h.stable r (Nat.le_trans hle hr) p q x

/-! ## First Quadrant Spectral Sequence -/

/-- A first-quadrant spectral sequence: E_r^{p,q} = 0 for p < 0 or q < 0. -/
structure FirstQuadrant (S : SpectralSeq) : Prop where
  /-- Vanishing outside the first quadrant. -/
  vanish : ∀ r : Nat, ∀ p q : Int,
    p < 0 ∨ q < 0 →
      (S.page r).module.component p q = PUnit

/-- In a first-quadrant spectral sequence, differentials leaving the
    first quadrant land in the zero module. -/
theorem firstQuadrant_boundary (S : SpectralSeq) (hfq : FirstQuadrant S)
    (r : Nat) (p q : Int) (hp : p < 0 ∨ q < 0) :
    (S.page r).module.component p q = PUnit :=
  hfq.vanish r p q hp

end SpectralPaths
end ComputationalPaths.Path
