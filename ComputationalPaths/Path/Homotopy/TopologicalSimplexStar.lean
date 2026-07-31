/-
# Open core-face stars in topological simplices

This module defines the point-set neighborhoods used to trivialize realized
simplicial coverings.  A core face consists of a face inclusion followed by a
degeneracy onto a fixed simplex.  Its open neighborhood consists of points for
which every barycentric mass over a core vertex is strictly larger than the
total mass outside the face.

Unlike a naive vertex star, these neighborhoods are stable under degeneracy:
coordinates which a degeneracy identifies are summed before the strict
inequality is tested.
-/

import ComputationalPaths.Path.Homotopy.TopologicalNerveContractible
import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate

open CategoryTheory Simplicial Opposite

namespace ComputationalPaths
namespace Path
namespace TopologicalNerve

universe u

/-- A face of `t` whose simplicial core is the simplex `c`. -/
structure SimplexCoreFace
    (X : SSet.{u}) {k n : ℕ}
    (c : X _⦋k⦌) (t : X _⦋n⦌) where
  /-- Dimension of the possibly degenerate face. -/
  dim : ℕ
  /-- Inclusion of the face into `t`. -/
  face : ⦋dim⦌ ⟶ ⦋n⦌
  /-- The face map is injective. -/
  face_injective : Function.Injective face.toOrderHom
  /-- Degeneracy collapsing the face to its core. -/
  collapse : ⦋dim⦌ ⟶ ⦋k⦌
  /-- Every core vertex has a preimage. -/
  collapse_surjective : Function.Surjective collapse.toOrderHom
  /-- The selected face is the indicated degeneracy of `c`. -/
  face_eq :
    X.map face.op t = X.map collapse.op c

namespace SimplexCoreFace

variable {X : SSet.{u}} {k n : ℕ}
  {c : X _⦋k⦌} {t : X _⦋n⦌}

/-- Total barycentric mass outside the selected face. -/
noncomputable def outsideMass
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) : NNReal :=
  ∑ j ∈ Finset.univ.filter
      (fun j : Fin (n + 1) =>
        j ∉ Set.range h.face.toOrderHom),
    p j

/-- Barycentric mass over one vertex of the nondegenerate core. -/
noncomputable def coreMass
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj)
    (i : Fin (k + 1)) : NNReal :=
  ∑ j ∈ Finset.univ.filter
      (fun j : Fin (h.dim + 1) =>
        h.collapse.toOrderHom j = i),
    p (h.face.toOrderHom j)

theorem continuous_outsideMass
    (h : SimplexCoreFace X c t) :
    Continuous h.outsideMass := by
  unfold outsideMass
  fun_prop

theorem continuous_coreMass
    (h : SimplexCoreFace X c t) (i : Fin (k + 1)) :
    Continuous (fun p => h.coreMass p i) := by
  unfold coreMass
  exact continuous_finset_sum _ fun j _ =>
    (continuous_apply (h.face.toOrderHom j)).comp
      continuous_subtype_val

/-- Open dominance condition defining the star of a core face. -/
def starSet (h : SimplexCoreFace X c t) : Set ⦋n⦌.toTopObj :=
  {p | ∀ i : Fin (k + 1), h.outsideMass p < h.coreMass p i}

theorem isOpen_starSet (h : SimplexCoreFace X c t) :
    IsOpen h.starSet := by
  rw [show h.starSet =
      ⋂ i : Fin (k + 1),
        {p | h.outsideMass p < h.coreMass p i} by
    ext p
    simp [starSet]]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (continuous_outsideMass h)
    (continuous_coreMass h i)

/-- The whole simplex is a core face of itself. -/
noncomputable def identity
    (s : X _⦋n⦌) :
    SimplexCoreFace X s s where
  dim := n
  face := 𝟙 _
  face_injective := Function.injective_id
  collapse := 𝟙 _
  collapse_surjective := Function.surjective_id
  face_eq := by simp

theorem mem_identity_starSet_iff
    (s : X _⦋n⦌) (p : ⦋n⦌.toTopObj) :
    p ∈ (identity s).starSet ↔ ∀ i, 0 < p i := by
  have hcore (i : Fin (n + 1)) :
      (identity s).coreMass p i = p i := by
    unfold coreMass identity
    have hf :
        Finset.univ.filter (fun j : Fin (n + 1) => j = i) =
          {i} := by
      ext j
      simp
    change
      ∑ j ∈ Finset.univ.filter
        (fun j : Fin (n + 1) => j = i), p j = p i
    rw [hf]
    simp
  constructor
  · intro hp i
    have hi := hp i
    rw [hcore] at hi
    simpa [outsideMass, identity] using hi
  · intro hp
    change ∀ i, (identity s).outsideMass p <
      (identity s).coreMass p i
    intro i
    rw [hcore]
    simpa [outsideMass, identity] using hp i

/-- The union of all open core-face stars of `c` inside the simplex `t`. -/
def simplexStar (X : SSet.{u}) {k n : ℕ}
    (c : X _⦋k⦌) (t : X _⦋n⦌) : Set ⦋n⦌.toTopObj :=
  ⋃ h : SimplexCoreFace X c t, h.starSet

theorem isOpen_simplexStar (X : SSet.{u}) {k n : ℕ}
    (c : X _⦋k⦌) (t : X _⦋n⦌) :
    IsOpen (simplexStar X c t) :=
  isOpen_iUnion fun h => h.isOpen_starSet

end SimplexCoreFace

/-! ## Computational-path certificate -/

/-- Reflexive path certificate for the nonnegative outside mass. -/
noncomputable def outsideMassNonnegativePath
    {X : SSet.{u}} {k n : ℕ}
    {c : X _⦋k⦌} {t : X _⦋n⦌}
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) :
    Path (0 + h.outsideMass p) (h.outsideMass p) :=
  Path.stepChain (zero_add _)

/-- Coherence of the outside-mass certificate. -/
noncomputable def outsideMassNonnegativeCoherence
    {X : SSet.{u}} {k n : ℕ}
    {c : X _⦋k⦌} {t : X _⦋n⦌}
    (h : SimplexCoreFace X c t) (p : ⦋n⦌.toTopObj) :
    RwEq
      (Path.trans (outsideMassNonnegativePath h p)
        (Path.refl (h.outsideMass p)))
      (outsideMassNonnegativePath h p) :=
  rweq_cmpA_refl_right (outsideMassNonnegativePath h p)

end TopologicalNerve
end Path
end ComputationalPaths
