import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Combinatorics.SimpleGraph.Basic

open Set

namespace TropicalGeometry

universe u

variable {α : Type u}

/-- Finite-ground matroid axiomatization by independent sets. -/
structure IndepAxiomatization (α : Type u) where
  E : Set α
  finite_ground : E.Finite
  Indep : Set α → Prop
  indep_empty : Indep ∅
  indep_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I
  indep_aug : ∀ ⦃I J⦄, Indep I → Indep J → I.ncard < J.ncard →
    ∃ e ∈ J, e ∉ I ∧ Indep (insert e I)
  subset_ground : ∀ ⦃I⦄, Indep I → I ⊆ E

namespace IndepAxiomatization

noncomputable def toIndepMatroid (A : IndepAxiomatization α) : IndepMatroid α :=
  IndepMatroid.ofFinite (E := A.E) (hE := A.finite_ground) (Indep := A.Indep)
    (indep_empty := A.indep_empty)
    (indep_subset := A.indep_subset)
    (indep_aug := A.indep_aug)
    (subset_ground := by
      intro I hI
      exact A.subset_ground hI)

noncomputable def toMatroid (A : IndepAxiomatization α) : Matroid α :=
  A.toIndepMatroid.matroid

@[simp] theorem toMatroid_ground (A : IndepAxiomatization α) : A.toMatroid.E = A.E := by
  simp [toMatroid, toIndepMatroid]

@[simp] theorem toMatroid_indep_iff (A : IndepAxiomatization α) {I : Set α} :
    A.toMatroid.Indep I ↔ A.Indep I := by
  simp [toMatroid, toIndepMatroid]

end IndepAxiomatization

/-- Finite-ground matroid axiomatization by bases. -/
structure BaseAxiomatization (α : Type u) where
  E : Set α
  finite_ground : E.Finite
  IsBase : Set α → Prop
  exists_isBase : ∃ B, IsBase B
  isBase_exchange : Matroid.ExchangeProperty IsBase
  subset_ground : ∀ ⦃B⦄, IsBase B → B ⊆ E

namespace BaseAxiomatization

noncomputable def toMatroid (A : BaseAxiomatization α) : Matroid α :=
  Matroid.ofIsBaseOfFinite (hE := A.finite_ground) (IsBase := A.IsBase)
    (exists_isBase := A.exists_isBase)
    (isBase_exchange := A.isBase_exchange)
    (subset_ground := fun _ hB => A.subset_ground hB)

@[simp] theorem toMatroid_ground (A : BaseAxiomatization α) : A.toMatroid.E = A.E := by
  simp [toMatroid]

@[simp] theorem toMatroid_isBase_iff (A : BaseAxiomatization α) {B : Set α} :
    A.toMatroid.IsBase B ↔ A.IsBase B := by
  simp [toMatroid]

end BaseAxiomatization

/-- Convert an independent-set axiomatization to a base axiomatization via the induced matroid. -/
noncomputable def IndepAxiomatization.toBaseAxiomatization (A : IndepAxiomatization α) :
    BaseAxiomatization α where
  E := A.E
  finite_ground := A.finite_ground
  IsBase := A.toMatroid.IsBase
  exists_isBase := A.toMatroid.exists_isBase
  isBase_exchange := A.toMatroid.isBase_exchange
  subset_ground := by
    intro B hB
    exact A.toMatroid.subset_ground B hB

@[simp] theorem indep_toBase_toMatroid (A : IndepAxiomatization α) :
    A.toBaseAxiomatization.toMatroid = A.toMatroid := by
  refine Matroid.ext_isBase rfl ?_
  intro B hB
  simp [IndepAxiomatization.toBaseAxiomatization, BaseAxiomatization.toMatroid]

/-- Convert a base axiomatization to an independent-set axiomatization via the induced matroid. -/
noncomputable def BaseAxiomatization.toIndepAxiomatization (A : BaseAxiomatization α) :
    IndepAxiomatization α where
  E := A.E
  finite_ground := A.finite_ground
  Indep := A.toMatroid.Indep
  indep_empty := A.toMatroid.empty_indep
  indep_subset := by
    intro I J hJ hIJ
    exact hJ.subset hIJ
  indep_aug := by
    intro I J hI hJ hIJ
    have hIfin : I.Finite := A.finite_ground.subset hI.subset_ground
    have hJfin : J.Finite := A.finite_ground.subset hJ.subset_ground
    have hencard : I.encard < J.encard := by
      rw [← hIfin.cast_ncard_eq, ← hJfin.cast_ncard_eq]
      exact Nat.cast_lt.2 hIJ
    obtain ⟨e, heJI, hins⟩ := hI.exists_insert_of_encard_lt hJ hencard
    exact ⟨e, heJI.1, heJI.2, hins⟩
  subset_ground := by
    intro I hI
    exact hI.subset_ground

@[simp] theorem base_toIndep_toMatroid (A : BaseAxiomatization α) :
    A.toIndepAxiomatization.toMatroid = A.toMatroid := by
  refine Matroid.ext_indep rfl ?_
  intro I hI
  simp [BaseAxiomatization.toIndepAxiomatization, IndepAxiomatization.toMatroid,
    IndepAxiomatization.toIndepMatroid, BaseAxiomatization.toMatroid]

theorem indep_base_equivalence (A : IndepAxiomatization α) :
    ∃ B : BaseAxiomatization α, B.toMatroid = A.toMatroid :=
  ⟨A.toBaseAxiomatization, indep_toBase_toMatroid A⟩

theorem base_indep_equivalence (A : BaseAxiomatization α) :
    ∃ B : IndepAxiomatization α, B.toMatroid = A.toMatroid :=
  ⟨A.toIndepAxiomatization, base_toIndep_toMatroid A⟩

/-- A circuit-based axiomatization: a matroid together with a circuit predicate specification. -/
structure CircuitAxiomatization (α : Type u) where
  M : Matroid α
  IsCircuit : Set α → Prop
  isCircuit_iff : ∀ C, IsCircuit C ↔ M.IsCircuit C

namespace Matroid

def toCircuitAxiomatization (M : Matroid α) : CircuitAxiomatization α where
  M := M
  IsCircuit := M.IsCircuit
  isCircuit_iff := by intro C; rfl

end Matroid

theorem CircuitAxiomatization.matroid_eq {A B : CircuitAxiomatization α}
    (hE : A.M.E = B.M.E) (hC : ∀ C, A.IsCircuit C ↔ B.IsCircuit C) :
    A.M = B.M := by
  refine Matroid.ext_isCircuit hE ?_
  intro C hCE
  exact (A.isCircuit_iff C).symm.trans ((hC C).trans (B.isCircuit_iff C))

/-- A rank-function axiomatization: a function identified with `eRk`. -/
structure RankAxiomatization (α : Type u) where
  M : Matroid α
  rk : Set α → ℕ∞
  rk_eq : ∀ X, rk X = M.eRk X

namespace Matroid

noncomputable def toRankAxiomatization (M : Matroid α) : RankAxiomatization α where
  M := M
  rk := M.eRk
  rk_eq := by intro X; rfl

end Matroid

namespace RankAxiomatization

@[simp] theorem rk_empty (A : RankAxiomatization α) : A.rk ∅ = 0 := by
  simp [A.rk_eq]

theorem rk_le_encard (A : RankAxiomatization α) (X : Set α) : A.rk X ≤ X.encard := by
  simpa [A.rk_eq] using A.M.eRk_le_encard X

theorem rk_mono (A : RankAxiomatization α) : Monotone A.rk := by
  intro X Y hXY
  simpa [A.rk_eq] using A.M.eRk_mono hXY

theorem rk_submod (A : RankAxiomatization α) (X Y : Set α) :
    A.rk (X ∩ Y) + A.rk (X ∪ Y) ≤ A.rk X + A.rk Y := by
  simpa [A.rk_eq] using A.M.eRk_inter_add_eRk_union_le X Y

end RankAxiomatization

section Uniform

variable (α : Type u) [Fintype α]

/-- Uniform matroid `U(r, α)` encoded by independent sets of size at most `r`. -/
noncomputable def uniformAxiomatization (r : ℕ) : IndepAxiomatization α where
  E := univ
  finite_ground := Set.toFinite _
  Indep := fun I => I.ncard ≤ r
  indep_empty := by simp
  indep_subset := by
    intro I J hJ hIJ
    exact (Set.ncard_le_ncard hIJ).trans hJ
  indep_aug := by
    intro I J hI hJ hIJ
    have hnot : ¬ J ⊆ I := by
      intro hJI
      exact (not_lt_of_ge (Set.ncard_le_ncard hJI)) hIJ
    have hJI_nonempty : (J \ I).Nonempty := by
      by_contra hJI_empty
      apply hnot
      intro e heJ
      by_contra heI
      exact hJI_empty ⟨e, heJ, heI⟩
    rcases hJI_nonempty with ⟨e, heJI⟩
    refine ⟨e, heJI.1, heJI.2, ?_⟩
    have hlt_r : I.ncard < r := lt_of_lt_of_le hIJ hJ
    have hsucc : I.ncard + 1 ≤ r := Nat.succ_le_of_lt hlt_r
    simpa [Set.ncard_insert_of_notMem heJI.2, Nat.succ_eq_add_one] using hsucc
  subset_ground := by
    intro I hI
    exact subset_univ I

noncomputable def uniformMatroid (r : ℕ) : Matroid α :=
  (uniformAxiomatization (α := α) r).toMatroid

@[simp] theorem uniformMatroid_indep_iff (r : ℕ) (I : Set α) :
    (uniformMatroid (α := α) r).Indep I ↔ I.ncard ≤ r := by
  simp [uniformMatroid, uniformAxiomatization, IndepAxiomatization.toMatroid,
    IndepAxiomatization.toIndepMatroid]

end Uniform

section Graphic

variable {V : Type u}

/-- A basic graphic-matroid example on the edge set of `G` (free on edges). -/
def graphicMatroid (G : SimpleGraph V) : Matroid (Sym2 V) :=
  Matroid.freeOn G.edgeSet

@[simp] theorem graphicMatroid_indep_iff (G : SimpleGraph V) (I : Set (Sym2 V)) :
    (graphicMatroid G).Indep I ↔ I ⊆ G.edgeSet := by
  simp [graphicMatroid]

end Graphic

/-- Matroid duality. -/
def matroidDual (M : Matroid α) : Matroid α := M✶

@[simp] theorem matroidDual_involutive (M : Matroid α) : matroidDual (matroidDual M) = M := by
  simp [matroidDual]

end TropicalGeometry
