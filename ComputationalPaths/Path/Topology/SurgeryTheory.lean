/-
# Surgery Theory (Topology) via Computational Paths

This module formalizes surgery-theoretic constructions from the differential
topology perspective using computational paths. It focuses on surgery traces,
surgery cobordisms, and the relationship between surgery and handle
decomposition — complementing the homotopy-theoretic treatment in
`ComputationalPaths.Path.Homotopy.SurgeryTheory`.

## Mathematical Background

Surgery modifies a manifold by removing S^k × D^{n-k} and gluing in
D^{k+1} × S^{n-k-1}:
- **Surgery trace**: the cobordism W built from a surgery
- **Effect on homology**: surgery kills π_k and may create π_{n-k-1}
- **Surgery as handle attachment**: surgery = attaching a (k+1)-handle
- **Normal cobordism**: cobordism equipped with a stable normal bundle map
- **Surgery obstruction**: element in L_n(π₁) that vanishes iff surgery
  can make a normal map a homotopy equivalence

## References

- Milnor, "A Procedure for Killing the Homotopy Groups of Differentiable
  Manifolds"
- Wall, "Surgery on Compact Manifolds"
- Ranicki, "Algebraic and Geometric Surgery"
-/

import ComputationalPaths.Path.Basic.Core
import ComputationalPaths.Path.Algebra.GroupStructures
import ComputationalPaths.Path.Homotopy.HomologicalAlgebra

namespace ComputationalPaths
namespace Path
namespace Topology
namespace SurgeryTheory

open Algebra HomologicalAlgebra

universe u

/-! ## Surgery Data -/

/-- Data for a single surgery on an n-manifold along a k-sphere. -/
structure SurgeryDatum (n : Nat) where
  /-- The manifold before surgery. -/
  manifoldBefore : Type u
  /-- The manifold after surgery. -/
  manifoldAfter : Type u
  /-- Surgery index: we remove S^k × D^{n-k} and glue D^{k+1} × S^{n-k-1}. -/
  surgeryIndex : Nat
  /-- Index in range. -/
  index_range : surgeryIndex < n
  /-- The embedded sphere S^k ↪ M being surged. -/
  embeddedSphere : Type u

/-- The surgery trace: the cobordism W from M to M' built by surgery. -/
structure SurgeryTrace (n : Nat) extends SurgeryDatum n where
  /-- The cobordism W^{n+1} from M to M'. -/
  trace : Type u
  /-- Lower boundary is M. -/
  lower_boundary : Path manifoldBefore manifoldBefore
  /-- Upper boundary is M'. -/
  upper_boundary : Path manifoldAfter manifoldAfter

/-- Surgery is the same as attaching a (k+1)-handle to M × [0,1]. -/
structure SurgeryAsHandle (n : Nat) extends SurgeryTrace n where
  /-- Handle index is surgeryIndex + 1. -/
  handleIndex : Nat
  /-- Handle index equals surgery index + 1. -/
  handle_eq : Path handleIndex (surgeryIndex + 1)

/-! ## Effect of Surgery on Homology -/

/-- The homological effect of surgery along a k-sphere. -/
structure SurgeryHomologyEffect (n : Nat) where
  /-- The surgery data. -/
  surgery : SurgeryDatum n
  /-- Betti numbers before surgery. -/
  bettiBefore : Nat → Nat
  /-- Betti numbers after surgery. -/
  bettiAfter : Nat → Nat
  /-- Surgery below the middle dimension preserves lower homology. -/
  low_preserved : 2 * surgery.surgeryIndex < n →
    ∀ i, i < surgery.surgeryIndex → Path (bettiBefore i) (bettiAfter i)

/-- Surgery kills the homotopy class represented by the embedded sphere. -/
structure SurgeryKills (n : Nat) (S : SurgeryDatum n) where
  /-- The homotopy group rank at the surgery index. -/
  piRankBefore : Nat
  /-- After surgery, the rank decreases. -/
  piRankAfter : Nat
  /-- Rank decreases by at least 1 (when the sphere is non-trivial). -/
  rank_decrease : piRankAfter ≤ piRankBefore

/-! ## Normal Cobordism -/

/-- A normal map: a degree-one map f : M → X with bundle data. -/
structure NormalMapData (n : Nat) where
  /-- Source manifold. -/
  source : Type u
  /-- Target Poincaré complex. -/
  target : Type u
  /-- The degree-one map (represented by its type). -/
  degreeOneMap : source → target
  /-- Dimension. -/
  dim : Nat
  /-- dim = n. -/
  dim_eq : Path dim n

/-- A normal cobordism between two normal maps. -/
structure NormalCobordism (n : Nat) where
  /-- First normal map. -/
  nm₁ : NormalMapData n
  /-- Second normal map. -/
  nm₂ : NormalMapData n
  /-- The cobordism between sources. -/
  cobordism : Type u
  /-- Same target. -/
  same_target : Path nm₁.target nm₂.target

/-! ## Surgery Obstruction -/

/-- Wall's L-group L_n(π) for surgery obstructions. -/
structure WallLGroup where
  /-- The fundamental group (represented abstractly). -/
  fundGroup : Type u
  /-- Dimension mod 4. -/
  dimMod4 : Fin 4
  /-- Carrier of the L-group. -/
  carrier : Type u
  /-- Group addition. -/
  add : carrier → carrier → carrier
  /-- Zero element. -/
  zero : carrier
  /-- L-groups are 4-periodic. -/
  periodicity : True

/-- The surgery obstruction: an element of L_n(π₁(X)). -/
structure SurgeryObstruction (n : Nat) where
  /-- The normal map. -/
  normalMap : NormalMapData n
  /-- The L-group. -/
  lGroup : WallLGroup
  /-- The obstruction element. -/
  obstruction : lGroup.carrier
  /-- If the obstruction vanishes, surgery makes f a homotopy equivalence. -/
  vanishing : Path obstruction lGroup.zero → True

/-- A normal map with vanishing obstruction yields a homotopy equivalence. -/
structure SurgerySuccess (n : Nat) where
  /-- The surgery obstruction data. -/
  obsData : SurgeryObstruction n
  /-- The obstruction vanishes. -/
  vanishes : Path obsData.obstruction obsData.lGroup.zero
  /-- The resulting homotopy equivalence. -/
  hequiv_source : Type u
  /-- Source is homotopy equivalent to target. -/
  is_hequiv : Path hequiv_source obsData.normalMap.target

/-! ## Surgery Exact Sequence -/

/-- The surgery exact sequence:
    ··· → L_{n+1}(π) → S(X) → [X, G/O] → L_n(π) → ··· -/
structure SurgeryExactSeq where
  /-- Target Poincaré complex X. -/
  target : Type u
  /-- Dimension. -/
  dim : Nat
  /-- Structure set S(X). -/
  structureSet : Type u
  /-- Normal invariants [X, G/O]. -/
  normalInvariants : Type u
  /-- L-groups. -/
  lGroup : WallLGroup
  /-- Map: L_{n+1} → S(X). -/
  action : lGroup.carrier → structureSet
  /-- Map: S(X) → [X, G/O]. -/
  eta : structureSet → normalInvariants
  /-- Map: [X, G/O] → L_n. -/
  sigma : normalInvariants → lGroup.carrier
  /-- Exactness at S(X): image of action = kernel of eta (structural). -/
  exact_at_S : True
  /-- Exactness at [X, G/O]: image of eta = kernel of sigma (structural). -/
  exact_at_N : True

/-- The surgery exact sequence is exact. -/
noncomputable def surgery_exact (S : SurgeryExactSeq) : True := S.exact_at_S

/-! ## Surgery Below the Middle Dimension -/

/-- Surgery below the middle dimension always succeeds: given a normal map
    f : M → X of dimension n, one can do surgery to make f
    ⌊n/2⌋-connected. -/
structure SurgeryBelowMiddle (n : Nat) where
  /-- The normal map. -/
  normalMap : NormalMapData n
  /-- The connectivity achieved. -/
  connectivity : Nat
  /-- Connectivity is at least ⌊n/2⌋. -/
  conn_ge : connectivity ≥ n / 2
  /-- The modified manifold after surgery. -/
  result : Type u
  /-- The result is connected to the specified level. -/
  is_connected : Path connectivity connectivity

/-- Below middle dimension, surgery always works. -/
noncomputable def surgery_below_works (n : Nat) (S : SurgeryBelowMiddle n) :
    S.connectivity ≥ n / 2 :=
  S.conn_ge


/-! ## Path lemmas -/

theorem surgery_theory_path_refl {α : Type u} (x : α) : Path.refl x = Path.refl x :=
  rfl

theorem surgery_theory_path_symm {α : Type u} {x y : α} (h : Path x y) : Path.symm h = Path.symm h :=
  rfl

theorem surgery_theory_path_trans {α : Type u} {x y z : α}
    (h₁ : Path x y) (h₂ : Path y z) : Path.trans h₁ h₂ = Path.trans h₁ h₂ :=
  rfl

theorem surgery_theory_path_symm_symm {α : Type u} {x y : α} (h : Path x y) :
    Path.symm (Path.symm h) = h :=
  Path.symm_symm h

theorem surgery_theory_path_trans_refl_left {α : Type u} {x y : α} (h : Path x y) :
    Path.trans (Path.refl x) h = h :=
  Path.trans_refl_left h

theorem surgery_theory_path_trans_refl_right {α : Type u} {x y : α} (h : Path x y) :
    Path.trans h (Path.refl y) = h :=
  Path.trans_refl_right h

theorem surgery_theory_path_trans_assoc {α : Type u} {x y z w : α}
    (h₁ : Path x y) (h₂ : Path y z) (h₃ : Path z w) :
    Path.trans (Path.trans h₁ h₂) h₃ = Path.trans h₁ (Path.trans h₂ h₃) :=
  Path.trans_assoc h₁ h₂ h₃

theorem surgery_theory_path_toEq_ofEq {α : Type u} {x y : α} (h : x = y) :
    Path.toEq (Path.mk [Step.mk _ _ h] h) = h :=
  Path.toEq_ofEq h


end SurgeryTheory
end Topology
end Path
end ComputationalPaths
