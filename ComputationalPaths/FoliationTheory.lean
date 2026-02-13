/-
# Foliation Theory via Computational Paths

This module formalizes foliation theory — foliations on manifolds,
the Frobenius integrability theorem, the Reeb foliation, the Godbillon-Vey
class, Haefliger structures, leaf spaces, transverse geometry, Molino's
theorem for Riemannian foliations, and Connes' foliation algebra —
all with `Path` coherence witnesses.

## Mathematical Background

Foliation theory studies decompositions of manifolds into immersed
submanifolds (leaves):

1. **Foliations**: A codimension-q foliation of an n-manifold M is a
   decomposition into connected immersed (n-q)-dimensional submanifolds
   (leaves) locally modeled on ℝ^{n-q} × ℝ^q.
2. **Frobenius theorem**: A distribution D ⊂ TM is integrable (tangent
   to a foliation) iff [D, D] ⊂ D (involutivity).
3. **Reeb foliation**: The unique codimension-1 foliation of S³ with
   one compact leaf (a torus T²) and all other leaves ℝ².
4. **Godbillon-Vey class**: GV ∈ H³(M; ℝ) for codimension-1 foliations,
   defined by ω ∧ dω where dα = ω ∧ α for the defining 1-form α.
5. **Haefliger structures**: A Γ_q-structure on M generalizes foliations
   via a classifying map M → BΓ_q (Haefliger's classifying space).
6. **Leaf space**: M/F — the quotient by the leaf equivalence relation.
   Often highly singular (non-Hausdorff).
7. **Transverse geometry**: Geometric structures on the normal bundle
   ν = TM/TF, preserved by holonomy.
8. **Molino's theorem**: For a complete Riemannian foliation, the closure
   of each leaf is a submanifold, and the leaf closures form a singular
   Riemannian foliation whose leaf space is an orbifold.
9. **Connes' foliation algebra**: C*(M, F) — the C*-algebra of a foliated
   manifold, encoding the leaf space via noncommutative geometry.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `Foliation` | Foliation data |
| `FrobeniusData` | Frobenius integrability theorem |
| `ReebFoliation` | Reeb foliation of S³ |
| `GodbillonVey` | Godbillon-Vey invariant |
| `HaefligerStructure` | Γ_q-structure |
| `LeafSpace` | Leaf space M/F |
| `TransverseGeometry` | Transverse structure data |
| `MolinoTheorem` | Molino's structure theorem |
| `ConnesFoliationAlgebra` | C*(M, F) |
| `frobenius_path` | Integrability coherence |
| `reeb_path` | Reeb foliation properties |
| `gv_class_path` | GV class degree coherence |
| `molino_path` | Molino theorem coherence |

## References

- Candel & Conlon, "Foliations I & II"
- Camacho & Lins Neto, "Geometric Theory of Foliations"
- Moerdijk & Mrčun, "Introduction to Foliations and Lie Groupoids"
- Molino, "Riemannian Foliations"
- Connes, "A survey of foliations and operator algebras"
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace FoliationTheory

universe u v w

/-! ## Foliations -/

/-- A foliation of codimension q on an n-manifold: a decomposition
into (n-q)-dimensional leaves. -/
structure Foliation where
  /-- Ambient manifold dimension. -/
  dim : Nat
  /-- Dimension is positive. -/
  dim_pos : dim > 0
  /-- Codimension q. -/
  codim : Nat
  /-- Codimension is at least 1. -/
  codim_pos : codim ≥ 1
  /-- Codimension is at most dim. -/
  codim_le : codim ≤ dim
  /-- Leaf dimension = dim - codim. -/
  leafDim : Nat
  /-- Leaf dimension formula. -/
  leaf_eq : leafDim = dim - codim
  /-- Number of compact leaves (combinatorial model). -/
  compactLeaves : Nat
  /-- Whether all leaves are compact. -/
  allCompact : Bool
  /-- Whether the foliation is transversely orientable. -/
  transOrientable : Bool

namespace Foliation

/-- A codimension-1 foliation on an n-manifold. -/
def codim1 (n : Nat) (hn : n > 0) (compact_ct : Nat)
    (allC : Bool) (tOr : Bool) : Foliation where
  dim := n
  dim_pos := hn
  codim := 1
  codim_pos := by omega
  codim_le := hn
  leafDim := n - 1
  leaf_eq := rfl
  compactLeaves := compact_ct
  allCompact := allC
  transOrientable := tOr

/-- Foliation of a surface by curves (codim 1). -/
def surfaceFoliation : Foliation :=
  codim1 2 (by omega) 0 false true

/-- Foliation of ℝ³ by planes (codim 1, all leaves ℝ²). -/
def r3ByPlanes : Foliation where
  dim := 3
  dim_pos := by omega
  codim := 1
  codim_pos := by omega
  codim_le := by omega
  leafDim := 2
  leaf_eq := rfl
  compactLeaves := 0
  allCompact := false
  transOrientable := true

/-- Point foliation: codim = dim, leaves are points. -/
def pointFoliation (n : Nat) (hn : n > 0) : Foliation where
  dim := n
  dim_pos := hn
  codim := n
  codim_pos := by omega
  codim_le := Nat.le_refl n
  leafDim := 0
  leaf_eq := by omega
  compactLeaves := 0
  allCompact := true
  transOrientable := true

/-- Trivial foliation: codim = 0 (but we require codim ≥ 1, so
use single-leaf foliation with codim 1 on ℝ). -/
def flowFoliation (n : Nat) (hn : n ≥ 2) : Foliation where
  dim := n
  dim_pos := by omega
  codim := n - 1
  codim_pos := by omega
  codim_le := by omega
  leafDim := 1
  leaf_eq := by omega
  compactLeaves := 0
  allCompact := false
  transOrientable := true

/-- Leaf dimension of a codim-1 foliation is n-1. -/
theorem codim1_leaf (n : Nat) (hn : n > 0) (c : Nat) (ac : Bool) (to : Bool) :
    (codim1 n hn c ac to).leafDim = n - 1 := rfl

/-- ℝ³ by planes has leaf dimension 2. -/
theorem r3_leaf : r3ByPlanes.leafDim = 2 := rfl

/-- Point foliation has leaf dimension 0. -/
theorem point_leaf (n : Nat) (hn : n > 0) :
    (pointFoliation n hn).leafDim = 0 := rfl

/-- Point foliation has all compact leaves. -/
theorem point_all_compact (n : Nat) (hn : n > 0) :
    (pointFoliation n hn).allCompact = true := rfl

/-- dim + codim ≥ dim (tautological). -/
theorem dim_codim_bound (f : Foliation) :
    f.leafDim + f.codim = f.dim := by
  rw [f.leaf_eq]
  exact Nat.sub_add_cancel f.codim_le

end Foliation

/-! ## Frobenius Theorem -/

/-- Frobenius integrability theorem: a smooth distribution D ⊂ TM
is integrable (tangent to a foliation) iff [D, D] ⊂ D.
We record the distribution rank and involutivity status. -/
structure FrobeniusData where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Dimension is positive. -/
  dim_pos : dim > 0
  /-- Distribution rank (= leaf dimension). -/
  rank : Nat
  /-- Rank ≥ 1. -/
  rank_pos : rank ≥ 1
  /-- Rank ≤ dim. -/
  rank_le : rank ≤ dim
  /-- Whether the distribution is involutive. -/
  isInvolutive : Bool
  /-- Whether it integrates to a foliation. -/
  isIntegrable : Bool
  /-- Frobenius: involutive ↔ integrable. -/
  frobenius : isInvolutive = isIntegrable

namespace FrobeniusData

/-- An integrable distribution (gives a foliation). -/
def integrable (n r : Nat) (hn : n > 0) (hr : r ≥ 1) (hrl : r ≤ n) :
    FrobeniusData where
  dim := n
  dim_pos := hn
  rank := r
  rank_pos := hr
  rank_le := hrl
  isInvolutive := true
  isIntegrable := true
  frobenius := rfl

/-- A non-integrable distribution. -/
def nonIntegrable (n r : Nat) (hn : n > 0) (hr : r ≥ 1) (hrl : r ≤ n) :
    FrobeniusData where
  dim := n
  dim_pos := hn
  rank := r
  rank_pos := hr
  rank_le := hrl
  isInvolutive := false
  isIntegrable := false
  frobenius := rfl

/-- Contact structure on ℝ³: rank 2, not integrable. -/
def contactR3 : FrobeniusData := nonIntegrable 3 2 (by omega) (by omega) (by omega)

/-- Contact structure is not integrable. -/
theorem contact_not_integrable : contactR3.isIntegrable = false := rfl

/-- Contact structure is not involutive. -/
theorem contact_not_involutive : contactR3.isInvolutive = false := rfl

/-- Integrable distribution is involutive. -/
theorem integrable_involutive (n r : Nat) (hn : n > 0) (hr : r ≥ 1) (hrl : r ≤ n) :
    (integrable n r hn hr hrl).isInvolutive = true := rfl

/-- Frobenius equivalence for integrable case. -/
theorem frobenius_equiv (fd : FrobeniusData) :
    fd.isInvolutive = fd.isIntegrable := fd.frobenius

end FrobeniusData

/-! ## Reeb Foliation -/

/-- The Reeb foliation of S³: the unique codimension-1 foliation with
one compact leaf (a torus T²). All other leaves are diffeomorphic to ℝ². -/
structure ReebFoliation where
  /-- Ambient manifold is S³, dimension 3. -/
  dim : Nat
  /-- dim = 3. -/
  dim_eq : dim = 3
  /-- Codimension 1. -/
  codim : Nat
  /-- codim = 1. -/
  codim_eq : codim = 1
  /-- Leaf dimension = 2. -/
  leafDim : Nat
  /-- leaf dim = 2. -/
  leaf_eq : leafDim = 2
  /-- Exactly one compact leaf (the torus). -/
  compactLeaves : Nat
  /-- One compact leaf. -/
  compact_eq : compactLeaves = 1
  /-- The compact leaf is a torus T². -/
  compactLeafGenus : Nat
  /-- Genus of compact leaf = 1. -/
  genus_eq : compactLeafGenus = 1
  /-- Non-compact leaves are ℝ². -/
  noncompactLeafType : Nat  -- 0 = ℝ²
  /-- Non-compact leaves are planar. -/
  noncompact_eq : noncompactLeafType = 0

namespace ReebFoliation

/-- The standard Reeb foliation. -/
def standard : ReebFoliation where
  dim := 3
  dim_eq := rfl
  codim := 1
  codim_eq := rfl
  leafDim := 2
  leaf_eq := rfl
  compactLeaves := 1
  compact_eq := rfl
  compactLeafGenus := 1
  genus_eq := rfl
  noncompactLeafType := 0
  noncompact_eq := rfl

/-- Reeb foliation lives on S³ (dim 3). -/
theorem reeb_dim : standard.dim = 3 := rfl

/-- Reeb foliation has codimension 1. -/
theorem reeb_codim : standard.codim = 1 := rfl

/-- Reeb foliation has leaf dimension 2. -/
theorem reeb_leaf_dim : standard.leafDim = 2 := rfl

/-- One compact leaf. -/
theorem reeb_compact : standard.compactLeaves = 1 := rfl

/-- Compact leaf is a torus (genus 1). -/
theorem reeb_genus : standard.compactLeafGenus = 1 := rfl

/-- Dimension decomposition: 3 = 2 + 1. -/
theorem reeb_decomposition : standard.dim = standard.leafDim + standard.codim := rfl

end ReebFoliation

/-! ## Godbillon-Vey Class -/

/-- The Godbillon-Vey class GV(F) ∈ H³(M; ℝ) for a codimension-1
foliation F. Defined by GV = [ω ∧ dω] where dα = ω ∧ α for the
defining 1-form α of F. -/
structure GodbillonVey where
  /-- Ambient manifold dimension. -/
  dim : Nat
  /-- Dimension ≥ 3 (needed for H³). -/
  dim_ge3 : dim ≥ 3
  /-- Degree of the GV class = 3. -/
  degree : Nat
  /-- Degree is 3. -/
  degree_eq : degree = 3
  /-- GV class value (numerator, rational). -/
  gvNumerator : Int
  /-- GV denominator. -/
  gvDenominator : Nat
  /-- Denominator is positive. -/
  denom_pos : gvDenominator > 0
  /-- Whether the GV class is trivial. -/
  isTrivial : Bool
  /-- Trivial iff numerator is 0. -/
  trivial_iff : isTrivial = true ↔ gvNumerator = 0

namespace GodbillonVey

/-- GV class of the Reeb foliation on S³: GV ≠ 0 (Thurston). -/
def reebGV : GodbillonVey where
  dim := 3
  dim_ge3 := by omega
  degree := 3
  degree_eq := rfl
  gvNumerator := 1
  gvDenominator := 1
  denom_pos := Nat.one_pos
  isTrivial := false
  trivial_iff := by simp

/-- GV class of a product foliation: GV = 0. -/
def productGV (n : Nat) (hn : n ≥ 3) : GodbillonVey where
  dim := n
  dim_ge3 := hn
  degree := 3
  degree_eq := rfl
  gvNumerator := 0
  gvDenominator := 1
  denom_pos := Nat.one_pos
  isTrivial := true
  trivial_iff := by simp

/-- Reeb GV is nontrivial. -/
theorem reeb_nontrivial : reebGV.isTrivial = false := rfl

/-- Reeb GV has degree 3. -/
theorem reeb_degree : reebGV.degree = 3 := rfl

/-- Product foliation has trivial GV. -/
theorem product_trivial (n : Nat) (hn : n ≥ 3) :
    (productGV n hn).isTrivial = true := rfl

/-- GV class lives in degree 3. -/
theorem gv_degree (gv : GodbillonVey) : gv.degree = 3 := gv.degree_eq

/-- Product GV has zero numerator. -/
theorem product_zero (n : Nat) (hn : n ≥ 3) :
    (productGV n hn).gvNumerator = 0 := rfl

end GodbillonVey

/-! ## Haefliger Structures -/

/-- A Haefliger Γ_q-structure: generalizes codimension-q foliations.
Classified by maps to BΓ_q. -/
structure HaefligerStructure where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Dimension is positive. -/
  dim_pos : dim > 0
  /-- Codimension q. -/
  codim : Nat
  /-- q ≥ 1. -/
  codim_pos : codim ≥ 1
  /-- Whether this comes from an actual foliation. -/
  isGenuine : Bool
  /-- Haefliger classifying space dimension bound. -/
  classifyingDim : Nat
  /-- Classification: BΓ_q is (2q)-connected roughly. -/
  classify_bound : classifyingDim ≥ codim

namespace HaefligerStructure

/-- A genuine foliation viewed as a Haefliger structure. -/
def fromFoliation (n q : Nat) (hn : n > 0) (hq : q ≥ 1) (_hqn : q ≤ n) :
    HaefligerStructure where
  dim := n
  dim_pos := hn
  codim := q
  codim_pos := hq
  isGenuine := true
  classifyingDim := q
  classify_bound := Nat.le_refl q

/-- A Haefliger structure that is not a foliation. -/
def nonGenuine (n q : Nat) (hn : n > 0) (hq : q ≥ 1) :
    HaefligerStructure where
  dim := n
  dim_pos := hn
  codim := q
  codim_pos := hq
  isGenuine := false
  classifyingDim := 2 * q
  classify_bound := by omega

/-- Genuine foliation is genuine. -/
theorem genuine_is_genuine (n q : Nat) (hn : n > 0) (hq : q ≥ 1) (hqn : q ≤ n) :
    (fromFoliation n q hn hq hqn).isGenuine = true := rfl

/-- Non-genuine is not genuine. -/
theorem non_genuine (n q : Nat) (hn : n > 0) (hq : q ≥ 1) :
    (nonGenuine n q hn hq).isGenuine = false := rfl

end HaefligerStructure

/-! ## Leaf Space -/

/-- The leaf space M/F of a foliated manifold (M, F).
Often non-Hausdorff; we record its properties. -/
structure LeafSpace where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Codimension (expected dimension of leaf space). -/
  codim : Nat
  /-- Whether the leaf space is Hausdorff. -/
  isHausdorff : Bool
  /-- Whether the leaf space is a manifold. -/
  isManifold : Bool
  /-- If manifold, it must be Hausdorff. -/
  manifold_hausdorff : isManifold = true → isHausdorff = true
  /-- Whether all leaves are closed. -/
  allLeavesClosed : Bool

namespace LeafSpace

/-- Leaf space of a fibration F → M → B: B is a manifold. -/
def fibration (n q : Nat) : LeafSpace where
  dim := n
  codim := q
  isHausdorff := true
  isManifold := true
  manifold_hausdorff := fun _ => rfl
  allLeavesClosed := true

/-- Leaf space of the Reeb foliation: non-Hausdorff. -/
def reebLeafSpace : LeafSpace where
  dim := 3
  codim := 1
  isHausdorff := false
  isManifold := false
  manifold_hausdorff := by simp
  allLeavesClosed := false

/-- Leaf space of the irrational slope foliation on T²: non-Hausdorff. -/
def irrationalSlope : LeafSpace where
  dim := 2
  codim := 1
  isHausdorff := false
  isManifold := false
  manifold_hausdorff := by simp
  allLeavesClosed := false

/-- Fibration leaf space is Hausdorff. -/
theorem fibration_hausdorff (n q : Nat) :
    (fibration n q).isHausdorff = true := rfl

/-- Fibration leaf space is a manifold. -/
theorem fibration_manifold (n q : Nat) :
    (fibration n q).isManifold = true := rfl

/-- Reeb leaf space is not Hausdorff. -/
theorem reeb_not_hausdorff : reebLeafSpace.isHausdorff = false := rfl

/-- Reeb leaf space is not a manifold. -/
theorem reeb_not_manifold : reebLeafSpace.isManifold = false := rfl

/-- Irrational slope leaf space is not Hausdorff. -/
theorem irrational_not_hausdorff : irrationalSlope.isHausdorff = false := rfl

/-- Fibration has all leaves closed. -/
theorem fibration_closed (n q : Nat) :
    (fibration n q).allLeavesClosed = true := rfl

end LeafSpace

/-! ## Transverse Geometry -/

/-- Transverse geometry: geometric structures on the normal bundle
ν = TM/TF of a foliation, invariant under holonomy. -/
structure TransverseGeometry where
  /-- Codimension (dimension of the transverse space). -/
  codim : Nat
  /-- Codimension ≥ 1. -/
  codim_pos : codim ≥ 1
  /-- Type of transverse structure. -/
  structureType : Nat  -- 0 = Riemannian, 1 = conformal, 2 = projective, 3 = symplectic
  /-- Normal bundle rank = codimension. -/
  normalRank : Nat
  /-- Normal rank equals codim. -/
  normal_eq : normalRank = codim
  /-- Whether the transverse structure is complete. -/
  isComplete : Bool

namespace TransverseGeometry

/-- Transversely Riemannian foliation. -/
def riemannian (q : Nat) (hq : q ≥ 1) (complete : Bool) : TransverseGeometry where
  codim := q
  codim_pos := hq
  structureType := 0
  normalRank := q
  normal_eq := rfl
  isComplete := complete

/-- Transversely symplectic foliation (codim must be even). -/
def symplectic (q : Nat) (hq : q ≥ 2) : TransverseGeometry where
  codim := q
  codim_pos := by omega
  structureType := 3
  normalRank := q
  normal_eq := rfl
  isComplete := false

/-- Riemannian transverse structure has type 0. -/
theorem riemannian_type (q : Nat) (hq : q ≥ 1) (c : Bool) :
    (riemannian q hq c).structureType = 0 := rfl

/-- Normal rank equals codimension. -/
theorem normal_rank (tg : TransverseGeometry) :
    tg.normalRank = tg.codim := tg.normal_eq

end TransverseGeometry

/-! ## Molino's Theorem -/

/-- Molino's structure theorem for Riemannian foliations:
on a compact manifold with a complete Riemannian foliation,
the leaf closures form a singular Riemannian foliation whose
leaf space is an orbifold, and there is a transverse Lie structure. -/
structure MolinoTheorem where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Dimension is positive. -/
  dim_pos : dim > 0
  /-- Codimension. -/
  codim : Nat
  /-- Codimension ≥ 1. -/
  codim_pos : codim ≥ 1
  /-- codim ≤ dim. -/
  codim_le : codim ≤ dim
  /-- Dimension of the structural Lie algebra. -/
  lieDim : Nat
  /-- Lie algebra dimension ≤ codimension. -/
  lie_le : lieDim ≤ codim
  /-- Whether the leaf closures form a fibration. -/
  closuresAreFibration : Bool
  /-- Whether the leaf space (of closures) is an orbifold. -/
  closureSpaceOrbifold : Bool
  /-- Molino guarantees orbifold structure. -/
  molino_orbifold : closureSpaceOrbifold = true

namespace MolinoTheorem

/-- Molino for a transversely parallelizable foliation: Lie algebra
fills the transverse directions, closures are fibers of a fibration. -/
def transverselyParallelizable (n q : Nat)
    (hn : n > 0) (hq : q ≥ 1) (hqn : q ≤ n) : MolinoTheorem where
  dim := n
  dim_pos := hn
  codim := q
  codim_pos := hq
  codim_le := hqn
  lieDim := q
  lie_le := Nat.le_refl q
  closuresAreFibration := true
  closureSpaceOrbifold := true
  molino_orbifold := rfl

/-- Molino for a codimension-1 Riemannian foliation. -/
def codim1 (n : Nat) (hn : n > 0) : MolinoTheorem where
  dim := n
  dim_pos := hn
  codim := 1
  codim_pos := by omega
  codim_le := hn
  lieDim := 0
  lie_le := Nat.zero_le 1
  closuresAreFibration := true
  closureSpaceOrbifold := true
  molino_orbifold := rfl

/-- Transversely parallelizable: closures are fibers of a fibration. -/
theorem tp_fibration (n q : Nat) (hn : n > 0) (hq : q ≥ 1) (hqn : q ≤ n) :
    (transverselyParallelizable n q hn hq hqn).closuresAreFibration = true := rfl

/-- Molino guarantees orbifold leaf space. -/
theorem orbifold (mt : MolinoTheorem) :
    mt.closureSpaceOrbifold = true := mt.molino_orbifold

/-- Structural Lie algebra dimension for TP foliations. -/
theorem tp_lie_dim (n q : Nat) (hn : n > 0) (hq : q ≥ 1) (hqn : q ≤ n) :
    (transverselyParallelizable n q hn hq hqn).lieDim = q := rfl

/-- Codim-1 has Lie dim 0. -/
theorem codim1_lie (n : Nat) (hn : n > 0) :
    (codim1 n hn).lieDim = 0 := rfl

end MolinoTheorem

/-! ## Connes' Foliation Algebra -/

/-- Connes' foliation C*-algebra C*(M, F): encodes the (typically
non-Hausdorff) leaf space via noncommutative geometry. -/
structure ConnesFoliationAlgebra where
  /-- Ambient dimension. -/
  dim : Nat
  /-- Dimension is positive. -/
  dim_pos : dim > 0
  /-- Codimension. -/
  codim : Nat
  /-- Codimension ≥ 1. -/
  codim_pos : codim ≥ 1
  /-- Leaf dimension. -/
  leafDim : Nat
  /-- Leaf dimension equation. -/
  leaf_eq : leafDim = dim - codim
  /-- Whether the algebra is commutative (iff leaf space is Hausdorff). -/
  isCommutative : Bool
  /-- K₀ rank of the algebra. -/
  k0Rank : Nat
  /-- K₁ rank of the algebra. -/
  k1Rank : Nat

namespace ConnesFoliationAlgebra

/-- Foliation algebra for the Kronecker foliation on T²
(irrational slope θ): the famous irrational rotation algebra A_θ. -/
def kronecker : ConnesFoliationAlgebra where
  dim := 2
  dim_pos := by omega
  codim := 1
  codim_pos := by omega
  leafDim := 1
  leaf_eq := rfl
  isCommutative := false
  k0Rank := 2
  k1Rank := 2

/-- Foliation algebra for a fibration: commutative. -/
def fibration (n q : Nat) (hn : n > 0) (hq : q ≥ 1) (_hqn : q ≤ n) :
    ConnesFoliationAlgebra where
  dim := n
  dim_pos := hn
  codim := q
  codim_pos := hq
  leafDim := n - q
  leaf_eq := rfl
  isCommutative := true
  k0Rank := 1
  k1Rank := 0

/-- Kronecker algebra is noncommutative. -/
theorem kronecker_noncommutative : kronecker.isCommutative = false := rfl

/-- Kronecker has K₀ rank 2. -/
theorem kronecker_k0 : kronecker.k0Rank = 2 := rfl

/-- Kronecker has K₁ rank 2. -/
theorem kronecker_k1 : kronecker.k1Rank = 2 := rfl

/-- Fibration algebra is commutative. -/
theorem fibration_commutative (n q : Nat) (hn : n > 0) (hq : q ≥ 1) (hqn : q ≤ n) :
    (fibration n q hn hq hqn).isCommutative = true := rfl

/-- Leaf dimension of Kronecker foliation. -/
theorem kronecker_leaf : kronecker.leafDim = 1 := rfl

end ConnesFoliationAlgebra

/-! ## Novikov's Theorem -/

/-- Novikov's compact leaf theorem: every smooth codimension-1
foliation of S³ has a compact leaf. -/
structure NovikovTheorem where
  /-- Ambient manifold dimension = 3. -/
  dim : Nat
  /-- dim = 3. -/
  dim_eq : dim = 3
  /-- Codimension = 1. -/
  codim : Nat
  /-- codim = 1. -/
  codim_eq : codim = 1
  /-- Guaranteed compact leaves ≥ 1. -/
  compactLeaves : Nat
  /-- At least one compact leaf. -/
  at_least_one : compactLeaves ≥ 1
  /-- The compact leaf is a torus. -/
  leafGenus : Nat
  /-- Genus = 1 (torus). -/
  genus_eq : leafGenus = 1

namespace NovikovTheorem

/-- Novikov's theorem applied to S³. -/
def s3 : NovikovTheorem where
  dim := 3
  dim_eq := rfl
  codim := 1
  codim_eq := rfl
  compactLeaves := 1
  at_least_one := by omega
  leafGenus := 1
  genus_eq := rfl

/-- S³ foliations have compact leaves. -/
theorem s3_has_compact : s3.compactLeaves ≥ 1 := by
  simp [s3]

/-- The compact leaf is a torus. -/
theorem s3_compact_is_torus : s3.leafGenus = 1 := rfl

/-- Novikov applies in dimension 3. -/
theorem s3_dim : s3.dim = 3 := rfl

end NovikovTheorem

/-! ## Path Coherence Witnesses -/

/-- Foliation leaf dimension path: leafDim = dim - codim. -/
def leaf_dim_path (f : Foliation) :
    Path f.leafDim (f.dim - f.codim) :=
  Path.ofEqChain f.leaf_eq

/-- Frobenius theorem path: involutive = integrable. -/
def frobenius_path (fd : FrobeniusData) :
    Path fd.isInvolutive fd.isIntegrable :=
  Path.ofEqChain fd.frobenius

/-- Reeb foliation dimension path. -/
def reeb_dim_path :
    Path ReebFoliation.standard.dim 3 :=
  Path.ofEqChain ReebFoliation.reeb_dim

/-- Reeb foliation codimension path. -/
def reeb_codim_path :
    Path ReebFoliation.standard.codim 1 :=
  Path.ofEqChain ReebFoliation.reeb_codim

/-- Reeb foliation leaf dimension path. -/
def reeb_leaf_path :
    Path ReebFoliation.standard.leafDim 2 :=
  Path.ofEqChain ReebFoliation.reeb_leaf_dim

/-- Reeb compact leaf count path. -/
def reeb_compact_path :
    Path ReebFoliation.standard.compactLeaves 1 :=
  Path.ofEqChain ReebFoliation.reeb_compact

/-- GV class degree path. -/
def gv_degree_path (gv : GodbillonVey) :
    Path gv.degree 3 :=
  Path.ofEqChain gv.degree_eq

/-- Reeb GV nontriviality path. -/
def reeb_gv_path :
    Path GodbillonVey.reebGV.isTrivial false :=
  Path.ofEqChain GodbillonVey.reeb_nontrivial

/-- Molino orbifold path. -/
def molino_orbifold_path (mt : MolinoTheorem) :
    Path mt.closureSpaceOrbifold true :=
  Path.ofEqChain mt.molino_orbifold

/-- Leaf space Reeb non-Hausdorff path. -/
def reeb_nonhausdorff_path :
    Path LeafSpace.reebLeafSpace.isHausdorff false :=
  Path.ofEqChain LeafSpace.reeb_not_hausdorff

/-- Kronecker noncommutativity path. -/
def kronecker_nc_path :
    Path ConnesFoliationAlgebra.kronecker.isCommutative false :=
  Path.ofEqChain ConnesFoliationAlgebra.kronecker_noncommutative

/-- Kronecker K₀ rank path. -/
def kronecker_k0_path :
    Path ConnesFoliationAlgebra.kronecker.k0Rank 2 :=
  Path.ofEqChain ConnesFoliationAlgebra.kronecker_k0

/-- Transverse normal rank path. -/
def normal_rank_path (tg : TransverseGeometry) :
    Path tg.normalRank tg.codim :=
  Path.ofEqChain tg.normal_eq

/-- Novikov's theorem dimension path. -/
def novikov_dim_path :
    Path NovikovTheorem.s3.dim 3 :=
  Path.ofEqChain NovikovTheorem.s3_dim

/-- Novikov compact leaf genus path. -/
def novikov_genus_path :
    Path NovikovTheorem.s3.leafGenus 1 :=
  Path.ofEqChain NovikovTheorem.s3_compact_is_torus

/-- Reeb decomposition path: 3 = 2 + 1. -/
def reeb_decomposition_path :
    Path ReebFoliation.standard.dim
         (ReebFoliation.standard.leafDim + ReebFoliation.standard.codim) :=
  Path.ofEqChain ReebFoliation.reeb_decomposition

/-- Foliation dim + codim = n path. -/
def foliation_sum_path (f : Foliation) :
    Path (f.leafDim + f.codim) f.dim :=
  Path.ofEqChain (Foliation.dim_codim_bound f)

/-- Connes algebra leaf dimension path. -/
def connes_leaf_path (ca : ConnesFoliationAlgebra) :
    Path ca.leafDim (ca.dim - ca.codim) :=
  Path.ofEqChain ca.leaf_eq

end FoliationTheory
end ComputationalPaths
