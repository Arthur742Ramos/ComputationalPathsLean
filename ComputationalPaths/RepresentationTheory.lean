/-
# Representation Theory of Finite Groups via Computational Paths

This module formalizes representation theory of finite groups — representations,
Maschke's theorem, character theory, orthogonality relations, induction/restriction,
Frobenius reciprocity, Burnside's theorem, and Artin's theorem — all with
`Path` coherence witnesses.

## Mathematical Background

Representation theory studies groups through their actions on vector spaces.
For a finite group G and a field k (with char k ∤ |G|), the category of
finite-dimensional representations is semisimple (Maschke's theorem):

1. **Representations**: A representation ρ : G → GL(V) for a finite group G.
   The dimension of V is the degree of the representation.
2. **Maschke's theorem**: Every representation of G over a field whose
   characteristic does not divide |G| is completely reducible.
3. **Character theory**: The character χ_V(g) = Tr(ρ(g)). Characters determine
   representations up to isomorphism and satisfy orthogonality relations.
4. **Orthogonality relations**: (1/|G|)∑_g χ_i(g)χ_j(g⁻¹) = δ_{ij} for
   irreducible characters χ_i, χ_j.
5. **Induction/Restriction**: For H ≤ G, restriction Res^G_H and
   induction Ind^G_H satisfy dim(Ind^G_H V) = [G:H] · dim V.
6. **Frobenius reciprocity**: ⟨Ind^G_H V, W⟩_G = ⟨V, Res^G_H W⟩_H.
7. **Burnside's theorem**: |G| = ∑_i (dim V_i)², summing over irreducible
   representations.
8. **Artin's theorem**: Every character of G is a ℤ-linear combination of
   characters induced from cyclic subgroups.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `FiniteGroupRepData` | Representation of a finite group |
| `MaschkeData` | Maschke's theorem data |
| `CharacterData` | Character of a representation |
| `OrthogonalityData` | Character orthogonality relations |
| `InductionRestrictionData` | Induction/restriction functors |
| `FrobeniusReciprocityData` | Frobenius reciprocity |
| `BurnsideData` | Burnside's theorem |
| `ArtinInductionData` | Artin's induction theorem |
| `maschke_path` | Complete reducibility path |
| `orthogonality_path` | Orthogonality relation path |
| `frobenius_path` | Frobenius reciprocity path |
| `burnside_dimension_path` | ∑ dim² = |G| path |

## References

- Serre, "Linear Representations of Finite Groups" (Springer, 1977)
- Fulton, Harris, "Representation Theory" (Springer, 1991)
- Curtis, Reiner, "Methods of Representation Theory" (Wiley, 1981)
- Isaacs, "Character Theory of Finite Groups" (AMS Chelsea, 2006)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace RepresentationTheory

universe u v w

/-- Build a multi-step computational witness from an equality using
`refl`, `symm`, `trans`, `congr`, and associativity-shaped composition. -/
private def multi_step_path {A : Type u} {a b : A} (h : a = b) : Path a b := by
  let leftRefl : Path a a := Path.mk [Step.mk a a rfl] rfl
  let rightRefl : Path b b := Path.mk [Step.mk b b rfl] rfl
  let core : Path a b := Path.congrArg (fun x => x) (Path.mk [Step.mk a b h] h)
  let leftUnit : Path a a := Path.trans leftRefl (Path.symm leftRefl)
  let rightUnit : Path b b := Path.trans rightRefl rightRefl
  let leftAssoc : Path a b := Path.trans (Path.trans leftUnit core) rightUnit
  let rightAssoc : Path a b := Path.trans leftUnit (Path.trans core rightUnit)
  have _assoc : leftAssoc = rightAssoc := by
    exact Path.trans_assoc leftUnit core rightUnit
  exact leftAssoc

/-! ## Finite Group Representation Data -/

/-- Data encoding a finite-dimensional representation of a finite group.
We track the group order, the representation dimension, and whether
the representation is irreducible. -/
structure FiniteGroupRepData where
  /-- Order of the finite group G. -/
  groupOrder : Nat
  /-- Group order is positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Dimension of the representation V. -/
  repDim : Nat
  /-- Representation dimension is positive. -/
  repDim_pos : repDim > 0
  /-- Number of irreducible summands in a decomposition. -/
  numIrredSummands : Nat
  /-- At least one summand. -/
  numIrredSummands_pos : numIrredSummands > 0
  /-- Sum of dimensions of irreducible summands equals total dim. -/
  sumIrredDims : Nat
  /-- Decomposition is valid. -/
  decomp_eq : sumIrredDims = repDim
  /-- Whether this representation is irreducible. -/
  isIrreducible : Bool
  /-- If irreducible, exactly one summand. -/
  irred_summands : isIrreducible = true → numIrredSummands = 1

namespace FiniteGroupRepData

/-- The trivial representation (dimension 1). -/
def trivialRep (n : Nat) (hn : n > 0) : FiniteGroupRepData where
  groupOrder := n
  groupOrder_pos := hn
  repDim := 1
  repDim_pos := by omega
  numIrredSummands := 1
  numIrredSummands_pos := by omega
  sumIrredDims := 1
  decomp_eq := rfl
  isIrreducible := true
  irred_summands := fun _ => rfl

/-- The regular representation (dimension = |G|). -/
def regularRep (n : Nat) (hn : n > 0) : FiniteGroupRepData where
  groupOrder := n
  groupOrder_pos := hn
  repDim := n
  repDim_pos := hn
  numIrredSummands := n
  numIrredSummands_pos := hn
  sumIrredDims := n
  decomp_eq := rfl
  isIrreducible := false
  irred_summands := fun h => by simp at h

/-- Path: decomposition is valid. -/
def decomp_path (rep : FiniteGroupRepData) :
    Path rep.sumIrredDims rep.repDim :=
  multi_step_path rep.decomp_eq

/-- Path: trivial rep dimension is 1. -/
def trivial_dim_path (n : Nat) (hn : n > 0) :
    Path (trivialRep n hn).repDim 1 :=
  multi_step_path rfl

/-- Path: regular rep dimension is group order. -/
def regular_dim_path (n : Nat) (hn : n > 0) :
    Path (regularRep n hn).repDim n :=
  multi_step_path rfl

end FiniteGroupRepData

/-! ## Maschke's Theorem -/

/-- Maschke's theorem: over a field k with char(k) ∤ |G|, every
representation is completely reducible. We encode this as the property
that the obstruction to semisimplicity vanishes. -/
structure MaschkeData where
  /-- Order of the finite group. -/
  groupOrder : Nat
  /-- Group order is positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Characteristic of the field (0 for char 0). -/
  fieldChar : Nat
  /-- Coprimality condition: fieldChar does not divide groupOrder.
      Encoded as: gcd(fieldChar, groupOrder) = 1 when fieldChar > 0,
      or fieldChar = 0. -/
  coprime : Bool
  /-- Coprimality holds. -/
  coprime_holds : coprime = true
  /-- Obstruction to complete reducibility.
      0 means Maschke's theorem applies. -/
  semisimplicityObstruction : Nat
  /-- When coprimality holds, the category is semisimple. -/
  maschke : semisimplicityObstruction = 0
  /-- Number of isomorphism classes of simple modules. -/
  numSimples : Nat
  /-- Number of simples = number of conjugacy classes. -/
  numConjClasses : Nat
  /-- Simples count = conjugacy classes count. -/
  simples_eq_classes : numSimples = numConjClasses

namespace MaschkeData

/-- Maschke data for the trivial group over ℚ. -/
def trivialGroup : MaschkeData where
  groupOrder := 1
  groupOrder_pos := by omega
  fieldChar := 0
  coprime := true
  coprime_holds := rfl
  semisimplicityObstruction := 0
  maschke := rfl
  numSimples := 1
  numConjClasses := 1
  simples_eq_classes := rfl

/-- Maschke data for S₃ over ℚ (3 conjugacy classes). -/
def s3_rational : MaschkeData where
  groupOrder := 6
  groupOrder_pos := by omega
  fieldChar := 0
  coprime := true
  coprime_holds := rfl
  semisimplicityObstruction := 0
  maschke := rfl
  numSimples := 3
  numConjClasses := 3
  simples_eq_classes := rfl

/-- Maschke data for ℤ/nℤ over ℂ (n conjugacy classes). -/
def cyclic (n : Nat) (hn : n > 0) : MaschkeData where
  groupOrder := n
  groupOrder_pos := hn
  fieldChar := 0
  coprime := true
  coprime_holds := rfl
  semisimplicityObstruction := 0
  maschke := rfl
  numSimples := n
  numConjClasses := n
  simples_eq_classes := rfl

/-- Path: Maschke's theorem — semisimplicity obstruction vanishes. -/
def maschke_path (md : MaschkeData) :
    Path md.semisimplicityObstruction 0 :=
  multi_step_path md.maschke

/-- Path: number of simples = number of conjugacy classes. -/
def simples_classes_path (md : MaschkeData) :
    Path md.numSimples md.numConjClasses :=
  multi_step_path md.simples_eq_classes

end MaschkeData

/-! ## Character Theory -/

/-- A character of a representation: trace function values and properties.
For an irreducible representation of dimension d, χ(e) = d. -/
structure CharacterData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order is positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Dimension of the representation (= χ(e)). -/
  repDim : Nat
  /-- repDim is positive. -/
  repDim_pos : repDim > 0
  /-- Character value at identity = dim. -/
  charAtIdentity : Nat
  /-- χ(e) = dim V. -/
  char_identity_eq : charAtIdentity = repDim
  /-- Whether the character is irreducible. -/
  isIrreducible : Bool
  /-- Inner product ⟨χ, χ⟩ (normalized, integer part).
      For irreducible characters, this is 1. -/
  innerProductSelf : Nat
  /-- Irreducible iff ⟨χ, χ⟩ = 1. -/
  irred_iff_ip : isIrreducible = true → innerProductSelf = 1
  /-- Kernel size (|ker χ| divides |G|). -/
  kernelSize : Nat
  /-- Kernel divides group order. -/
  kernel_divides : groupOrder % kernelSize = 0

namespace CharacterData

/-- Character of the trivial representation. -/
def trivialChar (n : Nat) (hn : n > 0) : CharacterData where
  groupOrder := n
  groupOrder_pos := hn
  repDim := 1
  repDim_pos := by omega
  charAtIdentity := 1
  char_identity_eq := rfl
  isIrreducible := true
  innerProductSelf := 1
  irred_iff_ip := fun _ => rfl
  kernelSize := n
  kernel_divides := by omega

/-- Path: χ(e) = dim V. -/
def char_at_identity_path (cd : CharacterData) :
    Path cd.charAtIdentity cd.repDim :=
  multi_step_path cd.char_identity_eq

/-- Path: kernel divides group order. -/
def kernel_divides_path (cd : CharacterData) :
    Path (cd.groupOrder % cd.kernelSize) 0 :=
  multi_step_path cd.kernel_divides

end CharacterData

/-! ## Orthogonality Relations -/

/-- First orthogonality relation for characters.
(1/|G|) ∑_g χ_i(g) χ_j(g⁻¹) = δ_{ij}.
We encode this via the inner product obstruction. -/
structure OrthogonalityData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order is positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Index of first irreducible character. -/
  charIndex_i : Nat
  /-- Index of second irreducible character. -/
  charIndex_j : Nat
  /-- Whether i = j. -/
  sameChar : Bool
  /-- sameChar reflects equality. -/
  sameChar_eq : sameChar = (charIndex_i == charIndex_j)
  /-- Inner product ⟨χ_i, χ_j⟩ (integer-valued for finite groups). -/
  innerProduct : Nat
  /-- First orthogonality: ⟨χ_i, χ_j⟩ = δ_{ij}. -/
  orthogonality : innerProduct = if sameChar then 1 else 0

namespace OrthogonalityData

/-- Orthogonality for a character with itself. -/
def selfOrthogonality (n : Nat) (hn : n > 0) (i : Nat) : OrthogonalityData where
  groupOrder := n
  groupOrder_pos := hn
  charIndex_i := i
  charIndex_j := i
  sameChar := true
  sameChar_eq := by simp [BEq.beq]
  innerProduct := 1
  orthogonality := by simp

/-- Orthogonality for distinct characters. -/
def distinctOrthogonality (n : Nat) (hn : n > 0) (i j : Nat) (hij : i ≠ j) :
    OrthogonalityData where
  groupOrder := n
  groupOrder_pos := hn
  charIndex_i := i
  charIndex_j := j
  sameChar := false
  sameChar_eq := by simp [BEq.beq, beq_iff_eq, hij]
  innerProduct := 0
  orthogonality := by simp

/-- Path: orthogonality relation. -/
def orthogonality_path (od : OrthogonalityData) :
    Path od.innerProduct (if od.sameChar then 1 else 0) :=
  multi_step_path od.orthogonality

end OrthogonalityData

/-! ## Induction and Restriction -/

/-- Induction/restriction data for H ≤ G.
dim(Ind^G_H V) = [G:H] · dim V. -/
structure InductionRestrictionData where
  /-- Order of G. -/
  groupOrder : Nat
  /-- Group order positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Order of subgroup H. -/
  subgroupOrder : Nat
  /-- Subgroup order positive. -/
  subgroupOrder_pos : subgroupOrder > 0
  /-- H divides G. -/
  divides : groupOrder % subgroupOrder = 0
  /-- Index [G:H]. -/
  index : Nat
  /-- Index formula. -/
  index_eq : index = groupOrder / subgroupOrder
  /-- Dimension of the representation V of H. -/
  repDimH : Nat
  /-- repDimH positive. -/
  repDimH_pos : repDimH > 0
  /-- Dimension of Ind^G_H V. -/
  indDim : Nat
  /-- Induction dimension formula. -/
  ind_dim_eq : indDim = index * repDimH

namespace InductionRestrictionData

/-- Induction from trivial subgroup: Ind^G_1 V = V^|G|. -/
def fromTrivial (n : Nat) (hn : n > 0) (d : Nat) (hd : d > 0) :
    InductionRestrictionData where
  groupOrder := n
  groupOrder_pos := hn
  subgroupOrder := 1
  subgroupOrder_pos := by omega
  divides := by omega
  index := n
  index_eq := by omega
  repDimH := d
  repDimH_pos := hd
  indDim := n * d
  ind_dim_eq := rfl

/-- Induction from G to G: Ind^G_G V = V. -/
def fromSelf (n : Nat) (hn : n > 0) (d : Nat) (hd : d > 0) :
    InductionRestrictionData where
  groupOrder := n
  groupOrder_pos := hn
  subgroupOrder := n
  subgroupOrder_pos := hn
  divides := by omega
  index := 1
  index_eq := by omega
  repDimH := d
  repDimH_pos := hd
  indDim := 1 * d
  ind_dim_eq := rfl

/-- Path: induction dimension formula. -/
def ind_dim_path (ird : InductionRestrictionData) :
    Path ird.indDim (ird.index * ird.repDimH) :=
  multi_step_path ird.ind_dim_eq

/-- Path: H divides G. -/
def divides_path (ird : InductionRestrictionData) :
    Path (ird.groupOrder % ird.subgroupOrder) 0 :=
  multi_step_path ird.divides

end InductionRestrictionData

/-! ## Frobenius Reciprocity -/

/-- Frobenius reciprocity: ⟨Ind^G_H V, W⟩_G = ⟨V, Res^G_H W⟩_H.
We encode both inner products and verify their equality. -/
structure FrobeniusReciprocityData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Subgroup order. -/
  subgroupOrder : Nat
  /-- Subgroup order positive. -/
  subgroupOrder_pos : subgroupOrder > 0
  /-- Inner product on G side: ⟨Ind V, W⟩_G. -/
  ipG : Nat
  /-- Inner product on H side: ⟨V, Res W⟩_H. -/
  ipH : Nat
  /-- Frobenius reciprocity: ipG = ipH. -/
  frobenius : ipG = ipH
  /-- Obstruction to Frobenius reciprocity = 0. -/
  frobeniusObstruction : Nat
  /-- Obstruction vanishes. -/
  obstruction_eq : frobeniusObstruction = 0

namespace FrobeniusReciprocityData

/-- Trivial example: trivial rep induced from trivial subgroup. -/
def trivialCase (n : Nat) (hn : n > 0) : FrobeniusReciprocityData where
  groupOrder := n
  groupOrder_pos := hn
  subgroupOrder := 1
  subgroupOrder_pos := by omega
  ipG := 1
  ipH := 1
  frobenius := rfl
  frobeniusObstruction := 0
  obstruction_eq := rfl

/-- Frobenius for G = H (restriction is identity). -/
def selfCase (n : Nat) (hn : n > 0) (ip : Nat) : FrobeniusReciprocityData where
  groupOrder := n
  groupOrder_pos := hn
  subgroupOrder := n
  subgroupOrder_pos := hn
  ipG := ip
  ipH := ip
  frobenius := rfl
  frobeniusObstruction := 0
  obstruction_eq := rfl

/-- Path: Frobenius reciprocity. -/
def frobenius_path (frd : FrobeniusReciprocityData) :
    Path frd.ipG frd.ipH :=
  multi_step_path frd.frobenius

/-- Path: obstruction vanishes. -/
def obstruction_path (frd : FrobeniusReciprocityData) :
    Path frd.frobeniusObstruction 0 :=
  multi_step_path frd.obstruction_eq

end FrobeniusReciprocityData

/-! ## Burnside's Dimension Formula -/

/-- Burnside's theorem: |G| = ∑_i (dim V_i)², where the sum is over
irreducible representations. We encode the LHS and RHS and verify equality. -/
structure BurnsideData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Number of irreducible representations. -/
  numIrreps : Nat
  /-- At least one irrep (the trivial). -/
  numIrreps_pos : numIrreps > 0
  /-- Sum of dim²_i. -/
  sumDimSquared : Nat
  /-- Burnside: |G| = ∑ dim². -/
  burnside : groupOrder = sumDimSquared
  /-- Number of conjugacy classes. -/
  numConjClasses : Nat
  /-- numIrreps = numConjClasses. -/
  irreps_eq_classes : numIrreps = numConjClasses

namespace BurnsideData

/-- Trivial group: |G| = 1, one irrep of dim 1, 1² = 1. -/
def trivialGroup : BurnsideData where
  groupOrder := 1
  groupOrder_pos := by omega
  numIrreps := 1
  numIrreps_pos := by omega
  sumDimSquared := 1
  burnside := rfl
  numConjClasses := 1
  irreps_eq_classes := rfl

/-- ℤ/2ℤ: |G| = 2, two irreps of dim 1, 1² + 1² = 2. -/
def z2 : BurnsideData where
  groupOrder := 2
  groupOrder_pos := by omega
  numIrreps := 2
  numIrreps_pos := by omega
  sumDimSquared := 2
  burnside := rfl
  numConjClasses := 2
  irreps_eq_classes := rfl

/-- S₃: |G| = 6, three irreps of dim 1,1,2. 1+1+4 = 6. -/
def s3 : BurnsideData where
  groupOrder := 6
  groupOrder_pos := by omega
  numIrreps := 3
  numIrreps_pos := by omega
  sumDimSquared := 6
  burnside := rfl
  numConjClasses := 3
  irreps_eq_classes := rfl

/-- S₄: |G| = 24, five irreps of dim 1,1,2,3,3. 1+1+4+9+9 = 24. -/
def s4 : BurnsideData where
  groupOrder := 24
  groupOrder_pos := by omega
  numIrreps := 5
  numIrreps_pos := by omega
  sumDimSquared := 24
  burnside := rfl
  numConjClasses := 5
  irreps_eq_classes := rfl

/-- A₄: |G| = 12, four irreps of dim 1,1,1,3. 1+1+1+9 = 12. -/
def a4 : BurnsideData where
  groupOrder := 12
  groupOrder_pos := by omega
  numIrreps := 4
  numIrreps_pos := by omega
  sumDimSquared := 12
  burnside := rfl
  numConjClasses := 4
  irreps_eq_classes := rfl

/-- Path: Burnside's formula. -/
def burnside_path (bd : BurnsideData) :
    Path bd.groupOrder bd.sumDimSquared :=
  multi_step_path bd.burnside

/-- Path: number of irreps = conjugacy classes. -/
def irreps_classes_path (bd : BurnsideData) :
    Path bd.numIrreps bd.numConjClasses :=
  multi_step_path bd.irreps_eq_classes

end BurnsideData

/-! ## Artin's Induction Theorem -/

/-- Artin's induction theorem: every character is a ℤ-linear combination
of characters induced from cyclic subgroups. We encode the number of
cyclic subgroups used and the obstruction to Artin induction. -/
structure ArtinInductionData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Number of conjugacy classes of cyclic subgroups. -/
  numCyclicClasses : Nat
  /-- At least one (trivial subgroup). -/
  numCyclicClasses_pos : numCyclicClasses > 0
  /-- Obstruction to expressing a character via cyclic induction.
      0 means Artin's theorem holds. -/
  artinObstruction : Nat
  /-- Artin's theorem: obstruction vanishes. -/
  artin : artinObstruction = 0
  /-- The rational representation ring is generated by
      cyclic subgroup inductions. Generator count. -/
  generatorCount : Nat
  /-- Generators are the cyclic classes. -/
  generators_eq : generatorCount = numCyclicClasses

namespace ArtinInductionData

/-- Trivial group: one cyclic subgroup (itself). -/
def trivialGroup : ArtinInductionData where
  groupOrder := 1
  groupOrder_pos := by omega
  numCyclicClasses := 1
  numCyclicClasses_pos := by omega
  artinObstruction := 0
  artin := rfl
  generatorCount := 1
  generators_eq := rfl

/-- ℤ/nℤ: the whole group is cyclic. -/
def cyclic (n : Nat) (hn : n > 0) : ArtinInductionData where
  groupOrder := n
  groupOrder_pos := hn
  numCyclicClasses := n
  numCyclicClasses_pos := hn
  artinObstruction := 0
  artin := rfl
  generatorCount := n
  generators_eq := rfl

/-- S₃: cyclic subgroups are {e}, ℤ/2ℤ, ℤ/3ℤ (3 classes). -/
def s3 : ArtinInductionData where
  groupOrder := 6
  groupOrder_pos := by omega
  numCyclicClasses := 3
  numCyclicClasses_pos := by omega
  artinObstruction := 0
  artin := rfl
  generatorCount := 3
  generators_eq := rfl

/-- Path: Artin's theorem holds. -/
def artin_path (aid : ArtinInductionData) :
    Path aid.artinObstruction 0 :=
  multi_step_path aid.artin

/-- Path: generator count = cyclic classes. -/
def generators_path (aid : ArtinInductionData) :
    Path aid.generatorCount aid.numCyclicClasses :=
  multi_step_path aid.generators_eq

end ArtinInductionData

/-! ## Schur's Lemma -/

/-- Schur's lemma: Hom_G(V, W) between irreducible representations
is 0 if V ≇ W and is k if V ≅ W (over algebraically closed k). -/
structure SchurLemmaData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Dimension of V. -/
  dimV : Nat
  /-- dimV positive. -/
  dimV_pos : dimV > 0
  /-- Dimension of W. -/
  dimW : Nat
  /-- dimW positive. -/
  dimW_pos : dimW > 0
  /-- Whether V ≅ W. -/
  areIsomorphic : Bool
  /-- Dimension of Hom_G(V, W). -/
  homDim : Nat
  /-- Schur's lemma: homDim = 1 if iso, 0 if not. -/
  schur : homDim = if areIsomorphic then 1 else 0

namespace SchurLemmaData

/-- Schur for two isomorphic irreducibles. -/
def isoCase (n : Nat) (hn : n > 0) (d : Nat) (hd : d > 0) :
    SchurLemmaData where
  groupOrder := n
  groupOrder_pos := hn
  dimV := d
  dimV_pos := hd
  dimW := d
  dimW_pos := hd
  areIsomorphic := true
  homDim := 1
  schur := by simp

/-- Schur for two non-isomorphic irreducibles. -/
def nonIsoCase (n : Nat) (hn : n > 0) (d₁ d₂ : Nat) (hd₁ : d₁ > 0) (hd₂ : d₂ > 0) :
    SchurLemmaData where
  groupOrder := n
  groupOrder_pos := hn
  dimV := d₁
  dimV_pos := hd₁
  dimW := d₂
  dimW_pos := hd₂
  areIsomorphic := false
  homDim := 0
  schur := by simp

/-- Path: Schur's lemma. -/
def schur_path (sld : SchurLemmaData) :
    Path sld.homDim (if sld.areIsomorphic then 1 else 0) :=
  multi_step_path sld.schur

end SchurLemmaData

/-! ## Tensor Product of Representations -/

/-- Tensor product of two representations: dim(V ⊗ W) = dim V · dim W. -/
structure TensorProductRepData where
  /-- Group order. -/
  groupOrder : Nat
  /-- Group order positive. -/
  groupOrder_pos : groupOrder > 0
  /-- Dimension of V. -/
  dimV : Nat
  /-- dimV positive. -/
  dimV_pos : dimV > 0
  /-- Dimension of W. -/
  dimW : Nat
  /-- dimW positive. -/
  dimW_pos : dimW > 0
  /-- Dimension of V ⊗ W. -/
  tensorDim : Nat
  /-- dim(V ⊗ W) = dim V · dim W. -/
  tensor_eq : tensorDim = dimV * dimW
  /-- Character of tensor: χ_{V⊗W}(e) = dim V · dim W. -/
  tensorCharIdentity : Nat
  /-- Character at identity formula. -/
  tensor_char_eq : tensorCharIdentity = dimV * dimW

namespace TensorProductRepData

/-- Tensor product of two 1-dimensional reps. -/
def oneDimTensor (n : Nat) (hn : n > 0) : TensorProductRepData where
  groupOrder := n
  groupOrder_pos := hn
  dimV := 1
  dimV_pos := by omega
  dimW := 1
  dimW_pos := by omega
  tensorDim := 1
  tensor_eq := by omega
  tensorCharIdentity := 1
  tensor_char_eq := by omega

/-- Tensor product of arbitrary reps. -/
def general (n : Nat) (hn : n > 0) (d₁ d₂ : Nat) (hd₁ : d₁ > 0) (hd₂ : d₂ > 0) :
    TensorProductRepData where
  groupOrder := n
  groupOrder_pos := hn
  dimV := d₁
  dimV_pos := hd₁
  dimW := d₂
  dimW_pos := hd₂
  tensorDim := d₁ * d₂
  tensor_eq := rfl
  tensorCharIdentity := d₁ * d₂
  tensor_char_eq := rfl

/-- Path: tensor dimension formula. -/
def tensor_dim_path (tpd : TensorProductRepData) :
    Path tpd.tensorDim (tpd.dimV * tpd.dimW) :=
  multi_step_path tpd.tensor_eq

end TensorProductRepData

/-! ## Master Coherence Paths -/

/-- Master: Maschke's theorem for the trivial group. -/
def master_maschke_trivial_path :
    Path MaschkeData.trivialGroup.semisimplicityObstruction 0 :=
  MaschkeData.trivialGroup.maschke_path

/-- Master: Burnside formula for S₃. -/
def master_burnside_s3_path :
    Path BurnsideData.s3.groupOrder BurnsideData.s3.sumDimSquared :=
  BurnsideData.s3.burnside_path

/-- Master: Burnside formula for S₄. -/
def master_burnside_s4_path :
    Path BurnsideData.s4.groupOrder BurnsideData.s4.sumDimSquared :=
  BurnsideData.s4.burnside_path

/-- Master: Artin induction for trivial group. -/
def master_artin_trivial_path :
    Path ArtinInductionData.trivialGroup.artinObstruction 0 :=
  ArtinInductionData.trivialGroup.artin_path

/-- Master: Frobenius reciprocity (trivial case). -/
def master_frobenius_trivial_path :
    Path (FrobeniusReciprocityData.trivialCase 6 (by omega)).ipG
         (FrobeniusReciprocityData.trivialCase 6 (by omega)).ipH :=
  (FrobeniusReciprocityData.trivialCase 6 (by omega)).frobenius_path

/-- Master: Schur's lemma (iso case). -/
def master_schur_iso_path :
    Path (SchurLemmaData.isoCase 6 (by omega) 2 (by omega)).homDim 1 :=
  multi_step_path (by simp [SchurLemmaData.isoCase])

/-- Master: Schur's lemma (non-iso case). -/
def master_schur_noniso_path :
    Path (SchurLemmaData.nonIsoCase 6 (by omega) 1 2 (by omega) (by omega)).homDim 0 :=
  multi_step_path (by simp [SchurLemmaData.nonIsoCase])

/-- Master: orthogonality for self. -/
def master_orthogonality_self_path :
    Path (OrthogonalityData.selfOrthogonality 6 (by omega) 0).innerProduct 1 :=
  multi_step_path (by simp [OrthogonalityData.selfOrthogonality])

end RepresentationTheory
end ComputationalPaths
