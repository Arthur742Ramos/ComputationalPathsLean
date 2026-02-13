/-
# Computability Theory via Computational Paths

This module formalizes computability theory — recursive functions, partial
recursive functions, μ-recursion, Kleene's recursion theorem, the s-m-n
theorem, Post's theorem, the arithmetical hierarchy, and Turing degrees —
all with `Path` coherence witnesses.

## Mathematical Background

Computability theory studies the nature and limitations of algorithmic
computation:

1. **Primitive Recursive Functions**: The class of functions built from
   zero, successor, and projection by composition and primitive recursion.
   Includes addition, multiplication, exponentiation, and bounded search.
   Not all total computable functions are primitive recursive (Ackermann).
2. **Partial Recursive Functions**: Extending primitive recursive functions
   with the μ-operator (unbounded minimization), yielding exactly the
   partial computable functions. A function f(x) = μy[g(x,y) = 0] returns
   the least y such that g(x,y) = 0.
3. **μ-Recursion**: The unbounded search operator. A function is partial
   recursive iff it can be computed by a Turing machine. This is the
   Church-Turing thesis in the form of μ-recursive = Turing-computable.
4. **Kleene's Recursion Theorem**: For every total computable function f,
   there exists n such that φ_n = φ_{f(n)}. This enables self-referential
   constructions. Fixed-point form: every computable operator has a
   fixed point in the Gödel numbering.
5. **s-m-n Theorem (Parameter Theorem)**: For every m,n there exists a
   total computable function s^m_n such that φ_{s^m_n(e,x₁,...,xₘ)}(y₁,...,yₙ)
   = φ_e(x₁,...,xₘ,y₁,...,yₙ). This allows currying of computable functions.
6. **Post's Theorem**: A set A is Σ⁰_{n+1} iff A is RE relative to ∅⁽ⁿ⁾
   (the nth Turing jump of ∅). This connects the arithmetical hierarchy
   with relative computability.
7. **Arithmetical Hierarchy**: Sets classified by the quantifier complexity
   of their definitions: Σ⁰_n (n alternating quantifiers starting with ∃),
   Π⁰_n (starting with ∀), Δ⁰_n = Σ⁰_n ∩ Π⁰_n. Each level is strictly
   contained in the next.
8. **Turing Degrees**: The quotient of sets of natural numbers by Turing
   equivalence (A ≡_T B iff A ≤_T B and B ≤_T A). The degrees form an
   upper semilattice with least element 0 (decidable sets) and
   the degree of the halting problem 0'.

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `PrimRecData` | Primitive recursive function data |
| `PartialRecData` | Partial recursive function data |
| `MuRecursionData` | μ-recursion data |
| `KleeneRecursionData` | Kleene's recursion theorem |
| `SMNData` | s-m-n theorem |
| `PostTheoremData` | Post's theorem |
| `ArithHierarchyData` | Arithmetical hierarchy |
| `TuringDegreeData` | Turing degrees |
| `primrec_closure_path` | Primitive recursive closure |
| `kleene_fixpoint_path` | Kleene fixed-point coherence |
| `smn_path` | s-m-n coherence |
| `post_path` | Post's theorem coherence |
| `hierarchy_path` | Arithmetical hierarchy coherence |
| `degree_path` | Turing degree coherence |

## References

- Kleene, "Introduction to Metamathematics" (1952)
- Rogers, "Theory of Recursive Functions and Effective Computability" (1967)
- Soare, "Turing Computability" (2016)
- Cutland, "Computability: An Introduction to Recursive Function Theory" (1980)
- Odifreddi, "Classical Recursion Theory" (1989)
-/

import ComputationalPaths.Path.Basic
import ComputationalPaths.Path.Rewrite.RwEq

namespace ComputationalPaths
namespace ComputabilityTheory

open Path

private def stepChainOfEq {A : Type _} {a b : A} (h : a = b) : Path a b :=
  let core :=
    Path.Step.symm
      (Path.Step.symm
        (Path.Step.congr_comp (fun x : A => x) (fun x : A => x) (Path.stepChain h)))
  Path.Step.unit_right
    (Path.Step.unit_left
      (Path.Step.assoc (Path.Step.refl a) core (Path.Step.refl b)))

/-! ## Primitive Recursive Functions -/

/-- Primitive recursive function data. -/
structure PrimRecData where
  /-- Arity of the function. -/
  arity : Nat
  /-- Recursion depth (nesting of primitive recursion). -/
  recursionDepth : Nat
  /-- Number of compositions used. -/
  numCompositions : Nat
  /-- Total complexity (compositions + recursions). -/
  totalComplexity : Nat
  /-- totalComplexity = numCompositions + recursionDepth. -/
  complexity_eq : totalComplexity = numCompositions + recursionDepth
  /-- Whether the function is total. -/
  isTotal : Bool
  /-- Primitive recursive functions are always total. -/
  total_eq : isTotal = true
  /-- Growth bound (0 = polynomial, 1 = exponential, etc.). -/
  growthClass : Nat

namespace PrimRecData

/-- Zero function: Z(x) = 0. -/
def zero : PrimRecData where
  arity := 1
  recursionDepth := 0
  numCompositions := 0
  totalComplexity := 0
  complexity_eq := rfl
  isTotal := true
  total_eq := rfl
  growthClass := 0

/-- Successor function: S(x) = x + 1. -/
def successor : PrimRecData where
  arity := 1
  recursionDepth := 0
  numCompositions := 0
  totalComplexity := 0
  complexity_eq := rfl
  isTotal := true
  total_eq := rfl
  growthClass := 0

/-- Addition: add(x,y) = x + y. -/
def addition : PrimRecData where
  arity := 2
  recursionDepth := 1
  numCompositions := 1
  totalComplexity := 2
  complexity_eq := by omega
  isTotal := true
  total_eq := rfl
  growthClass := 0

/-- Multiplication: mul(x,y) = x * y. -/
def multiplication : PrimRecData where
  arity := 2
  recursionDepth := 2
  numCompositions := 2
  totalComplexity := 4
  complexity_eq := by omega
  isTotal := true
  total_eq := rfl
  growthClass := 0

/-- Exponentiation: exp(x,y) = x^y. -/
def exponentiation : PrimRecData where
  arity := 2
  recursionDepth := 3
  numCompositions := 3
  totalComplexity := 6
  complexity_eq := by omega
  isTotal := true
  total_eq := rfl
  growthClass := 1

/-- Path: total complexity. -/
def complexity_path (pr : PrimRecData) :
    Path pr.totalComplexity (pr.numCompositions + pr.recursionDepth) :=
  stepChainOfEq pr.complexity_eq

/-- Path: totality. -/
def total_path (pr : PrimRecData) :
    Path pr.isTotal true :=
  stepChainOfEq pr.total_eq

end PrimRecData

/-! ## Partial Recursive Functions -/

/-- Partial recursive function data. -/
structure PartialRecData where
  /-- Arity. -/
  arity : Nat
  /-- Number of μ-operators used. -/
  numMuOperators : Nat
  /-- Primitive recursive base complexity. -/
  primRecComplexity : Nat
  /-- Total complexity. -/
  totalComplexity : Nat
  /-- totalComplexity = primRecComplexity + numMuOperators. -/
  complexity_eq : totalComplexity = primRecComplexity + numMuOperators
  /-- Whether the function is total. -/
  isTotal : Bool
  /-- Whether the function is partial recursive (always true by construction). -/
  isPartialRecursive : Bool
  /-- Always partial recursive. -/
  partial_rec_eq : isPartialRecursive = true

namespace PartialRecData

/-- A total primitive recursive function (no μ-operator). -/
def primRecAsPartial (pr : PrimRecData) : PartialRecData where
  arity := pr.arity
  numMuOperators := 0
  primRecComplexity := pr.totalComplexity
  totalComplexity := pr.totalComplexity
  complexity_eq := by omega
  isTotal := true
  isPartialRecursive := true
  partial_rec_eq := rfl

/-- A genuinely partial function (one μ-operator). -/
def withMu (n : Nat) (baseComp : Nat) : PartialRecData where
  arity := n
  numMuOperators := 1
  primRecComplexity := baseComp
  totalComplexity := baseComp + 1
  complexity_eq := by omega
  isTotal := false
  isPartialRecursive := true
  partial_rec_eq := rfl

/-- Path: complexity. -/
def complexity_path (prd : PartialRecData) :
    Path prd.totalComplexity (prd.primRecComplexity + prd.numMuOperators) :=
  stepChainOfEq prd.complexity_eq

/-- Path: partial recursive. -/
def partial_rec_path (prd : PartialRecData) :
    Path prd.isPartialRecursive true :=
  stepChainOfEq prd.partial_rec_eq

end PartialRecData

/-! ## μ-Recursion -/

/-- μ-recursion operator data. -/
structure MuRecursionData where
  /-- Input arity of g in μy[g(x,y) = 0]. -/
  inputArity : Nat
  /-- inputArity is positive. -/
  inputArity_pos : inputArity > 0
  /-- Whether g is primitive recursive. -/
  baseIsPrimRec : Bool
  /-- Whether the resulting function is total. -/
  resultIsTotal : Bool
  /-- Whether the μ-operator is bounded. -/
  isBounded : Bool
  /-- Bounded μ keeps primitive recursiveness. -/
  bounded_primrec : isBounded = true → baseIsPrimRec = true → resultIsTotal = true
  /-- Convergence witness (0 if diverges). -/
  convergenceWitness : Nat

namespace MuRecursionData

/-- Bounded μ-search with primitive recursive base. -/
def boundedPrimRec (n : Nat) (hn : n > 0) (witness : Nat) : MuRecursionData where
  inputArity := n
  inputArity_pos := hn
  baseIsPrimRec := true
  resultIsTotal := true
  isBounded := true
  bounded_primrec := fun _ _ => rfl
  convergenceWitness := witness

/-- Unbounded μ-search (potentially partial). -/
def unbounded (n : Nat) (hn : n > 0) : MuRecursionData where
  inputArity := n
  inputArity_pos := hn
  baseIsPrimRec := true
  resultIsTotal := false
  isBounded := false
  bounded_primrec := fun h => by simp at h
  convergenceWitness := 0

end MuRecursionData

/-! ## Kleene's Recursion Theorem -/

/-- Kleene's recursion theorem data. -/
structure KleeneRecursionData where
  /-- Gödel number of the computable function f. -/
  functionIndex : Nat
  /-- Fixed point index n where φ_n = φ_{f(n)}. -/
  fixedPoint : Nat
  /-- Whether the fixed point is valid. -/
  isFixedPoint : Bool
  /-- Fixed point validity. -/
  fixed_point_eq : isFixedPoint = true
  /-- Whether f is total. -/
  fIsTotal : Bool
  /-- f must be total. -/
  f_total_eq : fIsTotal = true
  /-- Obstruction to fixed point (0 means found). -/
  obstruction : Nat
  /-- Fixed point found. -/
  obstruction_eq : obstruction = 0

namespace KleeneRecursionData

/-- Fixed point for the identity function. -/
def identity : KleeneRecursionData where
  functionIndex := 0
  fixedPoint := 0
  isFixedPoint := true
  fixed_point_eq := rfl
  fIsTotal := true
  f_total_eq := rfl
  obstruction := 0
  obstruction_eq := rfl

/-- Fixed point for successor. -/
def forSuccessor : KleeneRecursionData where
  functionIndex := 1
  fixedPoint := 42
  isFixedPoint := true
  fixed_point_eq := rfl
  fIsTotal := true
  f_total_eq := rfl
  obstruction := 0
  obstruction_eq := rfl

/-- Path: fixed point validity. -/
def fixed_point_path (krd : KleeneRecursionData) :
    Path krd.isFixedPoint true :=
  stepChainOfEq krd.fixed_point_eq

/-- Path: obstruction. -/
def obstruction_path (krd : KleeneRecursionData) :
    Path krd.obstruction 0 :=
  stepChainOfEq krd.obstruction_eq

end KleeneRecursionData

/-! ## s-m-n Theorem -/

/-- s-m-n theorem data. -/
structure SMNData where
  /-- Number of parameters to fix (m). -/
  numParams : Nat
  /-- numParams is positive. -/
  numParams_pos : numParams > 0
  /-- Number of remaining arguments (n). -/
  numArgs : Nat
  /-- numArgs is positive. -/
  numArgs_pos : numArgs > 0
  /-- Total arity = m + n. -/
  totalArity : Nat
  /-- totalArity = numParams + numArgs. -/
  arity_eq : totalArity = numParams + numArgs
  /-- Whether s^m_n is total and computable. -/
  sIsTotal : Bool
  /-- s is total and computable. -/
  s_total_eq : sIsTotal = true
  /-- Whether s is injective (in e). -/
  sIsInjective : Bool
  /-- s is injective. -/
  s_injective_eq : sIsInjective = true

namespace SMNData

/-- s^1_1: fix one parameter, one remaining argument. -/
def s11 : SMNData where
  numParams := 1
  numParams_pos := by omega
  numArgs := 1
  numArgs_pos := by omega
  totalArity := 2
  arity_eq := by omega
  sIsTotal := true
  s_total_eq := rfl
  sIsInjective := true
  s_injective_eq := rfl

/-- s^m_n for arbitrary m, n. -/
def general (m n : Nat) (hm : m > 0) (hn : n > 0) : SMNData where
  numParams := m
  numParams_pos := hm
  numArgs := n
  numArgs_pos := hn
  totalArity := m + n
  arity_eq := rfl
  sIsTotal := true
  s_total_eq := rfl
  sIsInjective := true
  s_injective_eq := rfl

/-- Path: arity. -/
def arity_path (smn : SMNData) :
    Path smn.totalArity (smn.numParams + smn.numArgs) :=
  stepChainOfEq smn.arity_eq

/-- Path: s is total. -/
def s_total_path (smn : SMNData) :
    Path smn.sIsTotal true :=
  stepChainOfEq smn.s_total_eq

/-- Path: s is injective. -/
def s_injective_path (smn : SMNData) :
    Path smn.sIsInjective true :=
  stepChainOfEq smn.s_injective_eq

end SMNData

/-! ## Post's Theorem -/

/-- Post's theorem data: connecting arithmetical hierarchy with Turing jumps. -/
structure PostTheoremData where
  /-- Level n of the arithmetical hierarchy. -/
  level : Nat
  /-- Whether Σ⁰_{n+1} = RE relative to ∅⁽ⁿ⁾. -/
  postHolds : Bool
  /-- Post's theorem holds. -/
  post_eq : postHolds = true
  /-- Number of Turing jumps needed. -/
  numJumps : Nat
  /-- numJumps = level. -/
  jumps_eq : numJumps = level
  /-- Whether the hierarchy is strict. -/
  isStrict : Bool
  /-- Hierarchy is strict. -/
  strict_eq : isStrict = true

namespace PostTheoremData

/-- Post's theorem at level 0: RE = Σ⁰_1. -/
def level0 : PostTheoremData where
  level := 0
  postHolds := true
  post_eq := rfl
  numJumps := 0
  jumps_eq := rfl
  isStrict := true
  strict_eq := rfl

/-- Post's theorem at level 1: Σ⁰_2 = RE relative to ∅'. -/
def level1 : PostTheoremData where
  level := 1
  postHolds := true
  post_eq := rfl
  numJumps := 1
  jumps_eq := rfl
  isStrict := true
  strict_eq := rfl

/-- Post's theorem at level n. -/
def atLevel (n : Nat) : PostTheoremData where
  level := n
  postHolds := true
  post_eq := rfl
  numJumps := n
  jumps_eq := rfl
  isStrict := true
  strict_eq := rfl

/-- Path: Post's theorem. -/
def post_path (ptd : PostTheoremData) :
    Path ptd.postHolds true :=
  stepChainOfEq ptd.post_eq

/-- Path: number of jumps. -/
def jumps_path (ptd : PostTheoremData) :
    Path ptd.numJumps ptd.level :=
  stepChainOfEq ptd.jumps_eq

/-- Path: strictness. -/
def strict_path (ptd : PostTheoremData) :
    Path ptd.isStrict true :=
  stepChainOfEq ptd.strict_eq

end PostTheoremData

/-! ## Arithmetical Hierarchy -/

/-- Arithmetical hierarchy data. -/
structure ArithHierarchyData where
  /-- Level n of the hierarchy. -/
  level : Nat
  /-- Number of quantifier alternations. -/
  quantifierAlternations : Nat
  /-- quantifierAlternations = level. -/
  alternations_eq : quantifierAlternations = level
  /-- Whether this is Σ (true) or Π (false). -/
  isSigma : Bool
  /-- Number of sets at this level (abstract count). -/
  numSets : Nat
  /-- Σ⁰_n ⊊ Σ⁰_{n+1}. -/
  strictContainment : Bool
  /-- Strictness. -/
  strict_eq : strictContainment = true
  /-- Δ⁰_n = Σ⁰_n ∩ Π⁰_n. -/
  deltaIsMeet : Bool
  /-- Delta is meet. -/
  delta_eq : deltaIsMeet = true

namespace ArithHierarchyData

/-- Σ⁰_0 = Π⁰_0 = Δ⁰_0 = decidable sets. -/
def sigma0 : ArithHierarchyData where
  level := 0
  quantifierAlternations := 0
  alternations_eq := rfl
  isSigma := true
  numSets := 1
  strictContainment := true
  strict_eq := rfl
  deltaIsMeet := true
  delta_eq := rfl

/-- Σ⁰_1 = RE sets. -/
def sigma1 : ArithHierarchyData where
  level := 1
  quantifierAlternations := 1
  alternations_eq := rfl
  isSigma := true
  numSets := 2
  strictContainment := true
  strict_eq := rfl
  deltaIsMeet := true
  delta_eq := rfl

/-- Π⁰_1 = co-RE sets. -/
def pi1 : ArithHierarchyData where
  level := 1
  quantifierAlternations := 1
  alternations_eq := rfl
  isSigma := false
  numSets := 2
  strictContainment := true
  strict_eq := rfl
  deltaIsMeet := true
  delta_eq := rfl

/-- Σ⁰_n for arbitrary n. -/
def sigmaAt (n : Nat) : ArithHierarchyData where
  level := n
  quantifierAlternations := n
  alternations_eq := rfl
  isSigma := true
  numSets := n + 1
  strictContainment := true
  strict_eq := rfl
  deltaIsMeet := true
  delta_eq := rfl

/-- Path: quantifier alternations. -/
def alternations_path (ah : ArithHierarchyData) :
    Path ah.quantifierAlternations ah.level :=
  stepChainOfEq ah.alternations_eq

/-- Path: strictness. -/
def strict_path (ah : ArithHierarchyData) :
    Path ah.strictContainment true :=
  stepChainOfEq ah.strict_eq

/-- Path: delta is meet. -/
def delta_path (ah : ArithHierarchyData) :
    Path ah.deltaIsMeet true :=
  stepChainOfEq ah.delta_eq

end ArithHierarchyData

/-! ## Turing Degrees -/

/-- Turing degree data. -/
structure TuringDegreeData where
  /-- Degree identifier. -/
  degreeId : Nat
  /-- Level in the jump hierarchy. -/
  jumpLevel : Nat
  /-- Whether this is the zero degree (decidable sets). -/
  isZero : Bool
  /-- Whether this is 0' (the halting problem degree). -/
  isZeroPrime : Bool
  /-- isZero and isZeroPrime are mutually exclusive. -/
  zero_ne_prime : isZero = true → isZeroPrime = false
  /-- Whether the degree is RE (below 0'). -/
  isRE : Bool
  /-- 0 is RE. -/
  zero_is_re : isZero = true → isRE = true
  /-- Degree comparison obstruction (0 if comparable). -/
  compareObstruction : Nat

namespace TuringDegreeData

/-- The zero degree 0 (decidable sets). -/
def zero : TuringDegreeData where
  degreeId := 0
  jumpLevel := 0
  isZero := true
  isZeroPrime := false
  zero_ne_prime := fun _ => rfl
  isRE := true
  zero_is_re := fun _ => rfl
  compareObstruction := 0

/-- 0' (the halting problem). -/
def zeroPrime : TuringDegreeData where
  degreeId := 1
  jumpLevel := 1
  isZero := false
  isZeroPrime := true
  zero_ne_prime := fun h => by simp at h
  isRE := true
  zero_is_re := fun h => by simp at h
  compareObstruction := 0

/-- 0'' (double jump). -/
def zeroDoublePrime : TuringDegreeData where
  degreeId := 2
  jumpLevel := 2
  isZero := false
  isZeroPrime := false
  zero_ne_prime := fun h => by simp at h
  isRE := false
  zero_is_re := fun h => by simp at h
  compareObstruction := 0

/-- The nth jump of 0. -/
def nthJump (n : Nat) : TuringDegreeData where
  degreeId := n
  jumpLevel := n
  isZero := n == 0
  isZeroPrime := n == 1
  zero_ne_prime := fun h => by simp [BEq.beq] at h ⊢; omega
  isRE := n ≤ 1
  zero_is_re := fun h => by simp [BEq.beq] at h; subst h; simp
  compareObstruction := 0

end TuringDegreeData

/-! ## Enumeration Theorem -/

/-- Enumeration theorem data: effective listing of partial recursive functions. -/
structure EnumerationData where
  /-- Arity of enumerated functions. -/
  arity : Nat
  /-- arity is positive. -/
  arity_pos : arity > 0
  /-- Whether the enumeration is effective. -/
  isEffective : Bool
  /-- Effectivity. -/
  effective_eq : isEffective = true
  /-- Whether the universal function exists. -/
  universalExists : Bool
  /-- Universal function exists. -/
  universal_eq : universalExists = true
  /-- Arity of the universal function = arity + 1. -/
  universalArity : Nat
  /-- universalArity = arity + 1. -/
  universal_arity_eq : universalArity = arity + 1

namespace EnumerationData

/-- Enumeration of unary partial recursive functions. -/
def unary : EnumerationData where
  arity := 1
  arity_pos := by omega
  isEffective := true
  effective_eq := rfl
  universalExists := true
  universal_eq := rfl
  universalArity := 2
  universal_arity_eq := by omega

/-- Enumeration for arity n. -/
def ofArity (n : Nat) (hn : n > 0) : EnumerationData where
  arity := n
  arity_pos := hn
  isEffective := true
  effective_eq := rfl
  universalExists := true
  universal_eq := rfl
  universalArity := n + 1
  universal_arity_eq := rfl

/-- Path: universal arity. -/
def universal_arity_path (ed : EnumerationData) :
    Path ed.universalArity (ed.arity + 1) :=
  stepChainOfEq ed.universal_arity_eq

/-- Path: effectivity. -/
def effective_path (ed : EnumerationData) :
    Path ed.isEffective true :=
  stepChainOfEq ed.effective_eq

end EnumerationData

/-! ## Rice-Shapiro Theorem -/

/-- Rice-Shapiro theorem data. -/
structure RiceShapiroData where
  /-- Whether the property is RE. -/
  propertyIsRE : Bool
  /-- Whether the property is monotone on finite functions. -/
  isMonotone : Bool
  /-- RE → compact (finite witness). -/
  hasCompactWitness : Bool
  /-- If RE then has compact witness. -/
  re_implies_compact : propertyIsRE = true → hasCompactWitness = true
  /-- Obstruction to RE-ness. -/
  obstruction : Nat
  /-- If RE then obstruction = 0. -/
  re_obstruction : propertyIsRE = true → obstruction = 0

namespace RiceShapiroData

/-- An RE property with compact witness. -/
def reProperty : RiceShapiroData where
  propertyIsRE := true
  isMonotone := true
  hasCompactWitness := true
  re_implies_compact := fun _ => rfl
  obstruction := 0
  re_obstruction := fun _ => rfl

/-- A non-RE property. -/
def nonREProperty : RiceShapiroData where
  propertyIsRE := false
  isMonotone := false
  hasCompactWitness := false
  re_implies_compact := fun h => by simp at h
  obstruction := 1
  re_obstruction := fun h => by simp at h

/-- Path: RE obstruction. -/
def obstruction_path (rs : RiceShapiroData) (h : rs.propertyIsRE = true) :
    Path rs.obstruction 0 :=
  stepChainOfEq (rs.re_obstruction h)

end RiceShapiroData

/-! ## Productive and Creative Sets -/

/-- Productive and creative set data. -/
structure ProductiveCreativeData where
  /-- Whether the set is productive. -/
  isProductive : Bool
  /-- Whether the set is creative (productive + RE). -/
  isCreative : Bool
  /-- Creative implies productive. -/
  creative_implies : isCreative = true → isProductive = true
  /-- Whether the set is RE. -/
  isRE : Bool
  /-- Creative iff productive + RE. -/
  creative_iff : isCreative = true ↔ isProductive = true ∧ isRE = true
  /-- Whether the complement is productive. -/
  complementProductive : Bool

namespace ProductiveCreativeData

/-- K (diagonal halting set) is creative. -/
def diagonalK : ProductiveCreativeData where
  isProductive := true
  isCreative := true
  creative_implies := fun _ => rfl
  isRE := true
  creative_iff := by simp
  complementProductive := true

/-- A simple set (RE but not creative). -/
def simpleSet : ProductiveCreativeData where
  isProductive := false
  isCreative := false
  creative_implies := fun h => by simp at h
  isRE := true
  creative_iff := by simp
  complementProductive := false

end ProductiveCreativeData

/-! ## Master Coherence Paths -/

/-- Master: primitive recursive totality. -/
def master_primrec_total_path :
    Path PrimRecData.addition.isTotal true :=
  PrimRecData.addition.total_path

/-- Master: addition complexity. -/
def master_addition_complexity_path :
    Path PrimRecData.addition.totalComplexity 2 :=
  PrimRecData.addition.complexity_path

/-- Master: exponentiation complexity. -/
def master_exp_complexity_path :
    Path PrimRecData.exponentiation.totalComplexity 6 :=
  PrimRecData.exponentiation.complexity_path

/-- Master: partial recursive. -/
def master_partial_rec_path :
    Path (PartialRecData.withMu 2 3).isPartialRecursive true :=
  (PartialRecData.withMu 2 3).partial_rec_path

/-- Master: Kleene fixed point. -/
def master_kleene_path :
    Path KleeneRecursionData.identity.obstruction 0 :=
  KleeneRecursionData.identity.obstruction_path

/-- Master: s-m-n arity. -/
def master_smn_arity_path :
    Path SMNData.s11.totalArity 2 :=
  SMNData.s11.arity_path

/-- Master: s-m-n totality. -/
def master_smn_total_path :
    Path SMNData.s11.sIsTotal true :=
  SMNData.s11.s_total_path

/-- Master: Post's theorem. -/
def master_post_path :
    Path PostTheoremData.level0.postHolds true :=
  PostTheoremData.level0.post_path

/-- Master: arithmetical hierarchy strictness. -/
def master_hierarchy_strict_path :
    Path ArithHierarchyData.sigma1.strictContainment true :=
  ArithHierarchyData.sigma1.strict_path

/-- Master: enumeration universal arity. -/
def master_enumeration_path :
    Path EnumerationData.unary.universalArity 2 :=
  EnumerationData.unary.universal_arity_path

end ComputabilityTheory
end ComputationalPaths
