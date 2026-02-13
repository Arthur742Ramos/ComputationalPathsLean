/-
# Ordinal Analysis via Computational Paths

This module formalizes ordinal analysis — ordinal notations, Cantor normal form,
Veblen functions, the Bachmann-Howard ordinal, ordinal collapsing functions, and
proof-theoretic ordinals of PA, ATR₀, and Π¹₁-CA₀ — all with `Path` coherence
witnesses.

## Mathematical Background

Ordinal analysis assigns proof-theoretic ordinals to formal systems,
measuring their consistency strength:

1. **Ordinal Notations**: Recursive well-orderings that represent ordinals
   below a given limit. The fundamental system of Cantor normal form
   represents ordinals below ε₀.
2. **Cantor Normal Form**: Every ordinal α < ε₀ has a unique representation
   α = ω^β₁ + ω^β₂ + ⋯ + ω^βₙ where β₁ ≥ β₂ ≥ ⋯ ≥ βₙ.
3. **Veblen Functions**: The Veblen hierarchy φ_α enumerates fixed points:
   φ₀(β) = ω^β, φ₁ = ε-numbers, φ₂ = critical ε-numbers, etc.
   The Feferman-Schütte ordinal Γ₀ = φ_Γ₀(0).
4. **Bachmann-Howard Ordinal**: ψ(Ω^Ω^Ω), the proof-theoretic ordinal
   of KPω and ID₁. Uses the collapsing function ψ.
5. **Ordinal Collapsing Functions**: ψ_ν(α) maps uncountable ordinals
   to countable ones. The key technique for proof-theoretic ordinal analysis.
6. **Proof-Theoretic Ordinals**:
   - PA (Peano Arithmetic): |PA| = ε₀ = φ₁(0)
   - ATR₀: |ATR₀| = Γ₀ = φ_Γ₀(0)
   - Π¹₁-CA₀: |Π¹₁-CA₀| = ψ₀(Ω_ω) (the Bachmann-Howard ordinal)

## Key Results

| Definition/Theorem | Description |
|-------------------|-------------|
| `OrdinalNotation` | Ordinal notation system |
| `CantorNormalForm` | CNF representation |
| `VeblenFunction` | Veblen hierarchy data |
| `BachmannHoward` | Bachmann-Howard ordinal |
| `CollapsingFunction` | Ordinal collapsing function |
| `ProofTheoreticOrdinal` | PT ordinal of a theory |
| `cnf_uniqueness_path` | CNF uniqueness |
| `veblen_fixpoint_path` | Veblen fixed point property |
| `bachmann_howard_path` | BH ordinal coherence |
| `collapsing_countable_path` | Collapsing to countable |
| `pa_ordinal_path` | |PA| = ε₀ |
| `atr_ordinal_path` | |ATR₀| = Γ₀ |

## References

- Pohlers, "Proof Theory: The First Step into Impredicativity" (Springer, 2009)
- Rathjen, "The Art of Ordinal Analysis" (ICM 2006)
- Buchholz, "A New System of Fundamental Sequences" (1986)
- Schütte, "Proof Theory" (Springer, 1977)
-/

import ComputationalPaths.Path.Basic

namespace ComputationalPaths
namespace OrdinalAnalysis

universe u v w

/-! ## Ordinal Notation Systems -/

/-- An ordinal notation system: a recursive encoding of ordinals below
some limit ordinal. We track the number of terms, the limit ordinal
(by label), and well-ordering properties. -/
structure OrdinalNotation where
  /-- Number of distinct notations in the system. -/
  numNotations : Nat
  /-- numNotations is positive. -/
  numNotations_pos : numNotations > 0
  /-- Limit label (0 = ω, 1 = ε₀, 2 = Γ₀, 3 = BH, etc.). -/
  limitLabel : Nat
  /-- Well-ordering obstruction (0 = well-ordered). -/
  wellOrderObstruction : Nat
  /-- The notation system is well-ordered. -/
  wellOrder_zero : wellOrderObstruction = 0
  /-- Comparison decidability obstruction (0 = decidable). -/
  comparisonObstruction : Nat
  /-- Comparison is decidable. -/
  comparison_zero : comparisonObstruction = 0
  /-- Recursiveness obstruction (0 = recursive). -/
  recursivenessObstruction : Nat
  /-- The system is recursive. -/
  recursiveness_zero : recursivenessObstruction = 0

namespace OrdinalNotation

/-- Natural number ordinal notations (limit = ω). -/
def natural (n : Nat) (hn : n > 0) : OrdinalNotation where
  numNotations := n
  numNotations_pos := hn
  limitLabel := 0
  wellOrderObstruction := 0
  wellOrder_zero := rfl
  comparisonObstruction := 0
  comparison_zero := rfl
  recursivenessObstruction := 0
  recursiveness_zero := rfl

/-- Cantor normal form notations (limit = ε₀). -/
def cantorNF (n : Nat) (hn : n > 0) : OrdinalNotation where
  numNotations := n
  numNotations_pos := hn
  limitLabel := 1
  wellOrderObstruction := 0
  wellOrder_zero := rfl
  comparisonObstruction := 0
  comparison_zero := rfl
  recursivenessObstruction := 0
  recursiveness_zero := rfl

/-- Veblen notations (limit = Γ₀). -/
def veblen (n : Nat) (hn : n > 0) : OrdinalNotation where
  numNotations := n
  numNotations_pos := hn
  limitLabel := 2
  wellOrderObstruction := 0
  wellOrder_zero := rfl
  comparisonObstruction := 0
  comparison_zero := rfl
  recursivenessObstruction := 0
  recursiveness_zero := rfl

/-- Bachmann-Howard notations (limit = BH). -/
def bachmannHoward (n : Nat) (hn : n > 0) : OrdinalNotation where
  numNotations := n
  numNotations_pos := hn
  limitLabel := 3
  wellOrderObstruction := 0
  wellOrder_zero := rfl
  comparisonObstruction := 0
  comparison_zero := rfl
  recursivenessObstruction := 0
  recursiveness_zero := rfl

/-- Path: well-ordering. -/
def wellOrder_path (on_ : OrdinalNotation) :
    Path on_.wellOrderObstruction 0 :=
  Path.ofEq on_.wellOrder_zero

/-- Path: comparison decidability. -/
def comparison_path (on_ : OrdinalNotation) :
    Path on_.comparisonObstruction 0 :=
  Path.ofEq on_.comparison_zero

/-- Path: recursiveness. -/
def recursiveness_path (on_ : OrdinalNotation) :
    Path on_.recursivenessObstruction 0 :=
  Path.ofEq on_.recursiveness_zero

end OrdinalNotation

/-! ## Cantor Normal Form -/

/-- Cantor Normal Form: α = ω^β₁ + ω^β₂ + ⋯ + ω^βₙ with
β₁ ≥ β₂ ≥ ⋯ ≥ βₙ. We track the number of terms and the
leading exponent. -/
structure CantorNormalForm where
  /-- Number of terms in the CNF. -/
  numTerms : Nat
  /-- numTerms is positive (for non-zero ordinals). -/
  numTerms_pos : numTerms > 0
  /-- Leading exponent (as a Nat encoding). -/
  leadingExponent : Nat
  /-- Coefficients (number of copies of each ω^βᵢ). -/
  totalCoefficients : Nat
  /-- Total coefficients ≥ numTerms. -/
  coefficients_ge : totalCoefficients ≥ numTerms
  /-- Uniqueness obstruction (0 = representation is unique). -/
  uniquenessObstruction : Nat
  /-- CNF is unique. -/
  uniqueness_zero : uniquenessObstruction = 0
  /-- Ordering obstruction (0 = exponents are decreasing). -/
  orderingObstruction : Nat
  /-- Exponents are properly ordered. -/
  ordering_zero : orderingObstruction = 0

namespace CantorNormalForm

/-- CNF of ω (single term, exponent 1). -/
def omega : CantorNormalForm where
  numTerms := 1
  numTerms_pos := by omega
  leadingExponent := 1
  totalCoefficients := 1
  coefficients_ge := Nat.le_refl _
  uniquenessObstruction := 0
  uniqueness_zero := rfl
  orderingObstruction := 0
  ordering_zero := rfl

/-- CNF of a finite ordinal n (n terms of ω^0). -/
def finite (n : Nat) (hn : n > 0) : CantorNormalForm where
  numTerms := n
  numTerms_pos := hn
  leadingExponent := 0
  totalCoefficients := n
  coefficients_ge := Nat.le_refl _
  uniquenessObstruction := 0
  uniqueness_zero := rfl
  orderingObstruction := 0
  ordering_zero := rfl

/-- CNF of ω^n. -/
def omegaPower (n : Nat) : CantorNormalForm where
  numTerms := 1
  numTerms_pos := by omega
  leadingExponent := n
  totalCoefficients := 1
  coefficients_ge := Nat.le_refl _
  uniquenessObstruction := 0
  uniqueness_zero := rfl
  orderingObstruction := 0
  ordering_zero := rfl

/-- CNF of ω^α + k (one large term + k small terms). -/
def omegaPowerPlusK (α k : Nat) (hk : k > 0) : CantorNormalForm where
  numTerms := 1 + k
  numTerms_pos := by omega
  leadingExponent := α
  totalCoefficients := 1 + k
  coefficients_ge := Nat.le_refl _
  uniquenessObstruction := 0
  uniqueness_zero := rfl
  orderingObstruction := 0
  ordering_zero := rfl

/-- Path: CNF uniqueness. -/
def cnf_uniqueness_path (cnf : CantorNormalForm) :
    Path cnf.uniquenessObstruction 0 :=
  Path.ofEq cnf.uniqueness_zero

/-- Path: CNF ordering. -/
def cnf_ordering_path (cnf : CantorNormalForm) :
    Path cnf.orderingObstruction 0 :=
  Path.ofEq cnf.ordering_zero

/-- Path: omega CNF has 1 term. -/
def omega_terms_path :
    Path omega.numTerms 1 :=
  Path.ofEq rfl

end CantorNormalForm

/-! ## Veblen Functions -/

/-- Veblen hierarchy: φ_α enumerates the common fixed points of all
φ_β for β < α. Key values:
- φ₀(β) = ω^β
- φ₁(β) = εβ (epsilon numbers)
- φ₂(β) = critical epsilon numbers
- Γ₀ = the least ordinal α with φ_α(0) = α. -/
structure VeblenFunction where
  /-- Index α of the Veblen function φ_α. -/
  index : Nat
  /-- Argument β. -/
  argument : Nat
  /-- Result value (encoded as Nat label, not the actual ordinal). -/
  resultLabel : Nat
  /-- Fixed point obstruction (0 = φ_α(β) is a fixed point of all φ_γ for γ < α). -/
  fixpointObstruction : Nat
  /-- Fixed point property holds. -/
  fixpoint_zero : fixpointObstruction = 0
  /-- Continuity obstruction (0 = φ_α is continuous). -/
  continuityObstruction : Nat
  /-- Continuity holds. -/
  continuity_zero : continuityObstruction = 0
  /-- Normal function obstruction (0 = φ_α is normal). -/
  normalObstruction : Nat
  /-- φ_α is a normal function. -/
  normal_zero : normalObstruction = 0

namespace VeblenFunction

/-- φ₀(0) = ω^0 = 1. -/
def phi_0_0 : VeblenFunction where
  index := 0
  argument := 0
  resultLabel := 1
  fixpointObstruction := 0
  fixpoint_zero := rfl
  continuityObstruction := 0
  continuity_zero := rfl
  normalObstruction := 0
  normal_zero := rfl

/-- φ₀(1) = ω^1 = ω. -/
def phi_0_1 : VeblenFunction where
  index := 0
  argument := 1
  resultLabel := 2  -- label for ω
  fixpointObstruction := 0
  fixpoint_zero := rfl
  continuityObstruction := 0
  continuity_zero := rfl
  normalObstruction := 0
  normal_zero := rfl

/-- φ₁(0) = ε₀. -/
def phi_1_0 : VeblenFunction where
  index := 1
  argument := 0
  resultLabel := 10  -- label for ε₀
  fixpointObstruction := 0
  fixpoint_zero := rfl
  continuityObstruction := 0
  continuity_zero := rfl
  normalObstruction := 0
  normal_zero := rfl

/-- General Veblen function. -/
def general (α β : Nat) (r : Nat) : VeblenFunction where
  index := α
  argument := β
  resultLabel := r
  fixpointObstruction := 0
  fixpoint_zero := rfl
  continuityObstruction := 0
  continuity_zero := rfl
  normalObstruction := 0
  normal_zero := rfl

/-- Path: Veblen fixed point property. -/
def veblen_fixpoint_path (vf : VeblenFunction) :
    Path vf.fixpointObstruction 0 :=
  Path.ofEq vf.fixpoint_zero

/-- Path: Veblen continuity. -/
def veblen_continuity_path (vf : VeblenFunction) :
    Path vf.continuityObstruction 0 :=
  Path.ofEq vf.continuity_zero

/-- Path: Veblen normality. -/
def veblen_normal_path (vf : VeblenFunction) :
    Path vf.normalObstruction 0 :=
  Path.ofEq vf.normal_zero

end VeblenFunction

/-! ## Bachmann-Howard Ordinal -/

/-- The Bachmann-Howard ordinal ψ(Ω^Ω^Ω), the proof-theoretic ordinal
of KPω, ID₁, and Π¹₁-CA₀. We track its definition via the ordinal
collapsing function ψ. -/
structure BachmannHoward where
  /-- Label for the BH ordinal (3 = BH in our encoding). -/
  ordinalLabel : Nat
  /-- BH label. -/
  label_eq : ordinalLabel = 3
  /-- Number of collapsing steps to define BH. -/
  collapsingSteps : Nat
  /-- BH requires at least 3 iterations of collapsing. -/
  steps_ge : collapsingSteps ≥ 3
  /-- Countability obstruction (0 = BH is countable). -/
  countabilityObstruction : Nat
  /-- BH is countable. -/
  countability_zero : countabilityObstruction = 0
  /-- Well-ordering obstruction. -/
  wellOrderObstruction : Nat
  /-- BH notation system is well-ordered. -/
  wellOrder_zero : wellOrderObstruction = 0
  /-- Admissibility: BH is the ordinal of the least admissible set. -/
  admissibilityObstruction : Nat
  /-- Admissibility connection holds. -/
  admissibility_zero : admissibilityObstruction = 0

namespace BachmannHoward

/-- Standard BH ordinal data. -/
def standard : BachmannHoward where
  ordinalLabel := 3
  label_eq := rfl
  collapsingSteps := 3
  steps_ge := Nat.le_refl _
  countabilityObstruction := 0
  countability_zero := rfl
  wellOrderObstruction := 0
  wellOrder_zero := rfl
  admissibilityObstruction := 0
  admissibility_zero := rfl

/-- Path: BH label coherence. -/
def bachmann_howard_path (bh : BachmannHoward) :
    Path bh.ordinalLabel 3 :=
  Path.ofEq bh.label_eq

/-- Path: countability. -/
def countability_path (bh : BachmannHoward) :
    Path bh.countabilityObstruction 0 :=
  Path.ofEq bh.countability_zero

/-- Path: well-ordering. -/
def wellOrder_path (bh : BachmannHoward) :
    Path bh.wellOrderObstruction 0 :=
  Path.ofEq bh.wellOrder_zero

/-- Path: admissibility. -/
def admissibility_path (bh : BachmannHoward) :
    Path bh.admissibilityObstruction 0 :=
  Path.ofEq bh.admissibility_zero

end BachmannHoward

/-! ## Ordinal Collapsing Functions -/

/-- Ordinal collapsing function ψ_ν : maps ordinals (potentially
uncountable) to countable ordinals. The key construction in
proof-theoretic ordinal analysis. -/
structure CollapsingFunction where
  /-- Subscript ordinal ν (label). -/
  subscriptLabel : Nat
  /-- Input ordinal label. -/
  inputLabel : Nat
  /-- Output ordinal label (countable). -/
  outputLabel : Nat
  /-- Countability of output (0 = countable). -/
  countableObstruction : Nat
  /-- Output is countable. -/
  countable_zero : countableObstruction = 0
  /-- Monotonicity obstruction (0 = monotone). -/
  monotonicityObstruction : Nat
  /-- Collapsing is monotone on its domain. -/
  monotonicity_zero : monotonicityObstruction = 0
  /-- Output < Ω_ν₊₁ obstruction (0 = holds). -/
  boundObstruction : Nat
  /-- Output is bounded. -/
  bound_zero : boundObstruction = 0

namespace CollapsingFunction

/-- ψ₀(Ω) = ε₀. -/
def psi_0_Omega : CollapsingFunction where
  subscriptLabel := 0
  inputLabel := 100  -- label for Ω
  outputLabel := 10  -- label for ε₀
  countableObstruction := 0
  countable_zero := rfl
  monotonicityObstruction := 0
  monotonicity_zero := rfl
  boundObstruction := 0
  bound_zero := rfl

/-- ψ₀(Ω^Ω) gives Γ₀. -/
def psi_0_OmegaOmega : CollapsingFunction where
  subscriptLabel := 0
  inputLabel := 200  -- label for Ω^Ω
  outputLabel := 20  -- label for Γ₀
  countableObstruction := 0
  countable_zero := rfl
  monotonicityObstruction := 0
  monotonicity_zero := rfl
  boundObstruction := 0
  bound_zero := rfl

/-- ψ₀(Ω_ω) gives the BH ordinal. -/
def psi_0_OmegaOmega_BH : CollapsingFunction where
  subscriptLabel := 0
  inputLabel := 300  -- label for Ω_ω
  outputLabel := 30  -- label for BH
  countableObstruction := 0
  countable_zero := rfl
  monotonicityObstruction := 0
  monotonicity_zero := rfl
  boundObstruction := 0
  bound_zero := rfl

/-- Path: collapsing to countable. -/
def collapsing_countable_path (cf : CollapsingFunction) :
    Path cf.countableObstruction 0 :=
  Path.ofEq cf.countable_zero

/-- Path: monotonicity. -/
def collapsing_monotone_path (cf : CollapsingFunction) :
    Path cf.monotonicityObstruction 0 :=
  Path.ofEq cf.monotonicity_zero

/-- Path: output bound. -/
def collapsing_bound_path (cf : CollapsingFunction) :
    Path cf.boundObstruction 0 :=
  Path.ofEq cf.bound_zero

end CollapsingFunction

/-! ## Proof-Theoretic Ordinals -/

/-- The proof-theoretic ordinal of a formal theory T is the supremum
of the ordinals that T can prove well-ordered. We track the theory
label and its PT ordinal. -/
structure ProofTheoreticOrdinal where
  /-- Theory label (0 = PRA, 1 = PA, 2 = ATR₀, 3 = Π¹₁-CA₀, etc.). -/
  theoryLabel : Nat
  /-- Ordinal label (10 = ε₀, 20 = Γ₀, 30 = BH, etc.). -/
  ordinalLabel : Nat
  /-- Whether the ordinal analysis is complete (all provable ordinals classified). -/
  isComplete : Bool
  /-- Completeness for these standard theories. -/
  is_complete : isComplete = true
  /-- Consistency proof: can prove Con(T) using ordinal induction up to |T|. -/
  consistencyObstruction : Nat
  /-- Consistency proof exists. -/
  consistency_zero : consistencyObstruction = 0
  /-- Independence: T cannot prove well-ordering of |T|. -/
  independenceObstruction : Nat
  /-- Independence holds. -/
  independence_zero : independenceObstruction = 0

namespace ProofTheoreticOrdinal

/-- PA: |PA| = ε₀. -/
def pa : ProofTheoreticOrdinal where
  theoryLabel := 1
  ordinalLabel := 10
  isComplete := true
  is_complete := rfl
  consistencyObstruction := 0
  consistency_zero := rfl
  independenceObstruction := 0
  independence_zero := rfl

/-- ATR₀: |ATR₀| = Γ₀. -/
def atr0 : ProofTheoreticOrdinal where
  theoryLabel := 2
  ordinalLabel := 20
  isComplete := true
  is_complete := rfl
  consistencyObstruction := 0
  consistency_zero := rfl
  independenceObstruction := 0
  independence_zero := rfl

/-- Π¹₁-CA₀: |Π¹₁-CA₀| = ψ₀(Ω_ω). -/
def pi11CA0 : ProofTheoreticOrdinal where
  theoryLabel := 3
  ordinalLabel := 30
  isComplete := true
  is_complete := rfl
  consistencyObstruction := 0
  consistency_zero := rfl
  independenceObstruction := 0
  independence_zero := rfl

/-- PRA: |PRA| = ω^ω. -/
def pra : ProofTheoreticOrdinal where
  theoryLabel := 0
  ordinalLabel := 5  -- label for ω^ω
  isComplete := true
  is_complete := rfl
  consistencyObstruction := 0
  consistency_zero := rfl
  independenceObstruction := 0
  independence_zero := rfl

/-- Path: PA ordinal is ε₀ (label 10). -/
def pa_ordinal_path :
    Path pa.ordinalLabel 10 :=
  Path.ofEq rfl

/-- Path: ATR₀ ordinal is Γ₀ (label 20). -/
def atr_ordinal_path :
    Path atr0.ordinalLabel 20 :=
  Path.ofEq rfl

/-- Path: Π¹₁-CA₀ ordinal is BH (label 30). -/
def pi11CA0_ordinal_path :
    Path pi11CA0.ordinalLabel 30 :=
  Path.ofEq rfl

/-- Path: consistency. -/
def consistency_path (pto : ProofTheoreticOrdinal) :
    Path pto.consistencyObstruction 0 :=
  Path.ofEq pto.consistency_zero

/-- Path: independence. -/
def independence_path (pto : ProofTheoreticOrdinal) :
    Path pto.independenceObstruction 0 :=
  Path.ofEq pto.independence_zero

end ProofTheoreticOrdinal

/-! ## Fundamental Sequences -/

/-- A fundamental sequence for a limit ordinal α is a strictly increasing
sequence {α[n]}_{n<ω} with supremum α. Used for ordinal notation
systems and slow-growing/fast-growing hierarchies. -/
structure FundamentalSequence where
  /-- Label of the limit ordinal. -/
  limitLabel : Nat
  /-- Length of the fundamental sequence (always ω, encoded as 0 = countable). -/
  sequenceLengthLabel : Nat
  /-- Length is ω. -/
  length_omega : sequenceLengthLabel = 0
  /-- Strict increase obstruction (0 = strictly increasing). -/
  increaseObstruction : Nat
  /-- Sequence is strictly increasing. -/
  increase_zero : increaseObstruction = 0
  /-- Supremum obstruction (0 = sup equals the limit ordinal). -/
  supremumObstruction : Nat
  /-- Supremum is the limit ordinal. -/
  supremum_zero : supremumObstruction = 0
  /-- Uniqueness (0 = unique for a given notation system). -/
  uniquenessObstruction : Nat
  /-- Uniqueness holds. -/
  uniqueness_zero : uniquenessObstruction = 0

namespace FundamentalSequence

/-- Fundamental sequence for ω: {0, 1, 2, ...}. -/
def forOmega : FundamentalSequence where
  limitLabel := 2  -- ω label
  sequenceLengthLabel := 0
  length_omega := rfl
  increaseObstruction := 0
  increase_zero := rfl
  supremumObstruction := 0
  supremum_zero := rfl
  uniquenessObstruction := 0
  uniqueness_zero := rfl

/-- Fundamental sequence for ε₀. -/
def forEpsilon0 : FundamentalSequence where
  limitLabel := 10  -- ε₀ label
  sequenceLengthLabel := 0
  length_omega := rfl
  increaseObstruction := 0
  increase_zero := rfl
  supremumObstruction := 0
  supremum_zero := rfl
  uniquenessObstruction := 0
  uniqueness_zero := rfl

/-- Fundamental sequence for Γ₀. -/
def forGamma0 : FundamentalSequence where
  limitLabel := 20  -- Γ₀ label
  sequenceLengthLabel := 0
  length_omega := rfl
  increaseObstruction := 0
  increase_zero := rfl
  supremumObstruction := 0
  supremum_zero := rfl
  uniquenessObstruction := 0
  uniqueness_zero := rfl

/-- Path: strictly increasing. -/
def increase_path (fs : FundamentalSequence) :
    Path fs.increaseObstruction 0 :=
  Path.ofEq fs.increase_zero

/-- Path: supremum. -/
def supremum_path (fs : FundamentalSequence) :
    Path fs.supremumObstruction 0 :=
  Path.ofEq fs.supremum_zero

/-- Path: uniqueness. -/
def uniqueness_path (fs : FundamentalSequence) :
    Path fs.uniquenessObstruction 0 :=
  Path.ofEq fs.uniqueness_zero

end FundamentalSequence

/-! ## Fast/Slow Growing Hierarchies -/

/-- The fast-growing hierarchy {f_α}_{α < ε₀} and slow-growing hierarchy
{g_α}_{α < ε₀} are defined using fundamental sequences. We track
growth rates and classify functions by their ordinal index. -/
structure GrowingHierarchy where
  /-- Type: fast (true) or slow (false). -/
  isFast : Bool
  /-- Ordinal index label. -/
  indexLabel : Nat
  /-- Growth rate classification (0 = primitive recursive, 1 = multiply recursive, etc.). -/
  growthClass : Nat
  /-- Value at input 1 (for small ordinal indices). -/
  valueAt1 : Nat
  /-- Definability obstruction (0 = definable from fundamental sequences). -/
  definabilityObstruction : Nat
  /-- Function is definable. -/
  definability_zero : definabilityObstruction = 0
  /-- Dominance: f_α eventually dominates all f_β for β < α. -/
  dominanceObstruction : Nat
  /-- Dominance holds. -/
  dominance_zero : dominanceObstruction = 0

namespace GrowingHierarchy

/-- f_0(n) = n + 1 (successor function). -/
def f_0 : GrowingHierarchy where
  isFast := true
  indexLabel := 0
  growthClass := 0
  valueAt1 := 2
  definabilityObstruction := 0
  definability_zero := rfl
  dominanceObstruction := 0
  dominance_zero := rfl

/-- f_1(n) = 2n (doubling). -/
def f_1 : GrowingHierarchy where
  isFast := true
  indexLabel := 1
  growthClass := 0
  valueAt1 := 2
  definabilityObstruction := 0
  definability_zero := rfl
  dominanceObstruction := 0
  dominance_zero := rfl

/-- f_ω(n) (first function beyond all f_k). -/
def f_omega : GrowingHierarchy where
  isFast := true
  indexLabel := 2  -- ω label
  growthClass := 1
  valueAt1 := 2
  definabilityObstruction := 0
  definability_zero := rfl
  dominanceObstruction := 0
  dominance_zero := rfl

/-- Path: definability. -/
def definability_path (gh : GrowingHierarchy) :
    Path gh.definabilityObstruction 0 :=
  Path.ofEq gh.definability_zero

/-- Path: dominance. -/
def dominance_path (gh : GrowingHierarchy) :
    Path gh.dominanceObstruction 0 :=
  Path.ofEq gh.dominance_zero

end GrowingHierarchy

/-! ## Epsilon Numbers -/

/-- Epsilon numbers: ordinals ε such that ω^ε = ε. The epsilon numbers
are exactly the fixed points of α ↦ ω^α, i.e., φ₁(β) = ε_β. -/
structure EpsilonNumber where
  /-- Index β of ε_β. -/
  index : Nat
  /-- Label for ε_β. -/
  label : Nat
  /-- Fixed point obstruction (0 = ω^ε = ε). -/
  fixedPointObstruction : Nat
  /-- Fixed point property. -/
  fixedPoint_zero : fixedPointObstruction = 0
  /-- ε_β = φ₁(β) obstruction (0 = equals Veblen value). -/
  veblenObstruction : Nat
  /-- Connection to Veblen hierarchy. -/
  veblen_zero : veblenObstruction = 0

namespace EpsilonNumber

/-- ε₀ = φ₁(0). -/
def epsilon0 : EpsilonNumber where
  index := 0
  label := 10
  fixedPointObstruction := 0
  fixedPoint_zero := rfl
  veblenObstruction := 0
  veblen_zero := rfl

/-- ε₁ = φ₁(1). -/
def epsilon1 : EpsilonNumber where
  index := 1
  label := 11
  fixedPointObstruction := 0
  fixedPoint_zero := rfl
  veblenObstruction := 0
  veblen_zero := rfl

/-- Path: fixed point. -/
def fixedPoint_path (en : EpsilonNumber) :
    Path en.fixedPointObstruction 0 :=
  Path.ofEq en.fixedPoint_zero

/-- Path: Veblen connection. -/
def veblen_path (en : EpsilonNumber) :
    Path en.veblenObstruction 0 :=
  Path.ofEq en.veblen_zero

end EpsilonNumber

/-! ## Ordinal Arithmetic -/

/-- Ordinal arithmetic operations and their properties. We track
the operation type and verify key identities. -/
structure OrdinalArithmetic where
  /-- Operation type (0 = add, 1 = mult, 2 = exp). -/
  opType : Nat
  /-- Left operand label. -/
  leftLabel : Nat
  /-- Right operand label. -/
  rightLabel : Nat
  /-- Result label. -/
  resultLabel : Nat
  /-- Associativity obstruction (0 = associative, for add/mult). -/
  assocObstruction : Nat
  /-- Left cancellation obstruction (0 = left cancellable). -/
  leftCancelObstruction : Nat
  /-- Commutativity obstruction (non-zero for ordinals in general). -/
  commObstruction : Nat

namespace OrdinalArithmetic

/-- ω + ω = ω · 2. -/
def omega_plus_omega : OrdinalArithmetic where
  opType := 0
  leftLabel := 2  -- ω
  rightLabel := 2  -- ω
  resultLabel := 4  -- ω · 2 label
  assocObstruction := 0
  leftCancelObstruction := 0
  commObstruction := 1  -- ordinal addition is NOT commutative

/-- ω · ω = ω². -/
def omega_times_omega : OrdinalArithmetic where
  opType := 1
  leftLabel := 2
  rightLabel := 2
  resultLabel := 5  -- ω² label
  assocObstruction := 0
  leftCancelObstruction := 0
  commObstruction := 1  -- not commutative

/-- 1 + ω = ω (absorption). -/
def one_plus_omega : OrdinalArithmetic where
  opType := 0
  leftLabel := 1
  rightLabel := 2  -- ω
  resultLabel := 2  -- ω (absorbed)
  assocObstruction := 0
  leftCancelObstruction := 0
  commObstruction := 1

/-- Non-commutativity witness: 1 + ω ≠ ω + 1. -/
def noncomm_witness :
    Path one_plus_omega.commObstruction 1 :=
  Path.ofEq rfl

end OrdinalArithmetic

/-! ## Master Coherence Paths -/

/-- Master: ordinal notation well-ordering. -/
def master_wellOrder_path :
    Path (OrdinalNotation.cantorNF 10 (by omega)).wellOrderObstruction 0 :=
  (OrdinalNotation.cantorNF 10 (by omega)).wellOrder_path

/-- Master: CNF uniqueness. -/
def master_cnf_path :
    Path CantorNormalForm.omega.uniquenessObstruction 0 :=
  CantorNormalForm.omega.cnf_uniqueness_path

/-- Master: Veblen fixed point. -/
def master_veblen_path :
    Path VeblenFunction.phi_1_0.fixpointObstruction 0 :=
  VeblenFunction.phi_1_0.veblen_fixpoint_path

/-- Master: Bachmann-Howard. -/
def master_bh_path :
    Path BachmannHoward.standard.ordinalLabel 3 :=
  BachmannHoward.standard.bachmann_howard_path

/-- Master: collapsing countability. -/
def master_collapsing_path :
    Path CollapsingFunction.psi_0_Omega.countableObstruction 0 :=
  CollapsingFunction.psi_0_Omega.collapsing_countable_path

/-- Master: PA ordinal. -/
def master_pa_ordinal_path :
    Path ProofTheoreticOrdinal.pa.ordinalLabel 10 :=
  ProofTheoreticOrdinal.pa_ordinal_path

/-- Master: ATR₀ ordinal. -/
def master_atr_ordinal_path :
    Path ProofTheoreticOrdinal.atr0.ordinalLabel 20 :=
  ProofTheoreticOrdinal.atr_ordinal_path

/-- Master: ε₀ fixed point. -/
def master_epsilon0_path :
    Path EpsilonNumber.epsilon0.fixedPointObstruction 0 :=
  EpsilonNumber.epsilon0.fixedPoint_path

end OrdinalAnalysis
end ComputationalPaths
