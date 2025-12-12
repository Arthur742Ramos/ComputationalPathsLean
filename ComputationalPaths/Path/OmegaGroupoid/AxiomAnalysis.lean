/-
# Deep Axiom Analysis: What Can Be Eliminated?

This module provides a rigorous analysis of the axiom structure and identifies
concrete paths to further reduction.

## Current Axiom Count

**Actual axioms (not definitions):**
- Level 3: `to_canonical` (1 schema, ~74 instances)
- Level 4: `contract₄` (1 axiom)
- Level 5+: `contract_high` (1 axiom)

**Definitional, not axiomatic:**
- Step constructors (74): These DEFINE the rewrite system
- Derivation₂ constructors (4): Free structure, no axioms

## Analysis of Each Axiom

### 1. `to_canonical` — Can It Be Eliminated?

**Current form:**
```
to_canonical (d : Derivation₂ p q) : MetaStep₃ d (canonical p q)
```

**Three paths to elimination:**

**Path A: Prove from confluence (HARD)**
We have confluence at the Prop level:
- `rw_normalizes p : Rw p (normalize p)`
- `rw_confluent : Rw p n₁ → Rw p n₂ → ∃ n, Rw n₁ n ∧ Rw n₂ n`

The gap: `Rw` and `RwEq` are in `Prop`, losing computational content.
`Derivation₂` and `Derivation₃` are in `Type`, preserving structure.

To prove `to_canonical`, we'd need to "internalize" the confluence proof
as a Type-valued witness. This requires:
1. A termination measure on derivations
2. A proof that measure-reducing steps produce 3-cells
3. Well-founded induction to build the full 3-cell

**Status:** Theoretically possible but requires significant machinery.

**Path B: Replace with bare contractibility (EASY but loses grounding)**
Instead of `to_canonical`, use:
```
contract₃ (d₁ d₂ : Derivation₂ p q) : MetaStep₃ d₁ d₂
```

This is ONE constructor vs the schema. It asserts contractibility directly
without grounding it in normalization.

**Tradeoff:** Simpler axiom, but loses the connection to computation.

**Path C: Reduce to minimal Step set (MODERATE)**
Remove redundant Step constructors:
- `trans_refl_right` (derivable from `trans_refl_left`)
- `symm_trans` (derivable from `trans_symm` + `symm_symm`)
- Potentially some η rules (derivable from β rules?)

This doesn't change the axiom schema, but reduces instances.

### 2. `contract₄` — Can It Be Eliminated?

**Current form:**
```
contract₄ (m₁ m₂ : Derivation₃ d₁ d₂) : MetaStep₄ m₁ m₂
```

**Analysis:**
If level 3 is contractible, why doesn't level 4 follow automatically?

The issue: `contractibility₃` produces 3-cells functionally:
```
contractibility₃ d₁ d₂ := vcomp (to_canonical d₁) (inv (to_canonical d₂))
```

But different inputs can produce different outputs! We need to show
these outputs are 4-equivalent, which requires `contract₄`.

**Path to elimination: Single truncation axiom**
```
axiom truncation₃ : ∀ (d₁ d₂ : Derivation₂ p q), Subsingleton (Derivation₃ d₁ d₂)
```

This says "3-cells are proof-irrelevant" and implies:
- `contract₄` (trivially, since source type is a subsingleton)
- `contract_high` (trivially, by iteration)

**Status:** Would require restructuring Derivation₃ or adding the axiom.

### 3. `contract_high` — Can It Be Eliminated?

**Analysis:** Same as `contract₄`. If we have `truncation₃`, this follows.

## Concrete Reduction Proposals

### Proposal 1: Bare Contractibility (Minimal Axiom Count)

Replace the current structure with:
```lean
-- Level 3: One bare axiom
| contract₃ (d₁ d₂ : Derivation₂ p q) : MetaStep₃ d₁ d₂

-- Level 4+: Subsumed by truncation
axiom truncation₃ : ∀ d₁ d₂, Subsingleton (Derivation₃ d₁ d₂)
```

**Result:** 2 axioms total (contract₃ + truncation₃)

**Tradeoff:** Loses the normalization-based grounding of `to_canonical`.

### Proposal 2: Prove to_canonical (Ideal)

Implement the termination-measure approach:
1. Define `measure : Derivation₂ p q → ℕ`
2. Show `canonical p q` has minimal measure
3. Show measure-reducing transformations produce 3-cells
4. Prove `to_canonical` by well-founded induction

**Result:** Level 3 has NO axioms! Only contract₄ and contract_high remain.

**Difficulty:** HIGH — requires careful measure definition and proofs.

### Proposal 3: Remove Redundant Steps (Incremental)

Remove from Step inductive:
- `trans_refl_right` (derivable via symmetry)
- `symm_trans` (derivable via involution)
- Analyze η rules: `prod_eta`, `sigma_eta`, `fun_eta` — are they derivable?

**Result:** Fewer Step constructors → fewer `step_to_canonical` instances.

**Difficulty:** MODERATE — requires rebuilding Step and re-verifying proofs.

### Proposal 4: Direct Analysis of Step Categories

**Category analysis of 74 Step constructors:**

| Category | Count | Potentially Derivable |
|----------|-------|----------------------|
| Groupoid laws | 8 | 2 (trans_refl_right, symm_trans) |
| Type: Products | 7 | 1-2 (prod_eta?) |
| Type: Sigma | 4 | 1 (sigma_eta?) |
| Type: Sum | 2 | 0 |
| Type: Functions | 4 | 1 (fun_eta?) |
| Type: Transport | 5 | ? |
| Context | 16 | Many? |
| DepContext | 12 | Many? |
| BiContext | 8 | Many? |
| Congruence | 4 | 0 (essential) |
| Canon | 1 | 0 (essential) |

**Potential reduction:** 74 → ~50-60 if η rules and some context rules are derivable.

## Why We "Feel" Like There Are Too Many Axioms

1. **Conflating definitions with axioms**: The 74 Step constructors are
   definitional, not axiomatic. They define what rewrites exist.

2. **Schema vs instances**: `to_canonical` is ONE schema that instantiates
   74 times. It's conceptually one assertion.

3. **Type-specific rules**: Most Step constructors are β/η rules for types
   (products, sums, functions, etc.). These are standard and expected.

4. **Context machinery**: The context_*, depContext_*, biContext_* rules
   (36 constructors!) are for compositional reasoning. Many might be derivable.

## Recommended Action Plan

**Phase 1 (Easy):** Remove `trans_refl_right` and `symm_trans` from Step.
- Saves 2 constructors
- RwEq relation unchanged (just longer derivations)
- Demonstrates the principle

**Phase 2 (Moderate):** Analyze context rules for redundancy.
- 36 context-related constructors might have dependencies
- Could potentially halve them

**Phase 3 (Hard):** Attempt to prove some η rules from β rules.
- Would remove 3 constructors (prod_eta, sigma_eta, fun_eta)
- Requires careful type-theoretic analysis

**Phase 4 (Research):** Attempt to prove `to_canonical` from confluence.
- Would eliminate the level-3 axiom entirely
- Major theoretical contribution if successful

## Summary

**Current state:** 3 axioms (schemas) + 74 definitional rules
**Achievable easily:** 3 axioms + ~70 rules (remove redundant groupoid laws)
**Achievable with work:** 2 axioms + ~50 rules (truncation + reduced Steps)
**Ideal (research goal):** 1-2 axioms + minimal Steps (prove to_canonical)
-/

import ComputationalPaths.Path.OmegaGroupoid

namespace ComputationalPaths
namespace Path
namespace OmegaGroupoid
namespace AxiomAnalysis

universe u

variable {A : Type u}

/-! ## Demonstration: Step Constructors Are Definitional

The Step inductive DEFINES what rewrites exist. These aren't axioms —
they're the specification of the rewrite system.
-/

/-- Count of Step constructors (for documentation). -/
def stepConstructorCount : Nat := 74

/-- The "axiom count" is actually just 3 schemas. -/
def actualAxiomCount : Nat := 3  -- to_canonical, contract₄, contract_high

/-! ## Alternative: Bare Contractibility

Here we show how the structure would look with bare contractibility
instead of `to_canonical`.
-/

/-- Bare contractibility asserts any two 2-cells are 3-connected, directly.
    This is equivalent to `to_canonical` but less computationally grounded. -/
def bareContract₃ {a b : A} {p q : Path a b}
    (d₁ d₂ : Derivation₂ p q) : Derivation₃ d₁ d₂ :=
  -- Currently derived from to_canonical
  contractibility₃ d₁ d₂

/-! ## Redundant Step Analysis

Here we identify which Step constructors are derivable from others
at the RwEq level (and thus could potentially be removed from Step).
-/

section RedundantSteps

variable {a b : A} (p : Path a b)

/-- trans_refl_right is derivable from trans_refl_left + symmetry rules. -/
theorem trans_refl_right_derivable :
    RwEq (Path.trans p (Path.refl b)) p :=
  rweq_cmpA_refl_right p

/-- symm_trans is derivable from trans_symm + symm_symm. -/
theorem symm_trans_derivable :
    RwEq (Path.trans (Path.symm p) p) (Path.refl b) :=
  rweq_cmpA_inv_left p

/-- These two are the "easy wins" for Step reduction. -/
def easyStepReductions : List String :=
  ["trans_refl_right", "symm_trans"]

end RedundantSteps

/-! ## Context Rules: Potential for Reduction

The 36 context-related Step constructors might have significant redundancy.
-/

/-- Context-related Step constructors (for analysis). -/
def contextStepCount : Nat := 36  -- context_* + depContext_* + biContext_*

/-- Potential savings from context rule analysis. -/
def potentialContextSavings : Nat := 15  -- conservative estimate

/-! ## The Path to Proving to_canonical

If we could prove to_canonical, we'd eliminate the level-3 axiom entirely.
The key insight is using a termination measure.
-/

/-- A potential measure for derivations (sketch). -/
def derivationMeasure {p q : Path a b} : Derivation₂ p q → Nat
  | .refl _ => 0
  | .step _ => 1
  | .inv d => derivationMeasure d
  | .vcomp d₁ d₂ => derivationMeasure d₁ + derivationMeasure d₂ + 1

/-- The canonical derivation has a specific measure. -/
def canonicalMeasure {p q : Path a b} : Nat :=
  derivationMeasure (canonical p q)

/-
To prove `to_canonical`, we would need to show:
1. Every derivation can be transformed to `canonical` via measure-reducing steps
2. Each step produces a 3-cell
3. Compose the 3-cells to get the full `to_canonical`

This is the "holy grail" of axiom elimination for this system.
-/

end AxiomAnalysis
end OmegaGroupoid
end Path
end ComputationalPaths
