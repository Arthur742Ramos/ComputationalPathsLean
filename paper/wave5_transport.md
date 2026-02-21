# Wave 5: Transport Confluence Analysis

## Analysis Date
2026-02-21

## Overview

Analysis of confluence properties of the transport rewrite rules
(Rules 26–32 from Step.lean) when combined with the groupoid TRS,
**without** proof irrelevance or UIP.

## Key Finding: Sort Separation

The groupoid TRS (`CStep` on `Expr`) and the transport rules operate
on **different sorts**:

- **Groupoid rules**: operate on `Expr` values (`atom`, `refl`, `symm`, `trans`)
- **Transport rules**: operate on `Path.stepChain` terms wrapping propositional
  equalities about `transport`

This means there are **no critical pairs** between groupoid and transport
rules at the top level. The two subsystems are orthogonal.

## Transport Rules Inventory

| Rule | Pattern | Result |
|------|---------|--------|
| `transport_refl_beta` | `stepChain (transport_refl ...)` | `refl` |
| `transport_trans_beta` | `stepChain (transport_trans p q x)` | composition |
| `transport_symm_left_beta` | `stepChain (transport_symm_left p x)` | identity |
| `transport_symm_right_beta` | `stepChain (transport_symm_right p y)` | identity |
| `transport_sigmaMk_fst_beta` | sigma transport on fst | projection |
| `transport_sigmaMk_dep_beta` | dependent sigma transport | composition |
| `subst_sigmaMk_dep_beta` | substitution sigma transport | composition |

## Critical Pair Analysis

### Identified Overlaps (5 families)

1. **symm ∘ transport_refl**: Sequential — transport reduces first,
   then groupoid rule fires. Joinable.

2. **trans_assoc ∘ transport_trans**: Orthogonal — different positions.
   Joinable by commutation.

3. **trans_refl_left ∘ transport_refl**: Sequential — both paths
   reach the same normal form. Joinable.

4. **Nested transports**: Path argument reducibility is in a different
   sort than transport evaluation. No critical pair.

5. **transport_inverse coherence**: `transport (trans p (symm p)) x`
   via two paths. Joinable via `step_toEq`.

### Result: All Critical Pairs Joinable

**Without proof irrelevance**, the combined system is confluent
*modulo propositional equality* (via `step_toEq`).

Full syntactic confluence would require canonicalizing Eq proofs
inside `stepChain`, which is essentially UIP. Without UIP, we have:

- ✅ Semantic confluence (same `toEq` value)
- ✅ Groupoid fragment: fully confluent (proven in GroupoidConfluence.lean)
- ✅ Transport fragment: self-confluent (disjoint head patterns)
- ⚠️ Combined syntactic confluence: requires UIP for full result

## Completion Candidates (if full syntactic confluence desired)

1. **transport_canon**: `stepChain eq₁ = stepChain eq₂` when `eq₁ = eq₂`
   (proof irrelevance)
2. **stepChain_symm**: `symm (stepChain h) ▷ stepChain (h.symm)`
3. **stepChain_trans**: `trans (stepChain h₁) (stepChain h₂) ▷ stepChain (h₁.trans h₂)`

## Significance

This analysis confirms the design decision in the library:
- The groupoid fragment is self-contained and confluent
- Transport rules handle a separate concern (dependent types)
- Full confluence of the combined system is achieved semantically
  via `step_toEq`, not syntactically
- This avoids assuming UIP while maintaining a clean theory
