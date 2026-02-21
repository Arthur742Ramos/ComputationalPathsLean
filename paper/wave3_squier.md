# Wave 3: Squier's Theorem Connection Report

## Summary

File: `ComputationalPaths/Path/Rewrite/Squier.lean`  
Lines: 157 | Definitions/Theorems: 13 | Sorry: 0 | Admit: 0

## Background: Squier's Theorem

Squier (1987) proved: A finitely presented monoid with a decidable word problem has a finite complete rewriting system **if and only if** it has finite derivation type (FDT).

FDT means: the 3-cells (homotopy generators / critical pair resolutions) of the 2-polygraph form a finite generating set for all derivation equivalences.

This connects rewriting theory to homological algebra — FDT is equivalent to `H_3` of the monoid being finitely generated.

## Results

### 1. Critical Pair Enumeration

Five families of critical pairs are formalized with explicit constructors:

| Critical Pair | Rules | Resolution |
|---|---|---|
| `cp_refl_left_assoc` | trans_refl_left vs trans_assoc | Both reach `trans p q` |
| `cp_symm_assoc` | trans_symm vs trans_assoc | Both reach `q` via cancel_left |
| `cp_symm_trans_assoc` | symm_trans vs trans_assoc | Both reach `q` via cancel_right |
| `cp_refl_right_assoc` | trans_refl_right vs trans_assoc | Both reach `trans p q` |
| `cp_assoc_assoc` | trans_assoc vs trans_assoc | Mac Lane pentagon → `p·(q·(r·s))` |

### 2. All Critical Pairs Resolved

Each critical pair has a formal proof that both reducts join:
- `cp_refl_left_assoc_resolves`
- `cp_symm_assoc_resolves`
- `cp_symm_trans_assoc_resolves`
- `cp_refl_right_assoc_resolves`
- `cp_assoc_assoc_resolves` (the Mac Lane pentagon!)

### 3. Convergence Theorem

**`convergent`**: The completed groupoid TRS is both confluent and terminating.

### 4. Squier's Hypotheses Verified

**`squier_hypotheses`**: Packages three formally verified facts:
1. **Confluence** (from GroupoidConfluence.lean)
2. **Termination** (well-foundedness from GroupoidTRS.lean)  
3. **Decidable word problem** (via reduced word comparison)

### 5. The Mac Lane Pentagon

The critical pair `cp_assoc_assoc` between two overlapping `trans_assoc` applications produces the **Mac Lane pentagon** — the coherence condition for monoidal categories. Its resolution requires three steps through the intermediate form, connecting our rewriting theory to categorical coherence.

## Paper-Relevant Claims

1. **All critical pairs of the completed groupoid TRS are explicitly enumerated and resolved.** This is the combinatorial core of showing finite derivation type.

2. **The Mac Lane pentagon appears naturally** as a critical pair resolution — this connects rewriting theory to categorical coherence.

3. **Squier's hypotheses are formally verified**: confluence + termination + decidable word problem. By Squier's theorem, this implies the groupoid fragment has FDT.

4. **FSCD pedigree**: The Squier–Lafont–Guiraud program is exactly the framework that FSCD reviewers recognize. Our formalization provides a concrete, fully verified example.

## Build Status

✅ `lake build` succeeds
