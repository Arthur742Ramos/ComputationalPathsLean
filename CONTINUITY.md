# CONTINUITY.md

## Goal
Minimize axioms in the ComputationalPaths Algebra modules while maintaining a building codebase.

## Constraints/Assumptions
- Follow repo CLAUDE.md: run `lake build` after non-trivial edits; zero-warning policy
- No sorries allowed
- Prefer eliminating axioms by proving them constructively over consolidation

## Key Decisions
- Consolidated 16+ axioms → 9 in NielsenSchreier.lean via structural grouping
- Consolidated 2 axioms → 1 in Abelianization.lean
- Proved `inverse_respects_rel` constructively (was axiom) - key technique: use `rw [hgen]` for generator unification

## State
- **Done**:
  - Eliminated `inverse_respects_rel` axiom via constructive proof
  - Consolidated graph π₁ axioms into single `graphPi1Equiv`
  - Consolidated Nielsen-Schreier axioms into `NielsenSchreierData` structure
  - Consolidated abelianization axioms into single `freeGroup_ab_equiv_axiom`
  - Derived `tree_pi1_trivial` theorem from `graphPi1Equiv`
  - Added partial constructive infrastructure for abelianization equivalence:
    - `singleGenWord`, `genPowAb`, `FreeGroupAb.mul`, `FreeGroupAb.one`
    - `liftWord`, `buildWordRec`, `intPowToFreeGroupAbAux`

- **Now**: Axiom minimization complete for current session

- **Next** (for future sessions):
  - Prove `encode_decode`: `wordToIntPow (buildWordRec n v) = v`
  - Prove `decode_encode`: any word equals canonical form in FreeGroupAb (complex - requires commutativity reordering)

## Current Axiom Count (Algebra modules)
- NielsenSchreier.lean: 9 axioms (structural + covering theory)
- Abelianization.lean: 1 axiom (abelianization equivalence)
- Total: 10 axioms

## Axioms by Category
1. **Structural HITs** (hard to eliminate without explicit constructions):
   - `GraphRealization`, `graphVertex`, `graphEdgePath`, `graphRealization_connected`

2. **Covering Space Theory** (deep theorems):
   - `graphPi1Equiv` - π₁ of graphs is free
   - `bouquetCovering_isGraph` - coverings are graphs
   - `nielsenSchreierData` - Nielsen-Schreier theorem
   - `schreierRankFormula` - Schreier index formula

3. **Potentially Provable** (infrastructure added):
   - `freeGroup_ab_equiv_axiom` - abelianization of free group is ℤⁿ

## Working Set
- Files: `NielsenSchreier.lean`, `Abelianization.lean`, `BouquetN.lean`
- Commands: `lake build`, `lake build ComputationalPaths.Path.Algebra.NielsenSchreier`
