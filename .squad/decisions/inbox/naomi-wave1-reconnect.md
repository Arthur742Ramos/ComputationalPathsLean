# Naomi Wave-1 Reconnect Notes

**Date:** 2026-03-04  
**Requested by:** Arthur Freitas Ramos  
**Owner:** Naomi (Core Dev)

## Decision
Re-enable the three disconnected aggregator imports and resolve resulting breakage using namespace disambiguation only (no broad refactors).

## Changes Applied
1. Re-enabled imports:
   - `ComputationalPaths.Coherence.CoherenceDeep` in `ComputationalPaths/Coherence.lean`
   - `ComputationalPaths.CwF.UniverseCoherence` in `ComputationalPaths/CwF.lean`
   - `ComputationalPaths.Equivalence.PathInfrastructure` in `ComputationalPaths/Equivalence.lean`
2. Collision fixes (local, namespace-only):
   - Wrapped `ComputationalPaths/Coherence/CoherenceDeep.lean` contents in `namespace Deep`
   - Wrapped `ComputationalPaths/CwF/UniverseCoherence.lean` contents in `namespace UniverseCoherence`
   - Wrapped `ComputationalPaths/Equivalence/PathInfrastructure.lean` contents in `namespace PathInfrastructure`

## Verification
- `lake build ComputationalPaths.Coherence` → exit code 0
- `lake build ComputationalPaths.CwF` → exit code 0
- `lake build ComputationalPaths.Equivalence` → exit code 0
- `lake build` (full) → exit code 0

## Blockers
None. All requested imports remain enabled after surgical disambiguation.
