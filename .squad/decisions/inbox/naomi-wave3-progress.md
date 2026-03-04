# Naomi Wave-3 Progress (Reconnect Sweep + KnotInvariants)

**Date:** 2026-03-04  
**By:** Naomi (Core Dev)  
**Requested by:** Arthur Freitas Ramos

## Scope Completed

### 1) Reconnect sweep in `ComputationalPaths/Path.lean`

Prioritized candidates were attempted in order:

1. `ComputationalPaths.Path.Homotopy.HomotopyGroup` ✅ **RE-ENABLED**
   - Local fix: one-line syntax hygiene in `Path/Homotopy/HomotopyGroup.lean`
     - converted detached doc comment before disabled code into regular comment.
   - Import now enabled in `ComputationalPaths/Path.lean`.

2. `ComputationalPaths.Path.Homotopy.HigherProductHomotopy` ⛔ **KEPT DISABLED**
   - Compile still fails with multiple non-local obligations (ULift/quotient branch alignment, n=1 operation preservation goals).
   - Repair exceeds “least-risk minimal local” scope for this wave.

3. `ComputationalPaths.Path.Homotopy.HomotopyGroupPaths` ⛔ **KEPT DISABLED**
   - Compile reports broad unresolved goals/type mismatches across the module.
   - Includes many unsolved proof obligations; not a surgical syntax/namespace/universe patch.

### 2) Deepening in `Path/Topology/KnotInvariants.lean`

Added one substantive RwEq theorem:

- `knot_invariant_step_cancel_with_tail_rweq`
  - Statement contracts a composed path
    `trans (trans step (symm step)) refl`
    to `refl` up to `RwEq`.
  - Proof uses nontrivial chain:
    - `rweq_trans`
    - `rweq_cmpA_refl_right`
    - `rweq_cmpA_inv_right`

Also added explicit import:
- `import ComputationalPaths.Path.Rewrite.RwEq`

## Validation

Targeted:
- `lake build ComputationalPaths.Path.Homotopy.HomotopyGroup` ✅
- `lake build ComputationalPaths.Path.Topology.KnotInvariants` ✅
- `lake build ComputationalPaths.Path` ✅

Full:
- `lake build` ✅

## Decisions / Blockers

- **Decision:** Keep `HigherProductHomotopy` and `HomotopyGroupPaths` disabled in `Path.lean` for now; failures are not solvable with low-risk surgical edits.
- **Blocker A (`HigherProductHomotopy`):** coupled ULift + quotient proofs in n=1 branches require broader proof refactoring.
- **Blocker B (`HomotopyGroupPaths`):** numerous unsolved goals/type mismatches across many declarations indicate module-level rehabilitation effort.

