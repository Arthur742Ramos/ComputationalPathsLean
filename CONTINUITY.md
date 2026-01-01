# CONTINUITY.md
## Goal
- Land “nice” homotopy/topology results in Lean (builds, no warnings, no `sorry`).

## Constraints/Assumptions
- Run `.\lake.cmd build` after non-trivial edits; keep build warning-free.
- No `sorry`.

## Key Decisions
- Basepoint-independence: prove conjugation respects π₁ operations (`conjugateByPath_comp`, `conjugateByPath_inv`).
- Covering classification: make `galois_correspondence` return an actual `SimpleEquiv` (currently via axiom `covering_equiv_subgroup`); keep `inducedSubgroup`/`IsRegularCover` as explicit placeholders pending functoriality infrastructure.

## State
- Done:
  - Added `conjugateByPath_comp` and `conjugateByPath_inv` in `ComputationalPaths/Path/Homotopy/FundamentalGroupoid.lean`.
  - Restated `galois_correspondence` as `SimpleEquiv (CoveringOf A a) (Subgroup A a)` in `ComputationalPaths/Path/Homotopy/CoveringClassification.lean`.
  - Silenced unused-binder warnings in `ComputationalPaths/Path/Algebra/NielsenSchreier.lean` (underscore binders).
  - `.\lake.cmd build` succeeds.
  - Removed stray benchmark scripts under `Scripts/` (were unrequested).
- Now:
  - Commit and push the current changes to `origin/main`.
- Next:
  - If desired: strengthen placeholders (`inducedSubgroup`, `IsRegularCover`) once π₁/covering functoriality exists.

## Open questions
- UNCONFIRMED: Mapping of “first 2” items to the two implemented results.

## Working set
- Files:
  - `ComputationalPaths/Path/Homotopy/FundamentalGroupoid.lean`
  - `ComputationalPaths/Path/Homotopy/CoveringClassification.lean`
  - `ComputationalPaths/Path/Algebra/NielsenSchreier.lean`
- Commands:
  - `.\lake.cmd build`
