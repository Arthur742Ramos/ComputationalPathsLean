# CONTINUITY.md
## Goal (incl. success criteria):
- Remove remaining contractibility axioms (contract₄, contract_high), derive constructively, no `sorry`/placeholders, and pass `source ~/.elan/env && lake build`.

## Constraints/Assumptions:
- User request: remove all contractibility axioms at any level; keep trying if approach fails.
- Run `source ~/.elan/env && lake build`; keep build warning-free.
- No `sorry`; no new axioms; no placeholders.
- Use `apply_patch` for single-file edits; prefer Read/Glob/Grep over bash for files.

## Key decisions:
- Derived contractibility₃ from proof irrelevance of `RwEq` using `MetaStep₃.rweq_eq`.

## State:
- Done:
  - Derived contractibility₃ from proof irrelevance; build succeeded.
-  - Replaced contract₄/contract_high axioms with derived `rweq_eq` steps using proof irrelevance.
-  - Added Prop-level projections `Derivation₃.toRwEqEq` and `Derivation₄.toRwEqEq`.
-  - Updated docs in `OmegaGroupoid`/`StepToCanonical`/`Derived` to remove axiom language.
-  - `source ~/.elan/env && lake build` succeeded.
- Now:
  - Ready for review.
- Next:
  - None.

## Open questions (UNCONFIRMED if needed):
- None.

## Working set (files/ids/commands):
- Files: `ComputationalPaths/Path/OmegaGroupoid.lean`, `ComputationalPaths/Path/OmegaGroupoid/Derived.lean`, `ComputationalPaths/Path/OmegaGroupoid/StepToCanonical.lean`, `CONTINUITY.md`.
- Commands: `source ~/.elan/env && lake build`.
