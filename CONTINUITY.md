# CONTINUITY.md
## Goal (incl. success criteria):
- Remove non-HIT assumptions by formalizing concrete entities or deleting legacy axiomatic modules; keep `sorry`-free; only HIT/strictly necessary axioms remain.
- Keep `to_canonical` unchanged; update docs/imports to match reality; commit/push after milestones.

## Constraints/Assumptions:
- Run `./lake.cmd build` after non-trivial edits; keep build warning-free.
- No `sorry`; avoid new axioms except HIT/strictly necessary limitations.
- Use `rg` for search; prefer `apply_patch` for single-file edits.
- Approval policy `never`; sandbox `danger-full-access`; shell PowerShell.

## Key decisions:
- Deleted legacy opt-in axiom wrapper files and multiple assumption-heavy modules; keep explicit typeclass assumptions where unavoidable.
- Removed univalence from default `ComputationalPaths.Path` import chain; use subsingleton-based `IsHSet`.
- Reworked confluence to minimal Prop-level version; removed legacy confluence bridge modules.
- Removed wedge encode wrapper class; use direct decode/bijective assumptions.

## State:
- Done:
  - Deleted covering-classification stack (`ComputationalPaths/Path/Homotopy/CoveringClassification.lean`, `ComputationalPaths/Path/Algebra/GraphHIT.lean`, `ComputationalPaths/Path/Algebra/NielsenSchreierDerived.lean`), removed imports, and cleaned README/docs/survey.
  - Deleted multiple legacy/axiom-heavy modules (OmegaGroupoid analysis, NatCharacterization, projective spaces, mobius/lens/hopf/pi2/pi3/james/CP, Freudenthal, cellular homology, homotopy placeholders).
  - Removed opt-in axiom wrapper files; cleaned docs/imports; build passes.
  - Wedge encode wrapper removed; figure-eight/bouquet equivalence claims pruned; docs updated.
  - Removed `HasSumDecodeEncodeRwEq` and `sum_isHSet` from `ComputationalPaths/Path/Homotopy/Coproduct.lean`.
  - Assumption survey rerun; remaining assumptions: circle/torus encode, SVK encode/decode (pushout + wedge), glue naturality.
  - Axiom inventory: 7 kernel axioms (Circle constructors/recursors).
  - `./lake.cmd build` succeeds after removals.
  - Committed and pushed removals/cleanup (`c3ac80c`).
- Now:
  - Update README note on coproduct assumptions and commit/push.
- Next:
  - Reassess remaining assumptions (circle/torus, SVK, glue naturality) for formalization vs necessary axioms.
  - Commit/push milestone after build passes.

## Open questions (UNCONFIRMED if needed):
- Which remaining non-HIT assumptions are strictly necessary due to Lean limitations?
- Any additional legacy modules to delete vs formalize after removing covering-classification stack?

## Working set (files/ids/commands):
- Files: `CONTINUITY.md`, `Scripts/AssumptionSurvey.lean`, `ComputationalPaths/Path/HIT/Pushout.lean`, `ComputationalPaths/Path/HIT/PushoutPaths.lean`, `ComputationalPaths/Path/HIT/CircleStep.lean`, `ComputationalPaths/Path/HIT/TorusStep.lean`, `docs/axioms.md`.
- Commands: `./lake.cmd env lean Scripts/AssumptionSurvey.lean`, `./lake.cmd env lean Scripts/AxiomInventory.lean`, `./lake.cmd build`.
