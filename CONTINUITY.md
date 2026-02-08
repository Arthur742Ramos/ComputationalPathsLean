# CONTINUITY.md

## Goal
- Add a new module proving pi_1(figure-eight) is the free group on two generators.

## Constraints/Assumptions
- No axioms, sorries, or #check in new code.
- Follow existing module/docstring conventions.
- Run `export PATH=$HOME/.elan/bin:$PATH && lake build 2>&1 | tail -30` before and after changes.

## Key Decisions
- Use the wedge SVK decode-bijective interface to obtain pi_1(Wedge Circle Circle).
- Identify the free group on two generators as FreeProductWord Int Int via circlePiOneEquivInt.

## State
- **Done**:
  - Read AGENTS.md, ARCHITECTURE.md, FigureEight.lean, BouquetN.lean, PushoutPaths.lean, CircleStep.lean, TorusStep.lean.
  - Baseline build completed.
- **Now**: Create plan, add FigureEightStep module, update imports/docs.
- **Next**: Run lake build and report results.

## Open Questions
- None.

## Working Set
- Files: ComputationalPaths/Path/CompPath/FigureEight.lean, ComputationalPaths/Path/CompPath/PushoutPaths.lean, ComputationalPaths/Path/CompPath/CircleStep.lean, ComputationalPaths/Path/CompPath/BouquetN.lean, ComputationalPaths/Path.lean, README.md, (new) ComputationalPaths/Path/CompPath/FigureEightStep.lean
- Commands: export PATH=$HOME/.elan/bin:$PATH && lake build 2>&1 | tail -30
