# CONTINUITY.md

## Goal
- Fix wedge provenance encode/decode proof, complete SVK theorem for Circle ∨ Circle, and build.

## Constraints/Assumptions
- No axioms and no sorries; proofs must be constructive
- Build must pass: `~/.elan/bin/lake build`
- Follow repo conventions (see CLAUDE.md)
- On success: commit and run `clawdbot gateway wake --text 'LEGION: SVK encode for Circle ∨ Circle complete!' --mode now`

## Key Decisions
- **Adopt provenance-tracking steps**: Introduce `PushoutStep` (inl/inr/glue + inverse) to enable encode by cases
- **Axiom-free policy remains**: Do not reintroduce `Step.canon`/UIP-style collapse
- **Define in PushoutCompPath**: Place new `PushoutStep`/`PushoutPath` in `PushoutCompPath.lean`
- **New quotient for wedge loops**: Use a provenance-based loop quotient for wedge sums as the encode target

## State
- **Done**:
  - `HasGlueNaturalLoopRwEq` instance for wedge sums (C = PUnit') in `PushoutCompPath.lean`
  - Build previously clean: 132 modules, no errors
  - Added `PushoutStep`/`PushoutPath` plus `toPath` in `PushoutCompPath.lean`
  - Added provenance-based wedge loop quotient and encode/decode in `PushoutPaths.lean`
  - Added Circle ∨ Circle provenance encode instance and equivalence in `FigureEight.lean`
  - Fixed `wedgeProvenanceEncodeDecode` consLeft/consRight proofs in `PushoutPaths.lean`
  - Added `FreeProductWord.map`/`FreeProductWord.equiv` helpers in `PushoutPaths.lean`
  - Added `figureEightPiOneEquiv` alias in `FigureEight.lean`
  - Full build succeeded (`timeout 3600 ~/.elan/bin/lake build`)

- **Now**: Commit changes and send clawdbot wake message.

- **Next**:
  - None

## Open Questions
- None (proceeding with provenance-based loop quotient for wedge sums).

## Working Set
- Files: `PushoutCompPath.lean`, `PushoutPaths.lean`, `FigureEight.lean`
- Commands: `~/.elan/bin/lake build`
