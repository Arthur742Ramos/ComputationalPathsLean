# CONTINUITY.md
## Goal
Remove assumptions by proving/formalizing concrete entities; delete legacy axiomatic modules; keep development `sorry`-free and use axioms only when strictly necessary (e.g., HIT constraints). Keep `to_canonical` unchanged. After commit/push, work on discharging encode/decode assumptions and major theorem assumptions so only HIT or strictly necessary axioms remain.

## Constraints/Assumptions
- Run `./lake.cmd build` after non-trivial edits; keep build warning-free.
- No `sorry`.
- Avoid new axioms; only introduce or keep axioms when strictly necessary (e.g., HIT constraints).
- Approval policy `never`; sandbox `danger-full-access`.

## Key Decisions
- Non-HIT assumptions are explicit typeclasses; no opt-in kernel-axiom wrapper files remain.
- HIT axioms remain as kernel axioms (necessary for the theory).
- Delete legacy OmegaGroupoid analysis modules; keep only derived/step/canonical/typed rewriting.
- Remove univalence from default `ComputationalPaths.Path` import chain (opt-in only).
- Remove `HasDecidableEqAxiomK` and questionable AxiomK/IsHSet instances; keep only subsingleton-based IsHSet for now.
- Deleted opt-in axiom wrapper files for non-HIT results (Circle/Torus/etc. pi1, WedgeSVK, HopfInvariantOne, CoveringClassification, ConfluenceConstructive).

## State
- **Done**:
  - Deleted legacy OmegaGroupoid analysis files and removed import from `ComputationalPaths/Path.lean`.
  - Removed univalence from default `ComputationalPaths.Path` import chain; updated README to note opt-in.
  - Removed `HasDecidableEqAxiomK` and Nat/Bool/Int AxiomK/IsHSet proofs; relied on subsingleton-based IsHSet only.
  - Updated truncation/PUnit/LieGroups/KleinBottleSVK/Sphere to use subsingleton IsHSet instead of `decidableEq_implies_isHSet`.
  - Deleted legacy `ComputationalPaths/Path/Homotopy/NatCharacterization.lean` (invalid axioms/refers to missing `reflexivity_theorem`).
  - `./lake.cmd build` succeeds after the deletion.
- **Done**:
  - Inspected unexpected modified files:
    - `ComputationalPaths/Path/Algebra/NielsenSchreier.lean` deleted (legacy axioms).
    - `ComputationalPaths/Path/Algebra/Abelianization.lean` now imports `NielsenSchreierDerived`.
    - `ComputationalPaths/Path/HIT/BouquetN.lean` adds constructive mul/inv on `BouquetFreeGroup`.
    - `ComputationalPaths/Path/HIT/Pushout.lean` removed `DecidableEq` + AxiomK shortcut instances.
    - Minor comment tweaks in `GraphHIT.lean` and `NielsenSchreierDerived.lean`.
- **Done**:
  - User chose to keep the inspected changes (option 1).
- **Done**:
  - Deleted legacy opt-in axiom wrapper files:
    - `ComputationalPaths/Path/HIT/CirclePiOneAxiom.lean`
    - `ComputationalPaths/Path/HIT/TorusPiOneAxiom.lean`
    - `ComputationalPaths/Path/HIT/ProjectivePiOneAxiom.lean`
    - `ComputationalPaths/Path/HIT/KleinPiOneAxiom.lean`
    - `ComputationalPaths/Path/HIT/LensPiOneAxiom.lean`
    - `ComputationalPaths/Path/HIT/WedgeSVKAxiom.lean`
    - `ComputationalPaths/Path/HIT/HopfInvariantOneAxiom.lean`
    - `ComputationalPaths/Path/Homotopy/CoveringClassificationAxiom.lean`
    - `ComputationalPaths/Path/Rewrite/ConfluenceConstructiveAxiom.lean`
  - Updated `ComputationalPaths/Path/Rewrite/ConfluenceConstructive.lean` docs to remove references to the deleted axiom file.
- **Done**:
  - Updated docs to remove deleted axiom wrapper references:
    - `ComputationalPaths/Path/Rewrite/StripLemma.lean`
    - `ComputationalPaths/Path/HIT/HopfInvariantOne.lean`
    - `ComputationalPaths/Path/Homotopy/CoveringClassification.lean`
    - `CLAUDE.md`
    - `README.md`
    - `docs/axioms.md` (rewrote affected sections to reflect explicit assumptions)
- **Now**: Validate docs for consistency and run a clean build.
- **Done**: `./lake.cmd build` completed successfully.
- **Now**: Commit and push the current cleanup changes.
- **Next**: Start discharging encode/decode assumptions and major theorem assumptions; use surveys to target remaining axioms if needed.

## Open Questions
- Which remote/branch should be pushed to? (UNCONFIRMED)
- Which remaining non-HIT axioms, if any, must stay due to Lean limitations? (UNCONFIRMED)

## Working Set
- Files: `CONTINUITY.md`, `README.md`, `docs/axioms.md`, `ComputationalPaths/Path/Rewrite/StripLemma.lean`, `ComputationalPaths/Path/Homotopy/CoveringClassification.lean`, `ComputationalPaths/Path/HIT/HopfInvariantOne.lean`, `CLAUDE.md`
- Commands: `rg -n "^\\s*axiom\\b" ComputationalPaths -g "*.lean"`, `rg -n "sorry" ComputationalPaths -g "*.lean"`, `rg -n "CirclePiOneAxiom|TorusPiOneAxiom|ProjectivePiOneAxiom|KleinPiOneAxiom|LensPiOneAxiom|WedgeSVKAxiom|HopfInvariantOneAxiom|CoveringClassificationAxiom|ConfluenceConstructiveAxiom"`, `./lake.cmd build`
