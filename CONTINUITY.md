# CONTINUITY.md
## Goal
Remove assumptions by proving/formalizing concrete entities; delete legacy axiomatic modules; keep development `sorry`-free and use axioms only when strictly necessary (e.g., HIT constraints). Keep `to_canonical` unchanged. Discharge encode/decode assumptions and major theorem assumptions in the recommended order so only HIT or strictly necessary axioms remain.

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
- **Done**: `./lake.cmd build` completed successfully.
- **Done**: Committed and pushed cleanup changes (`60c122b` to `main`).
- **Done**:
  - Reworked `ComputationalPaths/Path/Rewrite/ConfluenceProof.lean` to prove `step_strip_prop` constructively from `Rw` induction plus `diamond_prop`.
  - Rewrote `ComputationalPaths/Path/Rewrite/ConfluenceConstructive.lean` as a minimal Prop-level local confluence module (`HasLocalConfluenceProp`, `local_confluence_prop`, join lift lemmas).
  - Deleted legacy confluence bridge modules: `ComputationalPaths/Path/Rewrite/StripLemma.lean`, `ComputationalPaths/Path/Rewrite/ConfluenceFull.lean`, `ComputationalPaths/Path/Rewrite/TerminationBridge.lean`.
  - Removed those legacy imports from `ComputationalPaths/Path.lean`.
  - Added `rw_symm_congr` to `ComputationalPaths/Path/Rewrite/Rw.lean`.
  - Reintroduced Prop-level strip lemma as explicit assumption `HasStepStripProp` in `ComputationalPaths/Path/Rewrite/ConfluenceProof.lean` so confluence can be derived without sorries.
  - `./lake.cmd build` succeeds.
- **Now**: Move to circle/torus encode-decode assumptions (discharge where possible).
- **Next**: Covering classification, then Adams' theorem; survey remaining axioms as needed.

## Open Questions
- Which remaining non-HIT axioms, if any, must stay due to Lean limitations? (UNCONFIRMED)

## Working Set
- Files: `CONTINUITY.md`, `ComputationalPaths/Path.lean`, `ComputationalPaths/Path/Rewrite/ConfluenceProof.lean`, `ComputationalPaths/Path/Rewrite/ConfluenceConstructive.lean`
- Commands: `rg -n "HasLocalConfluence|HasStepStrip" ComputationalPaths -g "*.lean"`, `./lake.cmd build`


