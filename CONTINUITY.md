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
- **Done**:
  - Audited circle/torus encode-decode: `HasCircleLoopDecode`/`HasCirclePiOneEncode` remain necessary due to Prop-level equality (encode/decode transport inconsistency); torus encode/decode already derived from circle with no extra axioms.
- **Done**:
  - Implemented `inducedSubgroup` via induced π₁ map + conjugation in `ComputationalPaths/Path/Homotopy/CoveringClassification.lean`; removed placeholder regular-cover/exemplar theorems.
- **Done**:
  - Fixed `coveringPiOneMap_comp`/`coveringPiOneMap_inv` by aligning `PathRwQuot.trans/symm` with `LoopQuot.comp/inv`; build for `CoveringClassification` succeeds.
- **Done**:
  - Removed ProjectiveSpaces module and cleaned dependent imports/notes.
  - Cleaned LieGroups, Hurewicz, IntArith, LoopIteration, PushoutPaths, CoveringClassification references to deleted surfaces/projective/legacy modules.
  - Updated docs: `README.md`, `docs/axioms.md`, `CLAUDE.md`, and `ComplexProjectiveSpaces.lean` to remove deleted modules.
  - Deleted `docs/klein_bottle_plan.md` (legacy notes).
- **Done**:
  - `./lake.cmd build` succeeded after cleanup.
  - `Scripts/AxiomInventory.lean` reports 7 kernel axioms (Circle constructors/recursors only).
- **Done**:
  - Ran `./lake.cmd env lean Scripts/AssumptionSurvey.lean`; it reported assumptions for circle/torus/SVK/wedge targets, then errored on missing `projectivePiOneEquivZ2` and `kleinPiOneEquivIntProd` (definitions deleted).
  - Assumption survey output highlights remaining explicit classes: `HasCirclePiOneEncode`, `HasTorusPiOneEncode`, `HasPushoutSVKEncodeQuot`, `HasPushoutSVKDecodeEncode`, `HasPushoutSVKEncodeDecode`, `HasPushoutSVKEncodeDecodeFull`, `HasPushoutSVKDecodeAmalgBijective`, `HasPushoutSVKDecodeFullAmalgBijective`, `HasGlueNaturalLoopRwEq`, `HasWedgeSVKDecodeEncode`, `HasWedgeSVKEncodeDecode`, `HasWedgeSVKEncodeQuot`, `HasWedgeSVKDecodeBijective`.
  - Grepped remaining assumption classes: `HasLensPiOneEncode`, `HasGeneralLensPiOneEncode`, `HasMobiusLoopDecode`, `HasBouquetPiOneEquiv`, `HasFreeGroupDecomposition`, `HasSumDecodeEncodeRwEq`, `HasDeckEquivPiOneData`, `HasCoveringEquivSubgroup`, `HasUniversalCoverUniversalProperty`, `HasGraphPi1Equiv`, `HasEdgePaths`, `HasSubgroupCovering`, `HasSuspensionMap`, `HasFreudenthalTheorem`, `HasSpherePiNData`, `HasHopfFibrationData`, `HasJoinOfRw`, plus rewrite assumptions `HasLocalConfluenceProp` and `HasStepStripProp`.
  - Updated and re-ran `Scripts/AssumptionSurvey.lean` to completion. Additional dependencies found: `HasMobiusLoopDecode`, `HasLensPiOneEncode`, `HasGeneralLensPiOneEncode`, `HasBouquetPiOneEquiv`, `HasFreeGroupDecomposition`, `HasCirclePiOneEncode` for `Pi2Sphere.hopf_connecting_iso`/`sphere2_pi2_equiv_int'`, `HasDeckEquivPiOneData`, `HasCoveringEquivSubgroup`, `HasFreudenthalTheorem`.
  - Removed redundant wedge wrapper class and instance, and deleted `ComputationalPaths/Path/HIT/WedgeEncode.lean`. Wedge equivalence now uses `wedgeFundamentalGroupEquiv_of_decode_bijective` directly.
  - Updated `ComputationalPaths/Path/HIT/FigureEight.lean`, `README.md`, and `docs/axioms.md` to reflect wedge API change.
- **Done**:
  - Removed assumption-based π₁ equivalences from `ComputationalPaths/Path/HIT/FigureEight.lean` and `ComputationalPaths/Path/HIT/BouquetN.lean`; kept only decode map/loop generators.
  - Deleted legacy modules: `ComputationalPaths/Path/HIT/MobiusBand.lean`, `ComputationalPaths/Path/HIT/LensSpace.lean`, `ComputationalPaths/Path/HIT/HopfFibration.lean`, `ComputationalPaths/Path/HIT/Pi2Sphere.lean`, `ComputationalPaths/Path/HIT/Pi3Sphere.lean`, `ComputationalPaths/Path/HIT/JamesConstruction.lean`, `ComputationalPaths/Path/HIT/ComplexProjectiveSpaces.lean`, `ComputationalPaths/Path/Homotopy/FreudenthalSuspension.lean`, `ComputationalPaths/Path/Homotopy/CellularHomology.lean`.
  - Removed imports/usages of deleted modules from `ComputationalPaths/Path.lean` and homotopy files; updated `Scripts/AssumptionSurvey.lean` (dropped Freudenthal check).
  - Updated docs: `README.md`, `docs/axioms.md`, `CLAUDE.md` to mark legacy removals and align figure-eight/bouquet claims.
  - Fixed `ComputationalPaths/Path/HIT/PushoutPaths.lean` parse error (restore `end WedgeSVK`, move `open WedgeSVK` into `namespace WedgeSVKInstances`).
  - Fixed `ComputationalPaths/Path/HIT/SVKApplications.lean` to import `CircleStep` and use `{_ : HasCirclePiOneEncode}` binder.
  - Fixed unused variable warning in `ComputationalPaths/Path/Homotopy/Hurewicz.lean`.
  - `./lake.cmd build` completed successfully (warning-free).
  - `./lake.cmd env lean Scripts/AssumptionSurvey.lean` completed; remaining assumptions include `HasCirclePiOneEncode`, `HasTorusPiOneEncode`, SVK encode/decode classes, wedge decode bijective, and covering classification data.
  - `./lake.cmd env lean Scripts/AxiomInventory.lean` reports 7 kernel axioms (Circle constructors/recursors only).
  - Updated `README.md` figure-eight/bouquet sections to match removed equivalence claims and new wedge equivalence name.
  - Committed and pushed all current changes (`64a6c07` to `main`).
- **Now**:
  - Continue discharging remaining encode/decode and major-theorem assumptions.
- **Next**:
  - Continue discharging remaining encode/decode and major-theorem assumptions in the recommended order.

## Open Questions
- Which remaining non-HIT axioms, if any, must stay due to Lean limitations? (UNCONFIRMED)
- Any remaining non-HIT assumption modules to delete vs formalize? (UNCONFIRMED)

## Working Set
- Files: `CONTINUITY.md`, `ComputationalPaths/Path/HIT/PushoutPaths.lean`, `ComputationalPaths/Path/HIT/FigureEight.lean`, `ComputationalPaths/Path/HIT/BouquetN.lean`, `README.md`, `docs/axioms.md`, `Scripts/AssumptionSurvey.lean`
- Commands: `./lake.cmd build`, `./lake.cmd env lean Scripts/AxiomInventory.lean`, `./lake.cmd env lean Scripts/AssumptionSurvey.lean`


