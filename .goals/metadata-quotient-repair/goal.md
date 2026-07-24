# Goal: Universal quotient repair for equality metadata

## User Request

Strengthen the metadata-fiber paper substantially by developing any necessary
computational-path theory in Lean. Prove a universal quotient/recovery theorem,
analyze the natural `RwEq` quotient, and expand the paper beyond 20 pages when
the added mathematics warrants it.

## Refined Goal

Develop a diagnosis-plus-repair theory for equality decorated with observable
metadata. Classify exactly which setoid quotients restore unrestricted based
elimination with propositional beta, prove the canonical indiscrete repair and
its precise factorization property, generalize the metadata criterion to
arbitrary equality projections through their reflexivity kernels, and apply the
theory to `PathRwQuot`. Audit and formally separate genuine computational-path
quotients from the repository's synthetic winding-expression quotients for the
circle and torus, then rebuild the main article around these stronger results.

## Acceptance Criteria

- [ ] A new public Lean module, preferably
  `ComputationalPaths/Path/TypeTheory/MetadataRepair.lean`, defines metadata
  quotient families by explicit `Setoid`s and a `SetoidTotal` predicate with
  correct universe parameters.
- [ ] Lean proves for an inhabited metadata fiber that
  `IsContractible (Quotient S) ↔ SetoidTotal S`, using `Quotient.sound` for
  sufficiency and `Quotient.exact` for necessity.
- [ ] Lean combines this result with the metadata-fiber criterion to prove:
  quotient-repaired unrestricted based elimination with propositional beta
  exists iff the reflexivity-fiber setoid is total.
- [ ] Lean proves equality induction transports reflexivity-fiber totality to
  every equality-indexed metadata fiber where the theorem claims a family-wide
  result; empty-fiber edge cases are handled explicitly rather than hidden.
- [ ] Lean defines the indiscrete setoid repair, proves its quotient is
  contractible, and states/proves the precise quotient-injection-preserving
  factorization properties. The documentation calls the relation maximal and
  the retained information minimal, and avoids false initiality claims.
- [ ] Lean defines a generic reflexive equality projection
  `q : R b → a = b`, its reflexivity kernel, and proves a projection/kernel
  classification of unrestricted based elimination with propositional beta.
- [ ] Lean applies the projection/kernel theorem to `PathRwQuot.toEq` and proves
  an exact criterion relating based elimination for `PathRwQuot` to local
  `AxiomK`/triviality of the loop quotient.
- [ ] Lean proves the empty and singleton reflexive raw paths are distinct but
  `RwEq`-equivalent, documenting why raw trace observability and quotient-level
  observability differ.
- [ ] Lean proves the genuine `PathRwQuot` fundamental groups of the current
  one-constructor circle and corresponding torus representation are
  contractible, while the synthetic winding quotients are noncontractible.
- [ ] Lean proves no equivalence/bridge can exist between each genuine
  circle/torus `PathRwQuot` and its nontrivial synthetic winding quotient under
  the current definitions.
- [ ] Existing public comments/docs that conflate genuine and synthetic
  fundamental groups, characterize `RwEq` solely by the current normalization
  function, or describe an impossible bridge as merely open are corrected
  precisely without deleting the synthetic constructions.
- [ ] All new generic quotient, projection/kernel, `PathRwQuot`, circle, torus,
  and no-bridge results are named, documented, public, and exported through
  `ComputationalPaths.Path`.
- [ ] The focused mathematics paper is expanded to a coherent 20–30 pages (or
  longer if genuinely needed) around: metadata criterion, projection/kernel
  theorem, universal setoid repair, indiscrete factorization, `PathRwQuot`/K
  classification, raw-versus-quotient trace analysis, and circle/torus
  genuine-versus-synthetic case studies.
- [ ] The paper's title and abstract present diagnosis plus universal repair,
  not merely the elementary empty/singleton obstruction.
- [ ] The paper explicitly proves that every ordinary setoid quotient repair
  supporting unrestricted J must identify all reflexivity metadata; it explains
  that no set-level quotient can retain visible distinctions at reflexivity.
- [ ] The paper carefully distinguishes relation-theoretic maximality,
  information-minimality, and terminal factorization direction for the
  indiscrete repair.
- [ ] The `RwEq` case study states the exact local K criterion and does not claim
  that `RwEq` always repairs or always fails to repair J.
- [ ] The circle and torus discussion clearly distinguishes genuine
  `PathRwQuot` from synthetic winding-expression quotients and explains the
  implications for previous claims and future modeling.
- [ ] The existing 37-page raw-calculus companion remains available and builds;
  it is updated only where required for factual consistency.
- [ ] The formal-artifact/reproducibility section cites a stable theorem-bearing
  commit/tag; a future Zenodo DOI is mentioned without a fake placeholder.
- [ ] Every touched Lean module contains no `sorry`, `admit`, custom `axiom`,
  decorative theorem stubs, or unacknowledged classical choice. New files have
  substantive `Path`/`RwEq` evidence.
- [ ] Targeted builds, full `lake build`, invariant checks, `git diff --check`,
  focused-paper build, and companion build all pass with clean references and
  no meaningful overfull boxes.
- [ ] An independent Inspector verifies all mathematical claims, code/paper
  correspondence, corrected documentation, and quality gates.

## Scope Boundaries

**In scope:**
- Setoid quotient repairs of metadata in a proof-irrelevant extensional
  metatheory/Lean quotient setting.
- Generic projection/kernel classification.
- Local and global K/triviality criteria for `PathRwQuot`.
- Honest analysis of the repository's genuine and synthetic circle/torus
  quotients.
- Necessary corrections to code comments, architecture documentation, and the
  main/companion papers.
- Additional Lean theory needed to make the paper materially stronger.

**Out of scope:**
- Pretending a nontrivial synthetic winding quotient is already the genuine
  `PathRwQuot` fundamental group.
- Claiming the indiscrete quotient preserves computational trace information.
- Claiming a universal quotient repair in settings without quotient exactness.
- Full HoTT, univalence, HITs, judgmental-beta classification, or a new circle
  HIT construction unless independently and fully proved.
- Deleting synthetic circle/torus quotients; they remain valuable presentations
  but must be named accurately.
- Absolute novelty claims unsupported by literature.

## Applicable Project Conventions

**Quality gate command:**
- `lake build`
- `python3 scripts/check_invariants.py`
- `git diff --check`
- Targeted builds for `MetadataRepair`, `MetadataJ`, quotient, circle, and torus
  modules.
- Clean `latexmk` builds for focused and companion manuscripts.

**Commit convention:**
- Conventional commits are preferred.
- Builder commits use `feat(paths): [B] ...` and
  `Assisted-by: OpenAI:GPT-5.6-Sol`.
- Inspector commits use `chore(paths): [I] ...` and
  `Assisted-by: OpenAI:GPT-5.6-Luna`.

**Guidelines:**
- `AGENTS.md`
- No additional `CONSTITUTION.md` or guideline directory applies.

**Rules:**
- Zero `sorry`, `admit`, and custom `axiom`.
- Genuine computational-path integration with substantive `RwEq` evidence.
- Preserve public APIs where possible, but correct demonstrably inaccurate
  mathematical descriptions.
- Distinguish raw paths, `RwEq` quotients, synthetic presentations, and ambient
  equality at every stage.
- Prefer exact theorem names and restricted claims over broad slogans.
