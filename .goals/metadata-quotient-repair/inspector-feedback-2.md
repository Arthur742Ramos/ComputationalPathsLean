# Inspector Feedback — Iteration 2

## Verdict: FAIL

## Acceptance Criteria Check

- [x] **Metadata quotient families and universes** — the public
  `MetadataSetoidFamily`, `QuotientMetadata`, and `SetoidTotal` declarations
  remain present, and their `#check` output has the expected `max u v` and
  quotient universes.
- [x] **Empty-sensitive quotient classification** —
  `quotient_contractible_iff_nonempty_and_setoidTotal` still has the required
  inhabitance conjunct; the implementation contains both
  `Quotient.sound` and `Quotient.exact` directions and the explicit empty
  countertheorem.
- [x] **Universal metadata repair criterion** —
  `metadata_quotient_repair_criterion` still typechecks and combines the
  metadata-fiber and quotient classifications.
- [x] **Family-wide transport and empty fibers** — equality induction,
  `metadata_fibers_nonempty`, totality transport, and contractibility of every
  quotient fiber remain explicit.
- [x] **Indiscrete repair/factorization** — totality, quotient-map-preserving
  factor existence, uniqueness as a function, and the terminal direction
  remain formalized and correctly documented.
- [x] **Projection/kernel classification** — the generic reflexive projection,
  kernel, equivalence, and beta-bearing eliminator criterion remain public and
  typecheck.
- [x] **`PathRwQuot` local/global K** — `toEq`, the kernel-to-loop equivalence,
  local K, global K, and the exact elimination criteria remain present; no
  unconditional success/failure claim was introduced.
- [x] **Raw trace observability** — empty and singleton raw reflexive paths are
  unequal, while the explicit `transport_refl_beta` witness identifies them in
  `RwEq` and hence in `PathRwQuot`.
- [x] **Genuine/synthetic circle and torus results** — the current
  one-constructor circle and product torus genuine loop quotients remain
  contractible, while the synthetic winding quotients remain noncontractible.
- [x] **No-bridge theorem types** — both public theorems exclude
  `SimpleEquiv` inhabitants (via `Nonempty`) without claiming that arbitrary
  functions cannot exist.
- [ ] **Repository-wide documentation consistency** — **FAILED**.  The
  explicitly failed files from iteration 1 are corrected, and broad searches
  show the active README, `.github/copilot-instructions.md`, canonical
  `docs/ARCHITECTURE.md`/`docs/axioms.md`, focused paper, and direct circle/
  torus Lean comments now use the genuine-versus-synthetic distinction.
  However, two active source areas still undermine the requested complete
  audit:
  - `paper/main.tex:927` still says “the system is both complete and
    confluent”, and `paper/main.tex:2213` still lists “decidable rewrite
    equivalence via normalisation”.  These are in the same paper that defines
    the current `Path`/`\RwEq` story and explicitly says at lines 541--551 and
    1067--1092 that bare `Path.normalize` is only a sound invariant and that
    completeness requires an explicit completion package.  The remaining
    unqualified statements must be scoped to an expression relation such as
    `ExprRwEq` or to `CompleteStepSystem`; otherwise they continue to advertise
    the exact normalization-only characterization rejected by the goal.
  - `ComputationalPaths/Path/CompPath/MobiusBand.lean:13,38` still describes
    the `CircleCompPath` compatibility alias as a Möbius-band type obtained via
    a deformation retract (`Möbius band type (≃ S¹)` and “modeled by its
    deformation retract”), while the same file's header correctly says that
    no deformation retract is constructed and that only the synthetic winding
    model is reused.  This is an active public Lean comment/API description
    that remains internally inconsistent with the corrected carrier boundary.
- [x] **Public exports/API names** — `import ComputationalPaths.Path` and
  `#check` resolve all repair, K, trace, genuine, synthetic, and no-bridge
  declarations.  The iteration-2 Lean changes are comment/documentation
  changes; the full and targeted builds found no API break.
- [x] **Focused paper** — the clean focused article is 25 pages and covers all
  requested repair, kernel, trace, and genuine/synthetic sections.
- [x] **Title/abstract** — the focused title and abstract present diagnosis,
  universal repair, and the `PathRwQuot` boundary.
- [x] **Setoid impossibility statement** — the focused paper explicitly uses
  quotient exactness to show that successful ordinary repairs identify all
  reflexivity metadata.
- [x] **Indiscrete terminology and Prop relation** — the paper now writes
  `\top`, explicitly identifies it with Lean's Prop-valued `True` relation,
  and distinguishes maximal relation, minimal retained information, and
  terminal factorization.
- [x] **`RwEq` case study** — the focused paper states the local-K criterion
  and explicitly rejects both unconditional repair slogans.
- [x] **Circle/torus paper case study** — both focused and broad paper sources
  now label the `\mathbb Z`/`\mathbb Z^2` results as synthetic presentation
  results and state contractibility/no-bridge for the current genuine fibers,
  except for the residual unscoped normalization/completeness wording noted
  above.
- [x] **37-page companion** — the raw-calculus companion remains untouched and
  cleanly builds to 37 pages.
- [x] **Release citation** — the `metadata-quotient-repair-v1` tag exists and
  points to the theorem-bearing Builder commit `ae6dc3fa`; the bibliography
  has no fake DOI.  This tag predates the iteration-2 documentation-only
  corrections, so it is a valid theorem release but not a snapshot of all
  final documentation edits.
- [x] **Proof hygiene/axioms** — the invariant script reports zero
  `sorry`/`admit`/custom `axiom`; representative repair, K, factorization,
  trace, torus, and synthetic theorems depend only on `propext` and
  `Quot.sound`, with no `Classical.choice`.
- [x] **Listed quality gates** — all gates named in `goal.md` pass.
- [ ] **Independent verification of all claims** — **FAILED** because the
  active broad paper still contains the unscoped normalization/completeness
  claims and the MobiusBand public description remains contradictory.

## Quality Gate

- `lake build` — **PASS** (full build completed, 8701 jobs; only existing
  linter warnings).
- Targeted builds for `MetadataRepair`, `MetadataJ`, `Rewrite.Quot`,
  `CircleCompPath`, `CircleStep`, `Torus`, `TorusStep`,
  `FundamentalGroupCircle`, `FundamentalGroupTorus`, `LieGroups`,
  `KillerExamples`, `OmegaGroupoid`, and `SurfaceTopology` — **PASS**.
- `python3 scripts/check_invariants.py` — **PASS**.
- `git diff --check` against the implementation range and worktree — **PASS**.
- Clean focused-paper LaTeX build — **PASS**, 25 pages; no overfull boxes.
- Clean companion LaTeX build — **PASS**, 37 pages; no overfull boxes.
- Internal reference checks for all three manuscript sources — **PASS**,
  with no missing labels.
- Public-import `#check` and representative `#print axioms` probes — **PASS**.
- Release-tag existence/target check — **PASS** for the theorem-bearing
  `metadata-quotient-repair-v1` tag.

An additional clean build of the touched broad `paper/main.tex` was attempted.
It cannot run in this checkout because the external `BSLstyle.cls` is absent
(`LaTeX Error: File 'BSLstyle.cls' not found`).  This is not one of the
focused/companion gates listed in `goal.md`, but it should be documented or
made reproducible if `paper/main.tex` is intended as a buildable deliverable.

## Issues Found

1. The repository-wide search now passes for the specifically failed
   instruction/README/canonical-doc files and for the direct Circle/Torus
   comments, but the active broad paper still contradicts its own corrected
   normalization boundary.  The unqualified “complete and confluent” and
   “decidable rewrite equivalence via normalisation” wording must not be read
   as a theorem about the bare generated `Path.RwEq`/`Path.normalize` pair.
2. The `MobiusBandCompPath` compatibility alias is correctly described as a
   non-topological/synthetic reuse in the file header, but its public key-result
   table and definition doc still claim an actual Möbius-band deformation
   retract.  Those comments should be made consistently presentation-scoped.
3. The cited release tag is still the iteration-1 theorem commit, not the
   iteration-2 documentation-corrected commit.  This satisfies the literal
   stable-theorem-bearing-tag criterion, but a final reproducibility release
   should either cite the final commit or create a final tag containing the
   documentation audit.
4. The extra `paper/main.tex` build is blocked by a missing external class.
   The required focused and companion builds pass, so this is an additional
   reproducibility warning rather than the primary verdict.

## What Must Be Fixed (FAIL only)

1. In `paper/main.tex`, qualify or remove the remaining unscoped
   completeness/confluence/normalisation claims.  Use the actual
   `ExprRwEq`/expression fragment or an explicitly supplied
   `CompleteStepSystem`, and keep the statement that bare `Path.normalize`
   does not provide an `RwEq` converse.
2. Correct the `MobiusBand.lean` key-result table and definition comment to
   say “compatibility/presentation alias” rather than an implemented
   Möbius-band type or deformation retract.
3. Decide whether the cited release must include the iteration-2
   documentation fixes; if so, publish/cite a final theorem-bearing tag or
   commit after those corrections.
4. If `paper/main.tex` is a supported manuscript, supply/declare its
   `BSLstyle.cls` prerequisite and rerun its clean build.
