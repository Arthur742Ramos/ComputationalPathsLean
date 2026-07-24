# Inspector Feedback — Iteration 1

## Verdict: FAIL

## Acceptance Criteria Check

- [x] **Metadata quotient families and universes** — `MetadataRepair.lean`
  defines `MetadataSetoidFamily`, `QuotientMetadata`, and `SetoidTotal`.
  `#check` confirms the expected `max u v` family universe and quotient fiber
  universe.
- [x] **Empty-sensitive quotient classification** — the Lean theorem
  `quotient_contractible_iff_nonempty_and_setoidTotal` explicitly includes
  `Nonempty X`; the chosen-center theorem uses `Quotient.sound` for
  sufficiency and the necessity proof uses `Quotient.exact`.  The standalone
  empty-carrier countertheorem is present.
- [x] **Universal metadata repair criterion** —
  `metadata_quotient_repair_criterion` combines the metadata-fiber theorem
  with the chosen-center quotient theorem.
- [x] **Family-wide transport and empty fibers** —
  `metadata_fibers_nonempty`, `metadata_setoid_total_all_fibers`, and
  `metadata_quotient_fibers_contractible` explicitly handle equality
  induction and show why a supplied `m₀` rules out empty indexed fibers.
- [x] **Indiscrete repair and factorization** — relation inclusion, existence,
  uniqueness as a function, the terminal factor direction, and the reverse
  factor for a total setoid are all formalized.  The comments and paper use
  maximal-relation/minimal-information/terminal terminology rather than the
  false initiality direction.
- [x] **Generic projection/kernel theorem** —
  `ReflexiveEqualityProjection`, `ReflexivityKernel`, `projectionKernelEquiv`,
  and `projection_kernel_criterion` typecheck with the expected beta-bearing
  eliminator.
- [x] **`PathRwQuot`/local-K classification** — the `toEq` projection,
  kernel-to-loop equivalence, local and global K predicates, and exact
  elimination equivalences are public and compile.  The theorem is conditional
  on local K, not a blanket claim about `RwEq`.
- [x] **Raw versus quotient traces** — empty and singleton raw paths are
  formally unequal, while `raw_empty_rweq_singleton_reflexive_path` and the
  quotient equality use an explicit `Step.transport_refl_beta` witness.
- [x] **Genuine circle/torus and synthetic noncontractibility** —
  the current one-constructor `Circle` and product `Torus` genuine loop
  quotients are contracted by an explicit trace induction; the synthetic
  circle and torus quotients are shown noncontractible via their `Int` and
  `Int × Int` equivalences.
- [x] **No-bridge theorem types** — the formal statements correctly exclude
  `SimpleEquiv` inhabitants (wrapped in `Nonempty`) and do not overclaim that
  arbitrary noninvertible functions are impossible.
- [ ] **Public documentation/comments** — **FAILED**.  Important active
  comments still advertise the old, false genuine results or still define
  `RwEq` by normalization alone:
  - `.github/copilot-instructions.md:5,11,286` still says the key results are
    genuine `π₁(S¹) ≃ ℤ`/`π₁(T²) ≃ ℤ×ℤ` and that `RwEq` means equal
    normalization.
  - `ComputationalPaths/Examples/FundamentalGroupTorus.lean:4` still says it
    proves `π₁(T²) ≅ ℤ × ℤ`, and line 350 treats
    `circleLoop ≈ refl` as a contradiction with `π₁(S¹) ≅ ℤ`.  Under the
    current definitions the new theorem proves the genuine loop quotient is
    contractible and the current `RwEq` explicitly identifies the singleton
    reflexive trace with the empty trace, so this is mathematically false, not
    merely a naming issue.
  - `ComputationalPaths/Path/Homotopy/LieGroups.lean:137,465-498` still says
    that `SO(2)` is identified directly with the one-constructor `Circle` and
    that the inherited fundamental group is `ℤ`.  Its new header caveat does
    not remove the contradictory body and summary claims.
  - Active source comments in `Path/Homotopy/KillerExamples.lean`,
    `Path/OmegaGroupoid.lean`, `Path/Topology/SurfaceTopology.lean`, and
    `Path/Algebra/FreeGroupProperties.lean` continue to advertise genuine
    circle/torus `π₁` results without the synthetic qualification.  At
    minimum, each claim must be qualified or corrected consistently with the
    new theorem.
- [x] **Public exports and naming** — `ComputationalPaths.Path` imports
  `MetadataRepair`; direct `#check` calls through that public import resolve
  the repair, K, and no-bridge theorems.
- [x] **Focused paper length and coverage** — the clean focused build is 25
  pages and contains the requested repair, kernel, trace, and
  genuine/synthetic sections.
- [x] **Title and abstract** — both now present diagnosis plus universal
  repair and the `PathRwQuot` boundary.
- [x] **Set-level impossibility result** — the paper explicitly states that
  successful ordinary exact setoid repairs identify all reflexivity metadata
  and explains the role of quotient exactness.
- [x] **Indiscrete terminology in the paper** — maximality,
  information-minimality, and terminal factor direction are distinguished.
- [x] **`RwEq` case study in the paper** — the exact local-K criterion is
  stated without an always-repairs/always-fails slogan.
- [x] **Circle/torus case study in the paper** — the focused article itself
  clearly separates the current genuine quotients from synthetic winding
  presentations and states the no-equivalence result.
- [x] **37-page companion preservation** — the untouched companion builds and
  remains 37 pages.
- [x] **Release citation** — `MetadataJSoftware2026` cites
  `metadata-quotient-repair-v1`, and the tag resolves to the Builder commit;
  no fake DOI is present.
- [x] **Proof hygiene** — the touched Lean files contain no declarations of
  `sorry`, `admit`, or custom `axiom`; the apparent `axiom K` matches are
  comments only.  Key theorem axiom reports contain only `propext` and
  `Quot.sound`, with no `Classical.choice`.
- [x] **Quality gates** — all required gates below passed.
- [ ] **Independent verification of all claims** — **FAILED** because the
  active documentation contradictions above remain after the Builder change.

## Quality Gate

- `lake build` — **PASS** (full build completed, 8701 jobs).
- Focused targets
  (`MetadataRepair`, `MetadataJ`, `Rewrite.Quot`, `CircleCompPath`,
  `CircleStep`, `Torus`, `TorusStep`, and `Examples.FundamentalGroupCircle`)
  — **PASS**.
- `python3 scripts/check_invariants.py` — **PASS**.
- `git diff --check HEAD~1` and `git diff --check` — **PASS**.
- `latexmk -C && latexmk -pdf -interaction=nonstopmode -halt-on-error
  main.tex` in `paper/adequacy` — **PASS**, 25 pages, no overfull-box
  diagnostics.
- The same clean command in `paper/adequacy/companion` — **PASS**, 37 pages,
  no overfull-box diagnostics.
- Public-import `#check` and key-theorem `#print axioms` probes — **PASS**.
- The release tag `metadata-quotient-repair-v1` points at the Builder commit
  `ae6dc3fa` (the verified implementation commit) — **PASS**.

## Issues Found

1. The repository-wide correction is incomplete.  The new module proves that
   the current genuine circle and torus loop quotients are contractible, but
   several active source comments and project instructions still advertise
   those same quotients as `ℤ` and `ℤ × ℤ`.  The torus example's claimed
   contradiction is directly refuted by the new raw singleton/empty `RwEq`
   theorem.
2. The normalization warning was added to `AGENTS.md` and
   `docs/ARCHITECTURE.md`, but the active `.github/copilot-instructions.md`
   still teaches the opposite definition of `RwEq`.  This leaves a directly
   discoverable project instruction semantically wrong.
3. `paper/adequacy/README.md` is stale: it still calls the article a
   “Metadata-fiber paper”, says it is 15–20 pages, and names only
   `MetadataJ.lean` as the Lean counterpart.  The built article is 25 pages
   and its new formal counterpart includes `MetadataRepair.lean`.  In the
   article itself, line 1955 also calls `MetadataRepair.lean` the “companion
   module”, which is confusing because the separately preserved 37-page raw
   companion is `paper/adequacy/companion/main.tex`.
4. The paper writes the indiscrete setoid relation as
   `\nabla_X(x,y)=\Unit`.  The Lean `Setoid` relation is `Prop`-valued and the
   formal implementation uses `True`; the prose should use `\top`/`True` (or
   explicitly say “the proposition represented by `Unit`”) to avoid a
   type-level mismatch in the stated definition.

## What Must Be Fixed (FAIL only)

1. Audit all active (non-archived) source comments, README/instruction files,
   and architecture docs for circle/torus and `RwEq` claims.  Qualify the
   synthetic winding-expression models explicitly, remove the impossible
   genuine `π₁ ≃ ℤ` claims, and state the current genuine contractibility
   where appropriate.  In particular fix the files and lines listed above.
2. Update `paper/adequacy/README.md` and the formal-verification wording so
   the focused article, the new `MetadataRepair.lean` module, and the distinct
   37-page companion are named accurately.
3. Correct the indiscrete-relation notation in the paper, then rerun the full
   Lean, invariant, whitespace, axiom, focused-paper, and companion gates.
