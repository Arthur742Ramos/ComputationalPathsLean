# Inspector Feedback — Iteration 4

## Verdict: FAIL

## Acceptance Criteria Check

- [ ] Criterion 1 — FAILED: There is still no public unconditional proof of
  `Presented.Realization.TopologicalComparisonStatement P`.  The declaration
  remains the `Prop` wrapper at
  `ComputationalPaths/Path/Homotopy/PresentedGroupoidRealization.lean:117-119`.
  Its only constructors are still conditional on
  `(topologicalComparisonFunctor P).IsEquivalence` (`:123-126`) or on
  assumed `Full` and `Faithful` instances (`:130-138`).
- [ ] Criterion 2 — FAILED: `topologicalComparisonFunctor P` still has only
  the unconditional essential-surjectivity instance
  (`PresentedGroupoidRealization.lean:101-106`).  No unconditional
  `Functor.Full` or `Functor.Faithful` declaration was added.
- [ ] Criterion 3 — FAILED: No public definition packages
  `FundamentalGroupoid (topologicalRealization P) ≌ Object P`.  The existing
  conditional theorem constructs `asEquivalence.symm` only after an assumed
  equivalence and hides it inside `Nonempty`; the new cover file does not add
  an equivalence.
- [ ] Criterion 4 — FAILED: The new code is generic over arbitrary groupoids
  and is a useful local integration of the preceding combinatorial work:
  `coreFaceIndex`, `liftCoreFace`, `liftCoreFace_starSet_iff`, and
  `nerveCoverMap_liftSimplexAtCoreFace` compile and relate a lifted simplex to
  its base simplex.  However, `CoreFaceOpen` is only a subtype of points in a
  single standard topological simplex.  The
  `coreFaceSheetHomeomorph` at
  `TopologicalNerveCover.lean:450-456` is `Homeomorph.refl _` because the
  copied face/collapse data makes the two coordinate subtypes definitionally
  identical; `coreFaceSheetHomeomorph_realize` only proves a commuting
  equation for one simplex representative.  There is still no global
  quotient-saturated open set, coverage or disjointness of sheets, descent
  through the genuine `SSet.toTop` realization quotient, local
  trivialization, `IsCoveringMap`, or edge-path/hom-level
  surjectivity/injectivity proof.  Moreover,
  `PresentedGroupoidRealization.lean` does not import this cover module
  directly, and no declaration connects these local charts to the comparison
  functor.
- [x] Criterion 5 — VERIFIED: `python3 scripts/check_invariants.py` passes
  with zero `sorry`, `admit`, or custom `axiom` declarations.  The new
  statements use actual definitions and proofs rather than assuming the
  missing global covering theorem.  The `Iff.rfl` and `Homeomorph.refl`
  facts are valid coordinate-level identities, but they do not count as
  evidence for the absent global theorem and must not be read as such.
- [x] Criterion 6 — VERIFIED: `lean-toolchain` remains
  `leanprover/lean4:v4.24.0`; `lakefile.lean` still pins Mathlib to
  `v4.24.0`, and `lake-manifest.json` and dependency inputs were unchanged.
  No unmerged upstream WIP dependency was added.
- [x] Criterion 7 — VERIFIED: All requested gates pass independently:
  targeted realization build (1688 jobs), `python3
  scripts/check_invariants.py`, `python3 paper/svk/check_stats.py`, full
  `lake build` (8719 jobs, with only pre-existing linter warnings), and both
  requested `latexmk` commands.  `git diff --check` also passes.
- [ ] Criterion 8 — FAILED: The Builder commit changed no manuscript,
  reviewer-response, inventory, statistics, or tracked-PDF source.  Those
  documents still accurately state that full faithfulness and the
  realized-covering point-set theorem are open
  (`paper/svk/main.tex:606-633`, `paper/svk/response_to_reviewer.tex:60-70`,
  and `paper/svk/README.md:44-50`).  They therefore do not report the exact
  unconditional theorem required by this goal.

## Quality Gate

- Command: `lake build ComputationalPaths.Path.Homotopy.TopologicalNerve ComputationalPaths.Path.Homotopy.PresentedGroupoidRealization`
- Result: PASS (1688 jobs)
- Command: `python3 scripts/check_invariants.py`
- Result: PASS (zero `sorry` / `admit` / custom `axiom`)
- Command: `python3 paper/svk/check_stats.py`
- Result: PASS
- Command: `lake build`
- Result: PASS (8719 jobs; only pre-existing linter warnings)
- Command: `cd paper/svk && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && latexmk -pdf -interaction=nonstopmode -halt-on-error response_to_reviewer.tex`
- Result: PASS (both PDFs up to date)
- Additional check: `git diff --check`
- Result: PASS

## Issues Found

The Builder added a real and compiling intermediate layer: a base core face
can be lifted using a chosen under-category fiber element, the lifted
structure satisfies the copied core-face equation, and the simplicial
projection commutes with the chosen simplex chart.  This is useful
combinatorial/topological input for a future proof.

It does not yet identify actual open subsets of the quotient realization.
The local coordinate subtype and its identity homeomorphism do not establish
that different simplex representatives glue consistently, that the selected
stars are saturated under the realization quotient, or that sheets are
disjoint and collectively cover a neighborhood.  Consequently the claimed
local chart identities cannot be used to obtain a genuine `IsCoveringMap` or
the topological edge-path theorem.

The central comparison API is unchanged: there are no `Full`/`Faithful`
instances, no public equivalence definition, and no unconditional
`TopologicalComparisonStatement` theorem.  The paper's continued
“remaining/open” language is correct, but confirms that the requested goal
has not been reached.

## What Must Be Fixed

1. Prove an axiom-free global realization result: quotient-saturated open
   stars, coverage, disjoint lifted sheets, and genuine local
   homeomorphisms (or an equally strong general edge-path substitute) for
   arbitrary presented path groupoids.
2. Derive unconditional reusable `Functor.Full` and `Functor.Faithful`
   declarations for `topologicalComparisonFunctor P`.
3. Define the resulting
   `FundamentalGroupoid (topologicalRealization P) ≌ Object P` publicly and
   prove the unconditional `TopologicalComparisonStatement P`.
4. Only after those declarations exist, update the SVK manuscript,
   reviewer response, inventory, statistics, and tracked PDFs to the exact
   proved result, then rerun every quality gate.
