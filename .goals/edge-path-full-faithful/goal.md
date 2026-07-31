# Goal: Prove the topological edge-path comparison

## User Request

"ok let's do it as well" — complete the remaining full-faithfulness theorem
after constructing the canonical functor from a presented path groupoid to the
topological fundamental groupoid of its geometric nerve realization.

## Refined Goal

Prove, in Lean 4.24 with Mathlib v4.24, that the canonical functor
`Presented.Realization.topologicalComparisonFunctor P` is full and faithful for
every presented computational-path groupoid. Combine those results with the
already-proved essential surjectivity to construct an unconditional category
equivalence
`FundamentalGroupoid (topologicalRealization P) ≌ Object P` and discharge
`TopologicalComparisonStatement P`. The proof must formalize the missing
topological edge-path theorem or an equally general axiom-free substitute.

## Acceptance Criteria

- [ ] A public unconditional Lean declaration proves
      `Presented.Realization.TopologicalComparisonStatement P` for every
      presentation `P`, with no extra hypotheses or typeclass assumptions.
- [ ] `topologicalComparisonFunctor P` has unconditional `Functor.Full` and
      `Functor.Faithful` instances (or stronger reusable declarations from which
      those instances follow).
- [ ] The resulting equivalence is explicitly packaged as a public definition,
      not merely asserted through a proposition-only wrapper.
- [ ] The proof is general for arbitrary presented path groupoids; a
      circle-only, finite-only, connected-only, or finitely-presented result does
      not satisfy the goal.
- [ ] No `sorry`, `admit`, custom `axiom`, hidden bridge assumption, or
      success-shaped placeholder is introduced.
- [ ] The Lean 4.24 / Mathlib v4.24 pins remain unchanged, and no unmerged
      upstream WIP dependency is added.
- [ ] `python3 scripts/check_invariants.py`, `python3
      paper/svk/check_stats.py`, the targeted realization builds, and full
      `lake build` all succeed.
- [ ] The SVK manuscript, reviewer response, module inventory, statistics, and
      tracked PDFs are updated from "open/full-faithfulness remaining" to the
      exact proved result without overclaiming.

## Scope Boundaries

**In scope:**
- Reusable topology/simplicial infrastructure needed for edge paths,
  homotopies, open-star arguments, covering-space arguments, or topological
  van Kampen.
- New Lean modules under `ComputationalPaths/Path/Homotopy/`.
- Refactoring the existing `TopologicalNerve` construction when needed.
- Paper/SVK source, statistics, and generated PDF updates directly caused by
  the theorem.

**Out of scope:**
- Weakening or changing `TopologicalComparisonStatement`.
- Replacing Mathlib's genuine `SSet.toTop` or topological
  `FundamentalGroupoid` with a synthetic stand-in.
- Assuming full faithfulness through a typeclass, proposition, or global axiom.
- Updating Lean/Mathlib versions or importing the unmerged generated van
  Kampen PR.
- Treating the already-proved circle comparison or essential surjectivity as
  completion of the general theorem.

## Applicable Project Conventions

**Quality gate command:**
- `lake build ComputationalPaths.Path.Homotopy.TopologicalNerve ComputationalPaths.Path.Homotopy.PresentedGroupoidRealization`
- `python3 scripts/check_invariants.py`
- `python3 paper/svk/check_stats.py`
- `lake build`
- `cd paper/svk && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex && latexmk -pdf -interaction=nonstopmode -halt-on-error response_to_reviewer.tex`

**Commit convention:**
- Conventional commits with the Goal role marker:
  `type(scope): [B/I] description` (at most 72 characters).
- Builder trailer: `Assisted-by: OpenAI:GPT-5.6-Sol`
- Inspector trailer: `Assisted-by: OpenAI:GPT-5.6-Luna`
- Also include
  `Co-authored-by: Copilot App <223556219+Copilot@users.noreply.github.com>`.

**Guidelines:**
- `AGENTS.md`
- `.github/copilot-instructions.md`

**Rules:**
- Maintain zero `sorry`, zero `admit`, and zero custom `axiom`.
- Use genuine computational `Path`/`RwEq` evidence in every new project module.
- Do not infer `RwEq` from normalization equality without a proved complete
  step system.
- Preserve public APIs and avoid vacuous theorem/certificate scaffolding.
- Keep manuscript numerical claims synchronized with
  `paper/svk/check_stats.py`.
- Retain Lean and Mathlib v4.24.0.
