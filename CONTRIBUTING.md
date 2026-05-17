# Contributing

Thank you for helping improve `ComputationalPathsLean`. This repository is a
Lean 4 companion repository for computational paths, so contributions should
preserve proof hygiene and keep repository metadata clear for readers.

## Local setup

Install [elan](https://github.com/leanprover/elan), clone the repository, and
let Lake use the pinned toolchain from `lean-toolchain`.

```bash
lake -R --no-ansi env lean --version
lake build
```

For quick metadata or documentation changes, use the lightweight validation
wrapper for your shell before opening a PR:

```bash
# Windows / PowerShell
scripts\check.ps1

# Unix shells / GitHub Actions style runners
scripts/check.sh
```

These wrappers run `git diff --check`, print the pinned Lean version through
Lake, and build `ComputationalPaths.Basic`.

For Lean source changes, build the smallest affected module first, then run the
full `lake build` when practical.

## Proof and source hygiene

- Do not add new `sorry` placeholders.
- Avoid new global `axiom` declarations. If an assumption is unavoidable, keep
  it explicit and update `docs/axioms.md`.
- Prefer `Path` and `RwEq` reasoning for equality developments, following the
  conventions in `AGENTS.md` and the source-local README files.
- Prefer small imports over broad root imports unless a module intentionally
  exposes a larger surface.
- Keep generated artifacts, local build outputs, and scratch notes out of
  commits.

## Documentation expectations

- Keep stable reader-facing documentation under `docs/`.
- Use `docs/archive/` for historical audits or generated run outputs that must
  remain in the repository.
- Do not reproduce book text in repository documentation. Link to repository
  files and summarize only the maintained Lean entrypoints or metadata.
- If a change affects assumptions, build instructions, or repository layout,
  update the relevant documentation in the same PR.

## Pull requests

- Keep PRs focused and describe whether the change is Lean source, docs,
  metadata, CI, or paper-source maintenance.
- If a PR is stacked on another branch or PR, state the stack in the PR body.
- For docs-only or metadata-only PRs, avoid touching Lean source files.
- Include the checks you ran in the PR body.
