# Automation & Agents

This file is kept for backward compatibility; the canonical Codex CLI instructions live in `AGENTS.md`.

This repository is set up for interactive development with the Codex CLI and a
handful of lightweight build helpers. The sections below summarise what each
agent/tool is responsible for and when to invoke it.

## Coding agent (Codex CLI)
- **Purpose:** interactive code editing, documentation updates, refactors, and
  exploratory formalisation work in Lean.
- **Typical flow:** outline a plan, perform targeted edits (prefer
  `apply_patch` for single files), and finish with a build or relevant checks.
  When tackling larger features, favour an incremental loop:
  1. Sketch the next small milestone (update the plan or jot a quick checklist).
  2. Implement just that slice of work and run `.\lake.cmd build`.
  3. Commit immediately once the build goes green before moving on.
  4. If you already know the next step, keep iterating-even after pushing-until
     the user explicitly pauses you or you've achieved a substantial chunk of work.
- **When to use:** any time you need new definitions, proofs, documentation, or
  review feedback inside the repository.

## Build agent (`.\lake.cmd build`)
- **Purpose:** type-check the project and ensure the Lean kernel accepts every
  proof.
- **How to run:** invoke `.\lake.cmd build` from the repository root. The shim
  forwards to the toolchain selected via `elan`, so no additional PATH changes
  are required.
- **When to use:** after non-trivial edits, before submitting a PR, or whenever
  you need assurance that the current state compiles.

## Executable runner (`.\lake.cmd exe computational_paths`)
- **Purpose:** sanity-check the demo executable, which prints the library
  version marker.
- **When to use:** optional verification after bumping `libraryVersion` or
  wiring the library into downstream tooling.

## Formatting / linting
- Lean's formatter (`lake fmt`) is not currently enforced, but running it before
  large changes helps minimise incidental diffs.
- The simplifier linter will warn about unused simp arguments during builds;
  prefer trimming those hints when they appear.
- **Zero-warning policy:** The build should remain warning-free. Address any
  linter warnings (e.g., `unnecessarySimpa`) immediately.

## Tips for new contributors
- Skim `README.md` for the latest project status and roadmap.
- Keep doc updates (like this file) in sync with code changes when adding new
  capabilities.
- Reference Lean files via `import ComputationalPaths` in downstream projects to
  pick up the bundled modules.
