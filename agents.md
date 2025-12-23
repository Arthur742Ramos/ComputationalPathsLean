# Automation & Agents

## Continuity Ledger (compaction-safe)
Maintain a single Continuity Ledger for this workspace in "CONTINUITY.md". The ledger is the canonical session briefing designed to survive context compaction; do not rely on earlier chat text unless it's reflected in the ledger.

### How it works
- At the start of every assistant turn: read "CONTINUITY.md", update it to reflect the latest goal/constraints/decisions/state, then proceed with the work.
- Update "CONTINUITY.md" again whenever any of these change: goal, constraints/assumptions, key decisions, progress state (Done/Now/Next), or important tool outcomes.
- Keep it short and stable: facts only, no transcripts. Prefer bullets. Mark uncertainty as "UNCONFIRMED" (never guess).
- If you notice missing recall or a compaction/summary event: refresh/rebuild the ledger from visible context, mark gaps "UNCONFIRMED", ask up to 1-3 targeted questions, then continue.

### "functions.update_plan" vs the Ledger
- "functions.update_plan" is for short-term execution scaffolding while you work (a small 3-7 step plan with pending/in_progress/completed).
- "CONTINUITY.md" is for long-running continuity across compaction (the "what/why/current state"), not a step-by-step task list.
- Keep them consistent: when the plan or state changes, update the ledger at the intent/progress level (not every micro-step).

### In replies
- Begin with a brief "Ledger Snapshot" (Goal + Now/Next + Open Questions). Print the full ledger only when it materially changes or when the user asks.

### "CONTINUITY.md" format (keep headings)
- Goal (incl. success criteria):
- Constraints/Assumptions:
- Key decisions:
- State:
  - Done:
  - Now:
  - Next:
- Open questions (UNCONFIRMED if needed):
- Working set (files/ids/commands):

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
