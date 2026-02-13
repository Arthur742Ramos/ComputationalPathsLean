# AGENTS.md — ComputationalPathsLean

## Project Overview

**The Calculus of Computational Paths** is a Lean 4 formalization of propositional equality via explicit computational paths and rewrite equality. The core idea: `Path a b` wraps Lean's `Eq` with an explicit list of rewrite steps — a trace-carrying equality inside extensional type theory. Two paths are equivalent (`RwEq`) when they normalize to the same canonical form under the LND_EQ-TRS rewrite system.

This is explicitly **not HoTT** — it's computational rewrite traces over proof-irrelevant `Eq`.

## Quick Reference

| Metric | Value |
|--------|-------|
| **Lean version** | 4.24.0 |
| **Mathlib** | v4.24.0 |
| **Repository** | https://github.com/Arthur742Ramos/ComputationalPathsLean |
| **Paper** | "The Calculus of Computational Paths" (BSL format, 93 pages) |
| **Authors** | Arthur Freitas Ramos (Microsoft), Ruy de Queiroz (UFPE), Anjolina de Oliveira (UFPE), Tiago Veras (UFRPE) |

## Invariants (MUST be maintained)

1. **Zero `sorry`** — every theorem must be fully proved
2. **Zero `axiom` declarations** — no custom axioms (Lean kernel axioms only)
3. **Genuine Path integration** — all files must use `Path` type for equalities, not bare `=`
4. **Domain-specific Step types** where appropriate (e.g., `TQFTStep`, `KnotStep`)
5. **At least one `RwEq` or multi-step `Path.trans` construction per file**

## Architecture

```
ComputationalPaths/
├── Path/
│   ├── Basic/              # Core path definitions (Path, Step, RwEq)
│   ├── Rewrite/            # LND_EQ-TRS rewrite system, confluence, termination
│   ├── OmegaGroupoid/      # Weak ω-groupoid structure
│   ├── CompPath/           # Space constructions (spheres, torus, Klein, etc.)
│   ├── Homotopy/           # Homotopy theory (160+ files)
│   ├── Algebra/            # Homological & algebraic structures (130+ files)
│   ├── Topology/           # Advanced topology, stable homotopy (80+ files)
│   ├── Category/           # Higher category theory
│   └── Logic/              # HoTT connections, modal logic
├── ComputationalPaths.lean # Root import hub
├── Main.lean               # Entry point
└── paper/                  # LaTeX paper (BSL, SAJL, and amsbook variants)
```

## Core Concepts

- **`Path a b`**: Equality proof carrying an explicit list of `Step` rewrites
- **`Step`**: 75 constructors in 8 groups (the rewrite rules of LND_EQ-TRS)
- **`RwEq`**: Equivalence of paths — two paths are equivalent when they normalize to the same canonical form
- **`PathRing`**, **`PathModule`**, etc.: Algebraic structures with Path-valued coherences

## Armada Protocol

An "armada" is a batch deployment of 5 Lean 4 formalization files on a themed mathematical topic.

**Command:** `copex fleet "prompt with {topic}" -m gpt-5.3-codex -r xhigh`

**Requirements for each file:**
- Import from `ComputationalPaths.Path.Step`, `.Basic`, `.Rewrite`
- Use `Path` type (not bare `=`)
- Domain-specific `Step` inductive types where appropriate
- `Path.trans`/`Path.symm` compositions
- At least one `RwEq` or multi-step construction
- NO `sorry`, NO `axiom`
- Minimum 150 lines of substantive content
- Files go in appropriate subdirectory (Algebra/, Topology/, Homotopy/, etc.)

**Protocol v2:** "Fix first, nuke last" — broken files get a fix fleet before deletion.

**History:** 64+ armadas completed (Feb 2026), growing from 96 to 525+ files.

## Development Commands

```bash
# Build
lake build

# Check for sorries
grep -r "sorry" --include="*.lean" . | grep -v ".lake" | grep -v "-- "

# Check for axioms  
grep -r "^axiom " --include="*.lean" . | grep -v ".lake"

# File count
find . -name "*.lean" -not -path "./.lake/*" | wc -l

# Deploy an armada
copex fleet "Create a Lean 4 file formalizing {topic}..." -m gpt-5.3-codex -r xhigh
```

## Terminology

- **Armada**: Batch of 5 themed Lean files deployed via copex fleet
- **Fleet**: A single copex fleet run (may contain multiple tasks)
- **Path integration**: Using the `Path` type genuinely, not as a shallow wrapper
- **Deepening pass**: Reviewing files to ensure genuine Path/Step/RwEq usage
- **LND_EQ-TRS**: The equational term rewriting system underlying computational paths
