---
name: paper-companion-style
description: Keep ComputationalPaths modules suitable as book/paper companion material with clear mathematical narrative, named constructions, and meaningful computational-path evidence.
---

# Paper Companion Style

Use this skill when adding or deepening modules intended to accompany the
ComputationalPaths paper or book-style exposition.

## Module Shape

Each substantial module should have:

- a short module docstring explaining the mathematical object
- references or background when the topic is standard
- named structures for the main constructions
- named certificates or theorems for computational-path evidence
- minimal imports consistent with the topic

## Evidence Style

Prefer statements that expose computational content:

```lean
structure PresentationCertificate where
  generators : Nat
  relations : Nat
  generator_count : Path generators expectedGenerators
  relation_count : Path relations expectedRelations
  coherence : RwEq (Path.trans generator_count (Path.refl expectedGenerators)) generator_count
```

Avoid book-companion anti-patterns:

- theorem statements that only prove reflexivity
- `True` fields with no surrounding mathematical data
- string witnesses instead of typed data
- opaque names like `foo_theorem_1`
- broad imports used only to make a file look substantial

## Naming

- Types and structures: `PascalCase`
- Definitions: `camelCase` or established local convention
- Theorems and certificates: descriptive `snake_case` if the file already uses
  theorem-style naming
- Certificate records: `FooCertificate`, `FooCoherence`, or
  `FooRewriteCertificate`

## Validation

For code changes, run the smallest meaningful build:

```bash
lake build ComputationalPaths.Path.Area.ModuleName
```

For documentation-only companion edits, run:

```bash
git diff --check
```
