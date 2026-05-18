---
name: deep-audit-certificates
description: Audit and harden scaffold-heavy ComputationalPaths Lean modules by replacing selected True/trivial/rfl placeholders with typed Path/RwEq certificate records while preserving public APIs.
---

# Deep Audit Certificates

Use this skill when a task mentions deep audit, scaffold cleanup, `True`
placeholders, `trivial`, reflexive-only theorem stubs, or book-companion
quality improvements.

## Goal

Turn weak generated scaffolds into meaningful computational-path evidence
without destabilizing broad areas of the library.

## Workflow

1. Pick a narrow set of files, usually 2-3 modules.
2. Search for weak evidence:
   - `True`
   - `trivial`
   - theorem conclusions of the form `x = x`
   - `Path.refl _` used as the only meaningful witness
3. Preserve existing public APIs when possible.
4. Add certificate-returning variants instead of changing existing structures
   unless the user explicitly asks for a breaking cleanup.
5. Validate each touched Lean module with targeted `lake build`.
6. Run `git diff --check`.

## Certificate Pattern

Prefer records that carry concrete domain data plus path coherence:

```lean
structure FooCertificate where
  domainData : Nat
  computedData : Nat
  computed_matches : Path computedData domainData
  derived_witness : Path computedData 0
  coherence :
    RwEq (Path.trans derived_witness (Path.refl 0)) derived_witness
```

Use real domain quantities where possible:

- list lengths
- generator/relation counts
- boundary values
- ranks, indices, or dimensions
- presentation words
- decomposition sizes

## What to Avoid

- Do not simply replace `True` with another always-true proposition.
- Do not add certificate fields that are only `Path x x`.
- Do not make broad rewrites across many generated files in one PR.
- Do not touch files owned by another active session.

## Validation

For each touched module:

```bash
lake build ComputationalPaths.Path.Topology.YourModule
git diff --check
```
