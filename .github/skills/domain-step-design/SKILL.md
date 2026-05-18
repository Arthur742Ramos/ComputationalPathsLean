---
name: domain-step-design
description: Design domain-specific Step types and rewrite certificates in ComputationalPaths modules without confusing them with core Path.Step rewrite rules.
---

# Domain Step Design

Use this skill when adding or reviewing domain-specific rewrite systems such as
`TQFTStep`, `KnotStep`, `SurfaceStep`, or topology/algebra operation steps.

## Core Distinction

There are two common notions of step:

- `ComputationalPaths.Step A`: base equality steps used by `Path`.
- `ComputationalPaths.Path.Step p q`: rewrite steps between computational paths.

When names may collide, qualify the base-level step as
`ComputationalPaths.Step` or `_root_.ComputationalPaths.Step`.

## Domain Step Pattern

Use a domain-specific inductive type when the file models named mathematical
operations:

```lean
inductive FooStep : FooObject → FooObject → Type
  | normalize (x : FooObject) : FooStep x x
  | compose (x : FooObject) (n : Nat) : FooStep x x
```

Then expose path-level certificates:

```lean
structure FooRewriteCertificate (x : FooObject) where
  before : Nat
  after : Nat
  trace : Path before after
  stable : RwEq (Path.trans trace (Path.refl after)) trace
```

## Guidelines

- Use domain steps to name mathematical moves, not to hide missing proofs.
- Include at least one concrete value-level `Path`, not only `Path X.carrier X.carrier`.
- Prefer `rweq_of_step (Path.Step.trans_refl_right _)` or the path tactics for
  unit cleanup after a substantive domain trace; if `Path.Step` is not in scope,
  state explicitly that the core rewrite step is intended.
- If a file also imports `ComputationalPaths.Path.Rewrite.Step`, avoid unqualified
  `Step` in ambiguous contexts.
- Keep certificates small and composable; downstream modules can combine them
  with `Path.trans` and `RwEq.trans`.

## Review Checklist

- Does the domain step encode a real operation from the module narrative?
- Does the certificate carry concrete data (`Nat`, `Int`, lists, words, counts)?
- Is there at least one nontrivial `Path.trans` or `RwEq` witness?
- Does the module still build independently with `lake build <module>`?
