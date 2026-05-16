## Summary

<!-- Briefly describe the change and whether it is Lean source, docs, metadata, CI, or paper-source maintenance. -->

## Stack

<!-- If this PR depends on another PR or branch, name it here. Otherwise write "Not stacked." -->

## Checklist

- [ ] I ran the smallest relevant Lean check, or this is docs/metadata-only and I ran the lightweight sanity check.
- [ ] Lean source changes do not introduce new `sorry` placeholders.
- [ ] New assumptions or axioms are avoided, or `docs/axioms.md` is updated.
- [ ] Expected warnings are explained; new unexpected warnings are fixed.
- [ ] Docs-only or metadata-only changes do not touch Lean source files.

## Validation

<!-- List commands run, for example:
lake -R --no-ansi env lean --version
lake --no-ansi build ComputationalPaths.Basic
-->
