---
name: armada-review
description: Review armada/fleet-generated Lean files for ComputationalPaths invariants, duplicate modules, shallow Path usage, and scaffold-heavy theorem stubs.
---

# Armada Review

Use this skill when reviewing generated batches, fleet output, or "armada"
modules before merging or during a cleanup pass.

## Review Priorities

1. Build the touched modules first.
2. Check project invariants:
   - no `sorry`
   - no custom `axiom`
   - genuine `Path` usage
   - at least one `RwEq` or multi-step `Path.trans`
   - domain-specific `Step` types where appropriate
3. Find shallow scaffolds:
   - `True` fields with no certificate counterpart
   - `trivial` as the main proof payload
   - theorem stubs proving only `x = x`
   - unused imported theory
4. Check for duplicates or near-duplicates before adding new modules.

## Fix First, Nuke Last

Do not delete broken or shallow files as the first response. Prefer:

1. repair imports and build failures
2. add meaningful certificates or theorem statements
3. consolidate duplicates only when a better module already exists
4. delete only with clear evidence and user approval

## Suggested Commands

```bash
lake build ComputationalPaths.Path.Some.Module
rg "\bsorry\b|^axiom |: True|:= trivial|:= rfl" ComputationalPaths
git diff --check
```

The `rfl` alternative is intentionally broad: use it to find candidates, then
inspect the theorem statement to distinguish legitimate definitional proofs from
reflexive-only stubs. On Windows PowerShell, use `rg` rather than Unix `grep` for
reliable searches.

## PR Guidance

Keep armada review PRs focused:

- one theme or directory at a time
- list modules touched
- report targeted builds
- explicitly name deferred files
