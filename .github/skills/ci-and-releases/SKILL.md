---
name: ci-and-releases
description: A lightweight checklist for CI, toolchain bumps, and version/release hygiene for the ComputationalPaths Lean 4 project (Lake + lean-action CI).
---

# CI & Releases

## Local CI Mirror

```bash
# Build
lake build

# Run executable
lake exe computational_paths

# Clean rebuild
lake clean && lake build
```

## Version Bump

1. Update `ComputationalPaths/Basic.lean` (`libraryVersion`)
2. Build + run exe to confirm

## Toolchain Bump

1. Edit `lean-toolchain`
2. Build; run `lake update` if dependencies need repinning
3. Build again

## CI Configuration

GitHub Actions uses `leanprover/lean-action@v1`:

```yaml
# .github/workflows/lean_action_ci.yml
name: Lean Action CI

on:
  push:
    branches: [main]
  pull_request:
  workflow_dispatch:

permissions:
  contents: read

concurrency:
  group: lean-action-ci-${{ github.ref }}
  cancel-in-progress: true

jobs:
  build:
    name: Lake build
    runs-on: ubuntu-latest
    steps:
      - name: Check out repository
        uses: actions/checkout@v4
      - name: Build with lean-action
        uses: leanprover/lean-action@v1
        with:
          lake-package-directory: "."
          use-github-cache: "true"
          use-mathlib-cache: "true"
          build: "true"
```
