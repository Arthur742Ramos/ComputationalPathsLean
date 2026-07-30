# SVK revision package

This directory contains the revised manuscript and point-by-point response to
Reviewer 1.

## Build

```bash
cd paper/svk
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error response_to_reviewer.tex
```

Generated deliverables:

- `main.pdf` — revised manuscript
- `response_to_reviewer.pdf` — response letter

## Reproduce source claims

```bash
python3 paper/svk/check_stats.py
python3 scripts/check_invariants.py

lake build ComputationalPaths.Path.CompPath.PushoutCompPath
lake build ComputationalPaths.Path.CompPath.PushoutSVKInstances
lake build ComputationalPaths.Path.CompPath.ScopedSeifertVanKampen
lake build ComputationalPaths.Path.CompPath.ClassicalPresentationsScoped
lake build ComputationalPaths.Path.Homotopy.PresentedFundamentalGroup
lake build ComputationalPaths.Path.CompPath.CirclePresented
lake build ComputationalPaths.Path.CompPath.PresentedSeifertVanKampen
lake build ComputationalPaths.Path.Homotopy.Fibration
lake build ComputationalPaths.Path.CompPath.SuspensionDeep
```

The manuscript distinguishes presented computational fundamental groups,
global-rule `PathRwQuot` loop fibers, and completed expression quotients.  The
headline theorem is the proved presented SVK equivalence; the global-rule SVK
schema remains separately conditional.
