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
lake build ComputationalPaths.Path.Homotopy.TopologicalNerve
lake build ComputationalPaths.Path.Homotopy.PresentedGroupoidRealization
lake build ComputationalPaths.Path.CompPath.CirclePresented
lake build ComputationalPaths.Path.CompPath.CircleTopologicalRealization
lake build ComputationalPaths.Path.CompPath.PresentedSeifertVanKampen
lake build ComputationalPaths.Path.Homotopy.Fibration
lake build ComputationalPaths.Path.CompPath.SuspensionDeep
```

The manuscript distinguishes presented computational fundamental groups,
global-rule `PathRwQuot` loop fibers, and completed expression quotients.  The
headline theorem is the proved presented SVK equivalence; the global-rule SVK
schema remains separately conditional.  The circle presentation is additionally
identified with Mathlib's topological fundamental group of `AddCircle 1`.
Every presented path groupoid also has a checked nerve/geometric realization
and homotopy-category recovery theorem. The canonical functor to the
topological fundamental groupoid is constructed and proved essentially
surjective.  The realization quotient atlas, contraction of under-category
nerves, and unique simplex lifting for the categorical universal cover are now
formalized; the remaining full-faithfulness step is the realized-covering
point-set theorem.
