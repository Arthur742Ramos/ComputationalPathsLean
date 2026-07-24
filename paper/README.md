# Manuscript build matrix

The repository contains three manuscript sources with different build
requirements.

| Source | Role | Build prerequisites |
|---|---|---|
| `adequacy/main.tex` | Focused 25-page diagnosis and universal-repair article | Self-contained `amsart` source plus a standard TeX Live installation |
| `adequacy/companion/main.tex` | Distinct 37-page raw scoped-calculus companion | Self-contained `amsart` source plus a standard TeX Live installation |
| `main.tex` | Legacy broad computational-paths manuscript | External `BSLstyle.cls` and `BSLbibstyle.bst`, in addition to TeX Live |

The external BSL class and bibliography style are **not vendored** in this
repository. They must be obtained from their authoritative distribution under
applicable terms and made visible through `TEXINPUTS`/`BSTINPUTS` (or placed in
a local TeX search directory). Without them, building the legacy source fails
at `\documentclass{BSLstyle}`; this is an expected prerequisite failure, not a
failure of the focused or companion manuscripts. Do not substitute or copy an
unavailable third-party style file into the repository.

Build the self-contained manuscripts independently:

```bash
cd paper/adequacy
latexmk -C main.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

cd companion
latexmk -C main.tex
latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex
```

If the external BSL files are installed, the legacy manuscript can be built
from `paper/` with the analogous `latexmk` command.
