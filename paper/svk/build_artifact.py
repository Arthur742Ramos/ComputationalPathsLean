#!/usr/bin/env python3
"""Build the standalone Lean artifact deposited with the SVK paper."""

from __future__ import annotations

import argparse
import hashlib
import re
import subprocess
import tempfile
import zipfile
from pathlib import Path

from check_stats import SVK_CORE


ROOT = Path(__file__).resolve().parents[2]
DEFAULT_OUTPUT = ROOT / "paper" / "svk" / "dist"
VERSION_RE = re.compile(r"^[0-9]+\.[0-9]+\.[0-9]+$")


def git_bytes(*args: str) -> bytes:
    return subprocess.check_output(["git", *args], cwd=ROOT)


def git_text(*args: str) -> str:
    return git_bytes(*args).decode("utf-8").strip()


def ensure_clean() -> None:
    for args in (("diff", "--quiet"), ("diff", "--cached", "--quiet")):
        if subprocess.run(["git", *args], cwd=ROOT, check=False).returncode:
            raise SystemExit(
                "Refusing to archive tracked changes. Commit the artifact source first."
            )


def commit_file(commit: str, path: str) -> bytes:
    return git_bytes("show", f"{commit}:{path}")


def module_path(module: str) -> str:
    return module.replace(".", "/") + ".lean"


def imported_local_modules(source: str) -> list[str]:
    imports: list[str] = []
    for raw_line in source.splitlines():
        line = raw_line.split("--", 1)[0].strip()
        if not line.startswith("import "):
            continue
        imports.extend(
            name
            for name in line.removeprefix("import ").split()
            if name.startswith("ComputationalPaths.")
        )
    return imports


def dependency_closure(commit: str, entry_paths: list[str]) -> list[str]:
    pending = list(entry_paths)
    closure: set[str] = set()
    while pending:
        path = pending.pop()
        if path in closure:
            continue
        source = commit_file(commit, path).decode("utf-8")
        closure.add(path)
        pending.extend(module_path(module) for module in imported_local_modules(source))
    return sorted(closure)


def entry_module_names(entry_paths: list[str]) -> list[str]:
    return [path.removesuffix(".lean").replace("/", ".") for path in entry_paths]


def render_readme(
    version: str,
    commit: str,
    entry_count: int,
    dependency_count: int,
) -> str:
    total = entry_count + dependency_count
    return f"""# ComputationalPathsLean SVK Lean Artifact {version}

This archive contains the Lean 4 source relevant to the manuscript:

> *The Seifert-van Kampen Theorem via Computational Paths: A Formalized
> Approach to Computing Fundamental Groups*

It is a curated, standalone build artifact, not a copy of the full repository.
It contains the {entry_count} paper entry modules listed in
`ENTRY_MODULES.txt`, their {dependency_count} transitive local dependencies
({total} Lean files total), the Lean/Lake configuration, the MIT license, and
the invariant checker. It does **not** contain the manuscript or reviewer
response.

## Source

- Repository: <https://github.com/Arthur742Ramos/ComputationalPathsLean>
- Release: <https://github.com/Arthur742Ramos/ComputationalPathsLean/releases/tag/v{version}>
- Commit: `{commit}`
- Lean: `4.24.0`
- Mathlib: `v4.24.0`

## Build

```bash
lake update
lake build
python3 scripts/check_invariants.py
```

The default Lake target builds `SVKArtifact.lean`, whose imports are the exact
paper entry set.

## Scope

The archive includes:

- proof-relevant presented path groupoids and their fundamental groups;
- the presented Seifert-van Kampen group equivalence;
- circle and nontrivial figure-eight specializations;
- the topological circle comparison with Mathlib's
  `FundamentalGroup (AddCircle 1) 0`;
- the simplicial nerve and genuine Mathlib geometric realization of every
  presented path groupoid;
- the unconditional equivalence between the original presented groupoid and
  the topological fundamental groupoid of that realization;
- the quotient atlas, contractible categorical universal cover, descended open
  stars, covering-space theorem, and path/homotopy lifting used in that proof;
- the global `PathRwQuot` collapse analysis and obstruction theorems;
- scoped presentation completions for the other named examples;
- glue naturality, the low-degree fibration sequence, and sphere results.

## License

MIT. See `LICENSE`.
"""


def render_theorem_manifest() -> str:
    return """# Headline Lean declarations

## Presented fundamental groups and SVK

- `ComputationalPaths.Path.Presented.groupoid`
- `ComputationalPaths.Path.Presented.PiOne`
- `ComputationalPaths.Path.CompPath.CirclePresented.piOneEquivInt`
- `ComputationalPaths.Path.CompPath.PresentedSeifertVanKampen.presentedSeifertVanKampenGroupEquiv`
- `ComputationalPaths.Path.CompPath.PresentedSeifertVanKampen.figureEightPresentedPiOneGroupEquiv`
- `ComputationalPaths.Path.CompPath.PresentedSeifertVanKampen.figureEightPresented_nontrivial`

## Topological circle comparison

- `ComputationalPaths.Path.CompPath.CircleTopologicalRealization.isCoveringMap_circleCover`
- `ComputationalPaths.Path.CompPath.CircleTopologicalRealization.topologicalPiOneEquivInt`
- `ComputationalPaths.Path.CompPath.CircleTopologicalRealization.presentedCircleTopologicalPiOneGroupEquiv`

## General topological realization

- `ComputationalPaths.Path.Presented.Realization.nerve`
- `ComputationalPaths.Path.Presented.Realization.topologicalRealization`
- `ComputationalPaths.Path.Presented.Realization.hoNerveIso`
- `ComputationalPaths.Path.Presented.Realization.topologicalComparisonFunctor`
- `ComputationalPaths.Path.Presented.Realization.topologicalComparisonFunctor_full`
- `ComputationalPaths.Path.Presented.Realization.topologicalComparisonFunctor_faithful`
- `ComputationalPaths.Path.Presented.Realization.topologicalFundamentalGroupoidEquivalence`
- `ComputationalPaths.Path.Presented.Realization.topologicalComparisonStatement`
- `ComputationalPaths.Path.TopologicalNerve.realizationAtlas_isQuotientMap`
- `ComputationalPaths.Path.TopologicalNerve.contractibleSpace_nerve_of_isInitial`
- `ComputationalPaths.Path.TopologicalNerve.nerveCoverCertificate`
- `ComputationalPaths.Path.TopologicalNerve.isCoveringMap_nerveCoverMap`
- `ComputationalPaths.Path.TopologicalNerve.nerveRealizationHomEquiv`

## Pushout naturality and target analysis

- `ComputationalPaths.Path.CompPath.Pushout.glue_natural_square_rweq`
- `ComputationalPaths.Path.CompPath.Pushout.glue_natural_rearranged_rweq`
- `ComputationalPaths.Path.CompPath.PushoutSVKInstances.AmalgamationOnlyObstruction.hasPushoutSVKEncodeDecode_impossible`
- `ComputationalPaths.Path.CompPath.PushoutSVKInstances.CollapsedFullTarget.seifertVanKampenFullEquiv_collapsed`

## Scoped completions

- `ComputationalPaths.Path.ScopedCompletion.equivNormal`
- `ComputationalPaths.Path.CompPath.circleScopedPiOneEquivInt`
- `ComputationalPaths.Path.CompPath.torusScopedPiOneEquivIntProd`
- `ComputationalPaths.Path.CompPath.kleinBottleScopedPiOneEquivIntProd`
- `ComputationalPaths.Path.CompPath.realProjective2ScopedPiOneEquivZ2`
- `ComputationalPaths.Path.CompPath.lensScopedPiOneEquivZp`
- `ComputationalPaths.Path.CompPath.ScopedSeifertVanKampen.scopedSeifertVanKampenEquiv`

## Global quotient, sphere, and fibration

- `ComputationalPaths.Path.QuotientPathInduction.pathRwQuot_loop_contractible`
- `ComputationalPaths.Path.QuotientPathInduction.pathRwQuotLoopEquivUnit`
- `ComputationalPaths.Path.CompPath.sphereN_piOne_equiv_unit`
- `ComputationalPaths.Path.Fibration.lowDegreeFibrationSequence`
"""


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8", newline="\n")


def write_manifest(stage: Path) -> None:
    lines = []
    for path in sorted(p for p in stage.rglob("*") if p.is_file()):
        if path.name == "MANIFEST.sha256":
            continue
        digest = hashlib.sha256(path.read_bytes()).hexdigest()
        lines.append(f"{digest}  {path.relative_to(stage).as_posix()}")
    write_text(stage / "MANIFEST.sha256", "\n".join(lines) + "\n")


def write_zip(stage: Path, archive: Path, package_name: str) -> None:
    archive.parent.mkdir(parents=True, exist_ok=True)
    with zipfile.ZipFile(
        archive, "w", compression=zipfile.ZIP_DEFLATED, compresslevel=9
    ) as output:
        for path in sorted(p for p in stage.rglob("*") if p.is_file()):
            relative = path.relative_to(stage).as_posix()
            info = zipfile.ZipInfo(f"{package_name}/{relative}", (1980, 1, 1, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            output.writestr(info, path.read_bytes(), compresslevel=9)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--version", required=True, help="semantic version, e.g. 0.2.0")
    parser.add_argument(
        "--output-dir",
        type=Path,
        default=DEFAULT_OUTPUT,
        help=f"archive destination (default: {DEFAULT_OUTPUT.relative_to(ROOT)})",
    )
    args = parser.parse_args()

    if not VERSION_RE.fullmatch(args.version):
        raise SystemExit("--version must have MAJOR.MINOR.PATCH form")
    ensure_clean()

    commit = git_text("rev-parse", "HEAD")
    entry_paths = [path.relative_to(ROOT).as_posix() for path in SVK_CORE]
    closure = dependency_closure(commit, entry_paths)
    entry_set = set(entry_paths)
    dependencies = [path for path in closure if path not in entry_set]
    modules = entry_module_names(entry_paths)
    package_name = f"ComputationalPathsLean-SVK-Lean-Artifact-{args.version}"
    archive = args.output_dir.resolve() / f"{package_name}.zip"

    with tempfile.TemporaryDirectory(prefix="svk-artifact-") as temporary:
        stage = Path(temporary) / package_name
        stage.mkdir()
        for path in closure:
            target = stage / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(commit_file(commit, path))

        for path in (
            "LICENSE",
            "lean-toolchain",
            "lake-manifest.json",
            "scripts/check_invariants.py",
        ):
            target = stage / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(commit_file(commit, path))

        write_text(
            stage / "ENTRY_MODULES.txt",
            "\n".join(path.removeprefix("ComputationalPaths/") for path in entry_paths)
            + "\n",
        )
        write_text(stage / "SOURCE_COMMIT.txt", commit + "\n")
        write_text(
            stage / "SVKArtifact.lean",
            "\n".join(f"import {module}" for module in modules) + "\n",
        )
        write_text(
            stage / "lakefile.lean",
            f"""import Lake

open Lake DSL

package «computational_paths_svk_artifact» where
  version := v!"{args.version}"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.24.0"

lean_lib ComputationalPaths

@[default_target]
lean_lib SVKArtifact
""",
        )
        write_text(
            stage / "README.md",
            render_readme(args.version, commit, len(entry_paths), len(dependencies)),
        )
        write_text(stage / "THEOREM_MANIFEST.md", render_theorem_manifest())
        write_manifest(stage)
        write_zip(stage, archive, package_name)

    digest = hashlib.sha256(archive.read_bytes()).hexdigest()
    print(f"archive: {archive}")
    print(f"source commit: {commit}")
    print(f"entry modules: {len(entry_paths)}")
    print(f"transitive local dependencies: {len(dependencies)}")
    print(f"Lean files: {len(closure)}")
    print(f"sha256: {digest}")


if __name__ == "__main__":
    main()
