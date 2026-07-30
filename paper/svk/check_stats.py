#!/usr/bin/env python3
"""Reproduce source statistics quoted in the SVK manuscript."""

from __future__ import annotations

import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SRC = ROOT / "ComputationalPaths"

SVK_CORE = [
    SRC / "Path/Basic/Core.lean",
    SRC / "Path/Rewrite/RwEq.lean",
    SRC / "Path/Rewrite/ScopedCompletion.lean",
    SRC / "Path/Homotopy/FundamentalGroup.lean",
    SRC / "Path/Homotopy/PresentedFundamentalGroup.lean",
    SRC / "Path/Homotopy/PresentedGroupoidRealization.lean",
    SRC / "Path/CompPath/CircleScoped.lean",
    SRC / "Path/CompPath/CirclePresented.lean",
    SRC / "Path/CompPath/CircleTopologicalRealization.lean",
    SRC / "Path/CompPath/ClassicalPresentationsScoped.lean",
    SRC / "Path/CompPath/ScopedSeifertVanKampen.lean",
    SRC / "Path/CompPath/PresentedSeifertVanKampen.lean",
    SRC / "Path/CompPath/PushoutCompPath.lean",
    SRC / "Path/CompPath/PushoutPaths.lean",
    SRC / "Path/CompPath/PushoutSVKInstances.lean",
    SRC / "Path/CompPath/FigureEight.lean",
    SRC / "Path/CompPath/SuspensionDeep.lean",
    SRC / "Path/HIT/Sphere.lean",
    SRC / "Path/Homotopy/Fibration.lean",
    SRC / "Path/TypeTheory/QuotientPathInduction.lean",
    SRC / "Path/TypeTheory/MetadataRepair.lean",
]

TACTIC = re.compile(
    r"\b(?:path_auto!?|path_simp|path_rfl|path_normalize|"
    r"path_cancel_left|path_cancel_right|path_congr_left|path_congr_right)\b"
)
DECL = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(theorem|lemma|def|abbrev|instance|example)\s+([A-Za-z0-9_'.]+)\b",
    re.MULTILINE,
)
BOUNDARY = re.compile(
    r"^\s*(?:@\[[^\]]+\]\s*)?"
    r"(?:(?:private|protected|noncomputable|unsafe)\s+)*"
    r"(?:theorem|lemma|def|abbrev|structure|class|inductive|instance|example|"
    r"namespace|section|end)\b",
    re.MULTILINE,
)


def strip_comments(text: str) -> str:
    """Remove nested Lean block comments and line comments, preserving lines."""

    out: list[str] = []
    i = 0
    depth = 0
    in_string = False
    while i < len(text):
        pair = text[i : i + 2]
        char = text[i]
        if depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
        elif not in_string and pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif not in_string and pair == "--":
            while i < len(text) and text[i] != "\n":
                out.append(" ")
                i += 1
        else:
            out.append(char)
            if char == '"' and (i == 0 or text[i - 1] != "\\"):
                in_string = not in_string
            i += 1
    return "".join(out)


def declaration_blocks(text: str) -> list[tuple[str, str, str]]:
    clean = strip_comments(text)
    declarations = list(DECL.finditer(clean))
    blocks: list[tuple[str, str, str]] = []
    for declaration in declarations:
        next_boundary = BOUNDARY.search(clean, declaration.end())
        end = next_boundary.start() if next_boundary else len(clean)
        blocks.append(
            (
                declaration.group(1),
                declaration.group(2),
                clean[declaration.start() : end],
            )
        )
    return blocks


def main() -> None:
    lean_files = sorted(SRC.rglob("*.lean"))
    lean_lines = sum(
        len(path.read_text(encoding="utf-8", errors="ignore").splitlines())
        for path in lean_files
    )

    hard_patterns = {
        "sorry": re.compile(r"\bsorry\b"),
        "admit": re.compile(r"\badmit\b"),
        "axiom": re.compile(r"^\s*(?:noncomputable\s+)?axiom\s", re.MULTILINE),
    }
    hard_counts = dict.fromkeys(hard_patterns, 0)
    repository_blocks: list[tuple[str, str, str]] = []
    for path in lean_files:
        text = path.read_text(encoding="utf-8", errors="ignore")
        clean = strip_comments(text)
        for name, pattern in hard_patterns.items():
            hard_counts[name] += len(pattern.findall(clean))
        repository_blocks.extend(declaration_blocks(text))

    repository_theorems = [
        (kind, name, block)
        for kind, name, block in repository_blocks
        if kind in {"theorem", "lemma"}
    ]
    repository_tactic_theorems = [
        name
        for _, name, block in repository_theorems
        if TACTIC.search(block)
    ]
    repository_tactic_percentage = (
        100 * len(repository_tactic_theorems) / len(repository_theorems)
        if repository_theorems
        else 0
    )
    repository_tactic_declarations = [
        f"{kind} {name}"
        for kind, name, block in repository_blocks
        if TACTIC.search(block)
    ]
    repository_declaration_percentage = (
        100 * len(repository_tactic_declarations) / len(repository_blocks)
        if repository_blocks
        else 0
    )

    core_blocks: list[tuple[str, str, str]] = []
    core_lines = 0
    for path in SVK_CORE:
        text = path.read_text(encoding="utf-8")
        core_lines += len(text.splitlines())
        core_blocks.extend(declaration_blocks(text))

    theorem_blocks = [
        (kind, name, block)
        for kind, name, block in core_blocks
        if kind in {"theorem", "lemma"}
    ]
    tactic_theorems = [
        name for _, name, block in theorem_blocks if TACTIC.search(block)
    ]
    tactic_declarations = [
        f"{kind} {name}"
        for kind, name, block in core_blocks
        if TACTIC.search(block)
    ]
    total_theorems = len(theorem_blocks)
    theorem_percentage = (
        100 * len(tactic_theorems) / total_theorems if total_theorems else 0
    )
    declaration_percentage = (
        100 * len(tactic_declarations) / len(core_blocks) if core_blocks else 0
    )

    print(f"repository Lean files: {len(lean_files)}")
    print(f"repository Lean lines: {lean_lines}")
    print(
        "repository proof-hygiene tokens: "
        + ", ".join(f"{name}={count}" for name, count in hard_counts.items())
    )
    print(f"repository theorem/lemma declarations: {len(repository_theorems)}")
    print(
        "repository theorem/lemma declarations with direct path-tactic use: "
        f"{len(repository_tactic_theorems)} "
        f"({repository_tactic_percentage:.3f}%)"
    )
    print(f"repository total declarations audited: {len(repository_blocks)}")
    print(
        "repository declarations of any kind with direct path-tactic use: "
        f"{len(repository_tactic_declarations)} "
        f"({repository_declaration_percentage:.3f}%)"
    )
    print(f"SVK audit modules: {len(SVK_CORE)}")
    print(f"SVK audit lines: {core_lines}")
    print(f"SVK theorem/lemma declarations: {total_theorems}")
    print(
        "SVK theorem/lemma declarations with direct path-tactic use: "
        f"{len(tactic_theorems)} ({theorem_percentage:.3f}%)"
    )
    print(f"SVK total declarations audited: {len(core_blocks)}")
    print(
        "SVK declarations of any kind with direct path-tactic use: "
        f"{len(tactic_declarations)} ({declaration_percentage:.3f}%)"
    )
    if tactic_declarations:
        print("direct path-tactic users:")
        for declaration in tactic_declarations:
            print(f"  {declaration}")


if __name__ == "__main__":
    main()
