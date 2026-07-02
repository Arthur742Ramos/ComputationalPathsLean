#!/usr/bin/env python3
"""Enforce the repository's proof-hygiene invariants.

Strips Lean comments (block ``/- ... -/`` and line ``--``) before scanning, so
docstrings that *mention* forbidden tokens (e.g. "no sorry") do not trip the
guard. Exits non-zero if any real occurrence is found.

Hard invariants (fail the build):
  * zero ``sorry``
  * zero ``admit``
  * zero custom ``axiom`` declarations

Soft warnings (printed, do not fail):
  * ``native_decide`` — expands the trusted base with ``Lean.ofReduceBool`` +
    ``Lean.trustCompiler``; prefer kernel ``decide``/``rfl``/``omega``.
"""
from __future__ import annotations
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "ComputationalPaths"

HARD = {
    "sorry": re.compile(r"\bsorry\b"),
    "admit": re.compile(r"\badmit\b"),
    "axiom": re.compile(r"^\s*(noncomputable\s+)?axiom\s"),
}
SOFT = {
    "native_decide": re.compile(r"\bnative_decide\b"),
}


def strip_comments(text: str) -> str:
    text = re.sub(r"/-.*?-/", "", text, flags=re.S)
    return "\n".join(line.split("--", 1)[0] for line in text.splitlines())


def main() -> int:
    hard_hits: list[str] = []
    soft_hits: list[str] = []
    for path in SRC.rglob("*.lean"):
        if ".lake" in path.parts:
            continue
        code = strip_comments(path.read_text(encoding="utf-8", errors="ignore"))
        rel = path.relative_to(ROOT)
        for i, line in enumerate(code.splitlines(), 1):
            for name, rx in HARD.items():
                if rx.search(line):
                    hard_hits.append(f"{rel}:{i}: {name}: {line.strip()}")
            for name, rx in SOFT.items():
                if rx.search(line):
                    soft_hits.append(f"{rel}:{i}: {name}")

    if soft_hits:
        print(f"::warning::{len(soft_hits)} native_decide use(s) (soft — prefer kernel decide/rfl/omega):")
        for h in soft_hits[:50]:
            print("  " + h)

    if hard_hits:
        print(f"::error::{len(hard_hits)} invariant violation(s) found:")
        for h in hard_hits:
            print("  " + h)
        return 1

    print("invariants OK: zero sorry / admit / custom axiom in ComputationalPaths/")
    return 0


if __name__ == "__main__":
    sys.exit(main())
