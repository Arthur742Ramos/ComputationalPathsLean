#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

lake build
lake build ComputationalPaths.Path.OmegaGroupoid.PalomarStatement
lake env lean Challenge.lean
lake env lean Solution.lean

challenge_lines=$(wc -l < Challenge.lean)
challenge_bytes=$(wc -c < Challenge.lean)
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "Challenge.lean exceeds Palomar's 1,000-line/100 KiB limit" >&2
  echo "observed: ${challenge_lines} lines/${challenge_bytes} bytes" >&2
  exit 1
fi

if [ "$(rg -n '\bsorry\b' Challenge.lean | wc -l | tr -d ' ')" -ne 1 ]; then
  echo "Challenge.lean must contain exactly one deliberate statement-side sorry" >&2
  exit 1
fi

if rg -n '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
  Solution.lean ComputationalPaths/Path/OmegaGroupoid/PalomarStatement.lean; then
  echo "forbidden proof marker found in the selected proof boundary" >&2
  exit 1
fi

if rg -n '^axiom |native_decide|Lean\.ofReduceBool' \
  Challenge.lean Solution.lean ComputationalPaths/Path/OmegaGroupoid/PalomarStatement.lean; then
  echo "forbidden axiom or evaluator escape found in the selected boundary" >&2
  exit 1
fi

ruby -rjson -e '
  config = JSON.parse(File.binread("comparator.json"))
  abort "NanoDa replay is disabled" unless config["enable_nanoda"] == true
  expected = ["ComputationalPaths.Path.PalomarOmegaGroupoid.main_result"]
  abort "Comparator theorem target is wrong" unless config["theorem_names"] == expected
  expected_axioms = ["propext", "Quot.sound", "Classical.choice"]
  abort "Unexpected permitted axioms" unless config["permitted_axioms"] == expected_axioms
  puts "Comparator configuration validation passed"
'

git diff --check

echo "Palomar omega quality gate passed: Challenge.lean is ${challenge_lines} lines/${challenge_bytes} bytes"
