#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

expected_theorems=(
  ComputationalPaths.Path.PalomarAssociativity.assocStep_wellFounded
  ComputationalPaths.Path.PalomarAssociativity.assoc_normalizes
  ComputationalPaths.Path.PalomarAssociativity.rightComb_irreducible
  ComputationalPaths.Path.PalomarAssociativity.assoc_reduces_confluent
  ComputationalPaths.Path.PalomarAssociativity.assoc_rwEq_iff_freeSemigroup_eq
  ComputationalPaths.Path.PalomarAssociativity.assoc_rwEq_iff_assocQuotient_eq
  ComputationalPaths.Path.PalomarAssociativity.pentagon_route_counts
  ComputationalPaths.Path.PalomarAssociativity.pentagon_routes_distinct
)

lake build Challenge Solution
python3 scripts/check_invariants.py

challenge_lines=$(wc -l < Challenge.lean | tr -d ' ')
challenge_bytes=$(wc -c < Challenge.lean | tr -d ' ')
if [ "$challenge_lines" -gt 300 ] || [ "$challenge_bytes" -gt 32768 ]; then
  echo "Challenge.lean exceeds Palomar's warning-free 300-line/32 KiB envelope" >&2
  echo "observed: ${challenge_lines} lines/${challenge_bytes} bytes" >&2
  exit 1
fi

if [ "$(sed -n '1p' Challenge.lean)" != "import Mathlib.Algebra.Free" ]; then
  echo "Challenge.lean must have the single narrow Mathlib.Algebra.Free import" >&2
  exit 1
fi
if [ "$(rg -c '^import ' Challenge.lean)" -ne 1 ]; then
  echo "Challenge.lean must contain exactly one direct import" >&2
  exit 1
fi

challenge_holes=$(rg -c '^[[:space:]]*sorry[[:space:]]*$' Challenge.lean)
if [ "$challenge_holes" -ne 8 ]; then
  echo "Challenge.lean must contain exactly eight selected theorem holes" >&2
  exit 1
fi

if rg -n '\badmit\b|^[[:space:]]*(noncomputable[[:space:]]+)?axiom[[:space:]]|native_decide|Lean\.ofReduceBool' \
  Challenge.lean Solution.lean; then
  echo "forbidden axiom, admission, or evaluator escape found" >&2
  exit 1
fi
if rg -n '\bsorry\b' Solution.lean; then
  echo "Solution.lean contains a proof hole" >&2
  exit 1
fi

source_dependencies=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|"$repository_root/.lake/packages/mathlib/"*) ;;
    *)
      echo "Challenge import closure contains a non-allowlisted source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$source_dependencies"

ruby -rjson -ryaml - comparator.json formalization.yaml "${expected_theorems[@]}" <<'RUBY'
config_path, metadata_path, *expected = ARGV
config = JSON.parse(File.binread(config_path))
required_keys = %w[challenge_module solution_module theorem_names permitted_axioms]
allowed_keys = required_keys + %w[definition_names enable_nanoda]
abort "Comparator keys are incomplete" unless (required_keys - config.keys).empty?
abort "Comparator contains unsupported keys" unless (config.keys - allowed_keys).empty?
abort "Challenge module is wrong" unless config["challenge_module"] == "Challenge"
abort "Solution module is wrong" unless config["solution_module"] == "Solution"
abort "Comparator theorem selection is wrong" unless config["theorem_names"] == expected
abort "Comparator must not leave definitions unspecified" unless config["definition_names"] == []
abort "NanoDa replay must be enabled" unless config["enable_nanoda"] == true
allowed_axioms = ["propext", "Quot.sound", "Classical.choice"]
abort "Unexpected permitted axioms" unless config["permitted_axioms"] == allowed_axioms

metadata = YAML.safe_load(
  File.binread(metadata_path),
  permitted_classes: [],
  permitted_symbols: [],
  aliases: false
)
abort "formalization.yaml must contain one mapping" unless metadata.is_a?(Hash)
abort "Metadata version must be v0.4" unless metadata["version"] == "v0.4"
project = metadata.fetch("project")
abort "Project name is missing" unless project["name"].is_a?(String) && !project["name"].strip.empty?
description = project["description"]
abort "Project description is missing" unless description.is_a?(String) && description.strip.length.between?(1, 10_000)
abort "Repository licence metadata must match MIT LICENSE" unless project["license"] == "MIT"
abort "Project authors are missing" unless project["authors"].is_a?(Array) && !project["authors"].empty?
maintainers = project["responsible_maintainers"]
abort "Responsible maintainers are missing" unless maintainers.is_a?(Array) && !maintainers.empty?
abort "Substantive repositories should omit the thin-wrapper repository block" if metadata.key?("repository")

sources = metadata["sources"]
abort "Sources are missing" unless sources.is_a?(Array) && !sources.empty?
source_relationships = %w[formalizes adapts independently-proves background other]
source_types = ["paper", "book", "web discussion", "folklore", "original-proof", "other"]
sources.each do |source|
  abort "Every source needs a title" unless source["title"].is_a?(String) && !source["title"].strip.empty?
  abort "Noncanonical source relationship" unless source_relationships.include?(source["relationship"])
  abort "Noncanonical source type" if source.key?("type") && !source_types.include?(source["type"])
end
substantive = sources.map { |source| source["relationship"] } & %w[formalizes adapts independently-proves]
abort "Metadata does not identify a substantive source relationship" if substantive.empty?

status = metadata.fetch("status")
abort "Status must report no solution sorries" unless status["sorry_count"] == 0 && status["sorry_in_definitions"] == 0
abort "Status axiom inventory is wrong" unless status["axioms"] == allowed_axioms
main_results = status.fetch("main_results")
abort "Metadata main-result declarations disagree with Comparator" unless main_results.map { |item| item["declaration"] } == expected
abort "Every main result must point to Solution.lean" unless main_results.all? { |item| item["file"] == "Solution.lean" }
expected_result_axioms = [
  ["propext", "Classical.choice", "Quot.sound"],
  ["propext", "Quot.sound"],
  ["propext"],
  ["propext", "Quot.sound"],
  ["propext", "Quot.sound"],
  ["propext", "Quot.sound"],
  [],
  ["propext", "Quot.sound"]
]
abort "Per-result axiom inventories are not exact" unless main_results.map { |item| item["axioms"] } == expected_result_axioms

alignment = metadata.fetch("alignment")
abort "Alignment namespace is wrong" unless alignment["namespace"] == "ComputationalPaths.Path.PalomarAssociativity"
abort "Alignment declarations disagree with Comparator" unless alignment.fetch("statements").map { |item| item["lean"] } == expected

serialized = File.binread(metadata_path)
abort "Metadata contains a template sentinel" if serialized.match?(/\bTEMPLATE\b/)
puts "Comparator and formalization metadata validation passed"
RUBY

axiom_report=$(lake env lean scripts/PalomarAxiomAudit.lean 2>&1)
for theorem_name in "${expected_theorems[@]}"; do
  if ! grep -Fq "'$theorem_name'" <<< "$axiom_report"; then
    echo "Axiom report omitted $theorem_name" >&2
    exit 1
  fi
done
if grep -Eq 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler|declaration uses' <<< "$axiom_report"; then
  echo "Axiom report contains an untrusted dependency" >&2
  echo "$axiom_report" >&2
  exit 1
fi

git diff --check

echo "$axiom_report"
echo "Palomar associativity quality gate passed: Challenge.lean is ${challenge_lines} lines/${challenge_bytes} bytes"
