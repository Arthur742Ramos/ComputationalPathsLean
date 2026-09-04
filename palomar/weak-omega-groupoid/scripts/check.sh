#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$project_root"

expected_theorems=(
  ComputationalPaths.PalomarWeakOmegaGroupoid.trace_is_observable
  ComputationalPaths.PalomarWeakOmegaGroupoid.groupoid_laws
  ComputationalPaths.PalomarWeakOmegaGroupoid.derivation_groupoid_laws
  ComputationalPaths.PalomarWeakOmegaGroupoid.pentagon_route_counts
  ComputationalPaths.PalomarWeakOmegaGroupoid.computational_paths_form_weak_omega_groupoid_boundary
)
expected_definitions=(
  ComputationalPaths.PalomarWeakOmegaGroupoid.contractibility3
  ComputationalPaths.PalomarWeakOmegaGroupoid.contractibility4
  ComputationalPaths.PalomarWeakOmegaGroupoid.contractibilityHigher
  ComputationalPaths.PalomarWeakOmegaGroupoid.pentagon_coherence
  ComputationalPaths.PalomarWeakOmegaGroupoid.triangle_coherence
  ComputationalPaths.PalomarWeakOmegaGroupoid.interchange_coherence
  ComputationalPaths.PalomarWeakOmegaGroupoid.eckmann_hilton_coherence
  ComputationalPaths.PalomarWeakOmegaGroupoid.compPathOmegaGroupoidBoundary
)

lake build Challenge Solution

challenge_lines=$(wc -l < Challenge.lean | tr -d ' ')
challenge_bytes=$(wc -c < Challenge.lean | tr -d ' ')
if [ "$challenge_lines" -gt 300 ] || [ "$challenge_bytes" -gt 32768 ]; then
  echo "warning: Challenge.lean exceeds Palomar's 300-line/32 KiB audit-warning envelope" >&2
  echo "observed: ${challenge_lines} lines/${challenge_bytes} bytes" >&2
fi
if [ "$challenge_lines" -gt 1000 ] || [ "$challenge_bytes" -gt 102400 ]; then
  echo "Challenge.lean exceeds Palomar's hard size limit" >&2
  exit 1
fi

challenge_holes=$(grep -Ec '(^|[[:space:]])sorry([[:space:]]|$)' Challenge.lean)
if [ "$challenge_holes" -ne 12 ]; then
  echo "Challenge.lean must contain exactly twelve deliberate selected holes" >&2
  exit 1
fi
if grep -En '^[[:space:]]*(noncomputable[[:space:]]+)?axiom[[:space:]]|(^|[[:space:]])admit([[:space:]]|$)|native_decide|Lean\.ofReduceBool|Lean\.trustCompiler' \
  Challenge.lean Solution.lean scripts/*.lean; then
  echo "forbidden axiom, admission, or evaluator escape found" >&2
  exit 1
fi
if grep -En '^[[:space:]]*sorry([[:space:]]|$)' Solution.lean; then
  echo "Solution.lean contains a proof hole" >&2
  exit 1
fi

meta_step3_block=$(sed -n '/^inductive MetaStep3/,/^inductive Derivation3/p' Challenge.lean)
primitive_3_cells=$(grep -Ec '^[[:space:]]*\| ' <<< "$meta_step3_block")
if [ "$primitive_3_cells" -ne 1 ] || ! grep -Fq '| rweq_transport' <<< "$meta_step3_block"; then
  echo "MetaStep3 must expose exactly the proof-irrelevance transport generator" >&2
  exit 1
fi
if grep -En '^[[:space:]]*\| (pentagon|triangle|interchange|eckmann)' Challenge.lean Solution.lean; then
  echo "named coherences must not be primitive MetaStep3 constructors" >&2
  exit 1
fi
derived_coherences=$(grep -Ec '^  contractibility3 _ _$' Solution.lean)
if [ "$derived_coherences" -ne 4 ]; then
  echo "Solution coherence values must all route through contractibility3" >&2
  exit 1
fi
for interchange_name in 'α : Derivation2 p p' 'γ : Derivation2 p' 'β : Derivation2 q q' 'δ : Derivation2 q'; do
  if ! grep -Fq "$interchange_name" Challenge.lean; then
    echo "full four-cell interchange statement is incomplete: $interchange_name" >&2
    exit 1
  fi
done

source_dependencies=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dependency; do
  case "$dependency" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *)
      echo "Challenge import closure contains a non-allowlisted source: $dependency" >&2
      exit 1
      ;;
  esac
done <<< "$source_dependencies"

ruby -rjson -ryaml - comparator.json formalization.yaml "${expected_theorems[@]}" "${expected_definitions[@]}" <<'RUBY'
config_path, metadata_path, *names = ARGV
theorems = names.take(5)
definitions = names.drop(5)
config = JSON.parse(File.binread(config_path))
allowed_keys = %w[challenge_module solution_module theorem_names definition_names permitted_axioms enable_nanoda]
abort "Comparator contains unsupported keys" unless (config.keys - allowed_keys).empty?
abort "Comparator module pair is wrong" unless
  config["challenge_module"] == "Challenge" && config["solution_module"] == "Solution"
abort "Comparator theorem selection is wrong" unless config["theorem_names"] == theorems
abort "Comparator definition selection is wrong" unless config["definition_names"] == definitions
abort "Comparator axiom allowance is not minimal" unless config["permitted_axioms"] == ["propext"]

metadata = YAML.safe_load(File.binread(metadata_path), permitted_classes: [],
  permitted_symbols: [], aliases: false)
abort "formalization.yaml must contain one mapping" unless metadata.is_a?(Hash)
abort "Metadata version must be v0.4" unless metadata["version"] == "v0.4"
project = metadata.fetch("project")
abort "Project metadata is incomplete" unless
  project["name"].is_a?(String) && !project["name"].strip.empty? &&
  project["description"].is_a?(String) && project["license"] == "MIT" &&
  project["authors"].is_a?(Array) && project["authors"].length == 4
sources = metadata.fetch("sources")
paper = sources.find { |source| source["title"] == "Computational Paths Form a Weak ω-Groupoid: A Constructive Proof" }
abort "Accepted paper source is missing" unless paper && paper["relationship"] == "formalizes"
abort "Metadata does not identify the native related formalization" unless
  metadata.fetch("related_formalizations").any? { |item| item["id"].include?("ComputationalPathsLean/tree/") }
status = metadata.fetch("status")
abort "Status reports unresolved Solution work" unless
  status["sorry_count"] == 0 && status["sorry_in_definitions"] == 0 && status["axioms"] == ["propext"]
main_results = status.fetch("main_results")
expected = theorems + definitions
abort "Main-result selection disagrees with Comparator" unless
  main_results.map { |item| item["declaration"] } == expected
abort "Main results must point to Solution.lean" unless main_results.all? { |item| item["file"] == "Solution.lean" }
alignment = metadata.fetch("alignment")
alignment_names = alignment.fetch("statements").map { |item| item["lean"] }
abort "Alignment is missing a selected declaration" unless expected.all? { |name| alignment_names.include?(name) }
abort "Metadata contains a template sentinel" if File.binread(metadata_path).match?(/\bTEMPLATE\b/)
puts "Comparator and formalization metadata validation passed"
RUBY

axiom_report=$(lake env lean scripts/AxiomAudit.lean 2>&1)
for declaration in "${expected_theorems[@]}" "${expected_definitions[@]}"; do
  if ! grep -Fq "'$declaration'" <<< "$axiom_report"; then
    echo "Axiom report omitted $declaration" >&2
    exit 1
  fi
done
if grep -Eq 'sorryAx|Lean\.ofReduceBool|Lean\.trustCompiler|declaration uses' <<< "$axiom_report"; then
  echo "Axiom report contains an untrusted dependency" >&2
  echo "$axiom_report" >&2
  exit 1
fi
if ! grep -Fq "trace_is_observable' depends on axioms: [propext]" <<< "$axiom_report"; then
  echo "Axiom report changed: trace observability must use only propext" >&2
  exit 1
fi

if grep -En '[[:blank:]]$' Challenge.lean Solution.lean README.md formalization.yaml comparator.json scripts/*.lean scripts/*.sh; then
  echo "trailing whitespace found" >&2
  exit 1
fi

echo "$axiom_report"
echo "Palomar weak-omega-groupoid quality gate passed: Challenge.lean is ${challenge_lines} lines/${challenge_bytes} bytes"
