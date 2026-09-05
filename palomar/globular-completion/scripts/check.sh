#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build Challenge Solution
cmp Challenge.lean Solution.lean
lines=$(wc -l < Challenge.lean)
bytes=$(wc -c < Challenge.lean)
test "$lines" -le 1000 && test "$bytes" -le 102400
if [ "$lines" -gt 300 ] || [ "$bytes" -gt 32768 ]; then
  echo "Audit-envelope warning: $lines lines, $bytes bytes (below hard limits)"
fi
if grep -En '(^|[[:space:]])(sorry|admit|axiom)([[:space:]]|$)|native_decide|Lean\.ofReduceBool|Lean\.trustCompiler' Challenge.lean Solution.lean scripts/*.lean; then
  echo 'Forbidden proof hole, custom axiom or evaluator escape' >&2
  exit 1
fi
lake env lean scripts/Regression.lean
report=$(lake env lean scripts/AxiomAudit.lean)
echo "$report"
AXIOM_REPORT="$report" ruby -rjson -ryaml <<'RUBY'
config = JSON.parse(File.read('comparator.json'))
meta = YAML.safe_load(File.read('formalization.yaml'), aliases: false)
names = config.fetch('theorem_names')
raise 'Wrong selection' unless names.length == 16 && names.uniq == names
raise 'Wrong modules' unless config['challenge_module'] == 'Challenge' && config['solution_module'] == 'Solution'
raise 'Wrong axiom allowance' unless config['permitted_axioms'] == ['propext', 'Quot.sound']
results = meta.fetch('status').fetch('main_results')
raise 'Metadata selection mismatch' unless results.map { |r| r['declaration'] } == names
raise 'Schema mismatch' unless meta['version'] == 'v0.4'
raise 'Classification drift' unless meta['classification'] == {'arxiv'=>['math.CT', 'cs.LO'], 'msc2020'=>['18N20', '03B38', '68V20']}
raise 'License mismatch' unless meta['project']['license'] == 'MIT' && File.read('../../LICENSE').include?('MIT License')
report = ENV.fetch('AXIOM_REPORT')
results.each do |r|
  name = r.fetch('declaration')
  suffix = if r['axioms'].empty?
    'does not depend on any axioms'
  else
    "depends on axioms: [#{r['axioms'].join(', ')}]"
  end
  raise "Axiom drift: #{name}" unless report.lines.any? { |s| s.strip == "'#{name}' #{suffix}" }
end
raise 'Untrusted axiom' if report.match?(/sorryAx|Classical.choice|Lean.ofReduceBool/)
manifest = JSON.parse(File.read('lake-manifest.json'))
mathlib = manifest.fetch('packages').find { |p| p['name'] == 'mathlib' }
raise 'Wrong Mathlib pin' unless mathlib['rev'] == 'db584cd6d46c92f209a44c0f1c829460d327499d'
manifest['packages'].each do |p|
  raise 'Unpinned dependency' unless p['type'] == 'git' && p['rev'].match?(/\A[0-9a-f]{40}\z/)
  raise 'Nonpublic dependency' unless p['url'].match?(%r{\Ahttps://github.com/[^/?#]+/[^/?#]+\z})
end
puts 'Exact declaration, axiom, metadata and manifest checks passed'
RUBY
deps=$(lake env lean --src-deps Challenge.lean)
while IFS= read -r dep; do
  case "$dep" in
    */src/lean/*|*/.lake/packages/mathlib/*) ;;
    *) echo "Unexpected direct source dependency: $dep" >&2; exit 1 ;;
  esac
done <<< "$deps"
echo "$deps"
echo 'Direct imports are allowlisted; canonical transitive dependencies are checked by the pinned verifier.'
git diff --check
echo 'Local completion checks passed; no Palomar editorial result is implied.'
