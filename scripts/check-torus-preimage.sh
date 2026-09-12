#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cd "$repository_root"

lake build \
  ComputationalPaths.Path.Algebra.CertifiedIntegerMatrixPreimage \
  ComputationalPaths.Path.Topology.CertifiedTorusPreimageExistence \
  ComputationalPaths.Path.Topology.TorusConstraintApplication \
  Tests.CertifiedTorusPreimageFixtures \
  Tests.CertifiedTorusPreimageAdversarial \
  Tests.CertifiedTorusPreimageBenchmarks

diff -u Tests/CertifiedTorusPreimageFixtures.lean \
  <(python3 scripts/test-torus-preimage.py --lean)
diff -u Tests/CertifiedTorusPreimageBenchmarks.lean \
  <(python3 scripts/test-torus-preimage.py --lean --benchmark)

if rg -n '\bsorry\b|\badmit\b|^axiom |native_decide|Lean\.ofReduceBool' \
  ComputationalPaths/Path/Algebra/CertifiedIntegerMatrixPreimage.lean \
  ComputationalPaths/Path/Topology/CertifiedTorusPreimage*.lean \
  ComputationalPaths/Path/Topology/TorusConstraintApplication.lean \
  Tests/CertifiedTorusPreimage*.lean; then
  echo "Forbidden proof marker in certified torus preimage implementation" >&2
  exit 1
fi

python3 scripts/test-torus-preimage.py
git diff --check
echo "Certified torus preimage quality gate passed"
