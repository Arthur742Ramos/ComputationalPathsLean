#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build GlobularCompletion
lake env lean scripts/SemanticAudit.lean
lake env lean scripts/GlobularAudit.lean
if grep -En '\bsorry\b|^[[:space:]]*axiom[[:space:]]' GlobularCompletion.lean scripts/SemanticAudit.lean scripts/GlobularAudit.lean; then
  echo 'Unresolved proof or custom axiom in repair' >&2
  exit 1
fi
echo 'Repair checks passed. This is NOT Palomar submission readiness.'
