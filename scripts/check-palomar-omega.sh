#!/usr/bin/env bash
set -euo pipefail

# Compatibility entry point retained for the former omega-groupoid package.
repository_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
exec "$repository_root/scripts/check-palomar-associativity.sh" "$@"
