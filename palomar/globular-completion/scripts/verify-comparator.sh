#!/usr/bin/env bash
set -euo pipefail

project_root=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)
cache_root=${PALOMAR_COMPARATOR_CACHE:-"$project_root/.cache/palomar-comparator"}
bin_dir="$cache_root/bin"
comparator_dir="$cache_root/comparator"
lean4export_dir="$cache_root/lean4export"
nanoda_dir="$cache_root/nanoda"

# Reproducible verifier rehearsal pins (previously exercised on this repository).
# This is not a Palomar-hosted run; its exact tool revisions are explicit.
comparator_commit=575674928e239f5bc452aab72d1dd7b0f1326494
lean4export_commit=15f6055e299ad5b89345e533cc2192f4cc00f659
landrun_commit=811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
nanoda_commit=68d5ca9db226849b41a6fff59d796ff19d0a8840

for required_command in cargo git go lake python3; do
  command -v "$required_command" >/dev/null 2>&1 || {
    echo "error: $required_command is required to run Comparator" >&2
    exit 1
  }
done

mkdir -p "$cache_root" "$bin_dir"

checkout_exact() {
  local repository=$1
  local destination=$2
  local commit=$3
  if [ ! -d "$destination/.git" ]; then
    git clone --filter=blob:none "$repository" "$destination"
  fi
  git -C "$destination" fetch --depth 1 origin "$commit"
  git -C "$destination" checkout --detach "$commit"
}

checkout_exact https://github.com/leanprover/lean4export.git "$lean4export_dir" "$lean4export_commit"
checkout_exact https://github.com/leanprover/comparator.git "$comparator_dir" "$comparator_commit"
checkout_exact https://github.com/robsimmons/nanoda_lib.git "$nanoda_dir" "$nanoda_commit"

project_toolchain=$(tr -d '[:space:]' < "$project_root/lean-toolchain")
lean4export_toolchain=$(tr -d '[:space:]' < "$lean4export_dir/lean-toolchain")
if [ "$project_toolchain" != "$lean4export_toolchain" ]; then
  echo "error: project and lean4export toolchains do not match" >&2
  exit 1
fi

GOBIN="$bin_dir" go install "github.com/zouuup/landrun/cmd/landrun@$landrun_commit"
(cd "$comparator_dir" && lake build comparator)
(cd "$lean4export_dir" && lake build lean4export)
(cd "$nanoda_dir" && cargo build --release --locked)

cd "$project_root"
lake exe cache get Mathlib.Data.List.Basic
COMPARATOR_LEAN4EXPORT="$lean4export_dir/.lake/build/bin/lean4export" \
COMPARATOR_NANODA="$nanoda_dir/target/release/nanoda_bin" \
COMPARATOR_LANDRUN="$bin_dir/landrun" \
  lake env "$comparator_dir/.lake/build/bin/comparator" comparator.json

