#!/usr/bin/env sh
set -eu

usage() {
    printf 'Usage: %s [--full]\n' "$0" >&2
}

full=0
case "${1:-}" in
    "")
        ;;
    --full)
        full=1
        ;;
    *)
        usage
        exit 2
        ;;
esac

if [ "$#" -gt 1 ]; then
    usage
    exit 2
fi

repo_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$repo_root"

run() {
    printf '\n==> %s\n' "$1"
    shift
    "$@"
}

run "Checking diff whitespace" git diff --check
run "Printing Lean version" lake -R --no-ansi env lean --version
run "Building compact core module" lake --no-ansi build ComputationalPaths.Basic

if [ "$full" -eq 1 ]; then
    run "Building full library" lake --no-ansi build
else
    printf "\nSkipping full lake build by default. Run 'lake build' manually, or 'scripts/check.sh --full', when you need full validation.\n"
fi
