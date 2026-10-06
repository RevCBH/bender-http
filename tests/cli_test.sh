#!/usr/bin/env bash
# Local DNS + HTTP integration tests on both Bend runtimes; no internet.
set -euo pipefail
cd "$(dirname "$0")/.."
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
"${BEND:-bend}" cli.bend -o "$out/bender-http"
"${BEND:-bend}" tests/resolver_local.bend -o "$out/resolver"
python3 -B tests/cli_test.py "$out" "${BEND:-bend}"
