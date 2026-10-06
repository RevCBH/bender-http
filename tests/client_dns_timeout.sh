#!/usr/bin/env bash
# Native DNS timeout tests now run locally on both runtimes as part of the
# resolver/CLI integration suite (no getaddrinfo shim or public DNS needed).
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
exec bash "$root/tests/cli_test.sh"
