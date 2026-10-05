#!/usr/bin/env bash
# Runs tests/transport_live.bend (X.tls) on both lanes against
# tests/tls_server.py's local TLS servers (ports 48940..48955 on 127.0.0.1),
# trusting their self-signed certificate through SSL_CERT_FILE. Needs python3
# and the openssl CLI. Prints PASS / FAIL per case; exits 1 on any FAIL.
#   tests/transport_live.sh
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tmp="$(mktemp -d)"
trap 'kill "$server" 2>/dev/null || true; rm -rf "$tmp"' EXIT
python3 "$here/tls_server.py" "$tmp" 48940 > "$tmp/ready" 2> "$tmp/server.log" &
server=$!
for _ in $(seq 100); do
  grep -q ready "$tmp/ready" 2>/dev/null && break
  sleep 0.1
done
grep -q ready "$tmp/ready" || { echo "FAIL the test servers did not start"; cat "$tmp/server.log"; exit 1; }
export SSL_CERT_FILE="$tmp/trust.pem"
echo "== transport_live: JS lane"
bend "$here/transport_live.bend" | grep -v 'bend update' | tee "$tmp/js.out"
echo "== transport_live: C lane"
bend "$here/transport_live.bend" -o "$tmp/transport_live"
"$tmp/transport_live" | tee "$tmp/c.out"
if grep -q '^FAIL' "$tmp"/*.out || ! grep -q '^ALL PASS' "$tmp/js.out" || ! grep -q '^ALL PASS' "$tmp/c.out"; then
  exit 1
fi
