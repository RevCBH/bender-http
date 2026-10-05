#!/usr/bin/env bash
# Runs tests/tls_live.bend (Tls.exchange) and tests/tls_stream_live.bend
# (Tls.open / recv / close) on both lanes against tests/tls_server.py's local
# TLS servers (ports 18440..18455 on 127.0.0.1), trusting their self-signed
# certificates through SSL_CERT_FILE. Needs python3 and the openssl CLI.
#   tests/tls_live.sh
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
tmp="$(mktemp -d)"
trap 'kill "$server" 2>/dev/null || true; rm -rf "$tmp"' EXIT
python3 "$here/tls_server.py" "$tmp" 18440 > "$tmp/ready" 2> "$tmp/server.log" &
server=$!
for _ in $(seq 100); do
  grep -q ready "$tmp/ready" 2>/dev/null && break
  sleep 0.1
done
grep -q ready "$tmp/ready" || { echo "FAIL the test servers did not start"; cat "$tmp/server.log"; exit 1; }
export SSL_CERT_FILE="$tmp/trust.pem"
ulimit -n 256   # a descriptor leak per exchange shows within 300 of them
for t in tls_live tls_stream_live; do
  echo "== $t: JS lane"
  bend "$here/$t.bend" | tee "$tmp/$t.js.out"
  echo "== $t: C lane"
  bend "$here/$t.bend" -o "$tmp/$t"
  "$tmp/$t" | tee "$tmp/$t.c.out"
done
if grep -q '^FAIL' "$tmp"/*.out; then
  exit 1
fi
