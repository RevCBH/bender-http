#!/usr/bin/env bash
# Live tests of examples/fetch.bend (and so of the whole client) against
# public endpoints, on both lanes: the JS lane (`bend examples/fetch.bend --`)
# and the C lane (a binary built from it). Needs internet; depends on
# example.com, httpbin.org and badssl.com being up.
#   tests/client_live.sh            # both lanes
#   tests/client_live.sh js         # one lane
# Prints PASS / FAIL per case, then ALL PASS (exit 0) or SOME FAIL (exit 1).
set -u
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
lanes=("${@:-js c}")
fails=0

bend "$root/examples/fetch.bend" -o "$tmp/fetch" >/dev/null 2>&1 || { echo "FAIL build"; exit 1; }

run() { # lane args... -> output in $tmp/out, exit code in $rc
  if [ "$lane" = js ]; then
    timeout 120 bend "$root/examples/fetch.bend" -- "$@" >"$tmp/out" 2>&1
  else
    timeout 120 "$tmp/fetch" "$@" >"$tmp/out" 2>&1
  fi
  rc=$?
  grep -v 'bend update' "$tmp/out" >"$tmp/o" || true
}

# expect NAME RC PATTERN... -- ARGS: exit code RC and every pattern (grep -E) found
expect() {
  local name="$1" want_rc="$2"; shift 2
  local pats=()
  while [ "$1" != "--" ]; do pats+=("$1"); shift; done
  shift
  local t0=${EPOCHREALTIME/./}
  run "$@"
  local ms=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
  local ok=1
  [ "$rc" = "$want_rc" ] || ok=0
  for p in "${pats[@]}"; do grep -qE -- "$p" "$tmp/o" || ok=0; done
  if [ $ok = 1 ]; then
    echo "PASS [$lane] $name (${ms} ms): $(head -1 "$tmp/o")"
  else
    echo "FAIL [$lane] $name (rc=$rc, ${ms} ms):"; head -c 800 "$tmp/o" | sed 's/^/    /'
    fails=$((fails + 1))
  fi
}

for lane in ${lanes[@]}; do
  expect "http example.com" 0 '^HTTP/1.1 200' 'Example Domain' -- http://example.com/
  expect "https example.com" 0 '^HTTP/1.1 200' 'Example Domain' -- https://example.com/
  expect "httpbin get" 0 '^HTTP/1.1 200' '"url": "https://httpbin.org/get"' -- https://httpbin.org/get
  expect "binary 1024" 0 '^HTTP/1.1 200' '^<1024 bytes of binary>$' -- https://httpbin.org/bytes/1024
  expect "chunked 50000" 0 '^HTTP/1.1 200' '^Transfer-Encoding: chunked' '^<50000 bytes of binary>$' -- \
    'https://httpbin.org/stream-bytes/50000?chunk_size=1000'
  expect "plain chunked 50000" 0 '^HTTP/1.1 200' '^<50000 bytes of binary>$' -- \
    'http://httpbin.org/stream-bytes/50000?chunk_size=1000'
  expect "redirect/3 not followed" 0 '^HTTP/1.1 302' '^Location: /relative-redirect/2' -- https://httpbin.org/redirect/3
  expect "redirect/3 followed" 0 '^HTTP/1.1 200' '"url": "https://httpbin.org/get"' -- --follow https://httpbin.org/redirect/3
  expect "absolute redirects followed" 0 '^HTTP/1.1 200' '"url": "http://httpbin.org/get"' -- \
    --follow http://httpbin.org/absolute-redirect/2
  expect "redirect/11 too many" 1 'more than 10 redirects' -- --follow https://httpbin.org/redirect/11
  expect "status 204" 0 '^HTTP/1.1 204' -- https://httpbin.org/status/204
  expect "HEAD https" 0 '^HTTP/1.1 200' '^Content-Type: text/html' -- -X HEAD https://example.com/
  expect "HEAD http" 0 '^HTTP/1.1 200' '^Content-Length: [0-9]+' -- -X HEAD http://httpbin.org/get
  expect "POST echo" 0 '^HTTP/1.1 200' '"data": "hello bend"' '"Content-Type": "text/plain"' '"X-Test": "a:b"' -- \
    -H 'Content-Type: text/plain' -H 'X-Test: a:b' -d 'hello bend' https://httpbin.org/post
  expect "POST utf8 body" 0 '"data": "h\\u00e9llo"' '"Content-Length": "6"' -- -d 'héllo' https://httpbin.org/post
  expect "PUT plain" 0 '^HTTP/1.1 200' '"data": "x=1"' -- -X PUT -d 'x=1' http://httpbin.org/put
  expect "303 POST becomes GET" 0 '^HTTP/1.1 200' '"url": "https://httpbin.org/get"' -- \
    --follow -d 'x' 'https://httpbin.org/redirect-to?url=/get&status_code=303'
  expect "307 POST stays POST" 0 '^HTTP/1.1 200' '"data": "kept"' -- \
    --follow -d 'kept' 'https://httpbin.org/redirect-to?url=/post&status_code=307'
  expect "max bytes" 1 'larger than the limit' -- --max 100 https://example.com/
  expect "plain timeout" 1 'timed out' -- --timeout 1000 http://httpbin.org/delay/3
  expect "tls timeout" 1 'timed out' -- --timeout 1000 https://httpbin.org/delay/3
  expect "closed port" 1 'connect error 111' -- http://127.0.0.1:1/
  expect "expired certificate" 1 'TLS error 71: .*certificate has expired' -- https://expired.badssl.com/
  expect "wrong host" 1 'TLS error 71: .*mismatch' -- https://wrong.host.badssl.com/
  expect "unresolvable name" 1 'DNS error' -- http://no-such-host.invalid/
  expect "bad URL" 1 'bad URL: unsupported scheme' -- ftp://example.com/
  expect "bad header" 1 'bad request' -- -H 'Host: x' https://example.com/
  expect "trailing-dot host verifies" 0 '^HTTP/1.1 200' 'Example Domain' -- https://example.com./
  expect "ambiguous numeric host" 1 'bad URL: ambiguous IPv4 address' -- http://2130706433/
  expect "usage" 1 'usage: fetch' --
done

if [ $fails = 0 ]; then echo "ALL PASS"; else echo "SOME FAIL: $fails"; exit 1; fi
