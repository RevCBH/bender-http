#!/usr/bin/env bash
# The config's timeout bounds the name lookup (C lane): an LD_PRELOAD shim
# makes getaddrinfo sleep 6 s for names ending in "slow.test" (as a resolver
# whose nameservers do not answer would), and
# examples/fetch.bend with --timeout 1000 must answer "timed out" within 3 s
# (it exits with IO.die, so the stalled lookup thread does not hold it).
# The JS lane cannot be tested this way (bun loads libc directly, and its
# getaddrinfo blocks the event loop: see C.lookup_within). Needs clang.
#   tests/client_dns_timeout.sh
set -euo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
tmp="$(mktemp -d)"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/slowdns.c" <<'C'
#define _GNU_SOURCE
#include <dlfcn.h>
#include <netdb.h>
#include <string.h>
#include <unistd.h>
int getaddrinfo(const char* node, const char* service, const struct addrinfo* hints, struct addrinfo** res) {
  // A numeric-only parse (AI_NUMERICHOST) makes no query: answer at once.
  if (node && strstr(node, "slow.test") && !(hints && (hints->ai_flags & AI_NUMERICHOST))) {
    sleep(6);
    return EAI_AGAIN;
  }
  int (*real)(const char*, const char*, const struct addrinfo*, struct addrinfo**) = dlsym(RTLD_NEXT, "getaddrinfo");
  return real(node, service, hints, res);
}
C
clang -shared -fPIC -O1 -o "$tmp/slowdns.so" "$tmp/slowdns.c" -ldl
bend "$root/examples/fetch.bend" -o "$tmp/fetch" >/dev/null
fails=0
case_() { # name want_pattern max_ms args...
  local name="$1" want="$2" max="$3"; shift 3
  # ms: until the answer is printed (the process itself may live on until
  # the stalled lookup's thread ends, see C.lookup_within).
  local t0=${EPOCHREALTIME/./}
  local out="" ms=-1 line
  while IFS= read -r line; do
    [ "$ms" -ge 0 ] || ms=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
    out+="$line"$'\n'
  done < <(LD_PRELOAD="$tmp/slowdns.so" timeout 30 "$tmp/fetch" "$@" 2>&1 || true)
  local total=$(( (${EPOCHREALTIME/./} - t0) / 1000 ))
  echo "  ($name: answer at ${ms} ms, process ended at ${total} ms)"
  if grep -qE -- "$want" <<<"$out" && [ "$ms" -lt "$max" ]; then
    echo "PASS $name (${ms} ms)"
  else
    echo "FAIL $name (${ms} ms): $(head -c 300 <<<"$out")"
    fails=$((fails + 1))
  fi
}
case_ "slow lookup times out" 'timed out' 3000 --timeout 1000 http://a.slow.test/
case_ "slow lookup, https" 'timed out' 3000 --timeout 1000 https://a.slow.test/
case_ "slow lookup, no limit waits for the resolver" 'DNS error' 20000 --timeout 0 http://a.slow.test/
if [ $fails = 0 ]; then echo "ALL PASS"; else echo "SOME FAIL: $fails"; exit 1; fi
