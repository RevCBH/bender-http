#!/usr/bin/env bash
# The whole gate: proofs (checker and BendTT kernel), a check of every file,
# the checker-evaluated tests, the runtime tests on both lanes, and the live
# tests against local servers. CI runs it on every push to main; run it on any
# machine with Bend 2.0.32, Lean 4.34.0 (for --verdict), clang, Python 3 and
# OpenSSL 3. `--public` adds the tests that need internet endpoints.
set -uo pipefail
cd "$(dirname "$0")/.."
out="${BEND_OUT:-${RUNNER_TEMP:-/tmp}}/bender-http-ci"
mkdir -p "$out"
public=0
[[ ${1:-} == --public ]] && public=1
failures=()
pass() { printf 'ok    %s\n' "$1"; }
fail() { printf 'FAIL  %s\n' "$1"; failures+=("$1"); printf '%s\n' "$2" | tail -n 30 | sed 's/^/      /'; }

# A file passes the check if it is pure and checks, or if the only complaint is
# its reliance on the foreign effects (OS resolver API, TLS), which is expected.
check_file() {
  local f=$1 log
  log="$(bend "$f" --check-only 2>&1)"
  if grep -q 'ALL PROOFS CHECK' <<<"$log"; then pass "check $f"
  elif grep -q -E 'rel(y|ies) on unsafe or foreign code' <<<"$log" && ! grep -q -- '- expected' <<<"$log"; then pass "check $f (foreign)"
  else fail "check $f" "$log"; fi
}

# Runtime tests print PASS / FAIL lines; any FAIL or a nonzero exit fails.
run_js() {
  local f=$1 log rc
  log="$(bend "$f" 2>&1)"; rc=$?
  if (( rc == 0 )) && ! grep -q '^FAIL' <<<"$log"; then pass "js $f"; else fail "js $f (rc=$rc)" "$log"; fi
}
run_c() {
  local f=$1 bin log rc
  bin="$out/$(basename "$f" .bend)"
  log="$(bend "$f" -o "$bin" 2>&1)" || { fail "build $f" "$log"; return; }
  log="$("$bin" 2>&1)"; rc=$?
  if (( rc == 0 )) && ! grep -q '^FAIL' <<<"$log"; then pass "c  $f"; else fail "c  $f (rc=$rc)" "$log"; fi
}

echo '== proofs'
log="$(bend PROOF.bend 2>&1)"
grep -q 'ALL PROOFS CHECK' <<<"$log" && pass 'bend PROOF.bend' || fail 'bend PROOF.bend' "$log"
log="$(bend PROOF.bend --verdict 2>&1)"
grep -q 'ALL PROOFS CHECK' <<<"$log" && pass 'bend PROOF.bend --verdict' || fail 'bend PROOF.bend --verdict' "$log"

echo '== check every file'
for f in main.bend cli.bend src/*.bend examples/*.bend tests/resolver_local.bend tests/cli_output.bend; do check_file "$f"; done

echo '== checker-evaluated tests'
for f in tests/*_test.bend; do
  log="$(bend "$f" 2>&1)" && pass "checker $f" || fail "checker $f" "$log"
done

echo '== runtime tests'
c_only=(tests/decode_big_run.bend tests/encode_big_run.bend tests/url_long_run.bend)
for f in tests/*_run.bend; do
  # client_run includes live fetches of public endpoints.
  [[ $f == tests/client_run.bend && $public == 0 ]] && continue
  [[ " ${c_only[*]} " == *" $f "* ]] || run_js "$f"
  run_c "$f"
done

echo '== live tests (local servers)'
for s in tests/tls_live.sh tests/transport_live.sh tests/cli_offline.sh tests/cli_test.sh; do
  log="$(bash "$s" 2>&1)" && pass "$s" || fail "$s" "$log"
done
if (( public )); then
  echo '== live tests (public endpoints)'
  for s in tests/client_live.sh; do
    log="$(bash "$s" 2>&1)" && pass "$s" || fail "$s" "$log"
  done
  run_js tests/tls_public.bend
  run_c tests/tls_public.bend
fi

echo
if (( ${#failures[@]} )); then
  printf '%d failed:\n' "${#failures[@]}"; printf '  %s\n' "${failures[@]}"
  exit 1
fi
echo 'all passed'
