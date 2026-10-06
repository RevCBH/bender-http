#!/usr/bin/env bash
# Parser, byte-exact output and system-host/literal lookups without sockets.
set -euo pipefail
cd "$(dirname "$0")/.."
out="$(mktemp -d)"
trap 'rm -rf "$out"' EXIT
"${BEND:-bend}" cli.bend -o "$out/bender-http"
"${BEND:-bend}" tests/cli_output.bend -o "$out/output"
"${BEND:-bend}" tests/dns_run.bend -o "$out/dns"
python3 -B - "$out" "${BEND:-bend}" <<'PY'
import pathlib
import subprocess
import sys

out = pathlib.Path(sys.argv[1])
body = bytes(range(256)) * 256
# Several long headers exercise the JS stack limit in header output.
head = (b'HTTP/1.1 200 OK\r\n' + b'X-Long: ' + b'a' * 60000 + b'\r\n' +
        b'X-Long: ' + b'b' * 60000 + b'\r\nContent-Length: 65536\r\n\r\n')
fixture = out / 'response'
fixture.write_bytes(head + body)
failures = []


def check(label, cmd, args, code=0, stdout=None, stderr=None):
    try:
        r = subprocess.run(cmd + args, capture_output=True, timeout=25)
        assert r.returncode == code, f'exit {r.returncode}: {r.stderr[:300]!r}'
        if stdout is not None:
            assert r.stdout == stdout, f'stdout {len(r.stdout)} bytes: {r.stdout[:100]!r}'
        if stderr is not None:
            assert stderr in r.stderr, r.stderr
    except (AssertionError, subprocess.TimeoutExpired) as e:
        failures.append(f'[{lane}] {label}: {e}')
        print('FAIL ' + failures[-1], flush=True)
    else:
        print(f'PASS [{lane}] {label}', flush=True)
        return r


for lane, cli, writer, dns in (
    ('c', [str(out / 'bender-http')], [str(out / 'output')], [str(out / 'dns')]),
    ('js', [sys.argv[2], 'cli.bend', '--'], [sys.argv[2], 'tests/cli_output.bend', '--'],
     [sys.argv[2], 'tests/dns_run.bend']),
):
    r = check('help', cli, ['--help'])
    if r is not None and b'usage: bender-http' not in r.stdout:
        failures.append(f'[{lane}] missing help')
    check('no URL', cli, [], 1, b'', b'usage:')
    check('unknown flag', cli, ['--bogus'], 1, b'', b'unknown option')
    check('multiple URLs', cli, ['http://x.test', 'http://y.test'], 1, b'', b'more than one URL')
    for flag in ('-o', '-H', '-d', '-X', '--timeout', '--max', '--dns-server', '--dns-port'):
        check('missing ' + flag, cli, [flag], 1, b'', b'missing its value')
    for flag, value in (('--timeout', '-1'), ('--timeout', '4294967296'), ('--max', 'no'),
                        ('--max', '4294967296'), ('--dns-port', '0'), ('--dns-port', '65536'),
                        ('--dns-server', '127.1')):
        check(f'invalid {flag} {value}', cli, [flag, value, 'http://x.test'], 1, b'')
    check('bad header', cli, ['-H', 'oops', 'http://x.test'], 1, b'', b'bad header')
    check('binary stdout', writer, [str(fixture)], stdout=body)
    check('stdout alias', writer, [str(fixture), '-o', '-'], stdout=body)
    check('large headers + binary stdout', writer, [str(fixture), '-i'], stdout=head + body)
    dest = out / (lane + '.bin')
    check('binary file', writer, [str(fixture), '-o', str(dest)], stdout=b'')
    if not dest.exists() or dest.read_bytes() != body:
        failures.append(f'[{lane}] incorrect binary file')
    check('include headers in file', writer, [str(fixture), '-i', '-o', str(dest)], stdout=b'')
    if dest.read_bytes() != head + body:
        failures.append(f'[{lane}] incorrect header/body file')
    check('output open failure', writer, [str(fixture), '-o', str(out / 'missing' / 'file')], 1, b'', b'output error')
    check('output write failure', writer, [str(fixture), '-o', '/dev/full'], 1, b'', b'output error')
    r = check('native lookup inputs and system hosts', dns, [])
    if r is not None and b'FAIL' in r.stdout:
        failures.append(f'[{lane}] DNS input test failure: {r.stdout!r}')
if failures:
    sys.exit('\n'.join(failures))
print('ALL OFFLINE HTTP TESTS PASS')
PY
