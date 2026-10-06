# bender-http

Bend 2 HTTP and HTTPS client library.

The installed compiler is Bend 2.0.32 (`bend version`). Do not run `bend update` from this tree.

## Use

Consumers import only `main.bend`; every public def is an `Http.*` wrapper
(see its comments for the whole API).

```
import <this package>/main.bend as P

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&2, &2, P.Http.Error(), P.Http.Response()> <-
      P.Http.fetch(P.Http.default_config(), "https://example.com/")
    ...
```

- One request per connection (`Connection: close`), the response buffered
  whole up to `max_bytes` (16 MiB by default). HTTPS goes through OpenSSL 3,
  loaded at run time. IPv4 only. Redirects are computed by `Http.redirect`,
  never followed on their own.
- Errors: `Http.Error.show` gives one line; `Http.Error.kind` gives a tag
  to match on (`P.Timeout{}`, `P.Connect{}`, `P.Tls{}`, `P.Parse{}`, ...),
  `Http.Error.code` the errno of a Dns / Connect / Io / Tls error, and
  `Http.Error.parse_error` with `Http.ParseError.kind` what was wrong with a
  response.
- Hosts whose last label is a number must be dotted quads: `127.1`,
  `2130706433`, `0x7f.1`, `010.0.0.1` are refused (BadUrl), since the OS
  resolver would read them as addresses their text does not spell.
- Header names must be tokens; header values printable ASCII, space and tab,
  with no space or tab at either end (not trimmed), else BadRequest.

## DNS dependency

Keep the two packages in sibling directories named `http` and `dns`:

```bash
git clone https://github.com/RevCBH/bender-dns.git dns
git clone https://github.com/RevCBH/bender-http.git http
git -C dns checkout 6e69e403218ee5af53b38d65bb5acf94cc44f248
```

HTTP imports `../dns/main.bend` and uses `Dns.lookup_ipv4`, the native
DNS-over-TCP resolver. It loads `/etc/resolv.conf` and `/etc/hosts` lazily,
including search domains, retries and CNAME following. HTTP's `with_host`
overrides and literal addresses take precedence. For custom nameservers,
ports, DNS timeouts or hosts/search settings, pass a DNS config:

```bend
import ../dns/main.bend as D
import ./main.bend as P

def config() -> P.Http.Config():
  dns = D.Dns.with_servers(D.Dns.default_config(), ["1.1.1.1"])
  P.Http.with_dns(P.Http.default_config(), dns)
```

DNS timeouts map to `Http.Timeout`; a name without A records maps to
`Http.NoAddress`; other DNS failures map to `Http.Dns` with the DNS package's
message. The error code is the underlying errno when available, otherwise 0.
Native resolution does not implement nsswitch, mDNS or OS split DNS policy.

## Command line

Build the small curl-like CLI with Bend 2.0.32 and clang:

```bash
cd http
make
./bender-http https://example.com/                 # body to stdout
./bender-http -L -o page.html https://example.com/ # follow redirects, save
./bender-http -I https://example.com/              # HEAD with headers
./bender-http -i -H 'Accept: text/plain' http://example.com/
./bender-http -d hello -H 'Content-Type: text/plain' https://example.com/
./bender-http --dns-server 1.1.1.1 --timeout 2000 https://example.com/
./bender-http --help
```

`-X` selects a method, `-H` repeats request headers, `-d` sends UTF-8 text
(defaulting to POST), `-i` includes response headers, `-L` follows at most
10 redirects, and `-f` fails for HTTP status >= 400 without writing output.
`-o FILE` saves byte-exact output (including binary); `-o -` selects stdout.
`--max N` sets the response byte budget (default 16 MiB), `--timeout MS`
sets the whole DNS lookup and each network step's timeout (default 30000;
0 disables), and `--dns-port N` selects the DNS TCP port. Success exits 0,
argument/network/output errors exit 1. Base's explicit successful exit prints
a blank line to stderr. Stdout uses `/dev/stdout` on Linux/macOS.

Run from source with `bend cli.bend -- URL`. Install with
`make install PREFIX="$HOME/.local"`; the binary needs no Bend runtime.
`make test` runs the CLI and resolver integration tests on both runtimes
against local DNS, HTTP and HTTPS servers, without internet access.
`make test-offline` checks argument handling, binary/header output, and
system hosts/literals on both runtimes without creating sockets.

## Timeouts

`Http.with_timeout(cfg, ms)` (default 30 s, 0: no limit) bounds each blocking
step: the name lookup, the TCP connect, the send, each read, and for HTTPS
each step inside OpenSSL. HTTPS timeouts cancel the step. The others cannot
be cancelled (Base has no way to abort a blocked effect): the request answers
Timeout at once, but a stalled plain-HTTP connect or read keeps its socket
open, and a stalled DNS TCP step can also keep the program from ending
normally until the peer acts or the OS gives up. An explicit exit (`IO.die`)
still ends it at once. DNS deadlines work on both runtimes. The DNS config
also has independent per-step deadlines; `Http.with_timeout(cfg, 0n)` disables
only HTTP's deadline, while DNS keeps its configured timeouts.

## Lanes

`bend f.bend` runs on the JS lane; `bend f.bend -o f && ./f` builds the
native C lane. The C lane has no stack limit. The JS lane overflows its stack
("memory fault") on a recursion that is not a tail call once it is some
20-40 thousand calls deep. The library's request and response paths are
written as loops where the size is the caller's or the server's, but caller
code that builds a large body or string with non-tail recursion (Base's
`String.repeat`, `List.append`, `List.length` among them) can still overflow
there: build big values with tail-recursive loops, or use the C lane.

## Design and laws

`docs/DESIGN.md` holds the design and laws 1-18 about the pure codec (URLs,
headers, request encoding, response decoding). `LAWS.bend` states them as 21
laws (plus a corollary of law 15 and concrete URL cases); `proofs/*.bend` prove
them and `PROOF.bend` imports every proof file. All 21 are proven. The gate:

    bend PROOF.bend             # ALL PROOFS CHECK
    bend PROOF.bend --verdict   # ALL PROOFS CHECK (BendTT kernel; needs Lean 4.34.0)

CI runs both on every push to `main` (`.github/workflows/ci.yml`).

Law 11 (a chunked response decodes to itself) is stated for chunk sizes up to
65535: a bound on what is proven, not on the client, which reads any chunk
size up to 4294967295 within `max_bytes` (a 200000-byte chunk is tested end to
end). See "Proof status" in `docs/DESIGN.md`.

## Limitations

- **Protocol scope.** HTTP/1.1 client only: no server, HTTP/2 or HTTP/3,
  WebSocket, proxies or CONNECT, cookies, caching, compression (no
  `Accept-Encoding` is sent and coded bodies are returned as they are),
  multipart, keep-alive or connection pooling (every request sends
  `Connection: close`). Redirects are computed by `Http.redirect`, never
  followed on their own.
- **Addresses.** IPv4 only (Base's `TCP.connect` takes IPv4 addresses).
  Hosts whose last label is a number must be dotted quads (see Use).
- **Bodies are buffered** whole, up to `max_bytes` (16 MiB by default); no
  streaming. A response head is limited to 64 KiB per line and 1000 header
  fields (TooLarge past either).
- **Timeouts** cannot cancel a stalled plain-HTTP connect or read, or a
  stalled DNS lookup (see Timeouts). HTTPS steps are cancelled.
- **JS lane.** About 5x slower than the C lane; a stack limit for non-tail
  recursion in caller code (see Lanes).
  Three stress tests (`decode_big_run`, `encode_big_run`, `url_long_run`) run
  on the C lane only.
- **TLS.** Needs OpenSSL 3 at run time (`libssl.so.3` / `libcrypto.so.3`,
  loaded with `dlopen`; Homebrew's on macOS). Certificates are verified
  against the system trust store with hostname checks, TLS 1.2 or newer; no
  revocation checking (CRL/OCSP), and the subject CN is accepted as a
  fallback name, as curl and Python do.
- **Proofs** cover the pure codec only. DNS, TCP, TLS and the read loops are
  foreign or IO code and are tested, not proven.
- **Platforms.** Built and tested on Linux x86_64 (Arch locally, Ubuntu 24.04 in
  CI) with Bend 2.0.32. The macOS paths in `tls.c` / `tls.js`
  are written but untested. The C side of the foreign effect (`tls.c`) uses Bend runtime internals with no ABI promise: rebuild and rerun
  the tests after any compiler update.

## License

MIT; see `LICENSE`.

## Tests

Run them on both lanes (`bend f.bend` is the JS lane, `bend f.bend -o f && ./f`
the native C lane):
`tests/*_test.bend` are checker-evaluated (`ALL PROOFS CHECK`),
`tests/*_run.bend` print `PASS` / `FAIL` lines, and the `*_live.sh` scripts
start local servers or use public endpoints.
