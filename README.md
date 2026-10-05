# bend2

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

## Timeouts

`Http.with_timeout(cfg, ms)` (default 30 s, 0: no limit) bounds each blocking
step: the name lookup, the TCP connect, the send, each read, and for HTTPS
each step inside OpenSSL. HTTPS timeouts cancel the step. The others cannot
be cancelled (Base has no way to abort a blocked effect): the request answers
Timeout at once, but a stalled plain-HTTP connect or read keeps its socket
open, and a stalled lookup its resolver thread, and that keeps the program
from ending normally until the peer acts or the OS gives up. An explicit exit
(`IO.die`) still ends it at once. On the JS lane the name lookup blocks the
event loop, so its timeout cannot fire there.

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
  recursion in caller code (see Lanes); the DNS lookup blocks the event loop.
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
  are written but untested. The C side of the foreign effects (`dns.c`,
  `tls.c`) uses Bend runtime internals with no ABI promise: rebuild and rerun
  the tests after any compiler update.

## License

MIT; see `LICENSE`.

## Tests

Run them on both lanes (`bend f.bend` is the JS lane, `bend f.bend -o f && ./f`
the native C lane):
`tests/*_test.bend` are checker-evaluated (`ALL PROOFS CHECK`),
`tests/*_run.bend` print `PASS` / `FAIL` lines, and the `*_live.sh` scripts
start local servers or use public endpoints.
