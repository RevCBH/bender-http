# bend2 HTTP client: design

An HTTP/1.1 and HTTPS client for Bend 2 (compiler 2.0.32; do not run `bend update`).
The pure core (bytes, numbers, URLs, headers, request encoding, response decoding)
is specified by the laws below, stated in `LAWS.bend` (21 laws: 1-18 below,
plus the corollary `reject_cl_te_fails` and the concrete `url_examples` /
`url_refusals`) and proven in `proofs/*.bend`, which `PROOF.bend` imports.
All 21 are proven (see "Proof status" below; law 11 is stated for chunk sizes
up to 65535). The effects (DNS, TCP, TLS) are thin, and tested rather than proven.

Read `bend guide` and `bend guide effects` first. Bend's own sources at v2.0.32
(demos with LAWS/PROOF pairs, tests, the effect sources) are a good reference;
clone with `git clone --depth 1 --branch v2.0.32 https://github.com/bendlang/bend.git`.

## Non-goals

No server, HTTP/2, HTTP/3, WebSocket, CONNECT/proxies, cookies, caching,
compression, multipart, keep-alive or pooling (every request sends
`Connection: close`), IPv6 (Base's `TCP.connect` takes IPv4 only), TLS or crypto
written in Bend, streaming bodies (bodies are buffered up to a limit), automatic
redirects (`redirect` computes the next request; the caller loops).

## Layout

| File | Alias | What |
|---|---|---|
| `main.bend` | (consumers) | the publish entry: `Http.*` wrapper defs only |
| `src/bytes.bend` | `B` | `Bytes()`, the byte `Class`, ASCII/Latin-1 text |
| `src/message.bend` | `M` | Method, Scheme, Url, Header, Request, Response, ParseError, Decoded, Error |
| `src/num.bend` | `N` | decimal and hex show/read on Nat |
| `src/headers.bend` | `H` | token / field-value validation, case-insensitive lookup |
| `src/utf8.bend` | `T` | UTF-8 encode / strict decode |
| `src/url.bend` | `U` | URL parse / show / validity |
| `src/encode.bend` | `E` | request validation and encoding |
| `src/decode.bend` | `D` | the response decoder: a byte-at-a-time state machine |
| `src/spec.bend` | `S` | pure helpers that exist only so laws can be stated: the response encoder; never imported by main.bend |
| `src/spec_request.bend` | `SR` | the same for requests: a reader for what E emits |
| `src/dns.bend` + `.c/.js` | | `Dns.lookup`: getaddrinfo (foreign) |
| `src/tls.bend` + `.c/.js` | | `Tls.open` / `Tls.recv` / `Tls.close` (and `Tls.exchange`): HTTPS over OpenSSL (foreign) |
| `src/transport.bend` | `X` | IO: plain HTTP over Base TCP; HTTPS over Tls.open / recv / close |
| `src/client.bend` | `C` | IO: Config, resolve, send, fetch; pure redirect |
| `LAWS.bend` / `PROOF.bend` / `proofs/*.bend` | | laws; proofs (one file per law or lemma group) |
| `tests/*.bend` | | executable and checker-evaluated tests |
| `examples/*.bend` | | runnable examples |

**The proof boundary.** `LAWS.bend` imports only bytes, message, num, headers,
utf8, url, encode, decode, spec, spec_request. Never dns, tls, transport, client or main: any
file that imports foreign code makes the check report SOME PROOFS FAIL.

## Bend rules that bite (all verified on 2.0.32)

- A def may call only defs written **above** it in the same file. Order helpers first.
- A module's defs are visible to an importer as `Alias.name`; types and
  constructors as `Alias.Type` / `Alias.Ctor{..}`, and patterns must use the
  qualified constructor (`case M.Header{n, v}:`). Imports are **not** re-exported.
- `match` only on a parameter or a pattern-bound variable, never a computed value:
  pass the computed value to a helper that matches on its parameter.
- Recursion must be structural (the first changing argument a pattern-matched
  part of its parameter). Use a `Nat` fuel argument otherwise. No mutual recursion;
  no `@unsafe` anywhere in this library.
- Variables are affine: write `+x` to reuse a Data value; closures are affine.
- `Nat` is a native immediate at runtime: O(1) arithmetic up to 2^48-1; past
  that the program **aborts**. Never multiply a Nat parsed from the network
  without a bound (see `num.bend`). Nat literals go up to `4294967295n`.
- Equality of values is a call (`String.eq`, `Nat.is_eq`); `==` is the type.
- Operators need a type: `(a + b : U32)`; `&&`, `||` on Bool and `++` on String work anywhere.

## Proof-friendly rules (mandatory)

1. **One classifier.** Every byte or char is classified by `B.class` /
   `B.char_class` and the `B.Class.is_*` predicates. No module compares a byte
   with `U32.is_lt` / `U32.is_eq` itself. Validators and decoders both dispatch on
   the Class, so proofs reason from `{B.class(b) == K : B.Class}`.
2. **Bytes from text** go through `B.from_ascii` (encoding) and `B.to_latin1`
   (decoding a header line) / `Char.from_u32` per byte.
   `Char.to_u32(Char.from_u32(x)) == x` is definitional (plain `{==}`).
   `Char.from_u32(Char.to_u32(c)) == c` is not, because the checker has no eta
   for `Char` (`type Char is Data: Chr{code: U32}`): prove it with a lemma
   `match c: case Chr{x}: {==}` and apply it per char by induction over the
   string, or case-split the char where it appears.
3. **Numbers** are Nat. Decimal/hex text goes through `N.show` / `N.read` /
   `N.hex_show` / `N.hex_read` only.
4. **No hidden folds.** Prefer explicit structural recursion over Base templates
   (`List.foldl`, `List.map` with `~f`) in code that laws mention; templates are
   fine in IO code.
5. **Decoder = fold of `D.step`.** `D.feed` is plain structural recursion over the
   byte list. All decoding logic lives in `D.step`.
6. Keep every pure def total and simple; prefer a small helper per case over
   clever expressions. A law will be proven about it.
7. **Loops for sizes the caller or the server controls.** The JS lane overflows
   its stack on a recursion that is not a tail call some 20-40 thousand calls
   deep (`&&` with a recursive right operand is not a tail call; Base's
   `List.append` and `List.length` are not loops). A fold over a body, a line,
   a header list or a header value is therefore a tail loop at run time, paired
   with one equation a proof rewrites with once:
   - Bool folds: `X.go(xs, ok)` with `Bool.and(ok, P(h))`; `X.go(xs, ok) ==
     Bool.and(ok, X.spec(xs))`, corollary at `ok = True`.
   - Maps and filters: a reversed accumulator, reversed once at the end;
     `X.go(xs, acc) == List.append(List.reverse(acc), X.spec(xs))`, corollary
     at `acc = Nil`.
   Keep the plain structural def where a law names it (the law faces the simple
   form; the runtime calls the loop). `List.reverse` and `String.append` (`++`)
   are safe at any size.

## Interfaces

Names below are the def names inside each module (an importer writes `N.show`, …).

### num.bend (N)

- `LIMIT() -> Nat` = `4294967295n`. Every parsed number is at most LIMIT.
- `show(n: Nat) -> String`: decimal, no leading zeros (`"0"` for 0). Defined by
  increments on a little-endian digit list (`digits(0) = [0]`,
  `digits(1n+p) = inc(digits(p))`) so `read(show(n)) == Some{n}` is provable by
  induction; runtime cost is O(n) increments, fine for lengths and ports.
- `read(s: String) -> Maybe<&2, Nat>`: one or more decimal digits (leading zeros
  allowed), Some only if the value is <= LIMIT. The fold must never compute a
  value above `LIMIT * 10 + 9` (stop accumulating once the accumulator exceeds
  LIMIT, i.e. saturate), so hostile input cannot abort the program.
- `hex_show(n: Nat) -> String` (lowercase, same increment scheme), `hex_read(s) ->
  Maybe<&2, Nat>` (case-insensitive digits, same saturation, Some only if <= LIMIT).
- Laws: `read(show(n)) == Some{n}` and `hex_read(hex_show(n)) == Some{n}` for `n <= LIMIT`.

### headers.bend (H)

- `is_token(s: String) -> Bool`: nonempty, every char `Class.is_tchar`.
- `is_value(s: String) -> Bool`: every char `Class.is_field_char`, and neither the
  first nor the last char is OWS (SP/HTAB). Empty is allowed.
- `header_ok(h: M.Header) -> Bool`, `headers_ok(hs: List<&2, M.Header>) -> Bool`.
- `lower(s: String) -> String`: ASCII letters to lowercase (via Class: Letter /
  HexLetter chars in 'A'..'Z' map down; everything else unchanged).
- `name_eq(a: String, b: String) -> Bool`: `String.eq(lower(a), lower(b))`.
- `get(name: String, hs) -> Maybe<&2, String>`: the first value whose name
  matches case-insensitively. `get_all(name, hs) -> List<&2, String>`: all of them,
  in order. `has(name, hs) -> Bool`. `count(name, hs) -> Nat`.
- `reserved(name: String) -> Bool`: host, content-length, transfer-encoding,
  connection (case-insensitive). The client sets these; a request carrying one fails.
- Law: `get(lower(n), hs) == get(n, hs)`.

### utf8.bend (T)

- `encode(s: String) -> List<&2, U32>`; `decode(xs) -> Maybe<&2, String>` strict
  (no overlongs, no surrogates, nothing past U+10FFFF, no truncated sequences).
  Tested, not proven (bit arithmetic on U32).

### url.bend (U)

- `default_port(s: M.Scheme) -> Nat`: 80 / 443.
- `is_ipv4(host: String) -> Bool`: four decimal octets 0..255 separated by dots,
  no leading zeros (a canonical dotted quad).
- `ends_in_number(host) -> Bool`: the last dot-separated label is all decimal
  digits, or `0x` then zero or more hex digits (the WHATWG "ends in a number"
  rule). Such a host is an IPv4 address to the OS resolver (inet_aton reads
  `2130706433`, `127.1`, `0x7f.1`, and `010.0.0.1` as 8.0.0.1).
- `host_ok(host) -> Bool`: nonempty; lowercase letters, digits, `-`, `.` only;
  and when `ends_in_number(host)`, `is_ipv4(host)` (else parse fails with
  `BadUrl{"ambiguous IPv4 address"}`). A host ending in `.` is a name (its last
  label is empty). So a URL's host always spells the address it reaches
  (RFC 3986 §7.4), and `ok` and `parse` agree (law 17).
- `target_ok(t) -> Bool`: starts with `/`; every char VCHAR except `#`.
- `ok(u: M.Url) -> Bool`: host_ok, `1 <= port <= 65535`, target_ok.
- `parse(s: String) -> Result<&2, &2, M.Error, M.Url>`: `scheme "://" host [":" port] [target]`.
  Scheme case-insensitive (`http`, `https`); host lowercased; userinfo (`@` before
  the path), IPv6 literals (`[`), empty port, port out of range, empty host, or a
  bad char fail with `BadUrl{reason}`. Missing target means `/`. A fragment
  (`#...`) is dropped. A query without a path (`http://h?q`) becomes `/?q`.
- `show(u) -> String`: `scheme://host[:port]target`, the port omitted when it is
  the scheme's default.
- `host_header(u) -> String`: `host` or `host:port` (non-default port).
- Law: `ok(u) -> parse(show(u)) == Done{u}`. Concrete examples too.

### encode.bend (E)

- `method_name(m: M.Method) -> String`; `method_ok(m) -> Bool` (Other's name is a token).
- `wants_length(m: M.Method, body) -> Bool`: true when the body is nonempty or the
  method is POST, PUT or PATCH.
- `request_headers(r: M.Request) -> List<&2, M.Header>`: exactly
  `[Host: U.host_header(url)] ++ r.headers ++ [Content-Length: N.show(len body)]
  (when wants_length) ++ [Connection: close]`.
- `request_ok(r) -> Bool`: method_ok, `U.ok(url)`, `H.headers_ok(headers)`, no
  header `H.reserved`, `B.all_bytes(body)`.
- `header_line(h) -> String`: `name ": " value "\r\n"`.
- `request_head(r) -> String`: `method_name SP target SP "HTTP/1.1" CRLF`, the
  header lines of `request_headers(r)`, CRLF.
- `request_bytes(r) -> List<&2, U32>`: `B.from_ascii(request_head(r)) ++ body` (unchecked).
- `request(r) -> Result<&2, &2, M.Error, List<&2, U32>>`: `Fail{BadRequest{reason}}`
  unless request_ok; else `Done{request_bytes(r)}`.

### decode.bend (D)

The decoder is a state machine over bytes:

- `type State` (internal, Data). Holds the phase, partial line, headers so far,
  body so far (accumulate reversed, reverse once at the end), the method, the
  remaining byte budget, and the leftover bytes after a complete message.
- Limits besides the budget: a line (status, field, chunk size, trailer) holds
  at most `LINE_MAX()` = 65536 bytes before its CRLF, and a head (each interim
  head on its own) or a trailer section at most `FIELDS_MAX()` = 1000 field
  lines; past either, TooLarge.
- `init(method: M.Method, max: Nat) -> State`.
- `step(s: State, b: U32) -> State`: all logic. Every byte consumed by the
  message (status line, headers, body, chunk framing, skipped 1xx responses)
  spends one unit of budget; a byte arriving with budget 0 fails with TooLarge.
  Bytes after a complete message are appended to the leftover, spending nothing.
- `feed(s: State, xs: List<&2, U32>) -> State`: structural recursion, `feed(s, h<>t) = feed(step(s, h), t)`.
- `done(s) -> Bool`: the message is complete or has failed (the reader may stop).
- `finish(s) -> Result<&2, &2, M.ParseError, M.Decoded>`: call at end of input.
  A complete message gives `Done{Decoded{response, leftover}}`; a body delimited by
  the close completes here with leftover `[]`; anything else mid-message is
  `Fail{Incomplete}`; a failed state gives its error.
- `close_delimited(s) -> Bool`: the body runs to the close (only the end of
  input ends it). A transport that can tell a clean close from a cut one (TLS
  close_notify) must refuse a cut one in this state (RFC 9112 §9.8).
- `response(method, max, xs) = finish(feed(init(method, max), xs))`.

Grammar (strict CRLF; a bare LF is an error):

- Status line: `"HTTP/1." ("0"|"1") SP DIGIT DIGIT DIGIT SP reason CRLF`; reason is
  any bytes but CR/LF/CTL other than HTAB (obs-text allowed, read as Latin-1).
  `HTTP/1.1 200` without the SP+reason is tolerated (reason ""). Other versions: BadVersion.
- Field line: `token ":" OWS value OWS CRLF` (value: field chars and obs-text;
  surrounding OWS trimmed); a line starting with SP/HTAB (obs-fold) or any other
  shape is BadHeader. Empty line ends the head.
- Framing, decided when the head ends (RFC 9112 §6.3), from method and status:
  1. status 1xx other than 101: an interim response; discard it and read the next status line.
  2. 101: UnexpectedUpgrade.
  3. method HEAD, or status 204 or 304: no body; complete.
  4. Transfer-Encoding present: with any Content-Length, ConflictingFraming;
     exactly `chunked` (case-insensitive, one header, OWS around allowed): chunked;
     anything else: UnsupportedEncoding.
  5. Content-Length present: every value across all Content-Length headers (each a
     comma list) must be decimal and equal (`N.read`), else BadLength; exactly n bytes.
     `content_length(hs) -> Maybe<&2, Nat>` exposes this (None when absent or invalid).
  6. Otherwise: the body runs to the close.
- Chunked: `hexsize [";" ext] CRLF data CRLF` repeated, then `"0" [";" ext] CRLF`,
  trailer field lines (parsed like headers, then discarded), CRLF. Chunk size via
  `N.hex_read` (so at most LIMIT; anything larger fails, as TooLarge if it exceeds the budget).

### spec.bend (S)

- `status_line(r: M.Response) -> String`: `"HTTP/1.1 " ++ N.show(status) ++ " " ++ reason ++ "\r\n"` (1.0 for Http10).
- `encode_head(r) -> List<&2, U32>`: status line, field lines, CRLF (as ASCII bytes).
- `encode_response(r) = encode_head(r) ++ body`.
- `encode_chunked(n: Nat, body) -> List<&2, U32>`: chunks of n bytes (the last one
  shorter), each `hex_show(size) CRLF data CRLF`, then `"0\r\n\r\n"`. Needs `n >= 1`.
- `head_ok(r) -> Bool`: a head the decoder reads back as written, whatever its
  status: reason chars VCHAR/SP/HTAB (`all_reason_char`; leading OWS is fine),
  `H.headers_ok(headers)`, and `head_fits(r)` (every line within `D.LINE_MAX()`,
  at most `D.FIELDS_MAX()` fields). The hypothesis of laws 13 and 14.
- `response_ok(r) -> Bool`: `body_status_ok(status)` (200..999, not 204/304,
  written as the decoder tests it) and `head_ok(r)`. The hypothesis of laws
  10-12 and 15.
### spec_request.bend (SR)

- `type ParsedRequest is Data: ParsedRequest{method: String, target: String, headers: List<&2, M.Header>, body: List<&2, U32>}`
- `decode_request(xs) -> Maybe<&2, ParsedRequest>`: a reader for what E emits
  (request line, field lines, CRLF; the body is every byte after the blank line).

### dns.bend (exists)

`Dns.lookup(host: String) -> IO(Result<&1, &1, U32 & String, List<&2, String>>)`.
A canonical dotted quad answers itself; any other host the resolver would read
as an IPv4 address (getaddrinfo with AI_NUMERICHOST succeeds: inet_aton's octal,
hex, short and bare-number forms) fails with EINVAL before any lookup. No timeout
of its own (the caller races it, see `C.resolve`).

### tls.bend

A connection is opened, read and closed in three effects, so the transport can
stop reading as soon as the decoder is done (as plain HTTP does):

- `Tls.open(server_name: String, ip: String, port: U32, request: List<&2, U32>,
  timeout_ms: U32) -> IO(Result<&1, &1, U32 & String, U32>)`: connect to ip:port,
  TLS 1.2+ handshake with SNI = server_name (none for an IPv4 literal), verify
  the certificate chain against the system trust store and the name against
  server_name, write the whole request; answer a handle (never 0). The server
  name is used without one trailing dot for SNI and verification
  (`example.com.` is checked as `example.com`, RFC 6066 §3).
- `Tls.recv(conn: U32, max: U32) -> IO(Result<&1, &1, U32 & String, List<&2, U32>>)`:
  up to `max` bytes as soon as some arrive; `[]` after close_notify; a close
  without close_notify is ECONNRESET ("...without close_notify" after data,
  "...before any response" before); a failure right after some bytes comes on
  the next read.
- `Tls.close(conn: U32) -> IO(Unit)`: close_notify if still open, then free.
- `Tls.exchange(server_name, ip, port, request, max, timeout_ms)`: the older
  one-shot form (read until the close, more than `max` bytes is EFBIG), kept
  for tools; the client does not use it.

Every blocking step honors `timeout_ms` (ETIMEDOUT), and the foreign code
cancels the step. OpenSSL 3 is loaded at
runtime with `dlopen` (libssl.so.3 / libcrypto.so.3 on Linux; Homebrew's
libssl.3.dylib on macOS); if it cannot be loaded, fail with ENOSYS and a clear
message. C lane: the whole exchange runs on an IO helper thread (`io_work`) with a
blocking socket and SO_RCVTIMEO/SO_SNDTIMEO. JS lane: the same OpenSSL calls via
`bun:ffi`, synchronous (it blocks the loop; see bendlang/bend#1148).
Errors: certificate/hostname failures use a distinct code (EPROTO) and say why
(OpenSSL's verify string).

### transport.bend (X), client.bend (C)

- `X.plain(ip: String, port: Nat, req: List<&2, U32>, method: M.Method, max: Nat, timeout_ms: Nat) ->
  IO(Result<&2, &2, M.Error, M.Decoded>)`: TCP.connect, TCP.send_bytes, then read
  with `TCP.recv_bytes` (64 KiB at a time), feeding `D.step` through `D.feed`,
  until `D.done` or EOF (an empty read), then `D.finish`. The loop counts down a
  Nat fuel (each productive read consumes at least one byte of budget, so fuel =
  budget + head allowance suffices). Each step is bounded by `X.within(timeout)`.
  Base cannot cancel a blocked read, so after a timeout the read still holds the
  socket until the peer acts; document it. Close the socket on every path you can.
- `X.tls(host, ip, port, req, method, max, timeout_ms)`: `Tls.open`, then the
  plain reader's loop over `Tls.recv` (feed, stop at `D.done`, `D.finish` on
  `[]`), then `Tls.close` on every path. No raw byte cap: the decoder's budget
  is the limit, and bytes past the message are not charged. When a read fails
  before `D.done`: ECONNRESET after some bytes (a close without close_notify)
  is `Fail{Tls{..}}` if `D.close_delimited` (the body may be truncated, RFC 9112
  §9.8), else `D.finish`'s verdict (Incomplete); any other errno maps through
  `tls_error` (ETIMEDOUT to Timeout, refusals to Connect, else Tls).
- `X.within(A, ms, act) -> IO(Maybe<&1, A>)`: IO.within whose timer stops once
  the action wins (0: no limit); cannot cancel the action.
- `type Config is Data: Config{hosts: List<&2, M.Header>, timeout_ms: Nat, max_bytes: Nat}`
  where each hosts entry maps a name (Header.name) to an IPv4 address (Header.value).
  `default_config()`: no hosts, 30000 ms, 16 MiB (16777216).
- `C.resolve(cfg, host) -> IO(Result<&2, &2, M.Error, String>)`: an IPv4 literal
  (`U.is_ipv4`) is itself; else a host that `U.ends_in_number` fails with
  `BadUrl{"ambiguous IPv4 address"}`; else the hosts table (case-insensitive;
  an entry that is not `U.is_ipv4` fails with `BadRequest`); else `Dns.lookup`'s
  first address, raced against `timeout_ms` with `X.within` (Timeout). The late
  lookup is not cancelled (C: its helper thread runs on; JS: getaddrinfo blocks
  the event loop, so the race cannot fire).
- `C.send(cfg, req) -> IO(Result<&2, &2, M.Error, M.Response>)`: `E.request`, resolve,
  plain or tls by scheme, keep the response.
- `C.fetch(cfg, url: String)`: GET with no headers.
- `C.redirect(req, resp) -> Maybe<&2, M.Request>`: for 301/302/303/307/308 with a
  Location that is an absolute http(s) URL, an absolute path (same origin) or
  `//host/path`; 303 (except to HEAD), and 301/302 on POST, become GET with no
  body (and drop Content-Type); others keep method and body. Leaving the origin
  drops Authorization, Proxy-Authorization and Cookie. None otherwise.

### main.bend

The only file consumers import. Every public def is an `Http.*` wrapper over a
src module: type aliases (`def Http.Response() -> Data: M.Response`, ...),
constructors (`Http.get(url)`, `Http.request(method, url, headers, body)`,
`Http.header(name, value)`, method values), accessors (`Http.status`,
`Http.headers`, `Http.body`, `Http.reason`, `Http.Url.*`), `Http.Url.parse/show`,
`Http.encode`, `Http.decode`, `Http.get_header`, `Http.text`, `Http.is_success`,
`Http.redirect`, `Http.default_config`, `Http.with_host`/`with_timeout`/`with_max_bytes`,
`Http.send`, `Http.fetch`, `Http.lookup`, `Http.resolve`, `Http.Error.show`,
`Http.ParseError.show`.

Errors are matched through tags defined in main.bend itself (a consumer cannot
name M's constructors, since imports are not re-exported):
`type ErrorKind is Data: BadUrl{} BadRequest{} NoAddress{} Dns{} Connect{} Io{} Timeout{} Tls{} Parse{}`
and `type ParseErrorKind is Data:` one nullary tag per `M.ParseError` constructor,
with `Http.ErrorKind()` / `Http.ParseErrorKind()` aliases,
`Http.Error.kind(e) -> ErrorKind`, `Http.Error.code(e) -> Maybe<&2, U32>` (Some
for Dns/Connect/Io/Tls), `Http.Error.parse_error(e) -> Maybe<&2, M.ParseError>`
and `Http.ParseError.kind(e) -> ParseErrorKind`. A consumer writes
`match P.Http.Error.kind(e): case P.Timeout{}: ...`.

main.bend's comments must state the caveats a caller cannot see from the types:
header name/value rules, redirect rules, what each timeout bounds and that only
HTTPS timeouts cancel, the hosts-table IPv4 requirement, and the JS-lane stack
limit for caller-built values.

## Laws (LAWS.bend states them; the code must make them true)

1. `ascii_roundtrip`: `B.is_ascii(s)` ⇒ `B.to_ascii(B.from_ascii(s)) == Some{s}`.
2. `dec_roundtrip`: `n <= LIMIT` ⇒ `N.read(N.show(n)) == Some{n}`.
3. `hex_roundtrip`: `n <= LIMIT` ⇒ `N.hex_read(N.hex_show(n)) == Some{n}`.
4. `encode_bytes_in_range`: `E.request(r) == Done{b}` ⇒ `B.all_bytes(b) == True`.
5. `encode_total`: `E.request_ok(r)` ⇒ `E.request(r) == Done{E.request_bytes(r)}`.
6. `encode_rejects_bad_headers`: `H.headers_ok(r.headers) == False` ⇒ `E.request(r)` fails.
7. `request_roundtrip`: `E.request_ok(r)` ⇒ `SR.decode_request(E.request_bytes(r)) ==
   Some{ParsedRequest{E.method_name(m), target, E.request_headers(r), body}}`.
8. `host_once`: `E.request_ok(r)` ⇒ `H.count("host", E.request_headers(r)) == 1`.
9. `feed_split`: `D.feed(D.feed(s, a), b) == D.feed(s, a ++ b)`.
Laws 10-15 quantify over every method `meth` with `D.is_head(meth) == False`
(the decoder reads the method only in `no_body`), not just GET; keep the
hypothesis on `D.is_head`, not on a list of methods. "A budget covering the
message" is stated as `Nat.add(len(msg), slack)` for any `slack`: exactly the
message length passes, one less is TooLarge.

10. `response_length_roundtrip`: `D.is_head(meth) == False`, `S.response_ok(r)`,
    `D.content_length(r.headers) == Some{len body}` (equal duplicates are fine),
    no Transfer-Encoding ⇒ `D.response(meth, len(S.encode_response(r)) + slack,
    S.encode_response(r) ++ rest) == Done{Decoded{r, rest}}`.
11. `response_chunked_roundtrip`: `D.is_head(meth) == False`, `S.response_ok(r)`,
    `D.chunked_only(H.get_all("transfer-encoding", r.headers))`, no Content-Length,
    HTTP/1.1, `1 <= n` and `n <= N.LIMIT()` and `n <= 65535` (a bound of the proof, see Proof status) (every chunk size must pass `N.hex_read`; `n = 0`
    is a real counterexample) ⇒ with `msg = S.encode_head(r) ++
    S.encode_chunked(n, body)`, `D.response(meth, len(msg) + slack, msg ++ rest)
    == Done{Decoded{r, rest}}`.
12. `response_close_roundtrip`: `D.is_head(meth) == False`, `S.response_ok(r)`,
    neither framing header ⇒ `D.response(meth, len(S.encode_response(r)) + slack,
    S.encode_response(r)) == Done{Decoded{r, []}}`.
13. `no_body`: `D.no_body(meth, st) == True` (HEAD, 204 or 304), `200 <= st <= 999`,
    `S.head_ok(r)` ⇒ `D.response(meth, len(S.encode_head(r)) + slack,
    S.encode_head(r) ++ rest) == Done{Decoded{bodiless(r), rest}}` (bodiless:
    body `[]`). No condition on framing headers (RFC 9112 §6.3 rule 1). A 1xx
    status under HEAD is excluded on purpose (100 is Incomplete, 101 UnexpectedUpgrade).
14. `interim_skipped`: `D.is_head(meth) == False`; an interim `i` with
    `100 <= st_i < 200`, `st_i != 101`, `S.head_ok(i)` (its own framing headers are
    ignored); `r` meeting law 10's hypotheses ⇒ with `msg = S.encode_head(i) ++
    S.encode_response(r)`, `D.response(meth, len(msg) + slack, msg ++ rest) ==
    Done{Decoded{r, rest}}`.
15. `reject_cl_te`: `D.is_head(meth) == False`, `S.response_ok(r)`,
    `H.has("content-length", r.headers)` and `H.has("transfer-encoding", r.headers)`
    ⇒ `D.response(meth, len(S.encode_head(r)) + slack, S.encode_head(r) ++ rest)
    == Fail{M.ConflictingFraming{}}`. Corollary without a budget:
    `Result.is_fail(D.response(meth, m, S.encode_head(r) ++ rest))` for every `m`
    (a short budget gives TooLarge). HEAD, 1xx, 204 and 304 are excluded on
    purpose (they end at the blank line whatever the headers say, RFC 9112 §6.3
    rule 1, consistent with law 13), and so are invalid header fields (a CRLF
    inside a value ends the head early).
16. `size_bound`: `D.response(meth, m, x) == Done{d}` ⇒ `len(d.response.body) <= m`.
17. `url_roundtrip`: `U.ok(u)` ⇒ `U.parse(U.show(u)) == Done{u}`; plus concrete URL cases.
18. `header_lookup_case`: `H.get(H.lower(n), hs) == H.get(n, hs)`.

## Proof status

The gate, run on the build box (checking takes well under a minute):

    scripts/box 'bend PROOF.bend'             # ALL PROOFS CHECK once every law is proven
    scripts/box 'bend PROOF.bend --verdict'   # the same, rechecked by the BendTT kernel

`bend PROOF.bend` prints ALL PROOFS CHECK; `bend PROOF.bend --verdict` also prints ALL PROOFS CHECK (the BendTT kernel rechecks every law; about 50 s).

`PROOF.bend` imports every `proofs/*.bend` file; each defines
`def Laws.<name>` for its laws, plus its lemmas.

| file | laws proven |
|---|---|
| `proofs/url_concrete.bend` | `url_examples`, `url_refusals` |
| `proofs/num.bend` | 2 `dec_roundtrip`, 3 `hex_roundtrip` |
| `proofs/decode_lemmas.bend` | (lemma library: the head lemma, digit classes; used as `DL`) |
| `proofs/headers.bend` | 18 `header_lookup_case` |
| `proofs/url.bend` | 17 `url_roundtrip` |
| `proofs/encode_basic.bend` | 1 `ascii_roundtrip`, 4 `encode_bytes_in_range`, 5 `encode_total`, 6 `encode_rejects_bad_headers`, 8 `host_once` |
| `proofs/request_roundtrip.bend` | 7 `request_roundtrip` |
| `proofs/decode_basic.bend` | 9 `feed_split`, 16 `size_bound` |
| `proofs/decode_head.bend` | 13 `no_body`, 15 `reject_cl_te`, `reject_cl_te_fails` |
| `proofs/response_length.bend` | 10 `response_length_roundtrip`, 14 `interim_skipped` |
| `proofs/response_close.bend` | 12 `response_close_roundtrip` |
| `proofs/response_chunked.bend` | 11 `response_chunked_roundtrip` (chunk sizes up to 65535) |

Law 11 (`response_chunked_roundtrip`) is stated for chunk sizes `1 <= n <= 65535`
(hypothesis `es`). `proofs/response_chunked.bend` also proves it for every `n`
given one more hypothesis: the chunk-size line `N.hex_show(n)` fits
`D.LINE_MAX()`. That fact holds for every `n <= N.LIMIT()`, but no proof of it
can be checked: both checkers peel a Nat literal one Succ at a time, so any
bound involving 4294967295 costs about 4.3e9 steps (hours, and past the BendTT
kernel's fuel), and making `N.LIMIT()` structural does not help (the file
header has the measurements). The bound limits what is proven, not the client:
the decoder reads any chunk size up to `N.LIMIT()` within the byte budget, and
a 200000-byte chunk decodes on both lanes in an end-to-end test.

## Testing

- Checker-evaluated tests: a file whose `main` returns an equality, proven by
  `{==}`, e.g. `def main() -> {N.read("42") == Some{42n} : Maybe<&2, Nat>}: {==}`.
  `bend tests/x.bend` printing ALL PROOFS CHECK is a pass. Good for every pure module.
- Runtime tests: `tests/*_run.bend` with `main -> IO(Unit)` printing `PASS name` /
  `FAIL name`, run on both lanes: `bend f.bend` (JS) and `bend f.bend -o f && ./f` (C).
- Live tests run on the build box (`scripts/box`): local Python servers that send
  chunked bodies, split writes, 1xx responses, binary bodies, slow responses, and
  public endpoints (example.com, httpbin.org, badssl.com).
