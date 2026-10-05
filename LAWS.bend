# The laws of the bend2 HTTP client: what its pure core must do, stated
# for every input. PROOF.bend proves each one (`def Laws.<name>`); the gate is
# `bend PROOF.bend` (and `bend PROOF.bend --verdict` on a machine with Lean).
#
# These laws cover the pure modules only: bytes, num, headers, url, the request
# encoder and the response decoder (with spec / spec_request, which exist to
# state them). DNS, TLS and the socket loop are foreign or IO code and are
# tested, not proven.
import Base
import ./src/bytes.bend as B
import ./src/message.bend as M
import ./src/num.bend as N
import ./src/headers.bend as H
import ./src/url.bend as U
import ./src/encode.bend as E
import ./src/decode.bend as D
import ./src/spec.bend as S
import ./src/spec_request.bend as SR

def Res() -> Type:
  Result<&2, &2, M.ParseError, M.Decoded>

def ReqRes() -> Type:
  Result<&2, &2, M.Error, List<&2, U32>>

def UrlRes() -> Type:
  Result<&2, &2, M.Error, M.Url>

def len(xs: List<&2, U32>) -> Nat:
  List.length(&2, U32, xs)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, xs, ys)

# r with its body replaced by [] (what a bodiless response decodes to).
def bodiless(r: M.Response) -> M.Response:
  match r:
    case M.Response{v, st, rs, hs, b}:
      M.Response{v, st, rs, hs, []}

def status(r: M.Response) -> Nat:
  S.response_status(r)

def is_http11(r: M.Response) -> Bool:
  match r:
    case M.Response{v, st, rs, hs, b}:
      match v:
        case M.Http11{}:
          True{}
        case M.Http10{}:
          False{}

# 1. ASCII text survives the trip to bytes and back.
law ascii_roundtrip:
  for +s: String
  for e: {B.is_ascii(s) == True{} : Bool}
  {B.to_ascii(B.from_ascii(s)) == Some{s} : Maybe<&2, String>}

# 2. Decimal numbers up to N.LIMIT() read back as written.
law dec_roundtrip:
  for +n: Nat
  for e: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}
  {N.read(N.show(n)) == Some{n} : Maybe<&2, Nat>}

# 3. The same for hex (chunk sizes).
law hex_roundtrip:
  for +n: Nat
  for e: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}
  {N.hex_read(N.hex_show(n)) == Some{n} : Maybe<&2, Nat>}

# 4. Every cell of an encoded request is a byte (0..255).
law encode_bytes_in_range:
  for +r: M.Request
  for +b: List<&2, U32>
  for e: {E.request(r) == Done{b} : ReqRes()}
  {B.all_bytes(b) == True{} : Bool}

# 5. A valid request always encodes, to its head and body.
law encode_total:
  for +r: M.Request
  for e: {E.request_ok(r) == True{} : Bool}
  {E.request(r) == Done{E.request_bytes(r)} : ReqRes()}

# 6. A request with an invalid header name or value (CR, LF, NUL, ...) is refused.
law encode_rejects_bad_headers:
  for +m: M.Method
  for +u: M.Url
  for +hs: List<&2, M.Header>
  for +body: List<&2, U32>
  for e: {H.headers_ok(hs) == False{} : Bool}
  {E.request(M.Request{m, u, hs, body}) == Fail{M.BadRequest{"invalid header name or value"}} : ReqRes()}

# 7. A server reading the encoded request gets back the method, target,
#    the headers the client sends, and the body exactly.
law request_roundtrip:
  for +m: M.Method
  for +s: M.Scheme
  for +h: String
  for +p: Nat
  for +t: String
  for +hs: List<&2, M.Header>
  for +body: List<&2, U32>
  for e: {E.request_ok(M.Request{m, M.Url{s, h, p, t}, hs, body}) == True{} : Bool}
  {SR.decode_request(E.request_bytes(M.Request{m, M.Url{s, h, p, t}, hs, body}))
    == Some{SR.ParsedRequest{E.method_name(m), t,
         E.request_headers(M.Request{m, M.Url{s, h, p, t}, hs, body}), body}}
    : Maybe<&2, SR.ParsedRequest>}

# 8. An encoded request carries exactly one Host header.
law host_once:
  for +r: M.Request
  for e: {E.request_ok(r) == True{} : Bool}
  {H.count("host", E.request_headers(r)) == 1n : Nat}

# 9. How the response arrives in pieces never changes what is decoded.
law feed_split:
  for +s: D.State
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {D.feed(D.feed(s, a), b) == D.feed(s, cat(a, b)) : D.State}

# 10. A Content-Length response decodes to itself; bytes after it are left over.
law response_length_roundtrip:
  for +meth: M.Method
  for +r: M.Response
  for +rest: List<&2, U32>
  for +slack: Nat
  for e0: {D.is_head(meth) == False{} : Bool}
  for e1: {S.response_ok(r) == True{} : Bool}
  for e2: {D.content_length(S.response_headers(r)) == Some{len(S.response_body(r))} : Maybe<&2, Nat>}
  for e3: {H.has("transfer-encoding", S.response_headers(r)) == False{} : Bool}
  {D.response(meth, Nat.add(len(S.encode_response(r)), slack), cat(S.encode_response(r), rest))
    == Done{M.Decoded{r, rest}} : Res()}

# 11. A chunked response decodes to itself, whatever the chunk size up to 64 KiB.
#     The bound is a limit of the proof, not of the client: the decoder reads any
#     chunk size up to N.LIMIT() (and the byte budget). Bend's checkers count a Nat
#     literal one step at a time, so a fact about every size up to 4294967295
#     (here: its hex text fits the line limit) cannot be checked in practice; see
#     proofs/response_chunked.bend, which also proves the law for every size given
#     that fact. tests/decode_run.bend and decode_big_run.bend exercise larger chunks.
law response_chunked_roundtrip:
  for +meth: M.Method
  for +r: M.Response
  for +n: Nat
  for +rest: List<&2, U32>
  for +slack: Nat
  for e0: {D.is_head(meth) == False{} : Bool}
  for e1: {S.response_ok(r) == True{} : Bool}
  for e2: {D.chunked_only(H.get_all("transfer-encoding", S.response_headers(r))) == True{} : Bool}
  for e3: {H.has("content-length", S.response_headers(r)) == False{} : Bool}
  for e4: {Nat.is_le(1n, n) == True{} : Bool}
  for e5: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}
  for e6: {is_http11(r) == True{} : Bool}
  for es: {Nat.is_le(n, 65535n) == True{} : Bool}
  {D.response(meth,
      Nat.add(len(cat(S.encode_head(r), S.encode_chunked(n, S.response_body(r)))), slack),
      cat(S.encode_head(r), cat(S.encode_chunked(n, S.response_body(r)), rest)))
    == Done{M.Decoded{r, rest}} : Res()}

# 12. A response with neither framing header runs to the close and decodes to itself.
law response_close_roundtrip:
  for +meth: M.Method
  for +r: M.Response
  for +slack: Nat
  for e0: {D.is_head(meth) == False{} : Bool}
  for e1: {S.response_ok(r) == True{} : Bool}
  for e2: {H.has("transfer-encoding", S.response_headers(r)) == False{} : Bool}
  for e3: {H.has("content-length", S.response_headers(r)) == False{} : Bool}
  {D.response(meth, Nat.add(len(S.encode_response(r)), slack), S.encode_response(r))
    == Done{M.Decoded{r, []}} : Res()}

# 13. HEAD, 204 and 304 responses end at the blank line, whatever their headers say.
law no_body:
  for +meth: M.Method
  for +r: M.Response
  for +rest: List<&2, U32>
  for +slack: Nat
  for e0: {D.no_body(meth, status(r)) == True{} : Bool}
  for e1: {Nat.is_le(200n, status(r)) == True{} : Bool}
  for e2: {Nat.is_le(status(r), 999n) == True{} : Bool}
  for e3: {S.head_ok(r) == True{} : Bool}
  {D.response(meth, Nat.add(len(S.encode_head(r)), slack), cat(S.encode_head(r), rest))
    == Done{M.Decoded{bodiless(r), rest}} : Res()}

# 14. Interim 1xx responses (other than 101) are skipped.
law interim_skipped:
  for +meth: M.Method
  for +i: M.Response
  for +r: M.Response
  for +rest: List<&2, U32>
  for +slack: Nat
  for e0: {D.is_head(meth) == False{} : Bool}
  for e1: {Nat.is_le(100n, status(i)) == True{} : Bool}
  for e2: {Nat.is_lt(status(i), 200n) == True{} : Bool}
  for e3: {Nat.is_eq(status(i), 101n) == False{} : Bool}
  for e4: {S.head_ok(i) == True{} : Bool}
  for e5: {S.response_ok(r) == True{} : Bool}
  for e6: {D.content_length(S.response_headers(r)) == Some{len(S.response_body(r))} : Maybe<&2, Nat>}
  for e7: {H.has("transfer-encoding", S.response_headers(r)) == False{} : Bool}
  {D.response(meth, Nat.add(len(cat(S.encode_head(i), S.encode_response(r))), slack),
      cat(S.encode_head(i), cat(S.encode_response(r), rest)))
    == Done{M.Decoded{r, rest}} : Res()}

# 15. Content-Length together with Transfer-Encoding is refused (request smuggling).
law reject_cl_te:
  for +meth: M.Method
  for +r: M.Response
  for +rest: List<&2, U32>
  for +slack: Nat
  for e0: {D.is_head(meth) == False{} : Bool}
  for e1: {S.response_ok(r) == True{} : Bool}
  for e2: {H.has("content-length", S.response_headers(r)) == True{} : Bool}
  for e3: {H.has("transfer-encoding", S.response_headers(r)) == True{} : Bool}
  {D.response(meth, Nat.add(len(S.encode_head(r)), slack), cat(S.encode_head(r), rest))
    == Fail{M.ConflictingFraming{}} : Res()}

# 16. A decoded body is never longer than the byte budget.
law size_bound:
  for +meth: M.Method
  for +m: Nat
  for +x: List<&2, U32>
  for +r: M.Response
  for +rest: List<&2, U32>
  for e: {D.response(meth, m, x) == Done{M.Decoded{r, rest}} : Res()}
  {Nat.is_le(len(S.response_body(r)), m) == True{} : Bool}

# 17. A valid URL shows and parses back to itself.
law url_roundtrip:
  for +u: M.Url
  for e: {U.ok(u) == True{} : Bool}
  {U.parse(U.show(u)) == Done{u} : Result<&2, &2, M.Error, M.Url>}

# 18. Header lookup ignores the case of the name.
law header_lookup_case:
  for +n: String
  for +hs: List<&2, M.Header>
  {H.get(H.lower(n), hs) == H.get(n, hs) : Maybe<&2, String>}

# 15b. The same refusal holds for any budget (a short one fails with TooLarge).
law reject_cl_te_fails:
  for +meth: M.Method
  for +r: M.Response
  for +m: Nat
  for +rest: List<&2, U32>
  for e0: {D.is_head(meth) == False{} : Bool}
  for e1: {S.response_ok(r) == True{} : Bool}
  for e2: {H.has("content-length", S.response_headers(r)) == True{} : Bool}
  for e3: {H.has("transfer-encoding", S.response_headers(r)) == True{} : Bool}
  {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.response(meth, m, cat(S.encode_head(r), rest))) == True{} : Bool}

# 19. Concrete URLs: default ports, case, a query without a path, a dropped fragment.
law url_examples:
  {(U.parse("http://example.com"), (U.parse("HTTPS://Example.COM/a?b"),
    (U.parse("http://h?q=1#frag"), U.parse("http://10.0.0.1:81/x"))))
    == (Done{M.Url{M.Http{}, "example.com", 80n, "/"}},
       (Done{M.Url{M.Https{}, "example.com", 443n, "/a?b"}},
       (Done{M.Url{M.Http{}, "h", 80n, "/?q=1"}},
        Done{M.Url{M.Http{}, "10.0.0.1", 81n, "/x"}})))
    : Pair(UrlRes(), Pair(UrlRes(), Pair(UrlRes(), UrlRes())))}

# 20. URLs that would reach an unexpected host are refused.
law url_refusals:
  {(U.parse("http://user@evil.com/"), (U.parse("http://[::1]/"),
    (U.parse("http://0x7f.1/"), (U.parse("http://h:0/"), U.parse("ftp://h/")))))
    == (Fail{M.BadUrl{"userinfo is not supported"}},
       (Fail{M.BadUrl{"IPv6 literals are not supported"}},
       (Fail{M.BadUrl{"ambiguous IPv4 address"}},
       (Fail{M.BadUrl{"port out of range"}}, Fail{M.BadUrl{"unsupported scheme"}}))))
    : Pair(UrlRes(), Pair(UrlRes(), Pair(UrlRes(), Pair(UrlRes(), UrlRes()))))}
