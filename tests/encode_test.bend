import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/headers.bend as H
import ../src/encode.bend as E
import ../src/spec_request.bend as SR

# Checker-evaluated tests for encode.bend (E) and spec_request.bend (SR):
# `bend tests/encode_test.bend --check-only` printing ALL PROOFS CHECK is a
# pass. Exact bytes of requests, every refusal, and laws 7 (request_roundtrip)
# and 8 (host_once) evaluated on concrete requests.

def R() -> Type:
  Result<&2, &2, M.Error, List<&2, U32>>

def P() -> Type:
  Maybe<&2, SR.ParsedRequest>

def url(host: String, port: Nat, target: String) -> M.Url:
  M.Url{M.Http{}, host, port, target}

def get_req() -> M.Request:
  M.Request{M.GET{}, url("example.com", 80n, "/"), [], []}

def post_req() -> M.Request:
  M.Request{M.POST{}, url("api.test", 8080n, "/v1/items?x=1"),
    [M.Header{"Content-Type", "text/plain"}], B.from_ascii("hi")}

def post_empty() -> M.Request:
  M.Request{M.POST{}, url("a.b", 80n, "/"), [], []}

# Every header shape the encoder accepts: ':' inside a value, an empty value,
# inner SP and HTAB, an https URL on its default port.
def odd_req() -> M.Request:
  M.Request{M.Other{"PROPFIND"}, M.Url{M.Https{}, "10.0.0.1", 443n, "/a/b;c?d=e&f"},
    [M.Header{"X-Time", "12:30:00"}, M.Header{"X-Empty", ""},
     M.Header{"X-Mixed", "a b\tc"}, M.Header{"x-time", "dup"}], []}

# A body with CRLFs, a blank line and every byte value class, on a DELETE.
def body_req() -> M.Request:
  M.Request{M.DELETE{}, url("h", 1n, "/x"), [M.Header{"Accept", "*/*"}],
    [13, 10, 13, 10, 0, 255, 128, 58, 32]}

def with_headers(hs: List<&2, M.Header>) -> M.Request:
  M.Request{M.GET{}, url("example.com", 80n, "/"), hs, []}

# Three headers, for the loop / spec agreement cases.
def many_hs() -> List<&2, M.Header>:
  [M.Header{"X-A", "1"}, M.Header{"x-b", ""}, M.Header{"X-C", "c d"}]

def bad(reason: String) -> R():
  Fail{M.BadRequest{reason}}

def bad_header() -> String:
  "invalid header name or value"

def bad_reserved() -> String:
  "reserved header (Host, Content-Length, Transfer-Encoding or Connection)"

def roundtrip(r: M.Request) -> P():
  match r:
    case M.Request{+m, M.Url{s, h, p, +t}, hs, +body}:
      Some{SR.ParsedRequest{E.method_name(m), t,
        E.request_headers(M.Request{m, M.Url{s, h, p, t}, hs, body}), body}}

def ascii(s: String) -> R():
  Done{B.from_ascii(s)}

def main() ->
  # method names and validity
  {E.method_name(M.GET{}) == "GET" : String} &
  {E.method_name(M.OPTIONS{}) == "OPTIONS" : String} &
  {E.method_name(M.Other{"PROPFIND"}) == "PROPFIND" : String} &
  {E.method_ok(M.PATCH{}) == True{} : Bool} &
  {E.method_ok(M.Other{"M-SEARCH"}) == True{} : Bool} &
  {E.method_ok(M.Other{""}) == False{} : Bool} &
  {E.method_ok(M.Other{"GE T"}) == False{} : Bool} &
  {E.method_ok(M.Other{"GET\r\n"}) == False{} : Bool} &
  # method values are canonical: Other never holds a fixed name (finding
  # other-head-not-head); names are case-sensitive, so "head" is Other
  {E.method_ok(M.Other{"HEAD"}) == False{} : Bool} &
  {E.method_ok(M.Other{"GET"}) == False{} : Bool} &
  {E.method_ok(M.Other{"POST"}) == False{} : Bool} &
  {E.method_ok(M.Other{"PUT"}) == False{} : Bool} &
  {E.method_ok(M.Other{"DELETE"}) == False{} : Bool} &
  {E.method_ok(M.Other{"PATCH"}) == False{} : Bool} &
  {E.method_ok(M.Other{"OPTIONS"}) == False{} : Bool} &
  {E.method_ok(M.Other{"head"}) == True{} : Bool} &
  {E.method_ok(M.Other{"HEADX"}) == True{} : Bool} &
  {E.method_ok(M.Other{"GE"}) == True{} : Bool} &
  {E.method_of("HEAD") == M.HEAD{} : M.Method} &
  {E.method_of("OPTIONS") == M.OPTIONS{} : M.Method} &
  {E.method_of("head") == M.Other{"head"} : M.Method} &
  {E.method_of("PROPFIND") == M.Other{"PROPFIND"} : M.Method} &
  # wants_length
  {E.wants_length(M.GET{}, []) == False{} : Bool} &
  {E.wants_length(M.GET{}, [1]) == True{} : Bool} &
  {E.wants_length(M.POST{}, []) == True{} : Bool} &
  {E.wants_length(M.PUT{}, []) == True{} : Bool} &
  {E.wants_length(M.PATCH{}, []) == True{} : Bool} &
  {E.wants_length(M.DELETE{}, []) == False{} : Bool} &
  {E.wants_length(M.Other{"POST"}, []) == False{} : Bool} &
  # request_headers
  {E.request_headers(get_req()) ==
    [M.Header{"Host", "example.com"}, M.Header{"Connection", "close"}]
    : List<&2, M.Header>} &
  {E.request_headers(post_req()) ==
    [M.Header{"Host", "api.test:8080"}, M.Header{"Content-Type", "text/plain"},
     M.Header{"Content-Length", "2"}, M.Header{"Connection", "close"}]
    : List<&2, M.Header>} &
  {E.request_headers(post_empty()) ==
    [M.Header{"Host", "a.b"}, M.Header{"Content-Length", "0"}, M.Header{"Connection", "close"}]
    : List<&2, M.Header>} &
  # exact bytes
  {E.request(get_req()) == Done{[71, 69, 84, 32, 47, 32, 72, 84, 84, 80, 47, 49, 46, 49, 13, 10,
     72, 111, 115, 116, 58, 32, 101, 120, 97, 109, 112, 108, 101, 46, 99, 111, 109, 13, 10,
     67, 111, 110, 110, 101, 99, 116, 105, 111, 110, 58, 32, 99, 108, 111, 115, 101, 13, 10,
     13, 10]} : R()} &
  {E.request(post_req()) == ascii("POST /v1/items?x=1 HTTP/1.1\r\nHost: api.test:8080\r\nContent-Type: text/plain\r\nContent-Length: 2\r\nConnection: close\r\n\r\nhi") : R()} &
  {E.request(post_empty()) == ascii("POST / HTTP/1.1\r\nHost: a.b\r\nContent-Length: 0\r\nConnection: close\r\n\r\n") : R()} &
  {E.request(odd_req()) == ascii("PROPFIND /a/b;c?d=e&f HTTP/1.1\r\nHost: 10.0.0.1\r\nX-Time: 12:30:00\r\nX-Empty: \r\nX-Mixed: a b\tc\r\nx-time: dup\r\nConnection: close\r\n\r\n") : R()} &
  {E.request(body_req()) == Done{List.append(&2, U32,
     B.from_ascii("DELETE /x HTTP/1.1\r\nHost: h:1\r\nAccept: */*\r\nContent-Length: 9\r\nConnection: close\r\n\r\n"),
     [13, 10, 13, 10, 0, 255, 128, 58, 32])} : R()} &
  {E.request_head(get_req()) == "GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n" : String} &
  {E.header_line(M.Header{"A", "b"}) == "A: b\r\n" : String} &
  # refusals: header names and values
  {E.request(with_headers([M.Header{"X-Evil", "a\r\nX-Injected: 1"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-Evil", "a\nb"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-Evil", "a\rb"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-A\r\nX-B", "1"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"Bad Name", "1"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"Bad:Name", "1"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"", "1"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-A", " lead"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-A", "trail\t"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-A", "caf\u{e9}"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-A", "nul\u{0}"}])) == bad(bad_header()) : R()} &
  {E.request(with_headers([M.Header{"X-A", "ok"}, M.Header{"X-B", "a\r\n"}])) == bad(bad_header()) : R()} &
  # refusals: reserved headers, in any case
  {E.request(with_headers([M.Header{"Host", "evil.test"}])) == bad(bad_reserved()) : R()} &
  {E.request(with_headers([M.Header{"hOST", "evil.test"}])) == bad(bad_reserved()) : R()} &
  {E.request(with_headers([M.Header{"CONTENT-LENGTH", "5"}])) == bad(bad_reserved()) : R()} &
  {E.request(with_headers([M.Header{"Transfer-Encoding", "chunked"}])) == bad(bad_reserved()) : R()} &
  {E.request(with_headers([M.Header{"X-A", "1"}, M.Header{"connection", "keep-alive"}])) == bad(bad_reserved()) : R()} &
  {E.request(with_headers([M.Header{"Hostname", "x"}, M.Header{"X-Host", "y"}])) ==
    ascii("GET / HTTP/1.1\r\nHost: example.com\r\nHostname: x\r\nX-Host: y\r\nConnection: close\r\n\r\n") : R()} &
  # refusals: method, URL, body
  {E.request(M.Request{M.Other{"GE T"}, url("a", 80n, "/"), [], []}) == bad("invalid method name") : R()} &
  {E.request(M.Request{M.Other{""}, url("a", 80n, "/"), [], []}) == bad("invalid method name") : R()} &
  {E.request(M.Request{M.Other{"G\u{100}T"}, url("a", 80n, "/"), [], []}) == bad("invalid method name") : R()} &
  {E.request(M.Request{M.Other{"HEAD"}, url("a", 80n, "/"), [], []}) == bad("invalid method name") : R()} &
  {E.request(M.Request{M.Other{"POST"}, url("a", 80n, "/"), [], [1]}) == bad("invalid method name") : R()} &
  {E.request(M.Request{M.GET{}, url("a", 0n, "/"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.GET{}, url("a", 65536n, "/"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.GET{}, url("", 80n, "/"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.GET{}, url("Upper.Case", 80n, "/"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.GET{}, url("a", 80n, "x"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.GET{}, url("a", 80n, "/a b"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.GET{}, url("a", 80n, "/\r\n"), [], []}) == bad("invalid URL") : R()} &
  {E.request(M.Request{M.POST{}, url("a", 80n, "/"), [], [65, 256]}) == bad("body cell is not a byte") : R()} &
  {E.request(M.Request{M.POST{}, url("a", 80n, "/"), [], [4294967295]}) == bad("body cell is not a byte") : R()} &
  {E.request_ok(M.Request{M.POST{}, url("a", 80n, "/"), [], [0, 255]}) == True{} : Bool} &
  # host_once (law 8)
  {H.count("host", E.request_headers(get_req())) == 1n : Nat} &
  {H.count("host", E.request_headers(post_req())) == 1n : Nat} &
  {H.count("host", E.request_headers(odd_req())) == 1n : Nat} &
  {H.count("host", E.request_headers(body_req())) == 1n : Nat} &
  # each loop agrees with its spec (the corollaries in encode.bend's note)
  {E.none_reserved(many_hs()) == E.none_reserved.spec(many_hs()) : Bool} &
  {E.none_reserved(List.append(&2, M.Header, many_hs(), [M.Header{"Host", "x"}])) == False{} : Bool} &
  {E.none_reserved.spec(List.append(&2, M.Header, many_hs(), [M.Header{"Host", "x"}])) == False{} : Bool} &
  {E.none_reserved([]) == True{} : Bool} &
  {E.header_lines(many_hs()) == E.header_lines.spec(many_hs()) : String} &
  {E.header_lines(many_hs()) == "X-A: 1\r\nx-b: \r\nX-C: c d\r\n" : String} &
  {E.header_lines([]) == "" : String} &
  {E.request_headers(M.Request{M.PATCH{}, url("a", 80n, "/"), many_hs(), []}) ==
    M.Header{"Host", "a"} <> List.append(&2, M.Header, many_hs(),
      [M.Header{"Content-Length", "0"}, M.Header{"Connection", "close"}])
    : List<&2, M.Header>} &
  {E.request_bytes(body_req()) ==
    List.append(&2, U32, B.from_ascii.spec(E.request_head(body_req())), [13, 10, 13, 10, 0, 255, 128, 58, 32])
    : List<&2, U32>} &
  # request_roundtrip (law 7)
  {SR.decode_request(E.request_bytes(get_req())) == roundtrip(get_req()) : P()} &
  {SR.decode_request(E.request_bytes(post_req())) == roundtrip(post_req()) : P()} &
  {SR.decode_request(E.request_bytes(post_empty())) == roundtrip(post_empty()) : P()} &
  {SR.decode_request(E.request_bytes(odd_req())) == roundtrip(odd_req()) : P()} &
  {SR.decode_request(E.request_bytes(body_req())) == roundtrip(body_req()) : P()} &
  {SR.decode_request(E.request_bytes(get_req())) ==
    Some{SR.ParsedRequest{"GET", "/", [M.Header{"Host", "example.com"}, M.Header{"Connection", "close"}], []}} : P()} &
  # decode_request refuses what E never emits
  {SR.decode_request([]) == None{} : P()} &
  {SR.decode_request(B.from_ascii("\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\nHost: a\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\nHost: a\n\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\rHost: a\r\n\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\n\rx")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.0\r\n\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET /  HTTP/1.1\r\n\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET /\r\n\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\nNoColon\r\n\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\nA:b\r\n\r\n")) == None{} : P()} &
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\nA:\r\n\r\n")) == None{} : P()} &
  # ... and reads the minimal shapes
  {SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\n\r\n")) ==
    Some{SR.ParsedRequest{"GET", "/", [], []}} : P()} &
  {SR.decode_request(B.from_ascii("X Y HTTP/1.1\r\nA: \r\nB: c: d\r\n\r\nrest\r\n\r\n")) ==
    Some{SR.ParsedRequest{"X", "Y", [M.Header{"A", ""}, M.Header{"B", "c: d"}], B.from_ascii("rest\r\n\r\n")}} : P()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
