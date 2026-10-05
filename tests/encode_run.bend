import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/encode.bend as E
import ../src/spec_request.bend as SR

# Runtime tests for encode.bend and spec_request.bend, on both lanes:
#   bend tests/encode_run.bend
#   bend tests/encode_run.bend -o /tmp/encode_run && /tmp/encode_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL".
# These cover sizes too large for checker evaluation: long bodies (every
# byte value), long header names and values, many headers, and the
# roundtrip of each.
# Regression (finding js-request-body-head-overflow): E.request used to
# nest one call per body byte, head char and header, and the JS lane died
# with "memory fault" past ~30-40k of any of them. The "64 KB" / "1 MB" /
# "50000 headers" cases check the exact bytes E.request emits at those
# sizes, against an expected encoding built here with independent loops.
# The roundtrip cases stay smaller: SR.decode_request is a law-facing spec
# (plain recursion, one call per head byte and per header) and is never
# called at runtime. tests/encode_big_run.bend (C lane) roundtrips larger
# inputs and has the 1 MB header value cases: on JS, H.is_value is
# quadratic in the value's length (H.last_not_ows rebuilds SCon{d, u} per
# char; 256 KB takes 10 s), so header values here stay at 64 KB.

# Equality helpers (loops, so long lists do not grow the stack)
# -------------------------------------------------------------

def bytes_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      bytes_eq.go(xs, ys, ok && U32.is_eq(x, y))
    case _ _:
      False{}

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  bytes_eq.go(a, b, True{})

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def str_eq(a: String, b: String) -> Bool:
  str_eq.go(a, b, True{})

def headers_eq(a: List<&2, M.Header>, b: List<&2, M.Header>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{M.Header{n, v}, xs} Con{M.Header{m, w}, ys}:
      str_eq(n, m) && str_eq(v, w) && headers_eq(xs, ys)
    case _ _:
      False{}

def R() -> Type:
  Result<&2, &2, M.Error, List<&2, U32>>

def done_is(r: R(), b: List<&2, U32>) -> Bool:
  match r:
    case Done{x}:
      bytes_eq(x, b)
    case Fail{e}:
      False{}

def fail_is(r: R(), reason: String) -> Bool:
  match r:
    case Fail{M.BadRequest{why}}:
      str_eq(why, reason)
    case _:
      False{}

# Builders
# --------

# n bytes cycling through 0..255.
def cycle(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      +x = (b % 256 : U32)
      cycle(p, (b + 1 : U32), x <> acc)

def rep(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep(p, c, SCon{c, acc})

# s repeated n times, then acc.
def srep(n: Nat, +s: String, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      srep(p, s, s ++ acc)

# n copies of one header.
def same(n: Nat, +h: M.Header, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match n:
    case 0n:
      acc
    case 1n+p:
      same(p, h, h <> acc)

# xs reversed onto acc.
def rev_onto(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev_onto(t, h <> acc)

# The char codes of s, reversed onto acc.
def codes_rev(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      codes_rev(t, Char.to_u32(c) <> acc)

# The bytes of the head text, then the body (built without bytes.bend).
def expected(head: String, body: List<&2, U32>) -> List<&2, U32>:
  rev_onto(codes_rev(head, []), body)

# A GET of / on example.com with the given field lines between Host and
# Connection.
def get_head(lines: String) -> String:
  "GET / HTTP/1.1\r\nHost: example.com\r\n" ++ lines ++ "Connection: close\r\n\r\n"

# n headers X-0: v .. X-(n-1): v
def many(+n: Nat, +v: String, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match n:
    case 0n:
      acc
    case 1n+p:
      many(p, v, M.Header{"X-" ++ N.show(p), v} <> acc)

def url(host: String, port: Nat, target: String) -> M.Url:
  M.Url{M.Http{}, host, port, target}

def req(m: M.Method, hs: List<&2, M.Header>, body: List<&2, U32>) -> M.Request:
  M.Request{m, url("example.com", 80n, "/"), hs, body}

# The roundtrip law on one request: decode_request(request_bytes(r)) gives
# back the method name, target, request_headers(r) and body.
def roundtrip.check(p: Maybe<&2, SR.ParsedRequest>, +r: M.Request) -> Bool:
  match p:
    case Some{SR.ParsedRequest{m, t, hs, body}}:
      match r:
        case M.Request{+rm, M.Url{s, h, port, rt}, rhs, +rbody}:
          str_eq(m, E.method_name(rm)) && str_eq(t, rt)
            && headers_eq(hs, E.request_headers(M.Request{rm, M.Url{s, h, port, rt}, rhs, rbody}))
            && bytes_eq(body, rbody)
    case None{}:
      False{}

def roundtrip(+r: M.Request) -> Bool:
  roundtrip.check(SR.decode_request(E.request_bytes(r)), r)

def host_once(r: M.Request) -> Bool:
  Nat.is_eq(H.count("host", E.request_headers(r)), 1n)

# Cases
# -----

def check(name: String, +ok: Bool) -> IO(Bool):
  do IO<Bool>:
    IO.print(Bool.pick(String, ok, "PASS ", "FAIL ") ++ name)
    return ok

def run(cases: List<&1, String & Bool>, all: Bool) -> IO(Bool):
  match cases:
    case Nil{}:
      IO.pure(Bool, all)
    case Con{c, rest}:
      match c:
        case (name, ok):
          do IO<Bool>:
            r : Bool <- check(name, ok)
            run(rest, all && r)

def big_body() -> List<&2, U32>:
  cycle(10000n, 0, [])

def long_value() -> String:
  rep(2000n, 'v', "")

def kb64() -> Nat:
  65536n

def mb1() -> Nat:
  1048576n

def body_case(+n: Nat) -> Bool:
  done_is(E.request(req(M.POST{}, [], cycle(n, 0, []))),
    expected("POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: " ++ N.show(n)
      ++ "\r\nConnection: close\r\n\r\n", cycle(n, 0, [])))

def value_case(+n: Nat) -> Bool:
  done_is(E.request(req(M.GET{}, [M.Header{"X-Big", rep(n, 'v', "")}], [])),
    expected(get_head("X-Big: " ++ rep(n, 'v', "") ++ "\r\n"), []))

def name_case(+n: Nat) -> Bool:
  done_is(E.request(req(M.GET{}, [M.Header{rep(n, 'n', ""), "1"}], [])),
    expected(get_head(rep(n, 'n', "") ++ ": 1\r\n"), []))

def count_case(+n: Nat) -> Bool:
  done_is(E.request(req(M.GET{}, same(n, M.Header{"X-a", "v"}, []), [])),
    expected(get_head(srep(n, "X-a: v\r\n", "")), []))

def cases() -> List<&1, String & Bool>:
  [
    ("64 KB body bytes", body_case(kb64())),
    ("1 MB body bytes", body_case(mb1())),
    ("64 KB value bytes", value_case(kb64())),
    ("64 KB name bytes", name_case(kb64())),
    ("1 MB name bytes", name_case(mb1())),
    ("50000 headers bytes", count_case(50000n)),
    ("64 KB bad value refused", fail_is(E.request(req(M.GET{}, [M.Header{"X", rep(kb64(), 'v', "\n")}], [])), "invalid header name or value")),
    ("1 MB body then 256 refused", fail_is(E.request(req(M.POST{}, [], cycle(mb1(), 0, [256]))), "body cell is not a byte")),
    ("50000 headers then reserved refused", fail_is(E.request(req(M.GET{}, same(50000n, M.Header{"X-a", "v"}, [M.Header{"connection", "x"}]), [])), "reserved header (Host, Content-Length, Transfer-Encoding or Connection)")),
    ("50000 headers then bad refused", fail_is(E.request(req(M.GET{}, same(50000n, M.Header{"X-a", "v"}, [M.Header{"X b", "x"}]), [])), "invalid header name or value")),
    ("50000 headers host_once", host_once(req(M.GET{}, same(50000n, M.Header{"X-a", "v"}, []), []))),
    ("Other HEAD refused", fail_is(E.request(req(M.Other{"HEAD"}, [], [])), "invalid method name")),
    ("Other POST refused", fail_is(E.request(req(M.Other{"POST"}, [], [1])), "invalid method name")),
    ("Other head is its own method", done_is(E.request(req(M.Other{"head"}, [], [])),
      B.from_ascii("head / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"))),
    ("get bytes", done_is(E.request(req(M.GET{}, [], [])),
      B.from_ascii("GET / HTTP/1.1\r\nHost: example.com\r\nConnection: close\r\n\r\n"))),
    ("post bytes", done_is(E.request(M.Request{M.POST{}, url("api.test", 8080n, "/v1?q=1"),
        [M.Header{"Content-Type", "application/json"}], B.from_ascii("{}")}),
      B.from_ascii("POST /v1?q=1 HTTP/1.1\r\nHost: api.test:8080\r\nContent-Type: application/json\r\nContent-Length: 2\r\nConnection: close\r\n\r\n{}"))),
    ("https default port", done_is(E.request(M.Request{M.PUT{}, M.Url{M.Https{}, "h.io", 443n, "/"}, [], []}),
      B.from_ascii("PUT / HTTP/1.1\r\nHost: h.io\r\nContent-Length: 0\r\nConnection: close\r\n\r\n"))),
    ("https other port", done_is(E.request(M.Request{M.HEAD{}, M.Url{M.Https{}, "h.io", 80n, "/"}, [], []}),
      B.from_ascii("HEAD / HTTP/1.1\r\nHost: h.io:80\r\nConnection: close\r\n\r\n"))),
    ("big body length", done_is(E.request(req(M.POST{}, [], big_body())),
      List.append(&2, U32, B.from_ascii("POST / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 10000\r\nConnection: close\r\n\r\n"), big_body()))),
    ("big body roundtrip", roundtrip(req(M.POST{}, [], big_body()))),
    ("long value roundtrip", roundtrip(req(M.GET{}, [M.Header{"X-Long", long_value()}], []))),
    ("many headers roundtrip", roundtrip(req(M.GET{}, many(300n, "a: b\tc", []), [1, 2, 3]))),
    ("many headers host_once", host_once(req(M.GET{}, many(300n, "x", []), []))),
    ("other method roundtrip", roundtrip(M.Request{M.Other{"M-SEARCH"}, url("239.255.255.250", 1900n, "/*x"), [M.Header{"Man", "\"ssdp:discover\""}], []})),
    ("crlf body roundtrip", roundtrip(req(M.PATCH{}, [M.Header{"A", ""}], B.from_ascii("\r\n\r\nGET / HTTP/1.1\r\n\r\n")))),
    ("value crlf refused", fail_is(E.request(req(M.GET{}, [M.Header{"X", "a\r\nHost: evil"}], [])), "invalid header name or value")),
    ("long bad value refused", fail_is(E.request(req(M.GET{}, [M.Header{"X", long_value() ++ "\n"}], [])), "invalid header name or value")),
    ("bad header after many", fail_is(E.request(req(M.GET{}, List.append(&2, M.Header, many(200n, "ok", []), [M.Header{"Y Z", "1"}]), [])), "invalid header name or value")),
    ("reserved refused", fail_is(E.request(req(M.GET{}, [M.Header{"tRaNsFeR-eNcOdInG", "chunked"}], [])), "reserved header (Host, Content-Length, Transfer-Encoding or Connection)")),
    ("host refused", fail_is(E.request(req(M.GET{}, many(50n, "x", [M.Header{"HOST", "evil"}]), [])), "reserved header (Host, Content-Length, Transfer-Encoding or Connection)")),
    ("bad method refused", fail_is(E.request(req(M.Other{"GET /evil HTTP/1.1\r\n"}, [], [])), "invalid method name")),
    ("bad url refused", fail_is(E.request(M.Request{M.GET{}, url("a", 80n, "/x\r\nHost: b"), [], []}), "invalid URL")),
    ("byte 256 refused", fail_is(E.request(req(M.POST{}, [], List.append(&2, U32, big_body(), [256]))), "body cell is not a byte")),
    ("decode empty", Maybe.is_none(&2, SR.ParsedRequest, SR.decode_request([]))),
    ("decode truncated", Maybe.is_none(&2, SR.ParsedRequest, SR.decode_request(B.from_ascii("GET / HTTP/1.1\r\nA: b\r\n")))),
    ("decode bare lf", Maybe.is_none(&2, SR.ParsedRequest, SR.decode_request(B.from_ascii("GET / HTTP/1.1\nA: b\n\n")))),
    ("decode garbage", Maybe.is_none(&2, SR.ParsedRequest, SR.decode_request(big_body())))
  ]

def main() -> IO(Unit):
  do IO<Unit>:
    all : Bool <- run(cases(), True{})
    IO.print(Bool.pick(String, all, "ALL PASS", "SOME FAIL"))
