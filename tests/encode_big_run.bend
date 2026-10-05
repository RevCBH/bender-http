import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/encode.bend as E
import ../src/spec_request.bend as SR

# Large-input runtime tests for encode.bend and spec_request.bend. C LANE
# ONLY: E.request itself is stack-safe on both lanes (tests/encode_run.bend
# checks its bytes at 64 KB / 1 MB / 50000 headers on JS too), but the
# roundtrip cases here run SR.decode_request, a law-facing spec that nests
# one call per head byte and per header, and the long-target case runs
# U.ok, which walks the target with plain recursion (url.bend):
#   bend tests/encode_big_run.bend -o /tmp/encode_big_run && /tmp/encode_big_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL".

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

# n copies of one header.
def same(n: Nat, +h: M.Header, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match n:
    case 0n:
      acc
    case 1n+p:
      same(p, h, h <> acc)

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
  cycle(2000000n, 0, [])

def long_value() -> String:
  rep(100000n, 'v', "")

def cases() -> List<&1, String & Bool>:
  [
    ("2 MB body bytes", done_is(E.request(req(M.PUT{}, [], big_body())),
      List.append(&2, U32, B.from_ascii("PUT / HTTP/1.1\r\nHost: example.com\r\nContent-Length: 2000000\r\nConnection: close\r\n\r\n"), big_body()))),
    ("2 MB body roundtrip", roundtrip(req(M.POST{}, [M.Header{"Content-Type", "application/octet-stream"}], big_body()))),
    ("2 MB body host_once", host_once(req(M.POST{}, [], big_body()))),
    ("100k value roundtrip", roundtrip(req(M.GET{}, [M.Header{"X-Long", long_value()}], []))),
    ("100k bad value refused", fail_is(E.request(req(M.GET{}, [M.Header{"X", long_value() ++ "\r"}], [])), "invalid header name or value")),
    ("5000 headers roundtrip", roundtrip(req(M.GET{}, many(5000n, "a: b", []), [9]))),
    ("reserved after 5000 refused", fail_is(E.request(req(M.GET{}, List.append(&2, M.Header, many(5000n, "ok", []), [M.Header{"Content-Length", "1"}]), [])), "reserved header (Host, Content-Length, Transfer-Encoding or Connection)")),
    ("byte 256 after 2 MB refused", fail_is(E.request(req(M.POST{}, [], List.append(&2, U32, big_body(), [256]))), "body cell is not a byte")),
    ("64 KB target roundtrip", roundtrip(M.Request{M.GET{}, url("example.com", 80n, "/" ++ rep(65535n, 't', "")), [], []})),
    ("50000 headers roundtrip", roundtrip(req(M.GET{}, same(50000n, M.Header{"X-a", "v w"}, []), [1, 2]))),
    ("100k name roundtrip", roundtrip(req(M.GET{}, [M.Header{rep(100000n, 'n', ""), "1"}], []))),
    ("1 MB value bytes", done_is(E.request(req(M.GET{}, [M.Header{"X-Big", rep(1048576n, 'v', "")}], [])),
      B.from_ascii("GET / HTTP/1.1\r\nHost: example.com\r\nX-Big: " ++ rep(1048576n, 'v', "") ++ "\r\nConnection: close\r\n\r\n"))),
    ("1 MB bad value refused", fail_is(E.request(req(M.GET{}, [M.Header{"X", rep(1048576n, 'v', "\n")}], [])), "invalid header name or value")),
    ("Other HEAD refused", fail_is(E.request(req(M.Other{"HEAD"}, [], [])), "invalid method name")),
    ("decode 2 MB garbage", Maybe.is_none(&2, SR.ParsedRequest, SR.decode_request(big_body())))
  ]

def main() -> IO(Unit):
  do IO<Unit>:
    all : Bool <- run(cases(), True{})
    IO.print(Bool.pick(String, all, "ALL PASS", "SOME FAIL"))
