import Base
import ../src/message.bend as M
import ../src/headers.bend as H

# Runtime tests for headers.bend at sizes the JS lane's stack cannot nest
# (it overflows near 20-40k calls), on both lanes:
#   bend tests/headers_run.bend
#   bend tests/headers_run.bend -o /tmp/headers_run && /tmp/headers_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL". Regression
# for the JS-lane crashes on a long header name or value (is_token,
# is_value, lower), on many headers (headers_ok, get_all, get, has), and
# for the lookup lowering its query once. The helpers here are loops too.

# Builders and checks (loops)
# ---------------------------

# n copies of c, prepended to acc.
def chars.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      chars.go(p, c, SCon{c, acc})

# n copies of the header (name, value), prepended to acc.
def hdrs.go(n: Nat, +name: String, +value: String, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match n:
    case 0n:
      acc
    case 1n+p:
      hdrs.go(p, name, value, M.Header{name, value} <> acc)

def slen.go(xs: List<&2, String>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      slen.go(t, 1n+n)

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def str_is(m: Maybe<&2, String>, s: String) -> Bool:
  match m:
    case Some{x}:
      str_eq.go(x, s, True{})
    case None{}:
      False{}

def strs_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      String.eq(x, y) && strs_eq(xs, ys)
    case _ _:
      False{}

def M1() -> Nat:
  1000000n

def K200() -> Nat:
  200000n

# 200k "X-a: v" headers, then the given tail.
def many(tail: List<&2, M.Header>) -> List<&2, M.Header>:
  hdrs.go(K200(), "X-a", "v", tail)

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    ("is_token 1M", H.is_token(chars.go(M1(), 'x', SNil{}))),
    ("is_token 200k, space last", Bool.not(H.is_token(chars.go(K200(), 'x', " ")))),
    ("is_value 1M", H.is_value(chars.go(M1(), 'v', SNil{}))),
    ("is_value 200k, CR inside", Bool.not(H.is_value(chars.go(K200(), 'v', "\rv")))),
    ("header_ok 1M value", H.header_ok(M.Header{"X-Big", chars.go(M1(), 'v', SNil{})})),
    ("header_ok 1M name", H.header_ok(M.Header{chars.go(M1(), 'n', SNil{}), "v"})),
    ("headers_ok 200k", H.headers_ok(many(Nil{}))),
    ("headers_ok 200k, bad last", Bool.not(H.headers_ok(many([M.Header{"Bad Name", "v"}])))),
    ("lower 1M", str_eq.go(H.lower(chars.go(M1(), 'A', "Z-\u{c9}")), chars.go(M1(), 'a', "z-\u{c9}"), True{})),
    ("name_eq long vs short", Bool.not(H.name_eq("host", chars.go(K200(), 'H', SNil{})))),
    ("reserved 1M name", Bool.not(H.reserved(chars.go(M1(), 'h', SNil{})))),
    ("get_all 200k, one match last", strs_eq(H.get_all("content-length", many([M.Header{"Content-Length", "0"}])), ["0"])),
    ("get_all 200k matches", Nat.is_eq(slen.go(H.get_all("X-A", many(Nil{})), 0n), K200())),
    ("get_all order", strs_eq(H.get_all("x-a", M.Header{"x-A", "1"} <> hdrs.go(K200(), "Y", "v", [M.Header{"X-a", "2"}])), ["1", "2"])),
    ("has 200k, last", H.has("Content-Length", many([M.Header{"content-length", "0"}]))),
    ("has 200k, absent", Bool.not(H.has("transfer-encoding", many(Nil{})))),
    ("get 200k, last", str_is(H.get("CONTENT-LENGTH", many([M.Header{"Content-Length", "7"}])), "7")),
    ("get 200k, first of two", str_is(H.get("x-a", many(Nil{})), "v")),
    ("get 200k, absent", Maybe.is_none(&2, String, H.get("location", many(Nil{})))),
    ("get lower", str_is(H.get(H.lower("X-B"), [M.Header{"x-b", "1"}]), "1"))
  ]

def report(xs: List<(String & Bool)>, fails: Nat) -> IO(Unit):
  match xs:
    case Nil{}:
      match fails:
        case 0n:
          IO.print("ALL PASS")
        case 1n+p:
          IO.print("SOME FAIL: " ++ Nat.show(1n+p))
    case Con{c, t}:
      match c:
        case (name, ok):
          match ok:
            case True{}:
              do IO<Unit>:
                IO.print("PASS " ++ name)
                report(t, fails)
            case False{}:
              do IO<Unit>:
                IO.print("FAIL " ++ name)
                report(t, 1n+fails)

def main() -> IO(Unit):
  report(cases(), 0n)
