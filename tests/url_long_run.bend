import Base
import ../src/message.bend as M
import ../src/url.bend as U

# Long-input runtime tests for url.bend, C lane only:
#   bend tests/url_long_run.bend -o /tmp/url_long_run && /tmp/url_long_run
# parse and its helpers are plain (not tail) structural recursions, kept that
# way for the proofs. The C lane has no call stack, so any length works; the
# JS lane overflows its stack somewhere past 10k-20k chars (tests/url_run.bend
# stays below that). These cases check that hostile, very long URLs (say, a
# Location header) parse or fail on the C lane without aborting.

# Helpers
# -------

def scheme_is(a: M.Scheme, b: M.Scheme) -> Bool:
  match a b:
    case M.Http{} M.Http{}:
      True{}
    case M.Https{} M.Https{}:
      True{}
    case _ _:
      False{}

# String equality as a loop (Base's String.eq nests a call per char, which
# overflows the JS lane's stack near 15000 chars).
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

def url_eq(a: M.Url, b: M.Url) -> Bool:
  match a b:
    case M.Url{s1, h1, p1, t1} M.Url{s2, h2, p2, t2}:
      scheme_is(s1, s2) && str_eq(h1, h2) && Nat.is_eq(p1, p2) && str_eq(t1, t2)

def done_is(r: Result<&2, &2, M.Error, M.Url>, u: M.Url) -> Bool:
  match r:
    case Done{v}:
      url_eq(v, u)
    case Fail{e}:
      False{}

def http(h: String, p: Nat, t: String) -> M.Url:
  M.Url{M.Http{}, h, p, t}

def https(h: String, p: Nat, t: String) -> M.Url:
  M.Url{M.Https{}, h, p, t}

def parses(s: String, u: M.Url) -> Bool:
  done_is(U.parse(s), u)

def fail_is(r: Result<&2, &2, M.Error, M.Url>, reason: String) -> Bool:
  match r:
    case Fail{e}:
      match e:
        case M.BadUrl{x}:
          String.eq(x, reason)
        case _:
          False{}
    case Done{v}:
      False{}

def fails_with(s: String, reason: String) -> Bool:
  fail_is(U.parse(s), reason)

def fails(s: String) -> Bool:
  Result.is_fail(&2, &2, M.Error, M.Url, U.parse(s))

# ok(u) and parse(show(u)) == Done{u}
def rt(+u: M.Url) -> Bool:
  U.ok(u) && done_is(U.parse(U.show(u)), u)

# n copies of a char, prepended to acc (a loop)
def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rep(n: Nat, c: Char) -> String:
  rep.go(n, c, SNil{})

# Roundtrip for ports p, p - step, p - 2 step, ... (both schemes), while p > 0.
# Structural on a fuel count k.
def port_sweep(k: Nat, +p: Nat, +step: Nat) -> Bool:
  match k:
    case 0n:
      True{}
    case 1n+q:
      rt(http("h", p, "/")) && rt(https("example.com", p, "/a?b"))
        && port_sweep(q, Nat.sub(p, step), step)

# parse("http://h:" ++ show(p)) for p > 65535 must fail.
def high_port(+p: Nat) -> Bool:
  fails_with("http://h:" ++ Nat.show(p) ++ "/", "port out of range")

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    ("target 200k", rt(http("h", 80n, "/" ++ rep(200000n, 'a')))),
    ("host 100k", rt(https(rep(100000n, 'a') ++ ".com", 8443n, "/"))),
    ("query 100k no path", parses("http://h?" ++ rep(100000n, 'q'), http("h", 80n, "/?" ++ rep(100000n, 'q')))),
    ("fragment 100k", parses("http://h/p#" ++ rep(100000n, 'f'), http("h", 80n, "/p"))),
    ("port 100k nines", fails_with("http://h:" ++ rep(100000n, '9') ++ "/", "port out of range")),
    ("port 100k zeros then 80", parses("http://h:" ++ rep(100000n, '0') ++ "80/", http("h", 80n, "/"))),
    ("scheme 100k, no colon", fails_with(rep(100000n, 'h'), "unsupported scheme")),
    ("userinfo 100k", fails_with("http://" ++ rep(100000n, 'u') ++ "@h/", "userinfo is not supported")),
    ("space at the end of 100k", fails_with("http://h/" ++ rep(100000n, 'a') ++ " ", "bad char in target"))
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
