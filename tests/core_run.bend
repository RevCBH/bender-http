import Base
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/utf8.bend as T

# Runtime tests for num, headers and utf8, on both lanes:
#   bend tests/core_run.bend
#   bend tests/core_run.bend -o /tmp/core_run && /tmp/core_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL".
# These cover the values too large for checker evaluation (LIMIT-scale
# numbers, hostile digit strings that must saturate instead of aborting,
# and sweeps).

# Equality helpers
# ----------------

def nat_is(m: Maybe<&2, Nat>, n: Nat) -> Bool:
  match m:
    case Some{x}:
      Nat.is_eq(x, n)
    case None{}:
      False{}

def is_none(m: Maybe<&2, Nat>) -> Bool:
  Maybe.is_none(&2, Nat, m)

# String equality as a loop (Base's String.eq nests a call per char, which
# overflows the JS lane's stack on the long strings below).
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

def str_none(m: Maybe<&2, String>) -> Bool:
  Maybe.is_none(&2, String, m)

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      U32.is_eq(x, y) && bytes_eq(xs, ys)
    case _ _:
      False{}

# List length as a loop.
def len.go(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      len.go(t, 1n+n)

def strs_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, xs} Con{y, ys}:
      String.eq(x, y) && strs_eq(xs, ys)
    case _ _:
      False{}

# n copies of a char, prepended to acc (a loop)
def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rep(n: Nat, c: Char) -> String:
  rep.go(n, c, SNil{})

# Sweeps
# ------

def dec_rt(+n: Nat) -> Bool:
  nat_is(N.read(N.show(n)), n)

def hex_rt(+n: Nat) -> Bool:
  nat_is(N.hex_read(N.hex_show(n)), n)

# read(show(k)) and hex_read(hex_show(k)) for every k <= n.
def rt_upto(+n: Nat) -> Bool:
  match n:
    case 0n:
      dec_rt(0n) && hex_rt(0n)
    case 1n+p:
      dec_rt(1n+p) && hex_rt(1n+p) && rt_upto(p)

# A string of code points: k * 1009 for k = n .. 0, skipping surrogates
# (mapped to 'x'); spans every encoded width up to U+10FFFF.
def cp(+k: Nat) -> Char:
  +c = U32.from_nat(Nat.mul(k, 1009n))
  Char.from_u32(Bool.pick(U32, U32.is_le(55296, c) && U32.is_le(c, 57343), 120, c))

def sweep(+n: Nat) -> String:
  match n:
    case 0n:
      SCon{cp(0n), SNil{}}
    case 1n+p:
      SCon{cp(1n+p), sweep(p)}

def utf8_rt(+s: String) -> Bool:
  str_is(T.decode(T.encode(s)), s)

def hs() -> List<&2, M.Header>:
  [M.Header{"Content-Type", "text/plain"}, M.Header{"X-A", "1"},
   M.Header{"x-a", "2"}, M.Header{"Set-Cookie", "a=b"}, M.Header{"X-A", "3"}]

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    # num: show
    ("show 0", String.eq(N.show(0n), "0")),
    ("show 9", String.eq(N.show(9n), "9")),
    ("show 10", String.eq(N.show(10n), "10")),
    ("show 65535", String.eq(N.show(65535n), "65535")),
    ("show 1000000", String.eq(N.show(1000000n), "1000000")),
    ("show 100000", String.eq(N.show(100000n), "100000")),
    ("show 16777216", String.eq(N.show(16777216n), "16777216")),
    ("hex_show 0", String.eq(N.hex_show(0n), "0")),
    ("hex_show 255", String.eq(N.hex_show(255n), "ff")),
    ("hex_show 48879", String.eq(N.hex_show(48879n), "beef")),
    ("hex_show 16777216", String.eq(N.hex_show(16777216n), "1000000")),
    # num: read
    ("read 65535", nat_is(N.read("65535"), 65535n)),
    ("read LIMIT", nat_is(N.read("4294967295"), N.LIMIT())),
    ("read LIMIT zeros", nat_is(N.read("000000000004294967295"), N.LIMIT())),
    ("read LIMIT+1", is_none(N.read("4294967296"))),
    ("read 10*LIMIT", is_none(N.read("42949672950"))),
    ("read 26 nines", is_none(N.read("99999999999999999999999999"))),
    ("read 5000 nines", is_none(N.read(rep(5000n, '9')))),
    ("read 5000 zeros", nat_is(N.read(rep(5000n, '0')), 0n)),
    ("read nines then x", is_none(N.read("99999999999999999999999999x"))),
    ("read empty", is_none(N.read(""))),
    ("read sign", is_none(N.read("-1"))),
    ("read space", is_none(N.read("1 "))),
    ("read hex digit", is_none(N.read("1f"))),
    ("read non-byte char", is_none(N.read(SCon{'1', SCon{Char.from_u32(256), SNil{}}}))),
    ("hex_read ffffffff", nat_is(N.hex_read("ffffffff"), N.LIMIT())),
    ("hex_read FFFFFFFF", nat_is(N.hex_read("FFFFFFFF"), N.LIMIT())),
    ("hex_read BeEf", nat_is(N.hex_read("BeEf"), 48879n)),
    ("hex_read 100000000", is_none(N.hex_read("100000000"))),
    ("hex_read 30 fs", is_none(N.hex_read("ffffffffffffffffffffffffffffff"))),
    ("hex_read 5000 Fs", is_none(N.hex_read(rep(5000n, 'F')))),
    ("hex_read 0x", is_none(N.hex_read("0x10"))),
    ("hex_read empty", is_none(N.hex_read(""))),
    ("roundtrip sweep 0..3000", rt_upto(3000n)),
    ("roundtrip 16777216", dec_rt(16777216n) && hex_rt(16777216n)),
    # headers
    ("is_token", H.is_token("X-Request-Id") && Bool.not(H.is_token("X Y"))
      && Bool.not(H.is_token(""))),
    ("is_value", H.is_value("a b") && H.is_value("") && Bool.not(H.is_value(" a"))
      && Bool.not(H.is_value("a\t")) && Bool.not(H.is_value("a\r\nb"))),
    ("headers_ok", H.headers_ok(hs())
      && Bool.not(H.headers_ok([M.Header{"A", "ok"}, M.Header{"B:", "x"}]))),
    ("lower", String.eq(H.lower("Content-LENGTH \u{c9}@[`{Z"), "content-length \u{c9}@[`{z")),
    ("get first", str_is(H.get("x-a", hs()), "1")),
    ("get missing", str_none(H.get("x-b", hs()))),
    ("get lower", str_is(H.get(H.lower("SET-COOKIE"), hs()), "a=b")),
    ("get_all", strs_eq(H.get_all("X-a", hs()), ["1", "2", "3"])),
    ("has/count", H.has("content-type", hs()) && Bool.not(H.has("host", hs()))
      && Nat.is_eq(H.count("X-A", hs()), 3n)),
    ("reserved", H.reserved("HOST") && H.reserved("Content-Length")
      && H.reserved("Transfer-Encoding") && H.reserved("connection")
      && Bool.not(H.reserved("Content-Type"))),
    # utf8
    ("encode widths", bytes_eq(T.encode("A\u{e9}\u{20ac}\u{1f600}"),
      [65, 195, 169, 226, 130, 172, 240, 159, 152, 128])),
    ("decode", str_is(T.decode([99, 97, 102, 195, 169]), "caf\u{e9}")),
    ("decode overlong", str_none(T.decode([192, 175]))),
    ("decode overlong 3", str_none(T.decode([224, 128, 175]))),
    ("decode surrogate", str_none(T.decode([237, 160, 128]))),
    ("decode past max", str_none(T.decode([244, 144, 128, 128]))),
    ("decode truncated", str_none(T.decode([65, 240, 159, 152]))),
    ("decode stray", str_none(T.decode([128, 65]))),
    ("decode non-byte", str_none(T.decode([195, 425]))),
    ("utf8 sweep", utf8_rt(sweep(1103n))),
    ("utf8 long", utf8_rt(rep(200000n, '\u{20ac}'))),
    ("utf8 long length", Nat.is_eq(len.go(T.encode(rep(200000n, '\u{e9}')), 0n), 400000n))
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
