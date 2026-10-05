import Base
import ../src/bytes.bend as B

# Runtime tests for bytes.bend at sizes the JS lane's stack cannot nest
# (it overflows near 20-40k calls), on both lanes:
#   bend tests/bytes_run.bend
#   bend tests/bytes_run.bend -o /tmp/bytes_run && /tmp/bytes_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL". Regression
# for the JS-lane crashes on a 40 KB request body (all_bytes), head
# (is_ascii, from_ascii) and response line (to_latin1). The helpers here
# are loops too, so only the library is being tested.

# Builders and checks (loops)
# ---------------------------

# n copies of x, prepended to acc.
def cells.go(n: Nat, +x: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      cells.go(p, x, x <> acc)

# n copies of c, prepended to acc.
def chars.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      chars.go(p, c, SCon{c, acc})

def len.go(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      len.go(t, 1n+n)

def slen.go(s: String, n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{c, t}:
      slen.go(t, 1n+n)

# Every cell is x.
def all_is.go(xs: List<&2, U32>, +x: U32, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{h, t}:
      all_is.go(t, x, ok && U32.is_eq(h, x))

# Every char is c.
def all_char.go(s: String, +c: Char, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{d, t}:
      all_char.go(t, c, ok && Char.is_eq(d, c))

def bytes_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      bytes_eq.go(xs, ys, ok && U32.is_eq(x, y))
    case _ _:
      False{}

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def M1() -> Nat:
  1000000n

def K200() -> Nat:
  200000n

# The cases
# ---------

def cases() -> List<(String & Bool)>:
  [
    ("all_bytes 1M", B.all_bytes(cells.go(M1(), 255, Nil{}))),
    ("all_bytes 200k, 256 last", Bool.not(B.all_bytes(cells.go(K200(), 7, [256])))),
    ("all_bytes 200k, 300 first", Bool.not(B.all_bytes(300 <> cells.go(K200(), 7, Nil{})))),
    ("is_ascii 1M", B.is_ascii(chars.go(M1(), 'a', SNil{}))),
    ("is_ascii 200k, e-acute last", Bool.not(B.is_ascii(chars.go(K200(), 'a', "\u{e9}")))),
    ("from_ascii 1M length", Nat.is_eq(len.go(B.from_ascii(chars.go(M1(), 'a', SNil{})), 0n), M1())),
    ("from_ascii 1M values", all_is.go(B.from_ascii(chars.go(M1(), 'a', SNil{})), 97, True{})),
    ("from_ascii order", bytes_eq.go(B.from_ascii(chars.go(K200(), 'a', "\r\n")),
      List.reverse(&2, U32, 10 <> 13 <> cells.go(K200(), 97, Nil{})), True{})),
    ("from_ascii_onto 200k + body", bytes_eq.go(B.from_ascii_onto(chars.go(K200(), 'a', SNil{}), [1, 2]),
      cells.go(K200(), 97, [1, 2]), True{})),
    ("from_ascii_onto empty head", bytes_eq.go(B.from_ascii_onto("", cells.go(K200(), 5, Nil{})),
      cells.go(K200(), 5, Nil{}), True{})),
    ("to_latin1 1M length", Nat.is_eq(slen.go(B.to_latin1(cells.go(M1(), 233, Nil{})), 0n), M1())),
    ("to_latin1 1M values", all_char.go(B.to_latin1(cells.go(M1(), 233, Nil{})), '\u{e9}', True{})),
    ("to_latin1 order", str_eq.go(B.to_latin1(cells.go(K200(), 97, [13, 10])),
      chars.go(K200(), 'a', "\r\n"), True{})),
    ("latin1_onto reversed line", str_eq.go(B.latin1_onto(B.rev(U32, cells.go(K200(), 98, [65]), Nil{}), "z"),
      chars.go(K200(), 'b', "Az"), True{})),
    ("rev 1M", Nat.is_eq(len.go(B.rev(U32, cells.go(M1(), 1, Nil{}), [2]), 0n), 1000001n)),
    ("small: loops agree with specs", str_eq.go(B.to_latin1([72, 233, 255]), B.to_latin1.spec([72, 233, 255]), True{})
      && bytes_eq.go(B.from_ascii("Hi\r\n"), B.from_ascii.spec("Hi\r\n"), True{})
      && Bool.not(B.all_bytes([1, 256])) && B.all_bytes.spec([1, 255]))
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
