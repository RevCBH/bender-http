import Base
import ../src/bytes.bend as B
import ../src/tls.bend as T

# bend examples/tls_raw.bend -- HOST IP [PORT [TIMEOUT_MS]]
#   bend examples/tls_raw.bend -- example.com "$(getent ahostsv4 example.com | head -1 | cut -d' ' -f1)"
#
# One raw HTTPS exchange with Tls.exchange and none of the library's encoder
# or decoder: sends a hand-written "GET / HTTP/1.1" for HOST to IP:PORT
# (default 443, timeout 10000 ms, at most 16 MiB back) and prints the status
# line and the number of bytes received, or the error code and text.

def is_cr(k: B.Class) -> Bool:
  match k:
    case B.Cr{}:
      True{}
    case _:
      False{}

# The bytes before the first CR, reversed: once done, the rest is skipped
# (tail recursion, so a long response does not grow the stack).
def line_rev(xs: List<&2, U32>, done: Bool, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{+h, t}:
      +stop = done || is_cr(B.class(h))
      line_rev(t, stop, Bool.pick(List<&2, U32>, stop, acc, h <> acc))

# At most n bytes.
def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 1n+p Con{h, t}:
      h <> take(p, t)
    case _ _:
      []

# The first line, at most 200 bytes of it (to_latin1 recurses per byte).
def first_line(xs: List<&2, U32>) -> List<&2, U32>:
  List.reverse(&2, U32, line_rev(take(200n, xs), False{}, []))

def count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{_, t}:
      count(t, 1n+n)

def request(host: String) -> List<&2, U32>:
  B.from_ascii("GET / HTTP/1.1\r\nHost: " ++ host ++ "\r\nConnection: close\r\n\r\n")

def show(r: Result<&1, &1, U32 & String, List<&2, U32>>) -> IO(Unit):
  match r:
    case Fail{e}:
      (c, m) = e
      IO.print("error " ++ U32.show(c) ++ ": " ++ m)
    case Done{xs}:
      +ys = xs
      do IO<Unit>:
        IO.print(B.to_latin1(first_line(ys)))
        IO.print(Nat.show(count(ys, 0n)) ++ " bytes")

def number(s: String, default: U32) -> U32:
  Maybe.default(&2, U32, U32.read(s), default)

def timeout_of(rest: List<String>) -> U32:
  match rest:
    case Nil{}:
      10000
    case t <> _:
      number(t, 10000)

# PORT and TIMEOUT_MS, when given.
def settings(rest: List<String>) -> U32 & U32:
  match rest:
    case Nil{}:
      (443, 10000)
    case p <> t:
      (number(p, 443), timeout_of(t))

def run(host: String, ip: String, s: U32 & U32) -> IO(Unit):
  (port, timeout) = s
  +h = host
  IO.bind(Result<&1, &1, U32 & String, List<&2, U32>>, Unit,
    T.Tls.exchange(h, ip, port, request(h), 16777216, timeout), show)

def start(args: List<String>) -> IO(Unit):
  match args:
    case _ <> host <> ip <> rest:
      run(host, ip, settings(rest))
    case _:
      IO.print("usage: tls_raw HOST IP [PORT [TIMEOUT_MS]]")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    start(args)
