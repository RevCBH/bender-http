import Base
import ../src/bytes.bend as B
import ../src/tls.bend as T

# Tls.exchange against the local servers of tests/tls_server.py (one mode per
# port, from 18440), which tests/tls_live.sh starts with SSL_CERT_FILE set to
# their self-signed certificate (for localhost and 127.0.0.1). Linux errno
# values.
#   tests/tls_live.sh            (both lanes)

def R() -> Type:
  Result<&1, &1, U32 & String, List<&2, U32>>

type Want is Data:
  Code{code: U32}               # this failure
  Either{a: U32, b: U32}        # one of these failures
  Exactly{xs: List<&2, U32>}    # these bytes
  Size{n: Nat}                  # this many bytes

# CR ends the line; so do other control bytes (keeps the output printable).
def is_cr(k: B.Class) -> Bool:
  match k:
    case B.Cr{}:
      True{}
    case B.Lf{}:
      True{}
    case B.Ctl{}:
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

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      U32.is_eq(x, y) && bytes_eq(s, t)
    case _ _:
      False{}

def want_code(w: Want, +c: U32) -> Bool:
  match w:
    case Code{k}:
      U32.is_eq(k, c)
    case Either{a, b}:
      U32.is_eq(a, c) || U32.is_eq(b, c)
    case _:
      False{}

def want_bytes(w: Want, +ys: List<&2, U32>) -> Bool:
  match w:
    case Exactly{xs}:
      bytes_eq(xs, ys)
    case Size{n}:
      Nat.is_eq(n, count(ys, 0n))
    case _:
      False{}

def verdict(name: String, ok: Bool, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name ++ " (" ++ got ++ ")")
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got)

def expect(name: String, w: Want, r: R) -> IO(Unit):
  match r:
    case Fail{e}:
      (c, m) = e
      +k = c
      verdict(name, want_code(w, k), "error " ++ U32.show(k) ++ ": " ++ m)
    case Done{xs}:
      +ys = xs
      verdict(name, want_bytes(w, ys), Nat.show(count(ys, 0n)) ++ " bytes: "
        ++ B.to_latin1(first_line(ys)))

def check(name: String, w: Want, io: IO(R)) -> IO(Unit):
  IO.bind(R, Unit, io, r => expect(name, w, r))

def get(host: String) -> List<&2, U32>:
  B.from_ascii("GET / HTTP/1.1\r\nHost: " ++ host ++ "\r\nConnection: close\r\n\r\n")

def port(mode: U32) -> U32:
  (18440 + mode : U32)

# server_name localhost, the mode's port, a GET, max 1 MiB, timeout 2000 ms.
def x(mode: U32) -> IO(R):
  T.Tls.exchange("localhost", "127.0.0.1", port(mode), get("localhost"), 1048576, 2000)

def response() -> List<&2, U32>:
  B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")

# n copies of b, then tail (tail recursion: n may be millions).
def rep(n: Nat, +b: U32, tail: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      tail
    case 1n+p:
      rep(p, b, b <> tail)

def every_byte(n: Nat, tail: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      tail
    case 1n+p:
      +q = p
      every_byte(q, U32.from_nat(q) <> tail)

def crlf2() -> List<&2, U32>:
  [13, 10, 13, 10]

# The last of n + 1 exchanges in a row with one server: tls_live.sh lowers
# the descriptor limit to 256, so a leak per exchange ends in EMFILE (24).
def repeat(n: Nat, mode: U32) -> IO(R):
  match n:
    case 0n:
      x(mode)
    case 1n+p:
      +m = mode
      IO.bind(R, R, x(m), r => repeat(p, m))

def repeat_name(n: Nat, name: String) -> IO(R):
  match n:
    case 0n:
      T.Tls.exchange(name, "127.0.0.1", port(0), get("x"), 1000, 2000)
    case 1n+p:
      +s = name
      IO.bind(R, R, T.Tls.exchange(s, "127.0.0.1", port(0), get("x"), 1000, 2000),
        r => repeat_name(p, s))

# Four exchanges at once. Each parks on its socket while it waits (both
# lanes), so the silent server's 2 s timeout prints last.
def concurrently() -> IO(Unit):
  do IO<Unit>:
    a : Chan(Unit) <- IO.fork(Unit, check("concurrent: silent", Code{110}, x(3)))
    b : Chan(Unit) <- IO.fork(Unit, check("concurrent: ok", Exactly{response()}, x(0)))
    c : Chan(Unit) <- IO.fork(Unit, check("concurrent: big", Size{100000n}, x(2)))
    d : Chan(Unit) <- IO.fork(Unit, check("concurrent: bad name", Code{71},
      T.Tls.exchange("example.com", "127.0.0.1", port(0), get("x"), 1000, 2000)))
    IO.join(Unit, a)
    IO.join(Unit, b)
    IO.join(Unit, c)
    IO.join(Unit, d)

def main() -> IO(Unit):
  do IO<Unit>:
    check("ok", Exactly{response()}, x(0))
    check("ok with server_name 127.0.0.1 (IP SAN, no SNI)", Exactly{response()},
      T.Tls.exchange("127.0.0.1", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("name mismatch", Code{71},
      T.Tls.exchange("example.com", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("ip name mismatch", Code{71},
      T.Tls.exchange("127.0.0.2", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("no close_notify after data", Exactly{response()}, x(1))
    check("big within max", Size{100000n},
      T.Tls.exchange("localhost", "127.0.0.1", port(2), get("x"), 100000, 2000))
    check("big one past max", Code{27},
      T.Tls.exchange("localhost", "127.0.0.1", port(2), get("x"), 99999, 2000))
    check("big with max 0", Code{27},
      T.Tls.exchange("localhost", "127.0.0.1", port(2), get("x"), 0, 2000))
    check("empty response with max 0", Exactly{[]},
      T.Tls.exchange("localhost", "127.0.0.1", port(5), get("x"), 0, 2000))
    check("silent server: read timeout", Code{110}, x(3))
    check("close before any data, no close_notify", Code{104}, x(4))
    check("close_notify before any data", Exactly{[]}, x(5))
    check("not TLS", Code{103}, x(6))
    check("handshake stall: timeout", Code{110}, x(7))
    check("echo of every byte value", Exactly{every_byte(256n, crlf2())},
      T.Tls.exchange("localhost", "127.0.0.1", port(8), every_byte(256n, crlf2()), 1000, 2000))
    check("echo of a 2 MiB request", Size{2097156n},
      T.Tls.exchange("localhost", "127.0.0.1", port(8), rep(2097152n, 97, crlf2()), 4194304, 5000))
    check("peer gone while writing 4 MiB", Either{32, 104},
      T.Tls.exchange("localhost", "127.0.0.1", port(9), rep(4194304n, 97, []), 1000, 2000))
    check("TLS 1.1 server", Code{103}, x(10))
    check("trailing dot: localhost. verifies as localhost", Exactly{response()},
      T.Tls.exchange("localhost.", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("trailing dot on an ip name: no SNI, IP SAN", Exactly{response()},
      T.Tls.exchange("127.0.0.1.", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("trailing dot keeps a mismatch a mismatch", Code{71},
      T.Tls.exchange("example.com.", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("a lone dot is not stripped to nothing", Code{71},
      T.Tls.exchange(".", "127.0.0.1", port(0), get("x"), 1000, 2000))
    check("partial-label wildcard f*.example.test refused", Code{71},
      T.Tls.exchange("foo.example.test", "127.0.0.1", port(15), get("x"), 1000, 2000))
    check("whole-label wildcard *.wild.test accepted", Exactly{response()},
      T.Tls.exchange("a.wild.test", "127.0.0.1", port(15), get("x"), 1000, 2000))
    check("wildcard covers one label only", Code{71},
      T.Tls.exchange("a.b.wild.test", "127.0.0.1", port(15), get("x"), 1000, 2000))
    check("exchange reads to the close: keep-alive costs the timeout", Code{110},
      T.Tls.exchange("localhost", "127.0.0.1", port(11), get("x"), 1000, 1000))
    check("connection refused", Code{111},
      T.Tls.exchange("localhost", "127.0.0.1", port(30), get("x"), 1000, 2000))
    check("300 refused: no descriptor leak", Code{111}, repeat(300n, 30))
    check("300 not TLS: no descriptor leak", Code{103}, repeat(300n, 6))
    check("300 bad certificates: no descriptor leak", Code{71},
      repeat_name(300n, "example.com"))
    check("300 ok: no descriptor leak", Exactly{response()}, repeat(300n, 0))
    concurrently()
