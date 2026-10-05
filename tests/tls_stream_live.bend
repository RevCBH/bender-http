import Base
import ../src/bytes.bend as B
import ../src/dns.bend as D
import ../src/tls.bend as T

# Tls.open / Tls.recv / Tls.close against the local servers of
# tests/tls_server.py (one mode per port, from 18440), which tests/tls_live.sh
# starts with SSL_CERT_FILE trusting their self-signed certificates. Linux
# errno values.
#   tests/tls_live.sh            (both lanes)
#
# A session opens a connection and reads until the end, a failure or a read
# count; its trace is the total of the bytes read, then how it stopped:
# "end" (close_notify), "E<code>" (with " nc" when the text says the close
# came without close_notify), or "stop" (the read count ran out).

def R() -> Type:
  Result<&1, &1, U32 & String, List<&2, U32>>

def H() -> Type:
  Result<&1, &1, U32 & String, U32>

def count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{_, t}:
      count(t, 1n+n)

def verdict(name: String, ok: Bool, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name ++ " (" ++ got ++ ")")
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got)

def check.got(name: String, want: String, +got: String) -> IO(Unit):
  verdict(name, String.eq(want, got), got)

def check(name: String, want: String, io: IO(String)) -> IO(Unit):
  IO.bind(String, Unit, io, got => check.got(name, want, got))

def get(host: String) -> List<&2, U32>:
  B.from_ascii("GET / HTTP/1.1\r\nHost: " ++ host ++ "\r\nConnection: close\r\n\r\n")

def port(mode: U32) -> U32:
  (18440 + mode : U32)

# n copies of b, then tail.
def rep(n: Nat, +b: U32, tail: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      tail
    case 1n+p:
      rep(p, b, b <> tail)

def failed(code: U32, text: String) -> String:
  "E" ++ U32.show(code) ++ Bool.pick(String, String.contains(text, "without close_notify"), " nc", "")

# One read's outcome, added to the running total; `more` reads again.
def read_got(r: R, +total: Nat, more: Nat -> IO(String)) -> IO(String):
  match r:
    case Fail{e}:
      (code, text) = e
      IO.pure(String, Nat.show(total) ++ " " ++ failed(code, text))
    case Done{xs}:
      match xs:
        case Nil{}:
          IO.pure(String, Nat.show(total) ++ " end")
        case Con{h, t}:
          more(count(h <> t, total))

# At most n reads of up to 65536 bytes from c.
def reads(n: Nat, +c: U32, +total: Nat) -> IO(String):
  match n:
    case 0n:
      IO.pure(String, Nat.show(total) ++ " stop")
    case 1n+p:
      IO.bind(R, String, T.Tls.recv(c, 65536), r => read_got(r, total, t => reads(p, c, t)))

def closing(+c: U32, s: String) -> IO(String):
  do IO<String>:
    T.Tls.close(c)
    return s

# The trace of up to n reads, then close; "open E<code>" when the open fails.
def opened(h: H, n: Nat) -> IO(String):
  match h:
    case Fail{e}:
      (code, text) = e
      IO.pure(String, "open " ++ failed(code, text))
    case Done{c}:
      +k = c
      IO.bind(String, String, reads(n, k, 0n), s => closing(k, s))

def session(name: String, mode: U32, n: Nat) -> IO(String):
  +s = name
  IO.bind(H, String, T.Tls.open(s, "127.0.0.1", port(mode), get(s), 2000), h => opened(h, n))

def outcome(r: R) -> String:
  match r:
    case Fail{e}:
      (code, text) = e
      failed(code, text)
    case Done{xs}:
      match xs:
        case Nil{}:
          "end"
        case Con{h, t}:
          Nat.show(count(h <> t, 0n)) ++ " bytes"

def recv_outcome(c: U32, max: U32) -> IO(String):
  IO.bind(R, String, T.Tls.recv(c, max), r => IO.pure(String, outcome(r)))

def with_conn.got(h: H, act: U32 -> IO(String)) -> IO(String):
  match h:
    case Fail{e}:
      (code, text) = e
      IO.pure(String, "open " ++ failed(code, text))
    case Done{c}:
      +k = c
      IO.bind(String, String, act(k), s => closing(k, s))

# With an open connection, run `act` on its handle, then close it.
def with_conn(mode: U32, act: U32 -> IO(String)) -> IO(String):
  IO.bind(H, String, T.Tls.open("localhost", "127.0.0.1", port(mode), get("x"), 2000),
    h => with_conn.got(h, act))

# Reading to the end, then reading again: [] again.
def twice_at_end(conn: U32) -> IO(String):
  +c = conn
  do IO<String>:
    a : String <- reads(5n, c, 0n)
    b : String <- recv_outcome(c, 100)
    return a ++ ", then " ++ b

# A read of 0 bytes is EINVAL, and the connection still works.
def zero_read(conn: U32) -> IO(String):
  +c = conn
  do IO<String>:
    a : String <- recv_outcome(c, 0)
    b : String <- reads(5n, c, 0n)
    return a ++ ", then " ++ b

# After close the handle is gone (EBADF), and a second close does nothing.
def after_close(conn: U32) -> IO(String):
  +c = conn
  do IO<String>:
    T.Tls.close(c)
    T.Tls.close(c)
    recv_outcome(c, 100)

# A second read while one waits is EBUSY; the waiting one still answers.
def busy(conn: U32) -> IO(String):
  +c = conn
  do IO<String>:
    first : Chan(String) <- IO.fork(String, recv_outcome(c, 100))
    IO.sleep(200)
    second : String <- recv_outcome(c, 100)
    a : String <- IO.join(String, first)
    return second ++ ", waiting one " ++ a

# Close while a read waits: the read still ends (its timeout), then the
# handle is gone.
def close_while_waiting(conn: U32) -> IO(String):
  +c = conn
  do IO<String>:
    first : Chan(String) <- IO.fork(String, recv_outcome(c, 100))
    IO.sleep(200)
    T.Tls.close(c)
    a : String <- IO.join(String, first)
    b : String <- recv_outcome(c, 100)
    return a ++ ", then " ++ b

# n opens, each closed at once (tls_live.sh caps descriptors at 256).
def open_close(n: Nat, mode: U32) -> IO(String):
  match n:
    case 0n:
      session("localhost", mode, 5n)
    case 1n+p:
      +m = mode
      IO.bind(String, String, session("localhost", m, 1n), s => open_close(p, m))

# n connections stalled in the handshake (the stall server never answers),
# each in its own computation, with a 6000 ms timeout.
def stall(n: Nat) -> IO(Unit):
  match n:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+p:
      do IO<Unit>:
        IO.spawn(String, IO.bind(H, String,
          T.Tls.open("localhost", "127.0.0.1", port(7), get("x"), 6000), h => opened(h, 1n)))
        stall(p)

def quick(t0: Nat, t1: Nat, +s: String) -> String:
  +d = Nat.sub(t1, t0)
  Bool.pick(String, Nat.is_lt(d, 2000n), "within 2 s: " ++ s, "after " ++ Nat.show(d) ++ " ms: " ++ s)

def dns_text(r: Result<&1, &1, U32 & String, List<&2, String>>) -> String:
  match r:
    case Fail{e}:
      (code, text) = e
      "dns E" ++ U32.show(code)
    case Done{ips}:
      "dns ok"

# 80 stalled handshakes must not hold up a lookup or another connection: the
# effects park instead of holding one of the runtime's 64 IO helper threads
# (C lane) or blocking the loop (JS lane).
def no_starvation() -> IO(String):
  do IO<String>:
    stall(80n)
    IO.sleep(300)
    t0 : Nat <- IO.now()
    r : Result<&1, &1, U32 & String, List<&2, String>> <- D.Dns.lookup("localhost")
    s : String <- session("localhost", 0, 5n)
    t1 : Nat <- IO.now()
    return quick(t0, t1, dns_text(r) ++ ", " ++ s)

def main() -> IO(Unit):
  do IO<Unit>:
    check("ok: the response, then close_notify", "43 end", session("localhost", 0, 5n))
    check("keep-alive server: the response comes without waiting for the close",
      "43 stop", session("localhost", 11, 1n))
    check("reset after the response: the response first, then ECONNRESET",
      "43 E104", session("localhost", 12, 5n))
    check("close-delimited body cut by a FIN without close_notify",
      "57 E104 nc", session("localhost", 13, 5n))
    check("close-delimited body ended by close_notify", "57 end", session("localhost", 14, 5n))
    check("framed body, then a FIN without close_notify", "43 E104 nc", session("localhost", 1, 5n))
    check("big response in several reads", "100000 end", session("localhost", 2, 100n))
    check("silent server: read timeout", "0 E110", session("localhost", 3, 5n))
    check("close before any data", "0 E104", session("localhost", 4, 5n))
    check("close_notify before any data", "0 end", session("localhost", 5, 5n))
    check("[] again after the end", "43 end, then end", with_conn(0, twice_at_end))
    check("read of 0 bytes", "E22, then 43 end", with_conn(0, zero_read))
    check("closed handle", "E9", with_conn(0, after_close))
    check("unknown handle", "E9", recv_outcome(4000000000, 100))
    check("a second read while one waits", "E16, waiting one E110", with_conn(3, busy))
    check("close while a read waits", "E110, then E9", with_conn(3, close_while_waiting))
    check("open: name mismatch", "open E71", session("example.com", 0, 5n))
    check("open: not TLS", "open E103", session("localhost", 6, 5n))
    check("open: handshake stall", "open E110", session("localhost", 7, 5n))
    check("open: TLS 1.1 server", "open E103", session("localhost", 10, 5n))
    check("open: connection refused", "open E111", session("localhost", 30, 5n))
    check("open: empty name", "open E22", session("", 0, 5n))
    check("open: trailing dot", "43 end", session("localhost.", 0, 5n))
    check("open: partial-label wildcard refused", "open E71", session("foo.example.test", 15, 5n))
    check("open: whole-label wildcard accepted", "43 end", session("a.wild.test", 15, 5n))
    check("echo of a 2 MiB request", "2097156 end",
      IO.bind(H, String, T.Tls.open("localhost", "127.0.0.1", port(8), rep(2097152n, 97, [13, 10, 13, 10]), 5000),
        h => opened(h, 1000n)))
    check("300 opens and closes: no descriptor leak", "43 end", open_close(300n, 0))
    check("no starvation behind 80 stalled handshakes", "within 2 s: dns ok, 43 end", no_starvation())
