import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/transport.bend as X
import ../src/client.bend as C

# X.tls (Tls.open / recv / close plus the decoder) against the local TLS
# servers of tests/tls_server.py, one mode per port from BASE() (48940;
# tests/transport_live.sh starts them, trusting their
# certificate through SSL_CERT_FILE). Linux errno values.
#   tests/transport_live.sh            (both lanes)
#
# Regressions covered: the reader stops once the response is complete (a
# server that keeps the connection open, or resets it afterwards, costs
# nothing; timeout 0 does not hang); a body that runs to the close is
# refused when the close comes without close_notify (RFC 9112 §9.8) and
# accepted with it; a host with a trailing dot verifies as the name without
# it.

def count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{_, t}:
      count(t, 1n+n)

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 1n+p Con{h, t}:
      h <> take(p, t)
    case _ _:
      Nil{}

def shown(r: Result<&2, &2, M.Error, M.Decoded>) -> String:
  match r:
    case Fail{e}:
      "Fail " ++ C.error_show(e)
    case Done{d}:
      match d:
        case M.Decoded{x, rest}:
          match x:
            case M.Response{v, st, re, hs, +body}:
              N.show(st) ++ " " ++ re ++ " len=" ++ Nat.show(count(body, 0n)) ++ " "
                ++ B.to_latin1(take(20n, body))

def get(host: String) -> List<&2, U32>:
  B.from_ascii("GET / HTTP/1.1\r\nHost: " ++ host ++ "\r\nConnection: close\r\n\r\n")

# The client's answer, plus " SLOW <ms>" if it took `limit` ms or more.
def timed.end(+t0: Nat, out: String, +limit: Nat, +t1: Nat) -> String:
  out ++ Bool.pick(String, Nat.is_lt(Nat.sub(t1, t0), limit), "", " SLOW " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")

def timed(limit: Nat, act: IO(String)) -> IO(String):
  do IO<String>:
    t0 : Nat <- IO.now()
    out : String <- act
    t1 : Nat <- IO.now()
    return timed.end(t0, out, limit, t1)

# X.tls to 127.0.0.1 on base + mode, verifying `host`, GET, within `limit` ms.
def tls(+base: Nat, mode: Nat, +host: String, max: Nat, ms: Nat, limit: Nat) -> IO(String):
  timed(limit, IO.bind(Result<&2, &2, M.Error, M.Decoded>, String,
    X.tls(host, "127.0.0.1", Nat.add(base, mode), get(host), M.GET{}, max, ms),
    r => IO.pure(String, shown(r))))

def verdict(name: String, ok: Bool, got: String, +fails: Nat) -> IO(Nat):
  match ok:
    case True{}:
      do IO<Nat>:
        IO.print("PASS " ++ name)
        return fails
    case False{}:
      do IO<Nat>:
        IO.print("FAIL " ++ name ++ ": got " ++ got)
        return 1n+fails

def check.got(name: String, +want: String, +got: String, +fails: Nat) -> IO(Nat):
  verdict(name, String.eq(String.take(got, String.length(want)) ++ "", want) && Bool.not(String.contains(got, " SLOW ")),
    got, fails)

# PASS when the answer starts with `want` and came within its time limit.
def check(name: String, act: IO(String), +want: String, +fails: Nat) -> IO(Nat):
  IO.bind(String, Nat, act, got => check.got(name, want, got, fails))

def plain_shown(io: IO(Result<&2, &2, M.Error, M.Decoded>)) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, M.Decoded>, String, io, r => IO.pure(String, shown(r)))

def BIG() -> Nat:
  16777216n

def cases(+b: Nat) -> IO(Nat):
  do IO<Nat>:
    f1 : Nat <- check("ok", tls(b, 0n, "localhost", BIG(), 5000n, 3000n), "200 OK len=5 hello", 0n)
    f2 : Nat <- check("framed then FIN without close_notify", tls(b, 1n, "localhost", BIG(), 5000n, 3000n),
      "200 OK len=5 hello", f1)
    f3 : Nat <- check("100000 bytes", tls(b, 2n, "localhost", BIG(), 5000n, 5000n), "200 OK len=99958 xxxx", f2)
    f4 : Nat <- check("too large", tls(b, 2n, "localhost", 1000n, 5000n, 5000n),
      "Fail bad response: the response is larger than the limit", f3)
    f5 : Nat <- check("exact budget", tls(b, 0n, "localhost", 43n, 5000n, 3000n), "200 OK len=5 hello", f4)
    f6 : Nat <- check("budget one short", tls(b, 0n, "localhost", 42n, 5000n, 3000n),
      "Fail bad response: the response is larger than the limit", f5)
    f7 : Nat <- check("silent server times out", tls(b, 3n, "localhost", BIG(), 500n, 3000n), "Fail timed out", f6)
    f8 : Nat <- check("FIN before any data", tls(b, 4n, "localhost", BIG(), 5000n, 3000n), "Fail TLS error 104: ", f7)
    f9 : Nat <- check("close_notify before any data", tls(b, 5n, "localhost", BIG(), 5000n, 3000n),
      "Fail bad response: the connection closed before the response ended", f8)
    f10 : Nat <- check("keep-alive server: stop at the end of the message",
      tls(b, 11n, "localhost", BIG(), 5000n, 2000n), "200 OK len=5 hello", f9)
    f11 : Nat <- check("keep-alive server, timeout 0", tls(b, 11n, "localhost", BIG(), 0n, 2000n),
      "200 OK len=5 hello", f10)
    f12 : Nat <- check("reset after the response", tls(b, 12n, "localhost", BIG(), 5000n, 3000n),
      "200 OK len=5 hello", f11)
    f13 : Nat <- check("close-delimited cut without close_notify", tls(b, 13n, "localhost", BIG(), 5000n, 3000n),
      "Fail TLS error 104: ", f12)
    f14 : Nat <- check("close-delimited with close_notify", tls(b, 14n, "localhost", BIG(), 5000n, 3000n),
      "200 OK len=12 PARTIAL-BODY", f13)
    f15 : Nat <- check("trailing-dot host verifies", tls(b, 0n, "localhost.", BIG(), 5000n, 3000n),
      "200 OK len=5 hello", f14)
    f16 : Nat <- check("wrong name refused", tls(b, 0n, "example.com", BIG(), 5000n, 3000n), "Fail TLS error 71: ", f15)
    f17 : Nat <- check("IP literal verifies", tls(b, 0n, "127.0.0.1", BIG(), 5000n, 3000n), "200 OK len=5 hello", f16)
    f18 : Nat <- check("closed port", plain_shown(X.tls("localhost", "127.0.0.1", 1n, get("localhost"), M.GET{},
      BIG(), 5000n)), "Fail connect error 111", f17)
    return f18

def finish(+fails: Nat) -> IO(Unit):
  match fails:
    case 0n:
      IO.print("ALL PASS")
    case 1n+p:
      IO.print("SOME FAIL: " ++ Nat.show(1n+p))

# tests/transport_live.sh starts tls_server.py with this base port.
def BASE() -> Nat:
  48940n

def main() -> IO(Unit):
  IO.bind(Nat, Unit, cases(BASE()), f => finish(f))
