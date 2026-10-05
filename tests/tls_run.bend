import Base
import ../src/bytes.bend as B
import ../src/tls.bend as T

# Tls.exchange with no network: input checks (EINVAL, before any socket) and
# a refused connection (nothing listens on 127.0.0.1:1). Linux errno values.
#   bend tests/tls_run.bend
#   bend tests/tls_run.bend -o x && ./x

def R() -> Type:
  Result<&1, &1, U32 & String, List<&2, U32>>

def verdict(name: String, ok: Bool, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name)
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got)

# A failure with the code wanted; Done is always wrong here.
def expect(name: String, code: U32, r: R) -> IO(Unit):
  match r:
    case Fail{e}:
      (c, m) = e
      +k = c
      verdict(name, U32.is_eq(k, code), "error " ++ U32.show(k) ++ ": " ++ m)
    case Done{xs}:
      verdict(name, False{}, Nat.show(List.length(&2, U32, xs)) ++ " bytes")

def check(name: String, code: U32, io: IO(R)) -> IO(Unit):
  IO.bind(R, Unit, io, r => expect(name, code, r))

def get(host: String) -> List<&2, U32>:
  B.from_ascii("GET / HTTP/1.1\r\nHost: " ++ host ++ "\r\nConnection: close\r\n\r\n")

def x(name: String, ip: String, port: U32, req: List<&2, U32>) -> IO(R):
  T.Tls.exchange(name, ip, port, req, 1000, 2000)

def rep(n: Nat, s: String) -> String:
  match n:
    case 0n:
      ""
    case 1n+p:
      +t = s
      t ++ rep(p, t)

def bytes(n: Nat) -> List<&2, U32>:
  match n:
    case 0n:
      []
    case 1n+p:
      +q = p
      U32.from_nat(q) <> bytes(q)

def main() -> IO(Unit):
  do IO<Unit>:
    check("empty name", 22, x("", "127.0.0.1", 1, get("a")))
    check("name with NUL", 22, x("a\0b", "127.0.0.1", 1, get("a")))
    check("name of 256 bytes", 22, x(rep(256n, "a"), "127.0.0.1", 1, get("a")))
    check("name of 255 bytes passes the checks", 111, x(rep(255n, "a"), "127.0.0.1", 1, get("a")))
    check("empty ip", 22, x("a", "", 443, get("a")))
    check("ip with three parts", 22, x("a", "1.2.3", 443, get("a")))
    check("ip octet past 255", 22, x("a", "256.1.1.1", 443, get("a")))
    check("ip with a leading zero", 22, x("a", "01.2.3.4", 443, get("a")))
    check("ip with NUL", 22, x("a", "127.0.0.1\0", 443, get("a")))
    check("ip as a name", 22, x("a", "localhost", 443, get("a")))
    check("ip v6", 22, x("a", "::1", 443, get("a")))
    check("port 0", 22, x("a", "127.0.0.1", 0, get("a")))
    check("port 65536", 22, x("a", "127.0.0.1", 65536, get("a")))
    check("port past U16 far", 22, x("a", "127.0.0.1", 4294967295, get("a")))
    check("request byte 256", 22, x("a", "127.0.0.1", 1, [71, 69, 256]))
    check("request byte huge", 22, x("a", "127.0.0.1", 1, [71, 69, 84, 4294967295]))
    check("every byte value passes the checks", 111, x("a", "127.0.0.1", 1, bytes(256n)))
    check("empty request passes the checks", 111, x("a", "127.0.0.1", 1, []))
    check("connection refused", 111, x("localhost", "127.0.0.1", 1, get("localhost")))
    check("refused with an ip name", 111, x("127.0.0.1", "127.0.0.1", 1, get("x")))
