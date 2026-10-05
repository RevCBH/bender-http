import Base
import ../src/bytes.bend as B
import ../src/dns.bend as D
import ../src/tls.bend as T

# Tls.exchange against public hosts (needs the internet): a good server, the
# badssl.com certificate failures (EPROTO, 71), a TLS 1.0-only server (the
# handshake fails, ECONNABORTED, 103), a refused port (111) and a blackhole
# address (ETIMEDOUT, 110, after 2000 ms). Names resolve through Dns.lookup.
# Linux errno values.
#   bend tests/tls_public.bend
#   bend tests/tls_public.bend -o x && ./x

def R() -> Type:
  Result<&1, &1, U32 & String, List<&2, U32>>

def DnsR() -> Type:
  Result<&1, &1, U32 & String, List<&2, String>>

type Want is Data:
  Code{code: U32}               # this failure
  Status{line: String}          # a response whose first line is this

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

def line_rev(xs: List<&2, U32>, done: Bool, +acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{+h, t}:
      +stop = done || is_cr(B.class(h))
      line_rev(t, stop, Bool.pick(List<&2, U32>, stop, acc, h <> acc))

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 1n+p Con{h, t}:
      h <> take(p, t)
    case _ _:
      []

def first_line(xs: List<&2, U32>) -> String:
  B.to_latin1(List.reverse(&2, U32, line_rev(take(200n, xs), False{}, [])))

def count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{_, t}:
      count(t, 1n+n)

def want_code(w: Want, +c: U32) -> Bool:
  match w:
    case Code{k}:
      U32.is_eq(k, c)
    case _:
      False{}

def want_line(w: Want, line: String) -> Bool:
  match w:
    case Status{s}:
      String.eq(s, line)
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
      +line = first_line(ys)
      verdict(name, want_line(w, line), Nat.show(count(ys, 0n)) ++ " bytes: " ++ line)

def check(name: String, w: Want, io: IO(R)) -> IO(Unit):
  IO.bind(R, Unit, io, r => expect(name, w, r))

def get(host: String) -> List<&2, U32>:
  B.from_ascii("GET / HTTP/1.1\r\nHost: " ++ host ++ "\r\nConnection: close\r\n\r\n")

def first_ip(name: String, port: U32, timeout: U32, ips: List<&2, String>) -> IO(R):
  match ips:
    case Nil{}:
      IO.pure(R, Fail{(2, "no IPv4 address for " ++ name)})
    case ip <> _:
      +n = name
      T.Tls.exchange(n, ip, port, get(n), 16777216, timeout)

def resolved(name: String, port: U32, timeout: U32, r: DnsR) -> IO(R):
  match r:
    case Fail{e}:
      IO.pure(R, Fail{e})
    case Done{ips}:
      first_ip(name, port, timeout, ips)

# Resolve name, then one GET / to its first address.
def https(name: String, port: U32) -> IO(R):
  +n = name
  IO.bind(DnsR, R, D.Dns.lookup(n), r => resolved(n, port, 10000, r))

def main() -> IO(Unit):
  do IO<Unit>:
    check("example.com", Status{"HTTP/1.1 200 OK"}, https("example.com", 443))
    check("badssl.com", Status{"HTTP/1.1 200 OK"}, https("badssl.com", 443))
    check("tls-v1-2.badssl.com:1012", Status{"HTTP/1.1 200 OK"}, https("tls-v1-2.badssl.com", 1012))
    check("expired.badssl.com", Code{71}, https("expired.badssl.com", 443))
    check("wrong.host.badssl.com", Code{71}, https("wrong.host.badssl.com", 443))
    check("self-signed.badssl.com", Code{71}, https("self-signed.badssl.com", 443))
    check("untrusted-root.badssl.com", Code{71}, https("untrusted-root.badssl.com", 443))
    check("incomplete-chain.badssl.com", Code{71}, https("incomplete-chain.badssl.com", 443))
    check("tls-v1-0.badssl.com:1010 (TLS 1.0 only)", Code{103}, https("tls-v1-0.badssl.com", 1010))
    check("refused port", Code{111},
      T.Tls.exchange("localhost", "127.0.0.1", 1, get("localhost"), 1000, 2000))
    check("blackhole 10.255.255.1, 2000 ms", Code{110},
      T.Tls.exchange("example.com", "10.255.255.1", 443, get("example.com"), 1000, 2000))
