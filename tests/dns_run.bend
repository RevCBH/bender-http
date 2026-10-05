import Base
import ../src/dns.bend as D

# Dns.lookup with no network: input checks and numeric hosts. A canonical
# dotted quad answers itself; any other host the resolver would read as an
# IPv4 address (inet_aton's octal, hex, short and bare-number forms) is
# EINVAL (22) before any lookup; a trailing dot or a fifth part makes a name,
# which goes to the resolver (and fails there, but not with EINVAL).
#   bend tests/dns_run.bend
#   bend tests/dns_run.bend -o x && ./x

def R() -> Type:
  Result<&1, &1, U32 & String, List<&2, String>>

type Want is Data:
  Code{code: U32}             # this failure
  NotCode{code: U32}          # a failure, but not this one
  Addrs{ips: List<&2, String>} # exactly these addresses
  Has{ip: String}             # these addresses include this one

def verdict(name: String, ok: Bool, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name ++ " (" ++ got ++ ")")
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got)

def strings_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      String.eq(x, y) && strings_eq(s, t)
    case _ _:
      False{}

def has(ip: String, ips: List<&2, String>) -> Bool:
  match ips:
    case Nil{}:
      False{}
    case Con{x, t}:
      +s = ip
      String.eq(s, x) || has(s, t)

def want_code(w: Want, +c: U32) -> Bool:
  match w:
    case Code{k}:
      U32.is_eq(k, c)
    case NotCode{k}:
      Bool.not(U32.is_eq(k, c))
    case _:
      False{}

def want_ips(w: Want, +ips: List<&2, String>) -> Bool:
  match w:
    case Addrs{xs}:
      strings_eq(xs, ips)
    case Has{x}:
      has(x, ips)
    case _:
      False{}

def expect(name: String, w: Want, r: R) -> IO(Unit):
  match r:
    case Fail{e}:
      (c, m) = e
      +k = c
      verdict(name, want_code(w, k), "error " ++ U32.show(k) ++ ": " ++ m)
    case Done{ips}:
      +xs = ips
      verdict(name, want_ips(w, xs), String.join(xs, ", "))

def check(name: String, host: String, w: Want) -> IO(Unit):
  IO.bind(R, Unit, D.Dns.lookup(host), r => expect(name, w, r))

def main() -> IO(Unit):
  do IO<Unit>:
    check("empty name", "", Code{22})
    check("name with NUL", "a\0b", Code{22})
    check("bare 32-bit number", "2130706433", Code{22})
    check("bare 4294967295", "4294967295", Code{22})
    check("bare 0", "0", Code{22})
    check("short form 127.1", "127.1", Code{22})
    check("hex part 0x7f.1", "0x7f.1", Code{22})
    check("hex whole 0xffffffff", "0xffffffff", Code{22})
    check("octal 010.0.0.1 (would be 8.0.0.1)", "010.0.0.1", Code{22})
    check("octal 0177.0.0.1", "0177.0.0.1", Code{22})
    check("leading zero in the last part", "127.0.0.010", Code{22})
    check("00.0.0.0", "00.0.0.0", Code{22})
    check("canonical 1.2.3.4 is itself", "1.2.3.4", Addrs{["1.2.3.4"]})
    check("canonical 127.0.0.1 is itself", "127.0.0.1", Addrs{["127.0.0.1"]})
    check("canonical 0.0.0.0 is itself", "0.0.0.0", Addrs{["0.0.0.0"]})
    check("canonical 255.255.255.255 is itself", "255.255.255.255", Addrs{["255.255.255.255"]})
    check("localhost", "localhost", Has{"127.0.0.1"})
    check("trailing dot makes 127.1. a name", "127.1.", NotCode{22})
    check("five parts make a name", "1.2.3.4.5", NotCode{22})
