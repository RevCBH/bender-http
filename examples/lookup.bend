import Base
import ../src/dns.bend as D

# bend examples/lookup.bend -- example.com localhost
# Prints each name's IPv4 addresses, or the resolver's error.

def show(host: String, r: Result<&1, &1, U32 & String, List<&2, String>>) -> IO(Unit):
  match r:
    case Fail{e}:
      (c, m) = e
      IO.print(host ++ ": error " ++ U32.show(c) ++ " (" ++ m ++ ")")
    case Done{ips}:
      IO.print(host ++ ": " ++ String.join(ips, ", "))

def lookup(host: String) -> IO(Unit):
  +h = host
  IO.bind(Result<&1, &1, U32 & String, List<&2, String>>, Unit, D.Dns.lookup(h), r => show(h, r))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    List.for_each(~&1, ~String, ~lookup, List.tail(&1, String, args))
