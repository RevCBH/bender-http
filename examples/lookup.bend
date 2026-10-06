import Base
import ../main.bend as P

# bend examples/lookup.bend -- example.com localhost
# Prints each name's IPv4 addresses, or the resolver's error.

def show(host: String, r: Result<&2, &2, P.Http.Error(), List<&2, String>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print(host ++ ": " ++ P.Http.Error.show(e))
    case Done{ips}:
      IO.print(host ++ ": " ++ String.join(ips, ", "))

def lookup(host: String) -> IO(Unit):
  +h = host
  IO.bind(Result<&2, &2, P.Http.Error(), List<&2, String>>, Unit, P.Http.lookup(h), r => show(h, r))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    List.for_each(~&1, ~String, ~lookup, List.tail(&1, String, args))
