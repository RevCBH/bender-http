import Base
import ../cli.bend as C
import ../main.bend as P

# Test the CLI's actual parser/output writer using a response fixture file,
# without sockets. Invoked by cli_offline.sh: fixture followed by CLI flags.
def decoded(r: Result<&2, &2, P.Http.ParseError(), P.Http.Decoded()>, out: C.Output) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, P.Http.ParseError.show(e))
    case Done{d}:
      C.print_response(P.Http.Decoded.response(d), out)

def read_(pair: File & Result<&1, &1, U32 & String, List<&2, U32>>, out: C.Output) -> IO(Unit):
  match pair:
    case (file, result):
      do IO<Unit>:
        File.close(file)
        xs : List<&2, U32> <- IO.pass(List<&2, U32>, result)
        decoded(P.Http.decode(P.Http.GET(), 1048576n, xs), out)

def opened(r: Result<&1, &1, U32 & String, File>, out: C.Output) -> IO(Unit):
  match r:
    case Fail{(code, msg)}:
      IO.die(Unit, 1, msg)
    case Done{file}:
      IO.bind(File & Result<&1, &1, U32 & String, List<&2, U32>>, Unit, File.read_bytes(file, 1048576),
        pair => read_(pair, out))

def opts(o: C.Opts, fixture: String) -> IO(Unit):
  match o:
    case C.Opts{m, hs, b, mx, t, f, u, None{}, out}:
      IO.bind(Result<&1, &1, U32 & String, File>, Unit, File.open(fixture, "r"), r => opened(r, out))
    case C.Opts{m, hs, b, mx, t, f, u, Some{msg}, out}:
      IO.die(Unit, 1, msg)

def args_(args: List<String>) -> IO(Unit):
  match args:
    case Con{fixture, tail}:
      opts(C.parse(tail, None{}, C.opts0()), fixture)
    case Nil{}:
      IO.die(Unit, 1, "expected fixture path")

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    args_(List.tail(&1, String, args))
