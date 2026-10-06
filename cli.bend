import Base
import ./main.bend as P
import ../dns/main.bend as DNS

# bender-http: curl-like CLI over the public Http API.
# Bodies are buffered up to --max; output is byte-exact, including binary.
# Successful transfers exit explicitly to release any stalled DNS retry.

def die(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

def usage() -> String:
  "usage: bender-http [options] URL"

def help_text() -> String:
  usage() ++ "\n\n" ++
  "  -o, --output FILE  Save response to FILE (- means stdout)\n" ++
  "  -i, --include      Include status line and response headers\n" ++
  "  -I, --head         Send HEAD and include response headers\n" ++
  "  -L, --location     Follow up to 10 redirects (also --follow)\n" ++
  "  -f, --fail         Exit with an error for HTTP status >= 400\n" ++
  "  -X, --request M    Request method (default GET, POST with -d)\n" ++
  "  -H, --header H     Request header 'Name: value' (repeatable)\n" ++
  "  -d, --data TEXT    UTF-8 request body\n" ++
  "      --timeout MS   Per-step / whole-DNS timeout (default 30000; 0 disables)\n" ++
  "      --max N        Response byte limit (default 16777216)\n" ++
  "      --dns-server IP  Use this IPv4 DNS server\n" ++
  "      --dns-port N   DNS TCP port (default 53)\n" ++
  "  -h, --help         Show help\n\n" ++
  "Prints the body to stdout by default. HTTP and HTTPS; IPv4 only.\n" ++
  "DNS uses /etc/resolv.conf and /etc/hosts. Exits 0 on success, 1 on error."

# Command line
# ------------

# What an argument is, when no option is waiting for its value.
type Flag is Data:
  FMethod{}
  FHeader{}
  FData{}
  FMax{}
  FTimeout{}
  FFollow{}
  FOutput{}
  FInclude{}
  FHead{}
  FFail{}
  FHelp{}
  FDnsServer{}
  FDnsPort{}
  FUnknown{}
  FUrl{}

def flag(+a: String) -> Flag:
  Bool.pick(Flag, String.eq(a, "-X") || String.eq(a, "--request"), FMethod{},
  Bool.pick(Flag, String.eq(a, "-H") || String.eq(a, "--header"), FHeader{},
  Bool.pick(Flag, String.eq(a, "-d") || String.eq(a, "--data"), FData{},
  Bool.pick(Flag, String.eq(a, "--max"), FMax{},
  Bool.pick(Flag, String.eq(a, "--timeout"), FTimeout{},
  Bool.pick(Flag, String.eq(a, "--follow") || String.eq(a, "-L") || String.eq(a, "--location"), FFollow{},
  Bool.pick(Flag, String.eq(a, "-o") || String.eq(a, "--output"), FOutput{},
  Bool.pick(Flag, String.eq(a, "-i") || String.eq(a, "--include"), FInclude{},
  Bool.pick(Flag, String.eq(a, "-I") || String.eq(a, "--head"), FHead{},
  Bool.pick(Flag, String.eq(a, "-f") || String.eq(a, "--fail"), FFail{},
  Bool.pick(Flag, String.eq(a, "-h") || String.eq(a, "--help"), FHelp{},
  Bool.pick(Flag, String.eq(a, "--dns-server"), FDnsServer{},
  Bool.pick(Flag, String.eq(a, "--dns-port"), FDnsPort{},
  Bool.pick(Flag, String.starts_with(a, "-") && Nat.is_lt(1n, String.length(a)), FUnknown{},
  FUrl{}))))))))))))))

type Output is Data:
  Output{path: String, include: Bool, fail: Bool, help: Bool, server: Maybe<&2, String>, port: Nat}

def output0() -> Output:
  Output{"-", False{}, False{}, False{}, None{}, 53n}

type Opts is Data:
  Opts{method: Maybe<&2, String>, headers: List<&2, P.Http.Header()>, body: Maybe<&2, String>,
    max: Nat, timeout: Nat, follow: Bool, url: Maybe<&2, String>, bad: Maybe<&2, String>, out: Output}

def opts0() -> Opts:
  Opts{None{}, Nil{}, None{}, 16777216n, 30000n, False{}, None{}, None{}, output0()}

# The first complaint wins.
def complain(o: Opts, msg: String) -> Opts:
  match o:
    case Opts{m, hs, b, x, t, f, u, bad, out}:
      Opts{m, hs, b, x, t, f, u, Maybe.or(&2, String, bad, Some{msg}), out}

def header_of(parts: List<&2, String>) -> Maybe<&2, P.Http.Header()>:
  match parts:
    case Nil{}:
      None{}
    case Con{n, rest}:
      match rest:
        case Nil{}:
          None{}
        case Con{v, more}:
          Some{P.Http.header(String.trim(n), String.trim(String.join(v <> more, ":")))}

def add_header(h: Maybe<&2, P.Http.Header()>, o: Opts, +a: String) -> Opts:
  match h o:
    case None{} _:
      complain(o, "bad header (expected 'Name: value'): " ++ a)
    case Some{x} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{m, x <> hs, b, mx, t, f, u, bad, out}

def read_u32.of(r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case None{}:
      None{}
    case Some{+n}:
      Bool.pick(Maybe<&2, Nat>, Nat.is_le(n, 4294967295n), Some{n}, None{})

def read_u32(a: String) -> Maybe<&2, Nat>:
  read_u32.of(Nat.read(a))

def set_max(n: Maybe<&2, Nat>, o: Opts, +a: String) -> Opts:
  match n o:
    case None{} _:
      complain(o, "--max needs a number: " ++ a)
    case Some{x} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{m, hs, b, x, t, f, u, bad, out}

def set_timeout(n: Maybe<&2, Nat>, o: Opts, +a: String) -> Opts:
  match n o:
    case None{} _:
      complain(o, "--timeout needs a number: " ++ a)
    case Some{x} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{m, hs, b, mx, x, f, u, bad, out}

def output_value(k: Flag, a: String, out: Output) -> Output:
  match k out:
    case FOutput{} Output{p, i, f, h, s, port}:
      Output{a, i, f, h, s, port}
    case FInclude{} Output{p, i, f, h, s, port}:
      Output{p, True{}, f, h, s, port}
    case FFail{} Output{p, i, f, h, s, port}:
      Output{p, i, True{}, h, s, port}
    case FHelp{} Output{p, i, f, h, s, port}:
      Output{p, i, f, True{}, s, port}
    case FDnsServer{} Output{p, i, f, h, s, port}:
      Output{p, i, f, h, Some{a}, port}
    case _ _:
      out

def port_value(n: Maybe<&2, Nat>, +o: Opts) -> Opts:
  match n o:
    case Some{+n} Opts{m, hs, b, mx, t, f, u, bad, Output{p, i, fail, help, server, port}}:
      Bool.pick(Opts, Nat.is_lt(0n, n) && Nat.is_le(n, 65535n),
        Opts{m, hs, b, mx, t, f, u, bad, Output{p, i, fail, help, server, n}},
        complain(o, "DNS port must be 1..65535"))
    case None{} _:
      complain(o, "DNS port must be 1..65535")

def set_output(+k: Flag, +a: String, +o: Opts) -> Opts:
  match k o:
    case FDnsPort{} _:
      port_value(Nat.read(a), o)
    case FDnsServer{} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Bool.pick(Opts, DNS.Dns.Ip.is_ipv4(a),
        Opts{m, hs, b, mx, t, f, u, bad, output_value(k, a, out)},
        complain(o, "DNS server must be an IPv4 address"))
    case _ Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{m, hs, b, mx, t, f, u, bad, output_value(k, a, out)}

# `a` is the value of the option `p`.
def value(p: Flag, +a: String, o: Opts) -> Opts:
  match p o:
    case FMethod{} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{Some{a}, hs, b, mx, t, f, u, bad, out}
    case FHeader{} _:
      add_header(header_of(String.split(a, ':')), o, a)
    case FData{} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{m, hs, Some{a}, mx, t, f, u, bad, out}
    case FMax{} _:
      set_max(read_u32(a), o, a)
    case FTimeout{} _:
      set_timeout(read_u32(a), o, a)
    case _ _:
      set_output(p, a, o)

# `a` is not an option's value.
def word(k: Flag, +a: String, o: Opts) -> Opts:
  match k o:
    case FFollow{} Opts{m, hs, b, mx, t, f, u, bad, out}:
      Opts{m, hs, b, mx, t, True{}, u, bad, out}
    case FHead{} Opts{m, hs, b, mx, t, f, u, bad, out}:
      set_output(FInclude{}, a, Opts{Some{"HEAD"}, hs, b, mx, t, f, u, bad, out})
    case FInclude{} _:
      set_output(k, a, o)
    case FFail{} _:
      set_output(k, a, o)
    case FHelp{} _:
      set_output(k, a, o)
    case FUnknown{} _:
      complain(o, "unknown option: " ++ a)
    case FUrl{} Opts{m, hs, b, mx, t, f, u, bad, out}:
      match u:
        case None{}:
          Opts{m, hs, b, mx, t, f, Some{a}, bad, out}
        case Some{first}:
          complain(Opts{m, hs, b, mx, t, f, Some{first}, bad, out}, "more than one URL: " ++ a)
    case _ _:
      o

def takes_value(k: Flag) -> Bool:
  match k:
    case FMethod{}:
      True{}
    case FHeader{}:
      True{}
    case FData{}:
      True{}
    case FMax{}:
      True{}
    case FTimeout{}:
      True{}
    case FOutput{}:
      True{}
    case FDnsServer{}:
      True{}
    case FDnsPort{}:
      True{}
    case _:
      False{}

# The option waiting for its value after `a` (None if none waits).
def pending_after(waiting: Maybe<&2, Flag>, +a: String) -> Maybe<&2, Flag>:
  match waiting:
    case Some{p}:
      None{}
    case None{}:
      +k = flag(a)
      Bool.pick(Maybe<&2, Flag>, takes_value(k), Some{k}, None{})

def step(waiting: Maybe<&2, Flag>, +a: String, o: Opts) -> Opts:
  match waiting:
    case Some{p}:
      value(p, a, o)
    case None{}:
      word(flag(a), a, o)

def finish(waiting: Maybe<&2, Flag>, o: Opts) -> Opts:
  match waiting:
    case Some{p}:
      complain(o, "an option is missing its value")
    case None{}:
      o

# One pass over the arguments; `waiting` is the option whose value comes next.
def parse(args: List<String>, +waiting: Maybe<&2, Flag>, o: Opts) -> Opts:
  match args:
    case Nil{}:
      finish(waiting, o)
    case Con{+a, t}:
      parse(t, pending_after(waiting, a), step(waiting, a, o))

# Output
# ------

# Append byte lists with tail calls, including unusually long header values.
def prepend(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      prepend(t, h <> acc)

def append(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  prepend(List.reverse(&2, U32, xs), ys)

def write_result(pair: File & Result<&1, &1, U32 & String, Unit>) -> IO(File):
  match pair:
    case (file, Done{u}):
      IO.pure(File, file)
    case (file, Fail{(code, msg)}):
      do IO<File>:
        File.close(file)
        IO.die(File, 1, "output error " ++ U32.show(code) ++ ": " ++ msg)

def write_bytes(file: File, bytes: List<&2, U32>) -> IO(File):
  IO.bind(File & Result<&1, &1, U32 & String, Unit>, File, File.write_bytes(file, bytes), write_result)

def write_headers(hs: List<&2, P.Http.Header()>, file: File) -> IO(File):
  match hs:
    case Nil{}:
      write_bytes(file, [13, 10])
    case Con{+h, t}:
      line = append(P.Http.utf8(P.Http.Header.name(h)),
        append([58, 32], append(P.Http.utf8(P.Http.Header.value(h)), [13, 10])))
      IO.bind(File, File, write_bytes(file, line), f => write_headers(t, f))

def write_head(include: Bool, file: File, +r: P.Http.Response()) -> IO(File):
  match include:
    case False{}:
      IO.pure(File, file)
    case True{}:
      IO.bind(File, File, write_bytes(file, append(P.Http.utf8(P.Http.status_line(r)), [13, 10])),
        f => write_headers(P.Http.headers(r), f))

def finish_output(file: File) -> IO(Unit):
  do IO<Unit>:
    File.close(file)
    IO.die(Unit, 0, "")

def opened(result: Result<&1, &1, U32 & String, File>, include: Bool, +r: P.Http.Response()) -> IO(Unit):
  match result:
    case Fail{(code, msg)}:
      die("output error " ++ U32.show(code) ++ ": " ++ msg)
    case Done{file}:
      do IO<Unit>:
        f1 : File <- write_head(include, file, r)
        f2 : File <- write_bytes(f1, P.Http.body(r))
        finish_output(f2)

def print_response(+r: P.Http.Response(), out: Output) -> IO(Unit):
  match out:
    case Output{+path, include, fail, help, server, port}:
      +dest = Bool.pick(String, String.eq(path, "-"), "/dev/stdout", path)
      IO.bind(Result<&1, &1, U32 & String, File>, Unit, File.open(dest, "w"),
        result => opened(result, include, r))

# Sending, following redirects
# ----------------------------

def next_hop(next: Maybe<&2, P.Http.Request()>, +r: P.Http.Response(), out: Output, rest: P.Http.Request() -> IO(Unit)) ->
  IO(Unit):
  match next:
    case None{}:
      print_response(r, out)
    case Some{req}:
      rest(req)

def answered(res: Result<&2, &2, P.Http.Error(), P.Http.Response()>, follow: Bool, +req: P.Http.Request(),
  hops: Nat, +out: Output, rest: P.Http.Request() -> IO(Unit)) -> IO(Unit):
  match res:
    case Fail{e}:
      die("error: " ++ P.Http.Error.show(e))
    case Done{+r}:
      match follow hops:
        case False{} _:
          print_response(r, out)
        case True{} 0n:
          next_hop(P.Http.redirect(req, r), r, out, x => die("error: more than 10 redirects"))
        case True{} 1n+p:
          next_hop(P.Http.redirect(req, r), r, out, rest)

def should_fail(out: Output, r: P.Http.Response()) -> Bool:
  match out:
    case Output{path, include, fail, help, server, port}:
      fail && Nat.is_le(400n, P.Http.status(r))

def checked(res: Result<&2, &2, P.Http.Error(), P.Http.Response()>, follow: Bool,
  req: P.Http.Request(), hops: Nat, +out: Output, rest: P.Http.Request() -> IO(Unit)) -> IO(Unit):
  match res:
    case Fail{e}:
      die("error: " ++ P.Http.Error.show(e))
    case Done{+r}:
      Bool.pick(IO(Unit), should_fail(out, r), die("HTTP error " ++ Nat.show(P.Http.status(r))),
        answered(Done{r}, follow, req, hops, out, rest))

# Sends req; with --follow, sends what each redirect asks for, `hops` more
# times at most.
def go(hops: Nat, +follow: Bool, +cfg: P.Http.Config(), +req: P.Http.Request(), +out: Output) -> IO(Unit):
  match hops:
    case 0n:
      IO.bind(Result<&2, &2, P.Http.Error(), P.Http.Response()>, Unit, P.Http.send(cfg, req),
        res => checked(res, follow, req, 0n, out, x => die("error: more than 10 redirects")))
    case 1n++p:
      IO.bind(Result<&2, &2, P.Http.Error(), P.Http.Response()>, Unit, P.Http.send(cfg, req),
        res => checked(res, follow, req, 1n+p, out, next => go(p, follow, cfg, next, out)))

def method_of(m: Maybe<&2, String>, body: Maybe<&2, String>) -> P.Http.Method():
  match m:
    case Some{name}:
      P.Http.method(name)
    case None{}:
      match body:
        case Some{b}:
          P.Http.POST()
        case None{}:
          P.Http.GET()

def body_of(b: Maybe<&2, String>) -> List<&2, U32>:
  match b:
    case Some{s}:
      P.Http.utf8(s)
    case None{}:
      Nil{}

def start(req: Result<&2, &2, P.Http.Error(), P.Http.Request()>, follow: Bool, cfg: P.Http.Config(), out: Output) -> IO(Unit):
  match req:
    case Fail{e}:
      die("error: " ++ P.Http.Error.show(e))
    case Done{r}:
      go(10n, follow, cfg, r, out)

def configured(dns: Result<&2, &2, DNS.Dns.Error(), DNS.Dns.Config()>, o: Opts) -> IO(Unit):
  match dns o:
    case Fail{e} _:
      die("DNS configuration: " ++ DNS.Dns.Error.show(e))
    case Done{+dc} Opts{m, hs, +b, mx, +t, f, Some{url}, bad, +out}:
      match out:
        case Output{path, include, fail, help, server, port}:
          +servers = Maybe.default(&2, List<&2, String>, Maybe.map(&2, String, List<&2, String>, x => [x], server),
            DNS.Dns.Config.servers(dc))
          +resolver = DNS.Dns.with_port(DNS.Dns.with_timeout(DNS.Dns.with_servers(dc, servers), t), port)
          +cfg = P.Http.with_dns(P.Http.with_max_bytes(P.Http.with_timeout(P.Http.default_config(), t), mx), resolver)
          start(P.Http.request(method_of(m, b), url, List.reverse(&2, P.Http.Header(), hs), body_of(b)), f, cfg, out)
    case Done{dc} Opts{m, hs, b, mx, t, f, None{}, bad, out}:
      die(usage())

def run.options(help: Bool, bad: Maybe<&2, String>, url: Maybe<&2, String>, o: Opts) -> IO(Unit):
  match help bad url:
    case True{} _ _:
      IO.print(help_text())
    case False{} Some{msg} _:
      die(msg ++ "\n" ++ usage())
    case False{} None{} None{}:
      die(usage())
    case False{} None{} Some{url}:
      IO.bind(Result<&2, &2, DNS.Dns.Error(), DNS.Dns.Config()>, Unit, DNS.Dns.system(), r => configured(r, o))

def run(+o: Opts) -> IO(Unit):
  match o:
    case Opts{m, hs, b, mx, t, f, u, bad, Output{path, include, fail, help, server, port}}:
      run.options(help, bad, u, o)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(parse(List.tail(&1, String, args), None{}, opts0()))
