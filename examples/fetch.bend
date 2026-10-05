import Base
import ../main.bend as P

# bend examples/fetch.bend -- [-X METHOD] [-H 'Name: value']... [-d body]
#                             [--max N] [--timeout MS] [--follow] URL
#
# Sends one request and prints the status line, the headers, a blank line,
# then the body: as text if it is valid UTF-8, else "<N bytes of binary>".
# -d sends the text as the body (UTF-8) and makes the default method POST;
# --max caps the response at N bytes (default 16 MiB); --timeout bounds each
# blocking step: the name lookup, connect, send, each read (default 30000 ms;
# 0: no limit; see Http.with_timeout: a timed-out plain-HTTP read or lookup
# is not cancelled, so this example exits with IO.die on failure rather than
# wait for it); --follow follows up to 10 redirects with Http.redirect. On
# failure it prints why and exits with 1.
#
#   bend examples/fetch.bend -- https://example.com/
#   bend examples/fetch.bend -- -X POST -H 'Content-Type: text/plain' -d hi https://httpbin.org/post
#   bend examples/fetch.bend -- --follow https://httpbin.org/redirect/3

def usage() -> String:
  "usage: fetch [-X METHOD] [-H 'Name: value']... [-d body] [--max N] [--timeout MS] [--follow] URL"

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
  FUnknown{}
  FUrl{}

def flag(+a: String) -> Flag:
  Bool.pick(Flag, String.eq(a, "-X"), FMethod{},
  Bool.pick(Flag, String.eq(a, "-H"), FHeader{},
  Bool.pick(Flag, String.eq(a, "-d"), FData{},
  Bool.pick(Flag, String.eq(a, "--max"), FMax{},
  Bool.pick(Flag, String.eq(a, "--timeout"), FTimeout{},
  Bool.pick(Flag, String.eq(a, "--follow"), FFollow{},
  Bool.pick(Flag, String.starts_with(a, "-") && Nat.is_lt(1n, String.length(a)), FUnknown{},
  FUrl{})))))))

type Opts is Data:
  Opts{method: Maybe<&2, String>, headers: List<&2, P.Http.Header()>, body: Maybe<&2, String>,
    max: Nat, timeout: Nat, follow: Bool, url: Maybe<&2, String>, bad: Maybe<&2, String>}

def opts0() -> Opts:
  Opts{None{}, Nil{}, None{}, 16777216n, 30000n, False{}, None{}, None{}}

# The first complaint wins.
def complain(o: Opts, msg: String) -> Opts:
  match o:
    case Opts{m, hs, b, x, t, f, u, bad}:
      Opts{m, hs, b, x, t, f, u, Maybe.or(&2, String, bad, Some{msg})}

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
    case Some{x} Opts{m, hs, b, mx, t, f, u, bad}:
      Opts{m, x <> hs, b, mx, t, f, u, bad}

def set_max(n: Maybe<&2, Nat>, o: Opts, +a: String) -> Opts:
  match n o:
    case None{} _:
      complain(o, "--max needs a number: " ++ a)
    case Some{x} Opts{m, hs, b, mx, t, f, u, bad}:
      Opts{m, hs, b, x, t, f, u, bad}

def set_timeout(n: Maybe<&2, Nat>, o: Opts, +a: String) -> Opts:
  match n o:
    case None{} _:
      complain(o, "--timeout needs a number: " ++ a)
    case Some{x} Opts{m, hs, b, mx, t, f, u, bad}:
      Opts{m, hs, b, mx, x, f, u, bad}

# `a` is the value of the option `p`.
def value(p: Flag, +a: String, o: Opts) -> Opts:
  match p o:
    case FMethod{} Opts{m, hs, b, mx, t, f, u, bad}:
      Opts{Some{a}, hs, b, mx, t, f, u, bad}
    case FHeader{} _:
      add_header(header_of(String.split(a, ':')), o, a)
    case FData{} Opts{m, hs, b, mx, t, f, u, bad}:
      Opts{m, hs, Some{a}, mx, t, f, u, bad}
    case FMax{} _:
      set_max(Nat.read(a), o, a)
    case FTimeout{} _:
      set_timeout(Nat.read(a), o, a)
    case _ _:
      o

# `a` is not an option's value.
def word(k: Flag, +a: String, o: Opts) -> Opts:
  match k o:
    case FFollow{} Opts{m, hs, b, mx, t, f, u, bad}:
      Opts{m, hs, b, mx, t, True{}, u, bad}
    case FUnknown{} _:
      complain(o, "unknown option: " ++ a)
    case FUrl{} Opts{m, hs, b, mx, t, f, u, bad}:
      match u:
        case None{}:
          Opts{m, hs, b, mx, t, f, Some{a}, bad}
        case Some{first}:
          complain(Opts{m, hs, b, mx, t, f, Some{first}, bad}, "more than one URL: " ++ a)
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

def count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{_, t}:
      count(t, 1n+n)

def print_headers(hs: List<&2, P.Http.Header()>) -> IO(Unit):
  match hs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, t}:
      do IO<Unit>:
        IO.print(P.Http.Header.name(h) ++ ": " ++ P.Http.Header.value(h))
        print_headers(t)

def print_body(text: Maybe<&2, String>, n: Nat) -> IO(Unit):
  match text:
    case Some{s}:
      IO.write(s)
    case None{}:
      IO.print("<" ++ Nat.show(n) ++ " bytes of binary>")

def print_response(+r: P.Http.Response()) -> IO(Unit):
  do IO<Unit>:
    IO.print(P.Http.status_line(r))
    print_headers(P.Http.headers(r))
    IO.print("")
    print_body(P.Http.text(r), count(P.Http.body(r), 0n))

# Sending, following redirects
# ----------------------------

def die(msg: String) -> IO(Unit):
  IO.die(Unit, 1, msg)

def next_hop(next: Maybe<&2, P.Http.Request()>, +r: P.Http.Response(), rest: P.Http.Request() -> IO(Unit)) ->
  IO(Unit):
  match next:
    case None{}:
      print_response(r)
    case Some{req}:
      rest(req)

def answered(res: Result<&2, &2, P.Http.Error(), P.Http.Response()>, follow: Bool, +req: P.Http.Request(),
  hops: Nat, rest: P.Http.Request() -> IO(Unit)) -> IO(Unit):
  match res:
    case Fail{e}:
      die("error: " ++ P.Http.Error.show(e))
    case Done{+r}:
      match follow hops:
        case False{} _:
          print_response(r)
        case True{} 0n:
          next_hop(P.Http.redirect(req, r), r, x => die("error: more than 10 redirects"))
        case True{} 1n+p:
          next_hop(P.Http.redirect(req, r), r, rest)

# Sends req; with --follow, sends what each redirect asks for, `hops` more
# times at most.
def go(hops: Nat, +follow: Bool, +cfg: P.Http.Config(), +req: P.Http.Request()) -> IO(Unit):
  match hops:
    case 0n:
      IO.bind(Result<&2, &2, P.Http.Error(), P.Http.Response()>, Unit, P.Http.send(cfg, req),
        res => answered(res, follow, req, 0n, x => die("error: more than 10 redirects")))
    case 1n++p:
      IO.bind(Result<&2, &2, P.Http.Error(), P.Http.Response()>, Unit, P.Http.send(cfg, req),
        res => answered(res, follow, req, 1n+p, next => go(p, follow, cfg, next)))

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

def start(req: Result<&2, &2, P.Http.Error(), P.Http.Request()>, follow: Bool, cfg: P.Http.Config()) -> IO(Unit):
  match req:
    case Fail{e}:
      die("error: " ++ P.Http.Error.show(e))
    case Done{r}:
      go(10n, follow, cfg, r)

def run(o: Opts) -> IO(Unit):
  match o:
    case Opts{m, hs, +b, mx, t, f, u, bad}:
      match u bad:
        case _ Some{msg}:
          die(msg ++ "\n" ++ usage())
        case None{} None{}:
          die(usage())
        case Some{url} None{}:
          +cfg = P.Http.with_max_bytes(P.Http.with_timeout(P.Http.default_config(), t), mx)
          start(P.Http.request(method_of(m, b), url, List.reverse(&2, P.Http.Header(), hs), body_of(b)), f, cfg)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    run(parse(List.tail(&1, String, args), None{}, opts0()))
