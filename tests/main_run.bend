import Base
import ../main.bend as P
import ../src/message.bend as M

# Runtime tests of main.bend's error tags, on both lanes:
#   bend tests/main_run.bend
#   bend tests/main_run.bend -o /tmp/main_run && /tmp/main_run
# A consumer of main.bend cannot name src/message.bend's constructors, so it
# matches on Http.Error.kind / Http.ParseError.kind (P.Timeout{}, ...). The
# errors come from the public API where it can make them (a bad URL, a bad
# header, a closed port, malformed responses); message.bend is imported only
# to build the ones it cannot make offline (Timeout, Dns, Tls, NoAddress, Io).

def kind_name(k: P.Http.ErrorKind()) -> String:
  match k:
    case P.BadUrl{}:
      "BadUrl"
    case P.BadRequest{}:
      "BadRequest"
    case P.NoAddress{}:
      "NoAddress"
    case P.Dns{}:
      "Dns"
    case P.Connect{}:
      "Connect"
    case P.Io{}:
      "Io"
    case P.Timeout{}:
      "Timeout"
    case P.Tls{}:
      "Tls"
    case P.Parse{}:
      "Parse"

def parse_kind_name(k: P.Http.ParseErrorKind()) -> String:
  match k:
    case P.BadStatusLine{}:
      "BadStatusLine"
    case P.BadVersion{}:
      "BadVersion"
    case P.BadHeader{}:
      "BadHeader"
    case P.BadLength{}:
      "BadLength"
    case P.ConflictingFraming{}:
      "ConflictingFraming"
    case P.UnsupportedEncoding{}:
      "UnsupportedEncoding"
    case P.BadChunk{}:
      "BadChunk"
    case P.UnexpectedUpgrade{}:
      "UnexpectedUpgrade"
    case P.Incomplete{}:
      "Incomplete"
    case P.TooLarge{}:
      "TooLarge"

def code_text(c: Maybe<&2, U32>) -> String:
  match c:
    case None{}:
      "-"
    case Some{x}:
      U32.show(x)

def inner_text(p: Maybe<&2, P.Http.ParseError()>) -> String:
  match p:
    case None{}:
      "-"
    case Some{x}:
      parse_kind_name(P.Http.ParseError.kind(x))

# "Kind code parse"
def describe(+e: P.Http.Error()) -> String:
  kind_name(P.Http.Error.kind(e)) ++ " " ++ code_text(P.Http.Error.code(e)) ++ " "
    ++ inner_text(P.Http.Error.parse_error(e))

def err_text(-A: Data, r: Result<&2, &2, P.Http.Error(), A>) -> String:
  match r:
    case Fail{e}:
      describe(e)
    case Done{x}:
      "Done"

def decode_text(r: Result<&2, &2, P.Http.ParseError(), P.Http.Decoded()>) -> String:
  match r:
    case Fail{e}:
      parse_kind_name(P.Http.ParseError.kind(e))
    case Done{x}:
      "Done"

def a(s: String) -> List<&2, U32>:
  P.Http.utf8(s)

def dec(s: String) -> String:
  decode_text(P.Http.decode(P.Http.GET(), 100000n, a(s)))

def encoded(r: Result<&2, &2, P.Http.Error(), P.Http.Request()>) -> String:
  match r:
    case Fail{e}:
      describe(e)
    case Done{q}:
      err_text(P.Http.Bytes(), P.Http.encode(q))

# n copies of b / c, built by loops (so the JS lane can build them).
def fill(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      fill(p, b, b <> acc)

def chars(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      chars(p, c, SCon{c, acc})

def count(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{_, t}:
      count(t, 1n+n)

def size_text(r: Result<&2, &2, P.Http.Error(), List<&2, U32>>) -> String:
  match r:
    case Fail{e}:
      describe(e)
    case Done{xs}:
      Nat.show(count(xs, 0n)) ++ " bytes"

def big_encoded(r: Result<&2, &2, P.Http.Error(), P.Http.Request()>) -> String:
  match r:
    case Fail{e}:
      describe(e)
    case Done{q}:
      size_text(P.Http.encode(q))

# Http.encode of large requests (the JS lane overflowed its stack on a body
# or a header value of some 40 KB before).
def big_cases() -> List<(String & String & String)>:
  [
    ("encode a 200000-byte body", big_encoded(P.Http.request(P.Http.POST(), "http://h.example/", [],
      fill(200000n, 97, Nil{}))), "200079 bytes"),
    ("encode a 100000-char header value", big_encoded(P.Http.request(P.Http.GET(), "http://h.example/",
      [P.Http.header("X", chars(100000n, 'v', SNil{}))], [])), "100059 bytes")
  ]

def cases() -> List<(String & String & String)>:
  [
    ("bad URL", err_text(P.Http.Url(), P.Http.Url.parse("ftp://h.example/")), "BadUrl - -"),
    ("ambiguous host", err_text(P.Http.Url(), P.Http.Url.parse("http://127.1/")), "BadUrl - -"),
    ("bad header", encoded(P.Http.request(P.Http.GET(), "http://h.example/", [P.Http.header("X", " a")], [])),
      "BadRequest - -"),
    ("reserved header", encoded(P.Http.request(P.Http.GET(), "http://h.example/", [P.Http.header("Host", "a")], [])),
      "BadRequest - -"),
    ("non-ASCII header value", encoded(P.Http.request(P.Http.GET(), "http://h.example/",
      [P.Http.header("X", "b\u{e9}nd")], [])), "BadRequest - -"),
    ("Timeout", describe(M.Timeout{}), "Timeout - -"),
    ("NoAddress", describe(M.NoAddress{"h"}), "NoAddress - -"),
    ("Dns code", describe(M.Dns{2, "x"}), "Dns 2 -"),
    ("Io code", describe(M.Io{104, "x"}), "Io 104 -"),
    ("Tls code", describe(M.Tls{71, "x"}), "Tls 71 -"),
    ("Parse inner", describe(M.Parse{M.TooLarge{}}), "Parse - TooLarge"),
    ("decode BadStatusLine", dec("SSH-2.0\r\n\r\n"), "BadStatusLine"),
    ("decode BadVersion", dec("HTTP/2.0 200 OK\r\n\r\n"), "BadVersion"),
    ("decode BadHeader", dec("HTTP/1.1 200 OK\r\n x: y\r\n\r\n"), "BadHeader"),
    ("decode BadLength", dec("HTTP/1.1 200 OK\r\nContent-Length: x\r\n\r\n"), "BadLength"),
    ("decode ConflictingFraming", dec("HTTP/1.1 200 OK\r\nContent-Length: 1\r\nTransfer-Encoding: chunked\r\n\r\n"),
      "ConflictingFraming"),
    ("decode UnsupportedEncoding", dec("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\n"), "UnsupportedEncoding"),
    ("decode BadChunk", dec("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nz\r\n"), "BadChunk"),
    ("decode UnexpectedUpgrade", dec("HTTP/1.1 101 Switching\r\n\r\n"), "UnexpectedUpgrade"),
    ("decode Incomplete", dec("HTTP/1.1 200 OK\r\nContent-Length: 9\r\n\r\nab"), "Incomplete"),
    ("decode TooLarge", decode_text(P.Http.decode(P.Http.GET(), 3n, a("HTTP/1.1 200 OK\r\n\r\n"))), "TooLarge")
  ]

def report.line(ok: Bool, name: String, got: String) -> IO(Unit):
  match ok:
    case True{}:
      IO.print("PASS " ++ name)
    case False{}:
      IO.print("FAIL " ++ name ++ ": got " ++ got)

def report(xs: List<(String & String & String)>, +fails: Nat) -> IO(Nat):
  match xs:
    case Nil{}:
      IO.pure(Nat, fails)
    case Con{c, t}:
      match c:
        case (name, got, want):
          +g = got
          +ok = String.eq(g, want)
          do IO<Nat>:
            report.line(ok, name, g)
            report(t, Bool.pick(Nat, ok, fails, 1n+fails))

def finish(+fails: Nat) -> IO(Unit):
  match fails:
    case 0n:
      IO.print("ALL PASS")
    case 1n+p:
      IO.print("SOME FAIL: " ++ Nat.show(1n+p))

def connect_case(+f: Nat) -> IO(Nat):
  IO.bind(Result<&2, &2, P.Http.Error(), P.Http.Response()>, Nat,
    P.Http.fetch(P.Http.default_config(), "http://127.0.0.1:1/"),
    r => report([("closed port", err_text(P.Http.Response(), r), "Connect 111 -")], f))

def main() -> IO(Unit):
  do IO<Unit>:
    f1 : Nat <- report(cases(), 0n)
    f2 : Nat <- connect_case(f1)
    f3 : Nat <- report(big_cases(), f2)
    finish(f3)
