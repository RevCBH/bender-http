import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/url.bend as U
import ../src/encode.bend as E
import ../src/client.bend as C

# Runtime tests for client.bend and transport.bend, on both lanes:
#   bend tests/client_run.bend
#   bend tests/client_run.bend -o /tmp/client_run && /tmp/client_run
# Prints PASS / FAIL per case (a FAIL shows what came back), then "ALL PASS"
# or "SOME FAIL: n". Covers:
# - C.redirect: every redirect status, Location forms (absolute, path,
#   scheme-relative, relative, hostile), method and body rules, credentials
#   dropped across origins;
# - C.error_show for every error;
# - C.resolve: IPv4 literals, the hosts table, DNS (localhost, a name that
#   does not resolve); numeric hosts that are not dotted quads ("127.1",
#   "2130706433", "0x7f.1", "010.0.0.1") refused as ambiguous before any
#   lookup; hosts entries that are not IPv4 addresses refused;
# - C.redirect over 60000 request headers (the JS lane's stack);
# - X.plain against an in-process server on 127.0.0.1 (via the hosts
#   table): split writes, chunked, 1xx, close-delimited, truncated, too
#   large, binary, a read timeout, a response complete before the close;
# - live fetches of http://example.com/ and https://example.com/, and the
#   TLS lane's errors (needs internet).

# Helpers
# -------

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def str_eq(a: String, b: String) -> Bool:
  str_eq.go(a, b, True{})

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

def headers_text(hs: List<&2, M.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{h, t}:
      match h t:
        case M.Header{n, v} Nil{}:
          n ++ ": " ++ v
        case M.Header{n, v} _:
          n ++ ": " ++ v ++ ", " ++ headers_text(t)

# "METHOD url [headers] body"
def req_text(r: M.Request) -> String:
  match r:
    case M.Request{m, u, hs, body}:
      E.method_name(m) ++ " " ++ U.show(u) ++ " [" ++ headers_text(hs) ++ "] "
        ++ B.to_latin1(body)

def next_text(r: Maybe<&2, M.Request>) -> String:
  match r:
    case None{}:
      "None"
    case Some{x}:
      req_text(x)

def any_url() -> M.Url:
  M.Url{M.Http{}, "invalid", 1n, "/"}

def url_of(r: Result<&2, &2, M.Error, M.Url>) -> M.Url:
  match r:
    case Done{u}:
      u
    case Fail{e}:
      any_url()

def req(m: M.Method, url: String, hs: List<&2, M.Header>, body: String) -> M.Request:
  M.Request{m, url_of(U.parse(url)), hs, B.from_ascii(body)}

def hdr(n: String, v: String) -> M.Header:
  M.Header{n, v}

def resp(st: Nat, hs: List<&2, M.Header>) -> M.Response:
  M.Response{M.Http11{}, st, "R", hs, Nil{}}

def loc(l: String) -> List<&2, M.Header>:
  [hdr("Location", l)]

def redir(r: M.Request, st: Nat, hs: List<&2, M.Header>) -> String:
  next_text(C.redirect(r, resp(st, hs)))

def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rep(n: Nat, c: Char) -> String:
  rep.go(n, c, SNil{})

def ct_post() -> M.Request:
  req(M.POST{}, "http://h.example/form", [hdr("Content-Type", "text/plain"), hdr("X-A", "1")], "abc")

def creds() -> List<&2, M.Header>:
  [hdr("Authorization", "Bearer t"), hdr("X-A", "1"), hdr("COOKIE", "c=1"), hdr("proxy-authorization", "p")]

# Pure cases: (name, got, want)
# -----------------------------

def redirect_cases() -> List<(String & String & String)>:
  +g = req(M.GET{}, "http://h.example:8080/a/b?x=1", [], "")
  +s = req(M.GET{}, "https://h.example/a", creds(), "")
  [
    ("301 absolute", redir(g, 301n, loc("https://other.example/new")), "GET https://other.example/new [] "),
    ("302 path keeps origin", redir(g, 302n, loc("/p?q=1")), "GET http://h.example:8080/p?q=1 [] "),
    ("307 path", redir(g, 307n, loc("/")), "GET http://h.example:8080/ [] "),
    ("308 absolute port", redir(g, 308n, loc("http://h.example:9/z")), "GET http://h.example:9/z [] "),
    ("303 POST becomes GET", redir(ct_post(), 303n, loc("/done")), "GET http://h.example/done [X-A: 1] "),
    ("302 POST becomes GET", redir(ct_post(), 302n, loc("/done")), "GET http://h.example/done [X-A: 1] "),
    ("301 POST becomes GET", redir(ct_post(), 301n, loc("/done")), "GET http://h.example/done [X-A: 1] "),
    ("307 POST keeps body", redir(ct_post(), 307n, loc("/again")),
      "POST http://h.example/again [Content-Type: text/plain, X-A: 1] abc"),
    ("308 POST keeps body", redir(ct_post(), 308n, loc("/again")),
      "POST http://h.example/again [Content-Type: text/plain, X-A: 1] abc"),
    ("301 PUT keeps PUT", redir(req(M.PUT{}, "http://h.example/", [], "b"), 301n, loc("/n")), "PUT http://h.example/n [] b"),
    ("302 PUT keeps PUT", redir(req(M.PUT{}, "http://h.example/", [], "b"), 302n, loc("/n")), "PUT http://h.example/n [] b"),
    ("303 PUT becomes GET", redir(req(M.PUT{}, "http://h.example/", [], "b"), 303n, loc("/n")), "GET http://h.example/n [] "),
    ("303 HEAD stays HEAD", redir(req(M.HEAD{}, "http://h.example/", [], ""), 303n, loc("/n")), "HEAD http://h.example/n [] "),
    ("303 DELETE becomes GET", redir(req(M.DELETE{}, "http://h.example/", [], ""), 303n, loc("/n")), "GET http://h.example/n [] "),
    ("302 Other keeps method", redir(req(M.Other{"PROPFIND"}, "http://h.example/", [], ""), 302n, loc("/n")),
      "PROPFIND http://h.example/n [] "),
    ("303 Other becomes GET", redir(req(M.Other{"PROPFIND"}, "http://h.example/", [], ""), 303n, loc("/n")),
      "GET http://h.example/n [] "),
    ("scheme-relative", redir(s, 302n, loc("//cdn.example/x")), "GET https://cdn.example/x [X-A: 1] "),
    ("fragment dropped", redir(g, 302n, loc("/a#frag")), "GET http://h.example:8080/a [] "),
    ("query only path", redir(g, 302n, loc("/?a=b")), "GET http://h.example:8080/?a=b [] "),
    ("uppercase scheme and host", redir(g, 302n, loc("HTTPS://Other.Example/X")), "GET https://other.example/X [] "),
    ("Location name any case", redir(g, 302n, [hdr("LOCATION", "/up")]), "GET http://h.example:8080/up [] "),
    ("first Location wins", redir(g, 302n, [hdr("location", "/one"), hdr("Location", "/two")]),
      "GET http://h.example:8080/one [] "),
    ("same origin keeps credentials", redir(s, 302n, loc("/b")),
      "GET https://h.example/b [Authorization: Bearer t, X-A: 1, COOKIE: c=1, proxy-authorization: p] "),
    ("same origin absolute keeps credentials", redir(s, 302n, loc("https://H.EXAMPLE:443/c")),
      "GET https://h.example/c [Authorization: Bearer t, X-A: 1, COOKIE: c=1, proxy-authorization: p] "),
    ("other host drops credentials", redir(s, 302n, loc("https://evil.example/")), "GET https://evil.example/ [X-A: 1] "),
    ("https to http drops credentials", redir(s, 302n, loc("http://h.example/")), "GET http://h.example/ [X-A: 1] "),
    ("other port drops credentials", redir(s, 307n, loc("https://h.example:8443/")), "GET https://h.example:8443/ [X-A: 1] "),
    ("long path", redir(g, 302n, loc("/" ++ rep(3000n, 'p'))), "GET http://h.example:8080/" ++ rep(3000n, 'p') ++ " [] "),
    ("200 with Location", redir(g, 200n, loc("/x")), "None"),
    ("201 with Location", redir(g, 201n, loc("/x")), "None"),
    ("300", redir(g, 300n, loc("/x")), "None"),
    ("304", redir(g, 304n, loc("/x")), "None"),
    ("305", redir(g, 305n, loc("/x")), "None"),
    ("404", redir(g, 404n, loc("/x")), "None"),
    ("302 no Location", redir(g, 302n, [hdr("X-Location", "/x")]), "None"),
    ("302 empty Location", redir(g, 302n, loc("")), "None"),
    ("relative path refused", redir(g, 302n, loc("next/page")), "None"),
    ("dot path refused", redir(g, 302n, loc("../up")), "None"),
    ("ftp refused", redir(g, 302n, loc("ftp://h.example/")), "None"),
    ("javascript refused", redir(g, 302n, loc("javascript:alert(1)")), "None"),
    ("userinfo refused", redir(g, 302n, loc("http://user:pw@h.example/")), "None"),
    ("ipv6 refused", redir(g, 302n, loc("http://[::1]/")), "None"),
    ("port out of range refused", redir(g, 302n, loc("http://h.example:99999/")), "None"),
    ("space in path refused", redir(g, 302n, loc("/a b")), "None"),
    ("CRLF injection refused", redir(g, 302n, loc("/a\r\nX-Evil: 1")), "None"),
    ("bare slashes refused", redir(g, 302n, loc("//")), "None"),
    ("Latin-1 refused", redir(g, 302n, loc("/caf\u{e9}")), "None")
  ]

def error_cases() -> List<(String & String & String)>:
  [
    ("show BadUrl", C.error_show(M.BadUrl{"empty host"}), "bad URL: empty host"),
    ("show BadRequest", C.error_show(M.BadRequest{"bad header"}), "bad request: bad header"),
    ("show NoAddress", C.error_show(M.NoAddress{"h.example"}), "no IPv4 address for h.example"),
    ("show Dns", C.error_show(M.Dns{2, "Name or service not known"}), "DNS error 2: Name or service not known"),
    ("show Connect", C.error_show(M.Connect{111, "Connection refused"}), "connect error 111: Connection refused"),
    ("show Io", C.error_show(M.Io{104, "Connection reset by peer"}), "I/O error 104: Connection reset by peer"),
    ("show Timeout", C.error_show(M.Timeout{}), "timed out"),
    ("show Tls", C.error_show(M.Tls{71, "certificate has expired"}), "TLS error 71: certificate has expired"),
    ("show BadStatusLine", C.error_show(M.Parse{M.BadStatusLine{}}), "bad response: malformed status line"),
    ("show BadVersion", C.error_show(M.Parse{M.BadVersion{}}), "bad response: unsupported HTTP version"),
    ("show BadHeader", C.error_show(M.Parse{M.BadHeader{}}), "bad response: malformed header field"),
    ("show BadLength", C.error_show(M.Parse{M.BadLength{}}), "bad response: invalid Content-Length"),
    ("show ConflictingFraming", C.error_show(M.Parse{M.ConflictingFraming{}}),
      "bad response: both Transfer-Encoding and Content-Length"),
    ("show UnsupportedEncoding", C.error_show(M.Parse{M.UnsupportedEncoding{}}),
      "bad response: unsupported Transfer-Encoding"),
    ("show BadChunk", C.error_show(M.Parse{M.BadChunk{}}), "bad response: malformed chunked body"),
    ("show UnexpectedUpgrade", C.error_show(M.Parse{M.UnexpectedUpgrade{}}),
      "bad response: unexpected 101 Switching Protocols"),
    ("show Incomplete", C.error_show(M.Parse{M.Incomplete{}}),
      "bad response: the connection closed before the response ended"),
    ("show TooLarge", C.error_show(M.Parse{M.TooLarge{}}), "bad response: the response is larger than the limit"),
    ("show empty message", C.error_show(M.Io{0, ""}), "I/O error 0: ")
  ]

def misc_cases() -> List<(String & String & String)>:
  +r = {M.Response{M.Http10{}, 404n, "Not Found", [], B.from_ascii("x")} : M.Response}
  [
    ("status_line 1.0", C.status_line(r), "HTTP/1.0 404 Not Found"),
    ("status_line empty reason", C.status_line(M.Response{M.Http11{}, 200n, "", [], []}), "HTTP/1.1 200 "),
    ("is_success 404", Bool.show(C.is_success(r)), "False"),
    ("is_success 200", Bool.show(C.is_success(resp(200n, []))), "True"),
    ("is_success 299", Bool.show(C.is_success(resp(299n, []))), "True"),
    ("is_success 300", Bool.show(C.is_success(resp(300n, []))), "False"),
    ("is_success 199", Bool.show(C.is_success(resp(199n, []))), "False"),
    ("method_of GET", E.method_name(C.method_of("GET")), "GET"),
    ("method_of OPTIONS", E.method_name(C.method_of("OPTIONS")), "OPTIONS"),
    ("method_of lowercase is Other", req_text(M.Request{C.method_of("get"), any_url(), [], []}),
      "get http://invalid:1/ [] "),
    ("text utf8", Maybe.default(&2, String, C.text(M.Response{M.Http11{}, 200n, "", [], [104, 195, 169]}), "?"),
      "h\u{e9}"),
    ("text binary", Maybe.default(&2, String, C.text(M.Response{M.Http11{}, 200n, "", [], [255, 0]}), "?"), "?")
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
          +ok = str_eq(g, want)
          do IO<Nat>:
            report.line(ok, name, g)
            report(t, Bool.pick(Nat, ok, fails, 1n+fails))

# IO cases
# --------

# Runs act; PASS when what it gives starts with `want`.
def check(name: String, act: IO(String), +want: String, +fails: Nat) -> IO(Nat):
  IO.bind(String, Nat, act, got => report([(name, String.take(got, String.length(want)) ++ "", want)], fails))

def check_exact(name: String, act: IO(String), want: String, +fails: Nat) -> IO(Nat):
  IO.bind(String, Nat, act, got => report([(name, got, want)], fails))

def resolved_text(r: Result<&2, &2, M.Error, String>) -> String:
  match r:
    case Done{ip}:
      "Done " ++ ip
    case Fail{e}:
      "Fail " ++ C.error_show(e)

def resolve(cfg: C.Config, host: String) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, String>, String, C.resolve(cfg, host),
    r => IO.pure(String, resolved_text(r)))

def response_text(r: Result<&2, &2, M.Error, M.Response>) -> String:
  match r:
    case Fail{e}:
      "Fail " ++ C.error_show(e)
    case Done{x}:
      match x:
        case M.Response{v, st, re, hs, +body}:
          N.show(st) ++ " " ++ re ++ " len=" ++ Nat.show(count(body, 0n)) ++ " "
            ++ B.to_latin1(take(40n, body))

def sent(act: IO(Result<&2, &2, M.Error, M.Response>)) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, M.Response>, String, act, r => IO.pure(String, response_text(r)))

# Whether the body is exactly xs.
def bytes_eq(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      bytes_eq(xs, ys, ok && U32.is_eq(x, y))
    case _ _:
      False{}

def body_is(want: List<&2, U32>, r: Result<&2, &2, M.Error, M.Response>) -> String:
  match r:
    case Fail{e}:
      "Fail " ++ C.error_show(e)
    case Done{x}:
      match x:
        case M.Response{v, st, re, hs, body}:
          Bool.pick(String, bytes_eq(body, want, True{}), "exact", "differs")

# An in-process server
# --------------------

def send_next(sr: Socket & Result<&1, &1, U32 & String, Unit>, k: Socket -> IO(Socket)) -> IO(Socket):
  (s, r) = sr
  k(s)

# Sends each piece after sleeping `delay` ms (errors ignored: the client
# may have hung up on purpose).
def send_pieces(pieces: List<&2, List<&2, U32>>, sock: Socket, +delay: U32) -> IO(Socket):
  match pieces:
    case Nil{}:
      IO.pure(Socket, sock)
    case Con{p, rest}:
      do IO<Socket>:
        IO.sleep(delay)
        sr : Socket & Result<&1, &1, U32 & String, Unit> <- TCP.send_bytes(sock, p)
        send_next(sr, s2 => send_pieces(rest, s2, delay))

def drop_read(rr: Socket & Result<&1, &1, U32 & String, List<&2, U32>>) -> Socket:
  (s, r) = rr
  s

def talk(s: Socket, pieces: List<&2, List<&2, U32>>, delay: U32, hold: U32) -> IO(Unit):
  do IO<Unit>:
    rr : Socket & Result<&1, &1, U32 & String, List<&2, U32>> <- TCP.recv_bytes(s, 65536)
    s3 : Socket <- send_pieces(pieces, drop_read(rr), delay)
    IO.sleep(hold)
    Socket.close(s3)

def served(p: Listener & Result<&1, &1, U32 & String, Socket>, pieces: List<&2, List<&2, U32>>, delay: U32,
  hold: U32) -> IO(Unit):
  (l, r) = p
  match r:
    case Fail{e}:
      Listener.close(l)
    case Done{s}:
      do IO<Unit>:
        talk(s, pieces, delay, hold)
        Listener.close(l)

# Accepts one connection, reads the request (one read), sends the pieces
# (`delay` ms before each), waits `hold` ms, closes.
def serve(l: Listener, pieces: List<&2, List<&2, U32>>, delay: U32, hold: U32) -> IO(Unit):
  IO.bind(Listener & Result<&1, &1, U32 & String, Socket>, Unit, TCP.accept(l),
    p => served(p, pieces, delay, hold))

def listen_retry(+port: U32, r: Result<&1, &1, U32 & String, Listener>, rest: IO(Listener & U32)) ->
  IO(Listener & U32):
  match r:
    case Done{l}:
      IO.pure(Listener & U32, (l, port))
    case Fail{e}:
      rest

def listen_any(tries: Nat, +port: U32) -> IO(Listener & U32):
  match tries:
    case 0n:
      IO.die(Listener & U32, 1, "no free tcp port")
    case 1n+t:
      IO.bind(Result<&1, &1, U32 & String, Listener>, Listener & U32, TCP.listen("127.0.0.1", port),
        r => listen_retry(port, r, listen_any(t, (port + 1 : U32))))

def local_cfg(max: Nat, ms: Nat) -> C.Config:
  C.with_host(C.with_max_bytes(C.with_timeout(C.default_config(), ms), max), "Test.Local", "127.0.0.1")

def local_req(m: M.Method, port: U32) -> M.Request:
  M.Request{m, M.Url{M.Http{}, "test.local", U32.to_nat(port), "/x"}, [], []}

# What the client does with the server's port.
def with_server.go(b: Listener & U32, pieces: List<&2, List<&2, U32>>, delay: U32, hold: U32,
  client: U32 -> IO(String)) -> IO(String):
  (l, port) = b
  do IO<String>:
    ch : Chan(Unit) <- IO.fork(Unit, serve(l, pieces, delay, hold))
    out : String <- client(port)
    IO.join(Unit, ch)
    return out

def with_server(base: U32, pieces: List<&2, List<&2, U32>>, delay: U32, hold: U32, client: U32 -> IO(String)) ->
  IO(String):
  IO.bind(Listener & U32, String, listen_any(64n, base), b => with_server.go(b, pieces, delay, hold, client))

# The client's answer, plus " SLOW" if it took `limit` ms or more.
def timed.end(+t0: Nat, out: String, +limit: Nat, +t1: Nat) -> String:
  out ++ Bool.pick(String, Nat.is_lt(Nat.sub(t1, t0), limit), "", " SLOW " ++ Nat.show(Nat.sub(t1, t0)) ++ "ms")

def timed(limit: Nat, act: IO(String)) -> IO(String):
  do IO<String>:
    t0 : Nat <- IO.now()
    out : String <- act
    t1 : Nat <- IO.now()
    return timed.end(t0, out, limit, t1)

def local(base: U32, pieces: List<&2, List<&2, U32>>, delay: U32, hold: U32, m: M.Method, max: Nat, ms: Nat) ->
  IO(String):
  with_server(base, pieces, delay, hold, port => sent(C.send(local_cfg(max, ms), local_req(m, port))))

# The same, timing only the client's part (not the server's hold).
def local_timed(limit: Nat, base: U32, pieces: List<&2, List<&2, U32>>, delay: U32, hold: U32, m: M.Method, max: Nat,
  ms: Nat) -> IO(String):
  with_server(base, pieces, delay, hold, port => timed(limit, sent(C.send(local_cfg(max, ms), local_req(m, port)))))

def a(s: String) -> List<&2, U32>:
  B.from_ascii(s)

def bytes_up.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      bytes_up.go(p, (i - 1 : U32), i <> acc)

# 0, 1, ..., 255
def all_bytes() -> List<&2, U32>:
  bytes_up.go(256n, 255, Nil{})

def fill(n: Nat, +b: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      fill(p, b, b <> acc)

def binary_case(base: U32) -> IO(String):
  +body = all_bytes()
  with_server(base, [List.append(&2, U32, a("HTTP/1.1 200 OK\r\nContent-Length: 256\r\n\r\n"), body)], 0, 0,
    port => IO.bind(Result<&2, &2, M.Error, M.Response>, String, C.send(local_cfg(16777216n, 5000n),
      local_req(M.GET{}, port)), r => IO.pure(String, body_is(body, r))))

def big_case(base: U32) -> IO(String):
  # 300000 bytes: several 64 KiB reads.
  local(base, [a("HTTP/1.1 200 OK\r\nContent-Length: 300000\r\n\r\n"), fill(300000n, 122, Nil{})], 0, 0,
    M.GET{}, 16777216n, 5000n)

def fetch(url: String) -> IO(String):
  sent(C.fetch(C.default_config(), url))

def live_text(st: Nat, t: Maybe<&2, String>) -> String:
  match t:
    case None{}:
      "not UTF-8"
    case Some{x}:
      N.show(st) ++ Bool.pick(String, String.contains(x, "Example Domain"), " Example Domain", " ?")

def live_has(r: Result<&2, &2, M.Error, M.Response>) -> String:
  match r:
    case Fail{e}:
      "Fail " ++ C.error_show(e)
    case Done{+x}:
      match x:
        case M.Response{v, st, re, hs, body}:
          live_text(st, C.text(x))

def live(url: String) -> IO(String):
  IO.bind(Result<&2, &2, M.Error, M.Response>, String, C.fetch(C.default_config(), url), r => IO.pure(String, live_has(r)))

def numeric_cases(+f0: Nat) -> IO(Nat):
  +dflt = C.default_config()
  +want = {"Fail bad URL: ambiguous IPv4 address" : String}
  do IO<Nat>:
    f1 : Nat <- check_exact("resolve 127.1", resolve(dflt, "127.1"), want, f0)
    f2 : Nat <- check_exact("resolve 2130706433", resolve(dflt, "2130706433"), want, f1)
    f3 : Nat <- check_exact("resolve 0x7f.1", resolve(dflt, "0x7f.1"), want, f2)
    f4 : Nat <- check_exact("resolve 0X7F.1", resolve(dflt, "0X7F.1"), want, f3)
    f5 : Nat <- check_exact("resolve 010.0.0.1", resolve(dflt, "010.0.0.1"), want, f4)
    f6 : Nat <- check_exact("resolve 0177.0.0.1", resolve(dflt, "0177.0.0.1"), want, f5)
    f7 : Nat <- check_exact("resolve 4294967295", resolve(dflt, "4294967295"), want, f6)
    f8 : Nat <- check_exact("resolve 0", resolve(dflt, "0"), want, f7)
    f9 : Nat <- check_exact("resolve 1.2.3.4.5", resolve(dflt, "1.2.3.4.5"), want, f8)
    f10 : Nat <- check_exact("resolve 0x", resolve(dflt, "0x"), want, f9)
    f11 : Nat <- check_exact("fetch http://2130706433/", fetch("http://2130706433:1/"), want, f10)
    f12 : Nat <- check_exact("fetch http://0x7f.1/", fetch("http://0x7f.1:1/"), want, f11)
    f13 : Nat <- check_exact("fetch https://127.1/", fetch("https://127.1:1/"), want, f12)
    f14 : Nat <- check_exact("fetch http://0177.0.0.1/", fetch("http://0177.0.0.1:1/"), want, f13)
    f15 : Nat <- check("a1.b2 is a name", resolve(dflt, "a1.b2.invalid"), "Fail DNS error", f14)
    return f15

# n headers "X-n: v" after an Authorization header (a loop, so the JS lane
# can build many).
def many.go(n: Nat, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match n:
    case 0n:
      hdr("Authorization", "secret") <> acc
    case 1n+p:
      many.go(p, hdr("X-n", "v") <> acc)

def hcount(hs: List<&2, M.Header>, n: Nat) -> Nat:
  match hs:
    case Nil{}:
      n
    case Con{_, t}:
      hcount(t, 1n+n)

def many_text(r: Maybe<&2, M.Request>) -> String:
  match r:
    case None{}:
      "None"
    case Some{x}:
      match x:
        case M.Request{m, u, +hs, body}:
          Nat.show(hcount(hs, 0n)) ++ " headers"
            ++ Bool.pick(String, String.eq(Maybe.default(&2, String, H.get("authorization", hs), "-"), "-"),
              ", no Authorization", ", Authorization kept")

def many_headers_redirect(n: Nat) -> String:
  many_text(C.redirect(req(M.GET{}, "https://h.example/a", many.go(n, Nil{}), ""),
    resp(302n, loc("https://other.example/b"))))

def io_cases(+f0: Nat) -> IO(Nat):
  +dflt = C.default_config()
  do IO<Nat>:
    # resolve
    f1 : Nat <- check_exact("resolve literal", resolve(dflt, "1.2.3.4"), "Done 1.2.3.4", f0)
    f2 : Nat <- check_exact("resolve 0.0.0.0", resolve(dflt, "0.0.0.0"), "Done 0.0.0.0", f1)
    f3 : Nat <- check_exact("resolve hosts table", resolve(C.with_host(dflt, "MyHost.Example", "10.0.0.7"), "myhost.example"),
      "Done 10.0.0.7", f2)
    f4 : Nat <- check_exact("resolve hosts table any case", resolve(C.with_host(dflt, "myhost.example", "10.0.0.7"),
      "MYHOST.EXAMPLE"), "Done 10.0.0.7", f3)
    f5 : Nat <- check_exact("resolve latest entry wins", resolve(C.with_host(C.with_host(dflt, "h", "10.0.0.1"), "H", "10.0.0.2"), "h"),
      "Done 10.0.0.2", f4)
    f6 : Nat <- check_exact("resolve literal before table", resolve(C.with_host(dflt, "1.2.3.4", "9.9.9.9"), "1.2.3.4"),
      "Done 1.2.3.4", f5)
    f7 : Nat <- check_exact("resolve localhost by DNS", resolve(dflt, "localhost"), "Done 127.0.0.1", f6)
    f8 : Nat <- check("resolve unknown name", resolve(dflt, "no-such-host.invalid"), "Fail DNS error", f7)
    f9 : Nat <- check("resolve empty name", resolve(dflt, ""), "Fail DNS error", f8)
    f10 : Nat <- check_exact("resolve octet 256 is ambiguous", resolve(dflt, "256.1.1.1"),
      "Fail bad URL: ambiguous IPv4 address", f9)
    # refused before any connection
    f11 : Nat <- check("send reserved header", sent(C.send(dflt, req(M.GET{}, "http://h.example/", [hdr("host", "x")], ""))),
      "Fail bad request: ", f10)
    f12 : Nat <- check("fetch bad URL", fetch("http://user@h.example/"), "Fail bad URL: userinfo is not supported", f11)
    f13 : Nat <- check("fetch unsupported scheme", fetch("ftp://h.example/"), "Fail bad URL: unsupported scheme", f12)
    f14 : Nat <- check("fetch closed port", fetch("http://127.0.0.1:1/"), "Fail connect error", f13)
    f15 : Nat <- check("fetch https closed port", fetch("https://127.0.0.1:1/"), "Fail connect error", f14)
    f16 : Nat <- check("fetch unknown name", fetch("http://no-such-host.invalid/"), "Fail DNS error", f15)
    # the plain transport against a local server
    f17 : Nat <- check_exact("split writes", local(18610, [a("HTTP/1.1 200 OK\r\nConte"), a("nt-Length: 11\r\n\r"), a("\nhello"),
      a(" world")], 30, 0, M.GET{}, 16777216n, 5000n), "200 OK len=11 hello world", f16)
    f18 : Nat <- check_exact("chunked split", local(18620, [a("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r"),
      a("\nhello\r\n6;x=y\r\n worl"), a("d\r\n0\r\n\r\n")], 20, 0, M.GET{}, 16777216n, 5000n), "200 OK len=11 hello world", f17)
    f19 : Nat <- check_exact("interim 100 skipped", local(18630, [a("HTTP/1.1 100 Continue\r\n\r\n"),
      a("HTTP/1.1 201 Created\r\nContent-Length: 2\r\n\r\nok")], 20, 0, M.POST{}, 16777216n, 5000n), "201 Created len=2 ok", f18)
    f20 : Nat <- check_exact("close-delimited", local(18640, [a("HTTP/1.0 200 OK\r\n\r\nuntil"), a(" the close")], 20, 0,
      M.GET{}, 16777216n, 5000n), "200 OK len=15 until the close", f19)
    f21 : Nat <- check_exact("truncated body", local(18650, [a("HTTP/1.1 200 OK\r\nContent-Length: 100\r\n\r\nshort")], 0, 0,
      M.GET{}, 16777216n, 5000n), "Fail bad response: the connection closed before the response ended", f20)
    f22 : Nat <- check_exact("too large", local(18660, [a("HTTP/1.1 200 OK\r\nContent-Length: 200\r\n\r\n"),
      fill(200n, 120, Nil{})], 0, 0, M.GET{}, 100n, 5000n), "Fail bad response: the response is larger than the limit", f21)
    f23 : Nat <- check_exact("not HTTP", local(18670, [a("SSH-2.0-OpenSSH\r\n")], 0, 0, M.GET{}, 16777216n, 5000n),
      "Fail bad response: malformed status line", f22)
    f24 : Nat <- check_exact("empty response", local(18680, [], 0, 0, M.GET{}, 16777216n, 5000n),
      "Fail bad response: the connection closed before the response ended", f23)
    f25 : Nat <- check_exact("binary body exact", binary_case(18690), "exact", f24)
    f26 : Nat <- check_exact("300000-byte body", big_case(18700), "200 OK len=300000 zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", f25)
    f27 : Nat <- check_exact("leftover ignored", local(18710, [a("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nokJUNK")], 0, 0,
      M.GET{}, 16777216n, 5000n), "200 OK len=2 ok", f26)
    f28 : Nat <- check_exact("read timeout", local_timed(700n, 18720, [a("HTTP/1.1 200 OK\r\n\r\nlate")], 900, 0, M.GET{},
      16777216n, 200n), "Fail timed out", f27)
    f29 : Nat <- check_exact("complete before close", local_timed(1000n, 18730, [a("HTTP/1.1 200 OK\r\nContent-Length: 4\r\n\r\nfast")],
      0, 1500, M.GET{}, 16777216n, 5000n), "200 OK len=4 fast", f28)
    f30 : Nat <- check_exact("HEAD complete before close", local_timed(1000n, 18740,
      [a("HTTP/1.1 200 OK\r\nContent-Length: 99\r\n\r\n")], 0, 1500, M.HEAD{}, 16777216n, 5000n), "200 OK len=0 ", f29)
    f31 : Nat <- check_exact("204 complete before close", local_timed(1000n, 18750,
      [a("HTTP/1.1 204 No Content\r\n\r\n")], 0, 1500, M.GET{}, 16777216n, 5000n), "204 No Content len=0 ", f30)
    f32 : Nat <- check_exact("101 refused", local(18760, [a("HTTP/1.1 101 Switching Protocols\r\n\r\n")], 0, 0,
      M.GET{}, 16777216n, 5000n), "Fail bad response: unexpected 101 Switching Protocols", f31)
    # live, over the internet
    f33 : Nat <- check_exact("live http://example.com/", live("http://example.com/"), "200 Example Domain", f32)
    f34 : Nat <- check_exact("live https://example.com/", live("https://example.com/"), "200 Example Domain", f33)
    f35 : Nat <- check("live expired certificate", fetch("https://expired.badssl.com/"), "Fail TLS error 71:", f34)
    f36 : Nat <- check("live wrong host", fetch("https://wrong.host.badssl.com/"), "Fail TLS error 71:", f35)
    # numeric hosts the OS would read as other addresses, refused before
    # the hosts table or any lookup; hosts entries must be dotted quads
    f37 : Nat <- numeric_cases(f36)
    f38 : Nat <- check_exact("hosts entry not IPv4", resolve(C.with_host(dflt, "x.test", "localhost"), "x.test"),
      "Fail bad request: hosts entry for x.test is not an IPv4 address: localhost", f37)
    f39 : Nat <- check_exact("hosts entry octet 999", resolve(C.with_host(dflt, "x.test", "999.1.1.1"), "x.test"),
      "Fail bad request: hosts entry for x.test is not an IPv4 address: 999.1.1.1", f38)
    f40 : Nat <- check_exact("send to a bad hosts entry", sent(C.send(C.with_host(dflt, "x.test", "localhost"),
      M.Request{M.GET{}, M.Url{M.Https{}, "x.test", 1n, "/"}, [], []})),
      "Fail bad request: hosts entry for x.test is not an IPv4 address: localhost", f39)
    f41 : Nat <- check_exact("hosts table cannot map a numeric host", resolve(C.with_host(dflt, "127.1", "10.0.0.1"),
      "127.1"), "Fail bad URL: ambiguous IPv4 address", f40)
    f42 : Nat <- check_exact("trailing dot is a name", resolve(C.with_host(dflt, "127.1.", "10.0.0.1"), "127.1."),
      "Done 10.0.0.1", f41)
    # (U.ok refuses it, so E.request does, before resolve would)
    f43 : Nat <- check_exact("hand-built URL with a numeric host", sent(C.send(dflt,
      M.Request{M.GET{}, M.Url{M.Http{}, "2130706433", 1n, "/"}, [], []})), "Fail bad request: invalid URL", f42)
    # a cross-origin redirect drops credentials from 60000 headers (a loop:
    # the JS lane's stack overflowed at some 30000 before)
    f44 : Nat <- check_exact("redirect with 60000 headers", IO.pure(String, many_headers_redirect(60000n)),
      "60000 headers, no Authorization", f43)
    return f44

def finish(+fails: Nat) -> IO(Unit):
  match fails:
    case 0n:
      IO.print("ALL PASS")
    case 1n+p:
      IO.print("SOME FAIL: " ++ Nat.show(1n+p))

def main() -> IO(Unit):
  do IO<Unit>:
    f1 : Nat <- report(redirect_cases(), 0n)
    f2 : Nat <- report(error_cases(), f1)
    f3 : Nat <- report(misc_cases(), f2)
    f4 : Nat <- io_cases(f3)
    finish(f4)
