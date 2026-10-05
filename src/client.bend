import Base
import ./bytes.bend as B
import ./message.bend as M
import ./num.bend as N
import ./headers.bend as H
import ./utf8.bend as T
import ./url.bend as U
import ./encode.bend as E
import ./dns.bend as Dns
import ./transport.bend as X

# The client: settings, name resolution, one request/response exchange, and
# the pure pieces a caller needs around it (the next request of a redirect,
# error texts). It follows no redirect by itself: `redirect` computes the
# next request and the caller decides whether to send it.
#
# This file imports foreign code (dns.bend, transport.bend), so nothing a law
# imports may import it.

# Settings
# --------

# hosts: names (Header.name, matched case-insensitively) mapped to IPv4
# addresses (Header.value), consulted before DNS; the first entry for a name
# wins, and an entry whose value is not a dotted-quad IPv4 address makes
# requests to that name fail with BadRequest. timeout_ms bounds each
# blocking step (the name lookup, connect, send, each read; for HTTPS each
# step inside OpenSSL); 0 means no limit. max_bytes bounds the response:
# status line, headers and body, all counted (bytes after the message are
# not counted; the reader stops once the message is complete).
type Config is Data:
  Config{hosts: List<&2, M.Header>, timeout_ms: Nat, max_bytes: Nat}

# No hosts entries, 30 s per step, 16 MiB.
def default_config() -> Config:
  Config{Nil{}, 30000n, 16777216n}

# The config with `name` mapped to `ip`, ahead of any earlier entry for it.
def with_host(cfg: Config, name: String, ip: String) -> Config:
  match cfg:
    case Config{hs, t, m}:
      Config{M.Header{name, ip} <> hs, t, m}

def with_timeout(cfg: Config, ms: Nat) -> Config:
  match cfg:
    case Config{hs, t, m}:
      Config{hs, ms, m}

def with_max_bytes(cfg: Config, n: Nat) -> Config:
  match cfg:
    case Config{hs, t, m}:
      Config{hs, t, n}

# Methods
# -------

def method_of.pick(hit: Bool, m: M.Method, rest: M.Method) -> M.Method:
  match hit:
    case True{}:
      m
    case False{}:
      rest

# The method a name stands for (exact, as methods are case-sensitive):
# GET, HEAD, POST, PUT, DELETE, PATCH, OPTIONS, else Other{name} (which
# E.request refuses unless the name is a token).
def method_of(+name: String) -> M.Method:
  method_of.pick(String.eq(name, "GET"), M.GET{},
  method_of.pick(String.eq(name, "HEAD"), M.HEAD{},
  method_of.pick(String.eq(name, "POST"), M.POST{},
  method_of.pick(String.eq(name, "PUT"), M.PUT{},
  method_of.pick(String.eq(name, "DELETE"), M.DELETE{},
  method_of.pick(String.eq(name, "PATCH"), M.PATCH{},
  method_of.pick(String.eq(name, "OPTIONS"), M.OPTIONS{},
  M.Other{name})))))))

# Responses
# ---------

# The body as text, if it is well-formed UTF-8.
def text(r: M.Response) -> Maybe<&2, String>:
  match r:
    case M.Response{v, st, re, hs, body}:
      T.decode(body)

def version_text(v: M.Version) -> String:
  match v:
    case M.Http10{}:
      "HTTP/1.0"
    case M.Http11{}:
      "HTTP/1.1"

# "HTTP/1.1 200 OK": the version, status and reason as received (no CRLF).
def status_line(r: M.Response) -> String:
  match r:
    case M.Response{v, st, re, hs, body}:
      version_text(v) ++ " " ++ N.show(st) ++ " " ++ re

# A 2xx status.
def is_success(r: M.Response) -> Bool:
  match r:
    case M.Response{v, +st, re, hs, body}:
      Nat.is_le(200n, st) && Nat.is_le(st, 299n)

# Errors
# ------

def parse_error_show(e: M.ParseError) -> String:
  match e:
    case M.BadStatusLine{}:
      "malformed status line"
    case M.BadVersion{}:
      "unsupported HTTP version"
    case M.BadHeader{}:
      "malformed header field"
    case M.BadLength{}:
      "invalid Content-Length"
    case M.ConflictingFraming{}:
      "both Transfer-Encoding and Content-Length"
    case M.UnsupportedEncoding{}:
      "unsupported Transfer-Encoding"
    case M.BadChunk{}:
      "malformed chunked body"
    case M.UnexpectedUpgrade{}:
      "unexpected 101 Switching Protocols"
    case M.Incomplete{}:
      "the connection closed before the response ended"
    case M.TooLarge{}:
      "the response is larger than the limit"

def coded(what: String, code: U32, message: String) -> String:
  what ++ " error " ++ U32.show(code) ++ ": " ++ message

# One line saying why a request failed.
def error_show(e: M.Error) -> String:
  match e:
    case M.BadUrl{r}:
      "bad URL: " ++ r
    case M.BadRequest{r}:
      "bad request: " ++ r
    case M.NoAddress{h}:
      "no IPv4 address for " ++ h
    case M.Dns{c, m}:
      coded("DNS", c, m)
    case M.Connect{c, m}:
      coded("connect", c, m)
    case M.Io{c, m}:
      coded("I/O", c, m)
    case M.Timeout{}:
      "timed out"
    case M.Tls{c, m}:
      coded("TLS", c, m)
    case M.Parse{p}:
      "bad response: " ++ parse_error_show(p)

# Resolving a host
# ----------------

def looked_up(r: Result<&1, &1, U32 & String, List<&2, String>>) -> Result<&2, &2, M.Error, List<&2, String>>:
  match r:
    case Fail{(code, message)}:
      Fail{M.Dns{code, message}}
    case Done{ips}:
      Done{ips}

# The host's IPv4 addresses from the OS resolver (Dns.lookup).
def lookup(host: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  IO.bind(Result<&1, &1, U32 & String, List<&2, String>>, Result<&2, &2, M.Error, List<&2, String>>,
    Dns.Dns.lookup(host), r => IO.pure(Result<&2, &2, M.Error, List<&2, String>>, looked_up(r)))

def first_address(host: String, r: Result<&2, &2, M.Error, List<&2, String>>) -> Result<&2, &2, M.Error, String>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{ips}:
      match ips:
        case Nil{}:
          Fail{M.NoAddress{host}}
        case Con{ip, rest}:
          Done{ip}

# The lookup's answer, or Timeout when the deadline passed first.
def timed_out(r: Maybe<&1, Result<&2, &2, M.Error, List<&2, String>>>) -> Result<&2, &2, M.Error, List<&2, String>>:
  match r:
    case None{}:
      Fail{M.Timeout{}}
    case Some{x}:
      x

# The first address of `host` from Dns.lookup, within `ms` (0: no limit).
# As with every timeout over Base (see transport.bend's `within`), a lookup
# past its deadline is not cancelled: on the C lane getaddrinfo keeps its
# helper thread until the resolver gives up, and the program cannot end
# normally before that; on the JS lane getaddrinfo blocks the event loop, so
# the deadline cannot interrupt it (bendlang/bend#1148).
def lookup_within(+host: String, ms: Nat) -> IO(Result<&2, &2, M.Error, String>):
  IO.bind(Maybe<&1, Result<&2, &2, M.Error, List<&2, String>>>, Result<&2, &2, M.Error, String>,
    X.within(Result<&2, &2, M.Error, List<&2, String>>, ms, lookup(host)),
    r => IO.pure(Result<&2, &2, M.Error, String>, first_address(host, timed_out(r))))

# A hosts-table entry: used only when it is a dotted-quad IPv4 address.
def resolve.entry(ok: Bool, ip: String, host: String) -> IO(Result<&2, &2, M.Error, String>):
  match ok:
    case True{}:
      IO.pure(Result<&2, &2, M.Error, String>, Done{ip})
    case False{}:
      IO.pure(Result<&2, &2, M.Error, String>,
        Fail{M.BadRequest{"hosts entry for " ++ host ++ " is not an IPv4 address: " ++ ip}})

def resolve.table(found: Maybe<&2, String>, +host: String, ms: Nat) -> IO(Result<&2, &2, M.Error, String>):
  match found:
    case Some{+ip}:
      resolve.entry(U.is_ipv4(ip), ip, host)
    case None{}:
      lookup_within(host, ms)

def resolve.numeric(num: Bool, +host: String, hosts: List<&2, M.Header>, ms: Nat) ->
  IO(Result<&2, &2, M.Error, String>):
  match num:
    case True{}:
      IO.pure(Result<&2, &2, M.Error, String>, Fail{M.BadUrl{"ambiguous IPv4 address"}})
    case False{}:
      resolve.table(H.get(host, hosts), host, ms)

def resolve.literal(literal: Bool, +host: String, hosts: List<&2, M.Header>, ms: Nat) ->
  IO(Result<&2, &2, M.Error, String>):
  match literal:
    case True{}:
      IO.pure(Result<&2, &2, M.Error, String>, Done{host})
    case False{}:
      resolve.numeric(U.ends_in_number(H.lower(host)), host, hosts, ms)

# The IPv4 address to connect to for `host`:
# - a dotted-quad IPv4 literal (U.is_ipv4) is itself;
# - any other host whose last label is a number ("127.1", "2130706433",
#   "0x7f.1", "010.0.0.1": forms the OS resolver would read as an address
#   the text does not spell) fails with BadUrl "ambiguous IPv4 address",
#   before the hosts table or any lookup (U.parse refuses these hosts too);
# - else the config's hosts table (case-insensitive; an entry that is not a
#   dotted quad fails with BadRequest);
# - else the first address Dns.lookup gives (NoAddress if it gives none),
#   within the config's timeout_ms (Timeout).
def resolve(cfg: Config, +host: String) -> IO(Result<&2, &2, M.Error, String>):
  match cfg:
    case Config{hosts, t, m}:
      resolve.literal(U.is_ipv4(host), host, hosts, t)

# Sending
# -------

def kept(r: Result<&2, &2, M.Error, M.Decoded>) -> Result<&2, &2, M.Error, M.Response>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{d}:
      match d:
        case M.Decoded{resp, rest}:
          Done{resp}

def wire(s: M.Scheme, host: String, ip: String, port: Nat, bytes: List<&2, U32>, m: M.Method, max: Nat,
  ms: Nat) -> IO(Result<&2, &2, M.Error, M.Decoded>):
  match s:
    case M.Http{}:
      X.plain(ip, port, bytes, m, max, ms)
    case M.Https{}:
      X.tls(host, ip, port, bytes, m, max, ms)

def resolved(r: Result<&2, &2, M.Error, String>, s: M.Scheme, host: String, port: Nat, bytes: List<&2, U32>,
  m: M.Method, max: Nat, ms: Nat) -> IO(Result<&2, &2, M.Error, M.Response>):
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, M.Error, M.Response>, Fail{e})
    case Done{ip}:
      IO.bind(Result<&2, &2, M.Error, M.Decoded>, Result<&2, &2, M.Error, M.Response>,
        wire(s, host, ip, port, bytes, m, max, ms),
        d => IO.pure(Result<&2, &2, M.Error, M.Response>, kept(d)))

def encoded(r: Result<&2, &2, M.Error, List<&2, U32>>, cfg: Config, req: M.Request) ->
  IO(Result<&2, &2, M.Error, M.Response>):
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, M.Error, M.Response>, Fail{e})
    case Done{bytes}:
      match cfg req:
        case Config{hosts, +ms, +max} M.Request{m, u, hs, body}:
          match u:
            case M.Url{s, +h, p, t}:
              IO.bind(Result<&2, &2, M.Error, String>, Result<&2, &2, M.Error, M.Response>,
                resolve(Config{hosts, ms, max}, h),
                ip => resolved(ip, s, h, p, bytes, m, max, ms))

# One exchange: encode the request (refusing an invalid one with
# BadRequest), resolve the host, then plain HTTP or HTTPS by the URL's
# scheme; the response, without whatever bytes followed it.
def send(cfg: Config, +req: M.Request) -> IO(Result<&2, &2, M.Error, M.Response>):
  encoded(E.request(req), cfg, req)

def fetched(cfg: Config, r: Result<&2, &2, M.Error, M.Url>) -> IO(Result<&2, &2, M.Error, M.Response>):
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, M.Error, M.Response>, Fail{e})
    case Done{u}:
      send(cfg, M.Request{M.GET{}, u, Nil{}, Nil{}})

# GET url with no headers and no body.
def fetch(cfg: Config, url: String) -> IO(Result<&2, &2, M.Error, M.Response>):
  fetched(cfg, U.parse(url))

# Redirects
# ---------

def is_redirect(+st: Nat) -> Bool:
  Nat.is_eq(st, 301n) || Nat.is_eq(st, 302n) || Nat.is_eq(st, 303n) || Nat.is_eq(st, 307n)
    || Nat.is_eq(st, 308n)

def is_post(m: M.Method) -> Bool:
  match m:
    case M.POST{}:
      True{}
    case _:
      False{}

def is_head(m: M.Method) -> Bool:
  match m:
    case M.HEAD{}:
      True{}
    case _:
      False{}

# Whether the next request is a GET with no body: a 303 (except for HEAD,
# which stays HEAD), and a 301 or 302 answering a POST (what every browser
# does). Every other redirect keeps the method and the body.
def becomes_get(+m: M.Method, +st: Nat) -> Bool:
  (Nat.is_eq(st, 303n) && Bool.not(is_head(m)))
    || ((Nat.is_eq(st, 301n) || Nat.is_eq(st, 302n)) && is_post(m))

def without.pick(hit: Bool, h: M.Header, rest: List<&2, M.Header>) -> List<&2, M.Header>:
  match hit:
    case True{}:
      rest
    case False{}:
      h <> rest

# A loop (the JS lane's stack would overflow on a recursion as deep as the
# header list): the kept headers pile up reversed in acc, then one reverse.
# Equation for a proof: without.go(name, hs, acc) ==
# List.append(List.reverse(acc), spec(name, hs)), where spec is the plain
# recursion `spec(name, h <> t) = without.pick(H.name_eq(name, n), h,
# spec(name, t))` (induction on hs, acc generalized).
def without.go(+name: String, hs: List<&2, M.Header>, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match hs:
    case Nil{}:
      List.reverse(&2, M.Header, acc)
    case Con{+h, t}:
      match h:
        case M.Header{n, v}:
          without.go(name, t, without.pick(H.name_eq(name, n), h, acc))

# The headers less every one named `name` (case-insensitively), in order.
def without(+name: String, hs: List<&2, M.Header>) -> List<&2, M.Header>:
  without.go(name, hs, Nil{})

def same_scheme(a: M.Scheme, b: M.Scheme) -> Bool:
  match a b:
    case M.Http{} M.Http{}:
      True{}
    case M.Https{} M.Https{}:
      True{}
    case _ _:
      False{}

def same_origin(a: M.Url, b: M.Url) -> Bool:
  match a b:
    case M.Url{s1, h1, p1, t1} M.Url{s2, h2, p2, t2}:
      same_scheme(s1, s2) && String.eq(h1, h2) && Nat.is_eq(p1, p2)

# Credentials go to the origin they were meant for only: a redirect to
# another scheme, host or port drops Authorization, Proxy-Authorization and
# Cookie (as curl and browsers do).
def credentials.pick(same: Bool, hs: List<&2, M.Header>) -> List<&2, M.Header>:
  match same:
    case True{}:
      hs
    case False{}:
      without("cookie", without("proxy-authorization", without("authorization", hs)))

def next_request(get: Bool, m: M.Method, u: M.Url, hs: List<&2, M.Header>, body: List<&2, U32>) -> M.Request:
  match get:
    case True{}:
      M.Request{M.GET{}, u, without("content-type", hs), Nil{}}
    case False{}:
      M.Request{m, u, hs, body}

# How a Location reads: "//host/..." (scheme-relative), "/path" (same
# origin), or anything else (it must then be an absolute http(s) URL).
type Ref is Data:
  RefAbsolute{}
  RefPath{}
  RefNet{}

def is_slash(k: B.Class) -> Bool:
  match k:
    case B.Slash{}:
      True{}
    case _:
      False{}

def ref_second.pick(slash: Bool) -> Ref:
  match slash:
    case True{}:
      RefNet{}
    case False{}:
      RefPath{}

def ref_second(s: String) -> Ref:
  match s:
    case SNil{}:
      RefPath{}
    case SCon{c, t}:
      ref_second.pick(is_slash(B.char_class(c)))

def ref_first(slash: Bool, t: String) -> Ref:
  match slash:
    case True{}:
      ref_second(t)
    case False{}:
      RefAbsolute{}

def ref_kind(s: String) -> Ref:
  match s:
    case SNil{}:
      RefAbsolute{}
    case SCon{c, t}:
      ref_first(is_slash(B.char_class(c)), t)

def parsed(r: Result<&2, &2, M.Error, M.Url>) -> Maybe<&2, M.Url>:
  match r:
    case Fail{e}:
      None{}
    case Done{u}:
      Some{u}

# The URL a Location names, read against the request's URL. Everything
# goes through U.parse, so the result is a valid URL (fragment dropped).
def target_url(k: Ref, base: M.Url, loc: String) -> Maybe<&2, M.Url>:
  match k base:
    case RefAbsolute{} _:
      parsed(U.parse(loc))
    case RefPath{} M.Url{s, h, p, t}:
      parsed(U.parse(U.show(M.Url{s, h, p, ""}) ++ loc))
    case RefNet{} M.Url{s, h, p, t}:
      parsed(U.parse(U.scheme_text(s) ++ ":" ++ loc))

def redirect.to(next: Maybe<&2, M.Url>, req: M.Request, +st: Nat) -> Maybe<&2, M.Request>:
  match next req:
    case None{} _:
      None{}
    case Some{+u2} M.Request{+m, u, hs, body}:
      +hs2 = credentials.pick(same_origin(u, u2), hs)
      Some{next_request(becomes_get(m, st), m, u2, hs2, body)}

def redirect.loc(loc: Maybe<&2, String>, +req: M.Request, +st: Nat) -> Maybe<&2, M.Request>:
  match loc:
    case None{}:
      None{}
    case Some{+l}:
      match req:
        case M.Request{m, u, hs, body}:
          redirect.to(target_url(ref_kind(l), u, l), req, st)

def redirect.when(hit: Bool, +req: M.Request, +st: Nat, hs: List<&2, M.Header>) -> Maybe<&2, M.Request>:
  match hit:
    case True{}:
      redirect.loc(H.get("location", hs), req, st)
    case False{}:
      None{}

# The request a redirect asks for: a 301/302/303/307/308 with a Location
# that is an absolute http(s) URL, an absolute path (same origin) or a
# scheme-relative "//host/path". A 303 (except to HEAD), and a 301/302
# answering a POST, become a GET with no body and no Content-Type; the others
# keep the method and the body. Leaving the origin drops credentials (see
# credentials.pick). None for any other response or an unusable Location.
def redirect(+req: M.Request, resp: M.Response) -> Maybe<&2, M.Request>:
  match resp:
    case M.Response{v, +st, re, hs, body}:
      redirect.when(is_redirect(st), req, st, hs)
