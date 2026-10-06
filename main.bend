import Base
import ../dns/main.bend as DNS
import ./src/bytes.bend as B
import ./src/message.bend as M
import ./src/headers.bend as H
import ./src/utf8.bend as T
import ./src/url.bend as U
import ./src/encode.bend as E
import ./src/decode.bend as D
import ./src/client.bend as C

# An HTTP/1.1 and HTTPS client for Bend.
#
#   import <this package>/main.bend as P
#
#   def main() -> IO(Unit):
#     do IO<Unit>:
#       r : Result<&2, &2, P.Http.Error(), P.Http.Response()> <-
#         P.Http.fetch(P.Http.default_config(), "https://example.com/")
#       ...
#
# Every request opens a fresh connection and sends `Connection: close`; the
# response is buffered whole (up to a limit). HTTPS goes through OpenSSL 3,
# loaded at run time. Redirects are not followed: `Http.redirect` gives the
# next request and the caller decides. Names resolve through bender-dns
# (native IPv4 resolver), after an optional hosts table in the config.
#
# This file defines only `Http.*` wrappers over the modules in src/, plus the
# ErrorKind / ParseErrorKind tags for matching on errors (imports are not
# re-exported, so these are the whole public surface). The pure codec (URLs,
# headers, request encoding, response decoding) is specified by laws 1-18
# (docs/DESIGN.md), to be stated in LAWS.bend and proven in PROOF.bend; this
# file and the IO entry points rely on foreign code (TLS), so checking
# it reports those defs as unproven.
#
# Lanes: the native C lane (`bend f.bend -o f`) has no stack limit. The JS
# lane (`bend f.bend`) overflows its stack ("memory fault") on a recursion
# that is not a tail call once it is some 20-40 thousand calls deep. The
# library's request and response paths are loops for request bodies,
# header values and header counts, but caller code that builds a large body
# or string with non-tail recursion (Base's String.repeat, List.append and
# List.length among them) can still overflow there: build big values with
# tail-recursive loops, or use the C lane.

# Types
# -----
# Aliases for the types a caller writes in annotations, e.g.
# `Result<&2, &2, P.Http.Error(), P.Http.Response()>`. All are Data.

def Http.Bytes() -> Data:
  B.Bytes()

def Http.Method() -> Data:
  M.Method

def Http.Url() -> Data:
  M.Url

def Http.Header() -> Data:
  M.Header

def Http.Request() -> Data:
  M.Request

def Http.Response() -> Data:
  M.Response

def Http.Decoded() -> Data:
  M.Decoded

def Http.ParseError() -> Data:
  M.ParseError

def Http.Error() -> Data:
  M.Error

def Http.Config() -> Data:
  C.Config

# Methods
# -------
# The standard methods, and `Http.method(name)` for any other (it must be a
# token, or the request is refused).

def Http.GET() -> M.Method:
  M.GET{}

def Http.HEAD() -> M.Method:
  M.HEAD{}

def Http.POST() -> M.Method:
  M.POST{}

def Http.PUT() -> M.Method:
  M.PUT{}

def Http.DELETE() -> M.Method:
  M.DELETE{}

def Http.PATCH() -> M.Method:
  M.PATCH{}

def Http.OPTIONS() -> M.Method:
  M.OPTIONS{}

# "GET" is GET{}, ..., any other name is that name (case-sensitive).
def Http.method(name: String) -> M.Method:
  C.method_of(name)

def Http.method_name(m: M.Method) -> String:
  E.method_name(m)

# URLs
# ----
# `scheme://host[:port][target]`, http or https only; the host lowercased,
# the port filled in (80 / 443) when absent, the target "/" when absent, a
# fragment dropped. Userinfo and IPv6 literals are refused.

def Http.Url.parse(s: String) -> Result<&2, &2, M.Error, M.Url>:
  U.parse(s)

def Http.Url.show(u: M.Url) -> String:
  U.show(u)

# The URL is one this library can send to (valid host, port 1..65535, target).
def Http.Url.ok(u: M.Url) -> Bool:
  U.ok(u)

def Http.Url.is_https(u: M.Url) -> Bool:
  match u:
    case M.Url{s, h, p, t}:
      match s:
        case M.Https{}:
          True{}
        case M.Http{}:
          False{}

def Http.Url.host(u: M.Url) -> String:
  match u:
    case M.Url{s, h, p, t}:
      h

def Http.Url.port(u: M.Url) -> Nat:
  match u:
    case M.Url{s, h, p, t}:
      p

# The path and query ("/" at least).
def Http.Url.target(u: M.Url) -> String:
  match u:
    case M.Url{s, h, p, t}:
      t

# Headers
# -------
# Names keep their case; every lookup ignores it. A request may not set
# Host, Content-Length, Transfer-Encoding or Connection: the client does.
# Names must be tokens. Values may hold only printable ASCII, space and tab,
# with no space or tab at either end (values are not trimmed). Otherwise the
# request fails with BadRequest when it is encoded or sent; Http.header
# itself does not check. Header values in a response may also hold bytes
# 128-255, read as Latin-1 chars.

def Http.header(name: String, value: String) -> M.Header:
  M.Header{name, value}

def Http.Header.name(h: M.Header) -> String:
  match h:
    case M.Header{n, v}:
      n

def Http.Header.value(h: M.Header) -> String:
  match h:
    case M.Header{n, v}:
      v

# The first value of the header `name`, if any.
def Http.get_header(name: String, hs: List<&2, M.Header>) -> Maybe<&2, String>:
  H.get(name, hs)

# Every value of the header `name`, in order.
def Http.get_headers(name: String, hs: List<&2, M.Header>) -> List<&2, String>:
  H.get_all(name, hs)

def Http.has_header(name: String, hs: List<&2, M.Header>) -> Bool:
  H.has(name, hs)

# Requests
# --------

# A request to a parsed URL.
def Http.request_to(method: M.Method, url: M.Url, headers: List<&2, M.Header>, body: List<&2, U32>) ->
  M.Request:
  M.Request{method, url, headers, body}

def Http.request.of(method: M.Method, headers: List<&2, M.Header>, body: List<&2, U32>,
  u: Result<&2, &2, M.Error, M.Url>) -> Result<&2, &2, M.Error, M.Request>:
  match u:
    case Fail{e}:
      Fail{e}
    case Done{url}:
      Done{M.Request{method, url, headers, body}}

# A request to a URL given as text (BadUrl if it does not parse).
def Http.request(method: M.Method, url: String, headers: List<&2, M.Header>, body: List<&2, U32>) ->
  Result<&2, &2, M.Error, M.Request>:
  Http.request.of(method, headers, body, U.parse(url))

# GET url, no headers, no body.
def Http.get(url: String) -> Result<&2, &2, M.Error, M.Request>:
  Http.request(M.GET{}, url, Nil{}, Nil{})

def Http.Request.method(r: M.Request) -> M.Method:
  match r:
    case M.Request{m, u, hs, b}:
      m

def Http.Request.url(r: M.Request) -> M.Url:
  match r:
    case M.Request{m, u, hs, b}:
      u

def Http.Request.headers(r: M.Request) -> List<&2, M.Header>:
  match r:
    case M.Request{m, u, hs, b}:
      hs

def Http.Request.body(r: M.Request) -> List<&2, U32>:
  match r:
    case M.Request{m, u, hs, b}:
      b

# Text as UTF-8 bytes, for a body.
def Http.utf8(s: String) -> List<&2, U32>:
  T.encode(s)

# Responses
# ---------

def Http.status(r: M.Response) -> Nat:
  match r:
    case M.Response{v, st, re, hs, b}:
      st

def Http.reason(r: M.Response) -> String:
  match r:
    case M.Response{v, st, re, hs, b}:
      re

def Http.headers(r: M.Response) -> List<&2, M.Header>:
  match r:
    case M.Response{v, st, re, hs, b}:
      hs

def Http.body(r: M.Response) -> List<&2, U32>:
  match r:
    case M.Response{v, st, re, hs, b}:
      b

# True for HTTP/1.1, False for HTTP/1.0.
def Http.is_http11(r: M.Response) -> Bool:
  match r:
    case M.Response{v, st, re, hs, b}:
      match v:
        case M.Http11{}:
          True{}
        case M.Http10{}:
          False{}

# "HTTP/1.1 200 OK".
def Http.status_line(r: M.Response) -> String:
  C.status_line(r)

# The body as text, if it is well-formed UTF-8.
def Http.text(r: M.Response) -> Maybe<&2, String>:
  C.text(r)

# A 2xx status.
def Http.is_success(r: M.Response) -> Bool:
  C.is_success(r)

# The request a 301/302/303/307/308 asks for. Location may be an absolute
# http(s) URL, an absolute path ("/p") or "//host/path"; any other relative
# form ("x", "../x", "?q") gives None. A 303 (except to HEAD), and a 301/302
# answering a POST, become a GET with no body and no Content-Type; the
# others keep the method and the body. Going to another scheme, host or port
# drops Authorization, Proxy-Authorization and Cookie; every other header is
# kept (custom secret headers such as X-Api-Key too). None for any other
# response. A None for a 3xx means its Location could not be used (missing,
# relative like "x" or "../x", a non-http(s) scheme, userinfo, ...), so treat
# that response as final. Following it is the caller's choice (loop with a
# limit).
def Http.redirect(req: M.Request, resp: M.Response) -> Maybe<&2, M.Request>:
  C.redirect(req, resp)

# The pure codec
# --------------
# The exact bytes a request is sent as, and a response read from bytes, for
# callers with their own transport.

# The request's bytes, or BadRequest naming the first check that failed.
# (On the JS lane see "Lanes" above for building large bodies.)
def Http.encode(r: M.Request) -> Result<&2, &2, M.Error, List<&2, U32>>:
  E.request(r)

# A whole response (the bytes up to the close) to a request with `method`,
# reading at most `max` bytes of it.
def Http.decode(method: M.Method, max: Nat, xs: List<&2, U32>) -> Result<&2, &2, M.ParseError, M.Decoded>:
  D.response(method, max, xs)

def Http.Decoded.response(d: M.Decoded) -> M.Response:
  match d:
    case M.Decoded{r, rest}:
      r

# The bytes that followed the response.
def Http.Decoded.rest(d: M.Decoded) -> List<&2, U32>:
  match d:
    case M.Decoded{r, rest}:
      rest

# Errors
# ------
# An Http.Error's constructors live in src/message.bend, which a consumer of
# this file cannot name, so these tags say which error it is:
#
#   match P.Http.Error.kind(e):
#     case P.Timeout{}: ...   # retry?
#     case P.Tls{}: ...       # certificate or TLS failure
#     case _: ...
#
#   BadUrl      the URL did not parse (or its host is an ambiguous number)
#   BadRequest  the request is invalid (headers, method, a bad hosts entry)
#   NoAddress   the name resolved to no IPv4 address
#   Dns         the resolver failed (code: errno if available, otherwise 0)
#   Connect     the TCP connect failed (code: errno, e.g. 111 refused)
#   Io          a send or read failed (code: errno)
#   Timeout     a blocking step passed the config's timeout_ms
#   Tls         TLS failed (code: errno; 71 EPROTO is a certificate or name
#               that failed verification)
#   Parse       the response is malformed or too large (see parse_error)

type ErrorKind is Data:
  BadUrl{}
  BadRequest{}
  NoAddress{}
  Dns{}
  Connect{}
  Io{}
  Timeout{}
  Tls{}
  Parse{}

# The same for an Http.ParseError, one tag per way a response can be bad.
type ParseErrorKind is Data:
  BadStatusLine{}
  BadVersion{}
  BadHeader{}
  BadLength{}
  ConflictingFraming{}
  UnsupportedEncoding{}
  BadChunk{}
  UnexpectedUpgrade{}
  Incomplete{}
  TooLarge{}

def Http.ErrorKind() -> Data:
  ErrorKind

def Http.ParseErrorKind() -> Data:
  ParseErrorKind

# Which error this is.
def Http.Error.kind(e: M.Error) -> ErrorKind:
  match e:
    case M.BadUrl{r}:
      BadUrl{}
    case M.BadRequest{r}:
      BadRequest{}
    case M.NoAddress{h}:
      NoAddress{}
    case M.Dns{c, m}:
      Dns{}
    case M.Connect{c, m}:
      Connect{}
    case M.Io{c, m}:
      Io{}
    case M.Timeout{}:
      Timeout{}
    case M.Tls{c, m}:
      Tls{}
    case M.Parse{p}:
      Parse{}

# The resolver / OS / OpenSSL code of a Dns, Connect, Io or Tls error (errno
# values, Linux numbering on Linux), else None.
def Http.Error.code(e: M.Error) -> Maybe<&2, U32>:
  match e:
    case M.Dns{c, m}:
      Some{c}
    case M.Connect{c, m}:
      Some{c}
    case M.Io{c, m}:
      Some{c}
    case M.Tls{c, m}:
      Some{c}
    case _:
      None{}

# The ParseError inside a Parse error, else None.
def Http.Error.parse_error(e: M.Error) -> Maybe<&2, M.ParseError>:
  match e:
    case M.Parse{p}:
      Some{p}
    case _:
      None{}

# Which parse error this is.
def Http.ParseError.kind(e: M.ParseError) -> ParseErrorKind:
  match e:
    case M.BadStatusLine{}:
      BadStatusLine{}
    case M.BadVersion{}:
      BadVersion{}
    case M.BadHeader{}:
      BadHeader{}
    case M.BadLength{}:
      BadLength{}
    case M.ConflictingFraming{}:
      ConflictingFraming{}
    case M.UnsupportedEncoding{}:
      UnsupportedEncoding{}
    case M.BadChunk{}:
      BadChunk{}
    case M.UnexpectedUpgrade{}:
      UnexpectedUpgrade{}
    case M.Incomplete{}:
      Incomplete{}
    case M.TooLarge{}:
      TooLarge{}

# One line saying why a request failed.
def Http.Error.show(e: M.Error) -> String:
  C.error_show(e)

def Http.ParseError.show(e: M.ParseError) -> String:
  C.parse_error_show(e)

# Settings
# --------
# The default: no hosts entries, 30 s per blocking step (see with_timeout),
# 16 MiB per response.

def Http.default_config() -> C.Config:
  C.default_config()

# Resolve `name` (case-insensitively) to the IPv4 address `ip` without DNS.
# `ip` must be a dotted quad ("10.0.0.7"): any other value makes requests to
# `name` (and Http.resolve of it) fail with BadRequest.
def Http.with_host(cfg: C.Config, name: String, ip: String) -> C.Config:
  C.with_host(cfg, name, ip)

# Bounds each blocking step of an exchange to `ms` milliseconds: the name
# lookup, TCP connect, send, each read, and for HTTPS each step inside
# OpenSSL. 0: no limit. HTTPS timeouts cancel the step. The others cannot be
# cancelled (Base has no way to abort a blocked effect): the request answers
# Timeout at once, but over plain HTTP the stalled connect or read keeps its
# socket open, and a stalled DNS TCP step also keeps
# the program from ending normally until the peer acts or the OS gives up
# (an explicit exit such as IO.die still ends it at once). DNS deadlines
# work on both runtimes; resolver step timeouts remain independently active.
def Http.with_timeout(cfg: C.Config, ms: Nat) -> C.Config:
  C.with_timeout(cfg, ms)

# Use a bender-dns config (import ../dns/main.bend as D to construct it).
# DNS step timeouts, nameservers, port, hosts and search settings are retained;
# Http.with_timeout separately bounds the whole lookup. HTTP hosts overrides
# and IPv4 literals take precedence. The default loads system files lazily.
def Http.with_dns(cfg: C.Config, resolver: DNS.Dns.Config()) -> C.Config:
  C.with_dns(cfg, resolver)

# At most `n` bytes of response (status line, headers and body).
def Http.with_max_bytes(cfg: C.Config, n: Nat) -> C.Config:
  C.with_max_bytes(cfg, n)

# Sending
# -------

# One request, one response. The response is read until it is complete
# (bytes the server sends after it are not read), so a server that keeps the
# connection open, or resets it after the response, costs nothing. Over
# HTTPS a body that runs to the close must end with TLS close_notify, else
# the request fails with a Tls error (it may have been cut short).
def Http.send(cfg: C.Config, req: M.Request) -> IO(Result<&2, &2, M.Error, M.Response>):
  C.send(cfg, req)

# GET url.
def Http.fetch(cfg: C.Config, url: String) -> IO(Result<&2, &2, M.Error, M.Response>):
  C.fetch(cfg, url)

# Native DNS IPv4 lookup using /etc/resolv.conf and /etc/hosts, including
# search domains and CNAMEs. DNS step timeouts come from resolv.conf.
# Canonical dotted quads answer themselves; ambiguous numeric hosts,
# empty names and NULs fail with Dns code 22.
def Http.lookup(host: String) -> IO(Result<&2, &2, M.Error, List<&2, String>>):
  C.lookup(host)

# The address a request to `host` would use: an IPv4 literal, the config's
# hosts table, then DNS (within the config's timeout). A host whose last
# label is a number but is not a dotted quad ("127.1", "2130706433",
# "0x7f.1") fails with BadUrl.
def Http.resolve(cfg: C.Config, host: String) -> IO(Result<&2, &2, M.Error, String>):
  C.resolve(cfg, host)
