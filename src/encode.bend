import Base
import ./bytes.bend as B
import ./message.bend as M
import ./num.bend as N
import ./headers.bend as H
import ./url.bend as U

# Request validation and encoding: the bytes the client writes.
#
# Laws (to be stated in LAWS.bend; see docs/DESIGN.md) hold by construction:
#   encode_total        request() is a match on request_ok(r) giving
#                       Done{request_bytes(r)}.
#   encode_rejects_bad_headers
#                       request_ok tests H.headers_ok(r.headers) first, so a
#                       bad header list makes request_ok False by computation.
#   encode_bytes_in_range
#                       request_ok tests B.is_ascii(request_head(r)) and
#                       B.all_bytes(body); request_bytes is
#                       from_ascii(head) ++ body.
#   host_once           request_ok refuses any header whose name is
#                       H.name_eq to "host" (the same test H.count uses), and
#                       request_headers adds exactly one Host header.
#   no_body (13), redirects
#                       method_ok refuses Other{n} when n is one of the seven
#                       fixed names, so a valid request's method is HEAD on
#                       the wire exactly when it is M.HEAD{} (likewise GET,
#                       POST, ...): consumers may match on the constructor.
#
# NOTE (loops and specs): as in bytes.bend and headers.bend, every def here
# that walks a caller-sized list (the body, the header list, the head) is a
# loop (direct tail calls only), because the JS lane's stack overflows near
# 20-40k nested calls. The plain recursion each loop computes stays beside it
# as `<name>.spec`, for the law proofs only. The equations a proof needs
# (each by induction on the list with the accumulator generalized; every
# step is definitional except where noted):
#   none_reserved.go(hs, ok) == Bool.and(ok, none_reserved.spec(hs))
#       (plus the case split on ok for Bool.and associativity)
#   lines_onto(B.rev(M.Header, hs, acc), s)
#       == lines_onto(acc, String.append(header_lines.spec(hs), s))
#       (plus String.append associativity)
#   B.rev(A, B.rev(A, xs, acc), ys) == B.rev(A, acc, List.append(A, xs, ys))
#   B.from_ascii_onto(s, ys) == List.append(U32, B.from_ascii.spec(s), ys)
#       (bytes.bend's lemma)
# Corollaries (acc = True{} / Nil{}, s = "", with s ++ "" == s):
#   none_reserved == none_reserved.spec      header_lines == header_lines.spec
#   headers_of(m, u, hs, body)
#     == Host <> List.append(hs, List.append(length_header(m, body), [Connection]))
#   request_bytes(r) == List.append(B.from_ascii.spec(request_head(r)), body)
# A law about the public def rewrites with its corollary once.

# Methods
# -------

def method_name(m: M.Method) -> String:
  match m:
    case M.GET{}:
      "GET"
    case M.HEAD{}:
      "HEAD"
    case M.POST{}:
      "POST"
    case M.PUT{}:
      "PUT"
    case M.DELETE{}:
      "DELETE"
    case M.PATCH{}:
      "PATCH"
    case M.OPTIONS{}:
      "OPTIONS"
    case M.Other{n}:
      n

def method_of.pick(hit: Bool, m: M.Method, rest: M.Method) -> M.Method:
  match hit:
    case True{}:
      m
    case False{}:
      rest

# The method a name stands for (exact, as methods are case-sensitive):
# GET, HEAD, POST, PUT, DELETE, PATCH, OPTIONS, else Other{name}. The one
# list of fixed names: method_ok and the client both use it.
def method_of(+name: String) -> M.Method:
  method_of.pick(String.eq(name, "GET"), M.GET{},
  method_of.pick(String.eq(name, "HEAD"), M.HEAD{},
  method_of.pick(String.eq(name, "POST"), M.POST{},
  method_of.pick(String.eq(name, "PUT"), M.PUT{},
  method_of.pick(String.eq(name, "DELETE"), M.DELETE{},
  method_of.pick(String.eq(name, "PATCH"), M.PATCH{},
  method_of.pick(String.eq(name, "OPTIONS"), M.OPTIONS{},
  M.Other{name})))))))

def is_other(m: M.Method) -> Bool:
  match m:
    case M.Other{n}:
      True{}
    case _:
      False{}

# The fixed methods are tokens. Other's name must be a token and not one of
# the fixed names: Other{"HEAD"} would go out as HEAD while every consumer
# (the decoder's framing, the redirect rules) matches M.HEAD{}, so a method
# value is valid only in its canonical form.
def method_ok(m: M.Method) -> Bool:
  match m:
    case M.Other{+n}:
      Bool.and(H.is_token(n), is_other(method_of(n)))
    case _:
      True{}

# POST, PUT and PATCH always say how long their body is (even when empty).
def sends_body(m: M.Method) -> Bool:
  match m:
    case M.POST{}:
      True{}
    case M.PUT{}:
      True{}
    case M.PATCH{}:
      True{}
    case _:
      False{}

# A Content-Length header is sent when the body is nonempty or the method
# is POST, PUT or PATCH.
def wants_length(m: M.Method, body: List<&2, U32>) -> Bool:
  match body:
    case Nil{}:
      sends_body(m)
    case Con{h, t}:
      True{}

# Headers
# -------

# The number of cells in a list (a loop: long bodies do not grow the stack).
def length.go(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      length.go(t, 1n+n)

def length(xs: List<&2, U32>) -> Nat:
  length.go(xs, 0n)

def length_header.pick(want: Bool, body: List<&2, U32>) -> List<&2, M.Header>:
  match want:
    case True{}:
      [M.Header{"Content-Length", N.show(length(body))}]
    case False{}:
      []

# [Content-Length: n] when wants_length, else [].
def length_header(+m: M.Method, +body: List<&2, U32>) -> List<&2, M.Header>:
  length_header.pick(wants_length(m, body), body)

# [Content-Length] (when wants_length) ++ [Connection: close].
def tail_headers(+m: M.Method, +body: List<&2, U32>) -> List<&2, M.Header>:
  List.append(&2, M.Header, length_header(m, body), [M.Header{"Connection", "close"}])

# Host, then hs, then tail_headers. hs ++ tail is built as
# rev(rev(hs, []), tail), two loops (Base List.append nests one call per
# header); see the note at the top for the equation.
def headers_of(
  m: M.Method, u: M.Url, hs: List<&2, M.Header>, body: List<&2, U32>
) -> List<&2, M.Header>:
  M.Header{"Host", U.host_header(u)}
    <> B.rev(M.Header, B.rev(M.Header, hs, Nil{}), tail_headers(m, body))

# Exactly [Host] ++ r.headers ++ [Content-Length] (when wants_length) ++
# [Connection: close].
def request_headers(r: M.Request) -> List<&2, M.Header>:
  match r:
    case M.Request{m, u, hs, body}:
      headers_of(m, u, hs, body)

# Text
# ----

# name ": " value CRLF
def header_line(h: M.Header) -> String:
  match h:
    case M.Header{n, v}:
      n ++ (": " ++ (v ++ "\r\n"))

def header_lines.spec(hs: List<&2, M.Header>) -> String:
  match hs:
    case Nil{}:
      ""
    case Con{h, t}:
      header_line(h) ++ header_lines.spec(t)

# The lines of acc, which holds the headers in reverse, prepended to s.
def lines_onto(acc: List<&2, M.Header>, s: String) -> String:
  match acc:
    case Nil{}:
      s
    case Con{h, t}:
      lines_onto(t, header_line(h) ++ s)

# The field lines of hs, in order.
def header_lines(hs: List<&2, M.Header>) -> String:
  lines_onto(B.rev(M.Header, hs, Nil{}), "")

def target_of(u: M.Url) -> String:
  match u:
    case M.Url{s, h, p, t}:
      t

def head_of(
  +m: M.Method, +u: M.Url, hs: List<&2, M.Header>, body: List<&2, U32>
) -> String:
  method_name(m) ++ (" " ++ (target_of(u) ++ (" HTTP/1.1\r\n"
    ++ (header_lines(headers_of(m, u, hs, body)) ++ "\r\n"))))

# method SP target SP "HTTP/1.1" CRLF, the field lines of request_headers(r),
# CRLF.
def request_head(r: M.Request) -> String:
  match r:
    case M.Request{+m, +u, hs, body}:
      head_of(m, u, hs, body)

# The whole request: the head as ASCII bytes, then the body
# (B.from_ascii(head) ++ body, as two loops). Unchecked: call request() for
# a validated encoding.
def request_bytes(r: M.Request) -> List<&2, U32>:
  match r:
    case M.Request{+m, +u, hs, +body}:
      B.from_ascii_onto(head_of(m, u, hs, body), body)

# Validation
# ----------

# A header the client sets itself (Host, Content-Length, Transfer-Encoding,
# Connection, in any case). The same names as H.reserved, tested with
# H.name_eq(name, n) as H.get_all / H.count do.
def is_reserved(+n: String) -> Bool:
  Bool.or(H.name_eq("host", n), Bool.or(H.name_eq("content-length", n),
    Bool.or(H.name_eq("transfer-encoding", n), H.name_eq("connection", n))))

def none_reserved.spec(hs: List<&2, M.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      match h:
        case M.Header{n, v}:
          Bool.and(Bool.not(is_reserved(n)), none_reserved.spec(t))

def none_reserved.go(hs: List<&2, M.Header>, ok: Bool) -> Bool:
  match hs:
    case Nil{}:
      ok
    case Con{h, t}:
      match h:
        case M.Header{n, v}:
          none_reserved.go(t, Bool.and(ok, Bool.not(is_reserved(n))))

# No header is reserved.
def none_reserved(hs: List<&2, M.Header>) -> Bool:
  none_reserved.go(hs, True{})

def fields_ok(m: M.Method, u: M.Url, +hs: List<&2, M.Header>, body: List<&2, U32>) -> Bool:
  Bool.and(H.headers_ok(hs), Bool.and(none_reserved(hs),
    Bool.and(method_ok(m), Bool.and(U.ok(u), B.all_bytes(body)))))

# headers_ok, no reserved header, method_ok, U.ok(url), every body cell a
# byte; and the head is ASCII (implied by the others; stated so that the
# bytes law needs no reasoning about each part of the head).
def request_ok(r: M.Request) -> Bool:
  match r:
    case M.Request{+m, +u, +hs, +body}:
      Bool.and(fields_ok(m, u, hs, body), B.is_ascii(head_of(m, u, hs, body)))

# Why a request is refused (the first failing check).
def why.pick(
  hs_ok: Bool, none_res: Bool, m_ok: Bool, u_ok: Bool
) -> String:
  match hs_ok none_res m_ok u_ok:
    case False{} _ _ _:
      "invalid header name or value"
    case True{} False{} _ _:
      "reserved header (Host, Content-Length, Transfer-Encoding or Connection)"
    case True{} True{} False{} _:
      "invalid method name"
    case True{} True{} True{} False{}:
      "invalid URL"
    case True{} True{} True{} True{}:
      "body cell is not a byte"

def why(r: M.Request) -> String:
  match r:
    case M.Request{m, u, +hs, body}:
      why.pick(H.headers_ok(hs), none_reserved(hs), method_ok(m), U.ok(u))

def request.pick(ok: Bool, +r: M.Request) -> Result<&2, &2, M.Error, List<&2, U32>>:
  match ok:
    case True{}:
      Done{request_bytes(r)}
    case False{}:
      Fail{M.BadRequest{why(r)}}

# The bytes of a valid request; BadRequest otherwise.
def request(+r: M.Request) -> Result<&2, &2, M.Error, List<&2, U32>>:
  request.pick(request_ok(r), r)
