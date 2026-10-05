import Base
import ./bytes.bend as B
import ./message.bend as M
import ./num.bend as N
import ./headers.bend as H
import ./decode.bend as D

# The response encoder: what a server would send. It exists only so the
# decoder's laws can be stated (D.response(.., encode_response(r) ++ rest)
# == Done{Decoded{r, rest}}); main.bend never imports it.

# Heads
# -----

def version_text(v: M.Version) -> String:
  match v:
    case M.Http10{}:
      "HTTP/1.0"
    case M.Http11{}:
      "HTTP/1.1"

# `HTTP/1.x SP status SP reason`, the status line before its CRLF (appends
# nested to the right, so the decoder's prefix tests reduce on the literal
# parts).
def status_text(r: M.Response) -> String:
  match r:
    case M.Response{v, st, rs, hs, b}:
      version_text(v) ++ (" " ++ (N.show(st) ++ (" " ++ rs)))

# `HTTP/1.x SP status SP reason CRLF`. Written as the text, then CRLF, so a
# proof reads the line the decoder reads (the text) off the definition.
def status_line(r: M.Response) -> String:
  status_text(r) ++ "\r\n"

# `name ": " value`, the field line before its CRLF.
def field_text(h: M.Header) -> String:
  match h:
    case M.Header{n, v}:
      n ++ (": " ++ v)

# `name ": " value CRLF`.
def field_line(h: M.Header) -> String:
  field_text(h) ++ "\r\n"

# The field lines, as ASCII bytes.
def field_bytes(hs: List<&2, M.Header>) -> List<&2, U32>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      List.append(&2, U32, B.from_ascii(field_line(h)), field_bytes(t))

def response_status(r: M.Response) -> Nat:
  match r:
    case M.Response{v, st, rs, hs, b}:
      st

def response_reason(r: M.Response) -> String:
  match r:
    case M.Response{v, st, rs, hs, b}:
      rs

def response_headers(r: M.Response) -> List<&2, M.Header>:
  match r:
    case M.Response{v, st, rs, hs, b}:
      hs

def response_body(r: M.Response) -> List<&2, U32>:
  match r:
    case M.Response{v, st, rs, hs, b}:
      b

# Status line, field lines, CRLF.
def encode_head(+r: M.Response) -> List<&2, U32>:
  List.append(&2, U32, B.from_ascii(status_line(r)),
    List.append(&2, U32, field_bytes(response_headers(r)), [13, 10]))

# The head, then the body as it is.
def encode_response(+r: M.Response) -> List<&2, U32>:
  List.append(&2, U32, encode_head(r), response_body(r))

# Chunked bodies
# --------------

# One chunk: `hex(size) CRLF data CRLF`.
def chunk(+data: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, B.from_ascii(N.hex_show(List.length(&2, U32, data)) ++ "\r\n"),
    List.append(&2, U32, data, [13, 10]))

# Chunks of n bytes of xs (the last one shorter); fuel bounds the rounds
# (each takes at least one byte when n >= 1, so len(xs) rounds suffice).
def chunks(fuel: Nat, +n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match fuel xs:
    case 0n _:
      Nil{}
    case 1n+f Nil{}:
      Nil{}
    case 1n+f Con{+h, +t}:
      List.append(&2, U32, chunk(List.take(&2, U32, Con{h, t}, n)),
        chunks(f, n, List.drop(&2, U32, Con{h, t}, n)))

# The body as chunks of n bytes (the last one shorter), each
# `hex_show(size) CRLF data CRLF`, then the last chunk and the empty
# trailer section `0 CRLF CRLF`. Needs 1 <= n (n = 0 emits "0" chunks, the
# last-chunk marker) and a chunk size N.hex_read accepts: n <= N.LIMIT()
# (or the body no longer than N.LIMIT()).
def encode_chunked(n: Nat, +body: List<&2, U32>) -> List<&2, U32>:
  List.append(&2, U32, chunks(List.length(&2, U32, body), n, body), B.from_ascii("0\r\n\r\n"))

# Validity
# --------

# A reason phrase's chars: VCHAR, SP, HTAB.
def all_reason_char(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      B.Class.is_field_char(B.char_class(c)) && all_reason_char(t)

# An encoded line (its CRLF included) fits the decoder's line limit: at most
# D.LINE_MAX() bytes before the CRLF.
def line_fits(s: String) -> Bool:
  Nat.is_le(String.length(s), Nat.add(2n, D.LINE_MAX()))

def fields_fit(hs: List<&2, M.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      line_fits(field_line(h)) && fields_fit(t)

# The head fits the decoder's limits: the status line and every field line
# fit D.LINE_MAX(), and there are at most D.FIELDS_MAX() field lines.
def head_fits(+r: M.Response) -> Bool:
  line_fits(status_line(r)) && fields_fit(response_headers(r))
    && Nat.is_le(List.length(&2, M.Header, response_headers(r)), D.FIELDS_MAX())

# A head the decoder reads back as it is, whatever its status: reason chars
# VCHAR/SP/HTAB (leading OWS is fine: the decoder keeps everything after the
# SP that ends the code), valid header fields, within the decoder's limits.
# The hypothesis of laws 13 and 14 (with their status bounds).
def head_ok(+r: M.Response) -> Bool:
  all_reason_char(response_reason(r)) && H.headers_ok(response_headers(r)) && head_fits(r)

# A status that may carry a body and is final, written as the decoder tests
# it (status_value, framing.upgrade, framing.interim, no_body), so each fact
# a proof needs is one && elimination: 100..999, not 101, not 1xx, not 204,
# not 304. The accepted set is 200..999 less 204 and 304.
def body_status_ok(+st: Nat) -> Bool:
  Nat.is_le(100n, st) && Nat.is_le(st, 999n) && Bool.not(Nat.is_eq(st, 101n))
    && Bool.not(Nat.is_lt(st, 200n)) && Bool.not(Nat.is_eq(st, 204n))
    && Bool.not(Nat.is_eq(st, 304n))

# A final response with a body-carrying status and a head_ok head: the
# hypothesis of laws 10-12 and 15.
def response_ok(+r: M.Response) -> Bool:
  body_status_ok(response_status(r)) && head_ok(r)
