import Base
import ./bytes.bend as B
import ./message.bend as M

# A reader for what encode.bend emits. It exists only so that the law
#   request_roundtrip: E.request_ok(r) ->
#     decode_request(E.request_bytes(r))
#       == Some{ParsedRequest{E.method_name(m), target, E.request_headers(r), body}}
# can be stated; main.bend never imports it.
#
# Two phases, each plain structural recursion:
#   1. head_lines splits the bytes into the head's lines (each ended by
#      CRLF; one char per byte, Latin-1) and the body, every byte after the
#      blank line.
#   2. The first line is the request line, split at SP twice
#      (method, target, "HTTP/1.1"); every other line is a field line,
#      split at its first ':' followed by one SP (name, value).

type ParsedRequest is Data:
  ParsedRequest{method: String, target: String, headers: List<&2, M.Header>, body: List<&2, U32>}

# Phase 1: lines
# --------------

# The head's lines in order, and the bytes after the blank line.
type Lines is Data:
  Lines{lines: List<&2, String>, body: List<&2, U32>}

# Where head_lines is.
type Mode is Data:
  Start{}                   # at the start of a line
  Mid{}                     # inside a line (after at least one char)
  Cr{}                      # after a line's CR: an LF must follow
  Blank{}                   # after a CR that began a line: an LF ends the head
  Body{}                    # the head has ended: the rest is the body
  Bad{}                     # not a head: no answer

# The mode after a byte of class k in mode m.
def next(m: Mode, k: B.Class) -> Mode:
  match m k:
    case Start{} B.Cr{}:
      Blank{}
    case Start{} _:
      Mid{}
    case Mid{} B.Cr{}:
      Cr{}
    case Mid{} _:
      Mid{}
    case Cr{} B.Lf{}:
      Start{}
    case Cr{} _:
      Bad{}
    case Blank{} B.Lf{}:
      Body{}
    case Blank{} _:
      Bad{}
    case Body{} _:
      Body{}
    case Bad{} _:
      Bad{}

# Prepends the char of byte h to the first line.
def cons_line(h: U32, r: Maybe<&2, Lines>) -> Maybe<&2, Lines>:
  match r:
    case Some{Lines{Con{l, ls}, body}}:
      Some{Lines{Con{SCon{Char.from_u32(h), l}, ls}, body}}
    case _:
      None{}

# Starts a new (empty) first line.
def new_line(r: Maybe<&2, Lines>) -> Maybe<&2, Lines>:
  match r:
    case Some{Lines{ls, body}}:
      Some{Lines{Con{SNil{}, ls}, body}}
    case None{}:
      None{}

# What a byte h of class k in mode m does to r, the answer for the bytes
# after it (read in mode next(m, k)).
def act(m: Mode, k: B.Class, h: U32, r: Maybe<&2, Lines>) -> Maybe<&2, Lines>:
  match m k:
    case Start{} B.Cr{}:
      r
    case Start{} _:
      cons_line(h, r)
    case Mid{} B.Cr{}:
      r
    case Mid{} _:
      cons_line(h, r)
    case Cr{} _:
      new_line(r)
    case _ _:
      r

# The lines of the head and the body after it. A line is every byte up to
# CRLF; a CR not followed by LF is refused; input that ends before the
# blank line is refused. Body and Bad answer at once, without reading on.
def head_lines.go(xs: List<&2, U32>, m: Mode) -> Maybe<&2, Lines>:
  match xs:
    case Nil{}:
      match m:
        case Body{}:
          Some{Lines{[], []}}
        case _:
          None{}
    case Con{+h, t}:
      match m:
        case Body{}:
          Some{Lines{[], h <> t}}
        case Bad{}:
          None{}
        case +m:
          +k = B.class(h)
          act(m, k, h, head_lines.go(t, next(m, k)))

def head_lines(xs: List<&2, U32>) -> Maybe<&2, Lines>:
  head_lines.go(xs, Start{})

# Phase 2: request line and field lines
# -------------------------------------

# A string cut at a stop char: the part before it and the part after it.
type Split is Data:
  Split{left: String, right: String}

def split.con(c: Char, r: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match r:
    case Some{Split{l, rest}}:
      Some{Split{SCon{c, l}, rest}}
    case None{}:
      None{}

def split_sp.pick(k: B.Class, c: Char, t: String, r: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match k:
    case B.Sp{}:
      Some{Split{SNil{}, t}}
    case _:
      split.con(c, r)

# Cut at the first SP; None if there is none.
def split_sp(s: String) -> Maybe<&2, Split>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      split_sp.pick(B.char_class(c), c, t, split_sp(t))

def split_colon.pick(k: B.Class, c: Char, t: String, r: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match k:
    case B.Colon{}:
      Some{Split{SNil{}, t}}
    case _:
      split.con(c, r)

# Cut at the first ':'; None if there is none.
def split_colon(s: String) -> Maybe<&2, Split>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      split_colon.pick(B.char_class(c), c, t, split_colon(t))

# The method and the target.
def request_line.version(ok: Bool, m: String, t: String) -> Maybe<&2, Split>:
  match ok:
    case True{}:
      Some{Split{m, t}}
    case False{}:
      None{}

def request_line.target(m: String, r: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match r:
    case Some{Split{t, v}}:
      request_line.version(String.eq(v, "HTTP/1.1"), m, t)
    case None{}:
      None{}

def request_line.method(r: Maybe<&2, Split>) -> Maybe<&2, Split>:
  match r:
    case Some{Split{m, rest}}:
      request_line.target(m, split_sp(rest))
    case None{}:
      None{}

# method SP target SP "HTTP/1.1": Split{method, target}.
def request_line(l: String) -> Maybe<&2, Split>:
  request_line.method(split_sp(l))

def field.sp(k: B.Class, n: String, v: String) -> Maybe<&2, M.Header>:
  match k:
    case B.Sp{}:
      Some{M.Header{n, v}}
    case _:
      None{}

def field.value(n: String, after: String) -> Maybe<&2, M.Header>:
  match after:
    case SCon{+c, v}:
      field.sp(B.char_class(c), n, v)
    case SNil{}:
      None{}

def field.name(r: Maybe<&2, Split>) -> Maybe<&2, M.Header>:
  match r:
    case Some{Split{n, after}}:
      field.value(n, after)
    case None{}:
      None{}

# name ":" SP value: the value is the rest of the line, as it is.
def field(l: String) -> Maybe<&2, M.Header>:
  field.name(split_colon(l))

def fields.con(h: Maybe<&2, M.Header>, r: Maybe<&2, List<&2, M.Header>>) -> Maybe<&2, List<&2, M.Header>>:
  match h r:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

# Every line a field line.
def fields(ls: List<&2, String>) -> Maybe<&2, List<&2, M.Header>>:
  match ls:
    case Nil{}:
      Some{[]}
    case Con{l, t}:
      fields.con(field(l), fields(t))

# The request
# -----------

def decode.build(
  rl: Maybe<&2, Split>, hs: Maybe<&2, List<&2, M.Header>>, body: List<&2, U32>
) -> Maybe<&2, ParsedRequest>:
  match rl hs:
    case Some{Split{m, t}} Some{h}:
      Some{ParsedRequest{m, t, h, body}}
    case _ _:
      None{}

def decode.lines(r: Maybe<&2, Lines>) -> Maybe<&2, ParsedRequest>:
  match r:
    case Some{Lines{Con{l, ls}, body}}:
      decode.build(request_line(l), fields(ls), body)
    case _:
      None{}

# The request line, the field lines, CRLF; the body is every byte after the
# blank line.
def decode_request(xs: List<&2, U32>) -> Maybe<&2, ParsedRequest>:
  decode.lines(head_lines(xs))
