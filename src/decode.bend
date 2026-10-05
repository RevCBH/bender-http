import Base
import ./bytes.bend as B
import ./message.bend as M
import ./num.bend as N
import ./headers.bend as H

# The response decoder: a state machine fed one byte at a time.
#
#   step(s, b)   all the logic: one match on the phase, one place that
#                spends budget (spend), one small def per phase.
#   feed(s, xs)  plain structural recursion: feed(s, h <> t) = feed(step(s, h), t)
#                (through feed.go(xs, s), the list first for the termination
#                check), so feed(feed(s, a), b) == feed(s, a ++ b) by induction on a.
#   finish(s)    at end of input: the response, or why there is none.
#
# Lines (status line, field lines, chunk-size lines, trailer lines) are read
# by one generic phase, ReadLine{kind, acc, room}: the bytes so far, reversed,
# until CR LF. A bare LF, a CR not followed by LF, or a cell that is not a
# byte (past 255) fails the line. The finished line is turned into text once
# (B.latin1_onto, so obs-text survives as chars 128..255) and parsed by small
# helpers. What the line means is its LineKind.
#
# Limits on the head (besides the budget): a line holds at most LINE_MAX
# bytes before its CR LF (`room` counts down), and a head or a trailer
# section at most FIELDS_MAX field lines; past either the response fails
# with TooLarge. They bound the work one line or one header list can cost.
# S.head_ok includes both, so laws 10-14 keep their statements.
#
# Bodies are accumulated reversed and reversed once when the message
# completes. After a complete message every byte goes to the leftover
# (reversed in the phase, reversed back by finish), spending no budget.
#
# Budget: every byte a non-final phase consumes (status lines, field lines,
# chunk framing, body bytes, the bytes of skipped 1xx responses) spends one
# unit, in spend and nowhere else. A byte arriving with budget 0 fails with
# TooLarge. So a decoded body is never longer than the budget (size_bound).
#
# NOTE (loops and specs): as in bytes.bend and headers.bend, every helper
# that walks a line's text is a loop (direct tail calls only): the JS lane's
# stack holds only about 20-40k nested calls, and evaluation is strict, so a
# fold written `P(c) && f(t)` or `pick(test, .., f(t))` would walk (and nest
# over) the whole line. The structural recursion each loop computes stays
# beside it as `<name>.spec`, for the law proofs only. One lemma per pair, by
# induction on the string with the extra arguments generalized:
#   split.go(t, stops(stop, c), c, acc, stop)
#     == (String.reverse(acc) ++ fst(split.spec(stop, SCon{c, t})), snd(split.spec(stop, SCon{c, t})))
#   trim_left.go(t, is_ows_char(c), c) == trim_left.spec(SCon{c, t})
#   String.reverse(trim_left.spec(String.reverse(s))) == trim_right.spec(s)
#   all_text.go(s, ok) == Bool.and(ok, all_text.spec(s))
#   all_hex.go(s, ok) == Bool.and(ok, all_hex.spec(s))
#   items.go(s, cur, acc) == B.rev(String, acc, items.onto(String.reverse(cur), items.spec(s)))
# and so split == split.spec, trim_left == trim_left.spec, trim_right ==
# trim_right.spec, all_text == all_text.spec, all_hex == all_hex.spec, items
# == items.spec. A line read as the bytes xs has acc == rev(U32, xs, Nil{}),
# and line_text(rev(U32, xs, Nil{})) == B.to_latin1.spec(xs) is the
# latin1_onto lemma in bytes.bend at acc = Nil{}, s = SNil{} (with ++ SNil
# right identity; B.rev and rev here are the same definition).

# Limits
# ------

# The most bytes a line may hold before its CR LF.
def LINE_MAX() -> Nat:
  65536n

# The most field lines a head (each interim head counts on its own) or a
# trailer section may hold.
def FIELDS_MAX() -> Nat:
  1000n

# State
# -----

# The head being read: version, status, reason, the field lines so far
# (reversed: the newest first), and how many more field lines it may hold.
type Head is Data:
  Head{version: M.Version, status: Nat, reason: String, headers: List<&2, M.Header>, room: Nat}

# What the line being read is.
type LineKind is Data:
  KStatus{}                                                  # a status line
  KField{head: Head}                                         # a field line of the head (or its end)
  KSize{resp: M.Response, body: List<&2, U32>}               # a chunk-size line
  KTrailer{resp: M.Response, body: List<&2, U32>, room: Nat} # a trailer line (or the end); room as in Head

# The phase. A response in a body phase has its final head and an empty
# body field; the body so far is beside it, reversed.
type Phase is Data:
  ReadLine{kind: LineKind, acc: List<&2, U32>, room: Nat}       # reading a line; acc reversed; room bytes more allowed
  ReadCr{kind: LineKind, acc: List<&2, U32>}                    # the line saw CR; LF must follow
  LengthBody{resp: M.Response, body: List<&2, U32>, left: Nat}  # Content-Length body; left >= 1 to go
  CloseBody{resp: M.Response, body: List<&2, U32>}              # body delimited by the close
  ChunkData{resp: M.Response, body: List<&2, U32>, left: Nat}   # chunk data; left = 0: CR must follow
  ChunkLf{resp: M.Response, body: List<&2, U32>}                # chunk data and CR read; LF must follow
  Complete{resp: M.Response, rest: List<&2, U32>}               # done; rest = leftover, reversed
  Failed{error: M.ParseError}                                   # failed; every later byte is ignored

type State is Data:
  State{method: M.Method, budget: Nat, phase: Phase}

# A new line of this kind, nothing read yet.
def line(kind: LineKind) -> Phase:
  ReadLine{kind, Nil{}, LINE_MAX()}

# List and text helpers
# ---------------------

# xs reversed, prepended to acc (a loop).
def rev(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev(A, t, h <> acc)

# The bytes of a reversed line, as text in reading order (one char per
# byte): latin1_onto reads the reversed list and builds the text from its
# end, with no reverse. Every cell is a byte here (line_byte refused the rest).
def line_text(acc: List<&2, U32>) -> String:
  B.latin1_onto(acc, SNil{})

# NOTE (classifier use): the byte Class does not tell letters apart, nor
# "," from the other delimiters, so the literal "HTTP/1.0", "HTTP/1.1",
# "HTTP/" (strip) and "," (stops) are matched char by char with Char.is_eq
# against literals. Every other decision dispatches on B.class / B.char_class.

def strip.pick(ok: Bool, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok:
    case True{}:
      r
    case False{}:
      None{}

# s without the prefix p, if s starts with p. (Nests one call per char of p,
# a short literal.)
def strip(p: String, s: String) -> Maybe<&2, String>:
  match p s:
    case SNil{} t:
      Some{t}
    case SCon{a, pt} SCon{b, st}:
      strip.pick(Char.is_eq(a, b), strip(pt, st))
    case _ _:
      None{}

# Where a split stops.
type Stop is Data:
  AtSp{}
  AtColon{}
  AtSemi{}
  AtComma{}

def stop_class(stop: Stop, k: B.Class) -> Bool:
  match stop k:
    case AtSp{} B.Sp{}:
      True{}
    case AtColon{} B.Colon{}:
      True{}
    case AtSemi{} B.Semi{}:
      True{}
    case _ _:
      False{}

def stops(stop: Stop, +c: Char) -> Bool:
  match stop:
    case AtComma{}:
      Char.is_eq(c, ',')
    case _:
      stop_class(stop, B.char_class(c))

def split.pick(hit: Bool, c: Char, t: String, r: String & Maybe<&2, String>) ->
  String & Maybe<&2, String>:
  match hit:
    case True{}:
      (SNil{}, Some{t})
    case False{}:
      (a, rest) = r
      (SCon{c, a}, rest)

# The chars before the first stop char, and Some(the chars after it), or
# None when there is no stop char. (Spec of split.)
def split.spec(+stop: Stop, s: String) -> String & Maybe<&2, String>:
  match s:
    case SNil{}:
      (SNil{}, None{})
    case SCon{+c, +t}:
      split.pick(stops(stop, c), c, t, split.spec(stop, t))

# c is the char at hand and hit whether it stops the split; t the chars
# after it; acc the chars before it, reversed. Stops at the first hit.
def split.go(t: String, hit: Bool, c: Char, acc: String, +stop: Stop) ->
  String & Maybe<&2, String>:
  match t hit:
    case SNil{} True{}:
      (String.reverse(acc), Some{SNil{}})
    case SCon{x, y} True{}:
      (String.reverse(acc), Some{SCon{x, y}})
    case SNil{} False{}:
      (String.reverse(SCon{c, acc}), None{})
    case SCon{+x, y} False{}:
      split.go(y, stops(stop, x), x, SCon{c, acc}, stop)

# The chars before the first stop char, and Some(the chars after it), or
# None when there is no stop char.
def split(+stop: Stop, s: String) -> String & Maybe<&2, String>:
  match s:
    case SNil{}:
      (SNil{}, None{})
    case SCon{+c, t}:
      split.go(t, stops(stop, c), c, SNil{}, stop)

def is_ows_char(+c: Char) -> Bool:
  B.Class.is_ows(B.char_class(c))

def trim_left.pick(ows: Bool, s: String, r: String) -> String:
  match ows:
    case True{}:
      r
    case False{}:
      s

# s without its leading SP/HTAB. (Spec of trim_left.)
def trim_left.spec(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      trim_left.pick(is_ows_char(c), SCon{c, t}, trim_left.spec(t))

# c is the char at hand and ows whether it is SP/HTAB; t the chars after it.
def trim_left.go(t: String, ows: Bool, c: Char) -> String:
  match t ows:
    case SNil{} True{}:
      SNil{}
    case SCon{+x, y} True{}:
      trim_left.go(y, is_ows_char(x), x)
    case SNil{} False{}:
      SCon{c, SNil{}}
    case SCon{x, y} False{}:
      SCon{c, SCon{x, y}}

# s without its leading SP/HTAB.
def trim_left(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      trim_left.go(t, is_ows_char(c), c)

def trim_right.con(ows: Bool, c: Char, r: String) -> String:
  match ows r:
    case True{} SNil{}:
      SNil{}
    case _ _:
      SCon{c, r}

# s without its trailing SP/HTAB. (Spec of trim_right.)
def trim_right.spec(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      trim_right.con(is_ows_char(c), c, trim_right.spec(t))

# s without its trailing SP/HTAB: the leading ones of s reversed (all loops).
def trim_right(s: String) -> String:
  String.reverse(trim_left(String.reverse(s)))

# s without SP/HTAB at either end.
def trim(s: String) -> String:
  trim_right(trim_left(s))

# A char a reason phrase, a field value or a chunk extension may hold:
# VCHAR, SP, HTAB, or obs-text (0x80-0xFF). Not CR, LF, other controls, DEL.
def text_class(k: B.Class) -> Bool:
  match k:
    case B.High{}:
      True{}
    case _:
      B.Class.is_field_char(k)

def all_text.spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      text_class(B.char_class(c)) && all_text.spec(t)

def all_text.go(s: String, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{c, t}:
      all_text.go(t, ok && text_class(B.char_class(c)))

# Every char is a text char.
def all_text(s: String) -> Bool:
  all_text.go(s, True{})

def all_hex.spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Maybe.is_some(&2, Nat, N.hex_value(B.char_class(c))) && all_hex.spec(t)

def all_hex.go(s: String, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{c, t}:
      all_hex.go(t, ok && Maybe.is_some(&2, Nat, N.hex_value(B.char_class(c))))

# Every char is a hex digit.
def all_hex(s: String) -> Bool:
  all_hex.go(s, True{})

# Field lines
# -----------

def field.of(ok: Bool, name: String, value: String) -> Maybe<&2, M.Header>:
  match ok:
    case True{}:
      Some{M.Header{name, value}}
    case False{}:
      None{}

def field.cut(+name: String, after: Maybe<&2, String>) -> Maybe<&2, M.Header>:
  match after:
    case None{}:
      None{}
    case Some{rest}:
      +v = trim(rest)
      field.of(H.is_token(name) && all_text(v), name, v)

# `token ":" OWS value OWS`: the name is everything before the first ":"
# and must be a token (so a line starting with SP/HTAB, an obs-fold, fails);
# the value is the rest with SP/HTAB trimmed at both ends, field chars and
# obs-text only.
def field.parts(r: String & Maybe<&2, String>) -> Maybe<&2, M.Header>:
  (name, after) = r
  field.cut(name, after)

def parse_field(text: String) -> Maybe<&2, M.Header>:
  field.parts(split(AtColon{}, text))

# Content-Length
# --------------

# The agreement of the Content-Length values seen so far.
type Cl is Data:
  ClNone{}            # none yet
  ClSome{n: Nat}      # all equal to n
  ClBad{}             # one was not decimal, or two differed

def cl_add.eq(same: Bool, n: Nat) -> Cl:
  match same:
    case True{}:
      ClSome{n}
    case False{}:
      ClBad{}

def cl_add(acc: Cl, x: Maybe<&2, Nat>) -> Cl:
  match acc x:
    case ClNone{} Some{n}:
      ClSome{n}
    case ClSome{+a} Some{b}:
      cl_add.eq(Nat.is_eq(a, b), a)
    case _ _:
      ClBad{}

def items.first(c: Char, r: List<&2, String>) -> List<&2, String>:
  match r:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{x, xs}:
      SCon{c, x} <> xs

def items.pick(comma: Bool, c: Char, r: List<&2, String>) -> List<&2, String>:
  match comma:
    case True{}:
      SNil{} <> r
    case False{}:
      items.first(c, r)

# The elements of a comma list, untrimmed: always at least one. (Spec of items.)
def items.spec(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+c, t}:
      items.pick(stops(AtComma{}, c), c, items.spec(t))

# p prepended to the first element (for the lemma about items.go).
def items.onto(p: String, xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      [p]
    case Con{x, t}:
      (p ++ x) <> t

# The element being read (reversed) after char c.
def items.cur(comma: Bool, c: Char, cur: String) -> String:
  match comma:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, cur}

# The finished elements (reversed) after char c.
def items.done(comma: Bool, cur: String, acc: List<&2, String>) -> List<&2, String>:
  match comma:
    case True{}:
      String.reverse(cur) <> acc
    case False{}:
      acc

# cur: the element being read, reversed; acc: the finished ones, reversed.
def items.go(s: String, +cur: String, acc: List<&2, String>) -> List<&2, String>:
  match s:
    case SNil{}:
      rev(String, String.reverse(cur) <> acc, Nil{})
    case SCon{+c, t}:
      +k = stops(AtComma{}, c)
      items.go(t, items.cur(k, c, cur), items.done(k, cur, acc))

# The elements of a comma list, untrimmed: always at least one.
def items(s: String) -> List<&2, String>:
  items.go(s, SNil{}, Nil{})

# Folds the elements of one comma list: each must be OWS decimal OWS.
def cl_items(xs: List<&2, String>, acc: Cl) -> Cl:
  match xs:
    case Nil{}:
      acc
    case Con{x, t}:
      cl_items(t, cl_add(acc, N.read(trim(x))))

# Folds every Content-Length value.
def cl_values(vs: List<&2, String>, acc: Cl) -> Cl:
  match vs:
    case Nil{}:
      acc
    case Con{v, t}:
      cl_values(t, cl_items(items(v), acc))

def cl_result(c: Cl) -> Maybe<&2, Nat>:
  match c:
    case ClSome{n}:
      Some{n}
    case _:
      None{}

# The body length the Content-Length values vs give (see content_length).
def cl_of(vs: List<&2, String>) -> Maybe<&2, Nat>:
  cl_result(cl_values(vs, ClNone{}))

# The body length the Content-Length headers give: every element of every
# Content-Length value (each a comma list) is decimal and they are all equal.
# None when there is no Content-Length header, or the values are bad.
def content_length(hs: List<&2, M.Header>) -> Maybe<&2, Nat>:
  cl_of(H.get_all("content-length", hs))

# Framing (RFC 9112 6.3), decided when the head ends
# --------------------------------------------------

# The response with its body: body_rev reversed.
def with_body(r: M.Response, body_rev: List<&2, U32>) -> M.Response:
  match r:
    case M.Response{v, s, rs, hs, b}:
      M.Response{v, s, rs, hs, rev(U32, body_rev, Nil{})}

# A Content-Length body with `left` bytes to go: complete at 0.
def length_next(r: M.Response, body: List<&2, U32>, left: Nat) -> Phase:
  match left:
    case 0n:
      Complete{with_body(r, body), Nil{}}
    case 1n+p:
      LengthBody{r, body, 1n+p}

def cl.fits(ok: Bool, n: Nat, r: M.Response) -> Phase:
  match ok:
    case True{}:
      length_next(r, Nil{}, n)
    case False{}:
      Failed{M.TooLarge{}}

# Content-Length present: n bytes, if the values agree and n fits the budget.
def cl_framing(+k: Nat, cl: Maybe<&2, Nat>, r: M.Response) -> Phase:
  match cl:
    case None{}:
      Failed{M.BadLength{}}
    case Some{+n}:
      cl.fits(Nat.is_le(n, k), n, r)

# One Transfer-Encoding header whose value is "chunked" in any case (the
# value was trimmed of OWS when its line was parsed).
def chunked_only(vs: List<&2, String>) -> Bool:
  match vs:
    case Con{v, Nil{}}:
      String.eq(H.lower(v), "chunked")
    case _:
      False{}

def is_http10(v: M.Version) -> Bool:
  match v:
    case M.Http10{}:
      True{}
    case M.Http11{}:
      False{}

def nonempty(vs: List<&2, String>) -> Bool:
  match vs:
    case Nil{}:
      False{}
    case Con{x, t}:
      True{}

# Transfer-Encoding present: with any Content-Length a conflict; in an
# HTTP/1.0 response faulty (RFC 9112 6.1: a 1.0 message has no transfer
# codings); chunked alone; else unsupported.
def te_framing(conflict: Bool, http10: Bool, chunked: Bool, r: M.Response) -> Phase:
  match conflict http10 chunked:
    case True{} _ _:
      Failed{M.ConflictingFraming{}}
    case False{} True{} _:
      Failed{M.UnsupportedEncoding{}}
    case False{} False{} True{}:
      line(KSize{r, Nil{}})
    case False{} False{} False{}:
      Failed{M.UnsupportedEncoding{}}

def is_head(m: M.Method) -> Bool:
  match m:
    case M.HEAD{}:
      True{}
    case _:
      False{}

# A response that has no body whatever its headers say.
def no_body(m: M.Method, +st: Nat) -> Bool:
  is_head(m) || Nat.is_eq(st, 204n) || Nat.is_eq(st, 304n)

# 5./6.: Content-Length (cl: its values), else the body runs to the close.
def framing.cl(cl: List<&2, String>, +k: Nat, r: M.Response) -> Phase:
  match cl:
    case Nil{}:
      CloseBody{r, Nil{}}
    case Con{x, t}:
      cl_framing(k, cl_of(Con{x, t}), r)

# 4.: Transfer-Encoding (te: its values; cl: the Content-Length values).
def framing.te(v: M.Version, te: List<&2, String>, +cl: List<&2, String>, +k: Nat,
  r: M.Response) -> Phase:
  match te:
    case Nil{}:
      framing.cl(cl, k, r)
    case Con{x, t}:
      te_framing(nonempty(cl), is_http10(v), chunked_only(Con{x, t}), r)

# 3.: HEAD, 204, 304: no body; complete. Otherwise each framing header's
# values are looked up once.
def framing.empty(e: Bool, v: M.Version, +k: Nat, +hs: List<&2, M.Header>, r: M.Response) -> Phase:
  match e:
    case True{}:
      Complete{r, Nil{}}
    case False{}:
      framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, r)

# 1.: another 1xx (statuses are 100..999 here): interim; read the next
# status line. Its bytes were charged to the budget as they came.
def framing.interim(i: Bool, m: M.Method, v: M.Version, +k: Nat, +st: Nat,
  hs: List<&2, M.Header>, r: M.Response) -> Phase:
  match i:
    case True{}:
      line(KStatus{})
    case False{}:
      framing.empty(no_body(m, st), v, k, hs, r)

# 2.: 101 Switching Protocols, never asked for.
def framing.upgrade(u: Bool, m: M.Method, v: M.Version, +k: Nat, +st: Nat,
  hs: List<&2, M.Header>, r: M.Response) -> Phase:
  match u:
    case True{}:
      Failed{M.UnexpectedUpgrade{}}
    case False{}:
      framing.interim(Nat.is_lt(st, 200n), m, v, k, st, hs, r)

# The head has ended (an empty field line): decide how the body is framed.
# k is the budget left after the head's last byte.
def head_end(m: M.Method, +k: Nat, head: Head) -> Phase:
  match head:
    case Head{+v, +st, rs, hs, n}:
      +h = rev(M.Header, hs, Nil{})
      framing.upgrade(Nat.is_eq(st, 101n), m, v, k, st, h, M.Response{v, st, rs, h, Nil{}})

# Status line
# -----------

def status_value.pick(ok: Bool, n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

def status_value.of(r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match r:
    case Some{+n}:
      status_value.pick(Nat.is_le(100n, n) && Nat.is_le(n, 999n), n)
    case None{}:
      None{}

# A leading "0" is refused; else the decimal value, 100..999.
def status_value.lead(k: B.Class, t: String) -> Maybe<&2, Nat>:
  match k:
    case B.Digit{0n}:
      None{}
    case _:
      status_value.of(N.read(t))

# A status code: 3DIGIT, 100..999. A decimal with no leading zero in
# 100..999 is exactly a 3-digit one (N.show(n) for n >= 1 never starts with
# "0"), so: no leading "0", N.read, the range.
def status_value(t: String) -> Maybe<&2, Nat>:
  match t:
    case SNil{}:
      None{}
    case SCon{+c, u}:
      status_value.lead(B.char_class(c), SCon{c, u})

def reason_of.pick(ok: Bool, t: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Some{t}
    case False{}:
      None{}

# The reason phrase after the SP: text chars only; "" when there is no SP.
def reason_of(r: Maybe<&2, String>) -> Maybe<&2, String>:
  match r:
    case None{}:
      Some{SNil{}}
    case Some{+t}:
      reason_of.pick(all_text(t), t)

def status.head(v: M.Version, code: Maybe<&2, Nat>, reason: Maybe<&2, String>) -> Phase:
  match code reason:
    case Some{n} Some{rs}:
      line(KField{Head{v, n, rs, Nil{}, FIELDS_MAX()}})
    case _ _:
      Failed{M.BadStatusLine{}}

def status.parts(v: M.Version, r: String & Maybe<&2, String>) -> Phase:
  (code, reason) = r
  status.head(v, status_value(code), reason_of(reason))

def status.sp(sp: Bool, v: M.Version, t: String) -> Phase:
  match sp:
    case True{}:
      status.parts(v, split(AtSp{}, t))
    case False{}:
      Failed{M.BadStatusLine{}}

# After the version: SP, the code, then SP and the reason (or nothing).
def status.rest(v: M.Version, s: String) -> Phase:
  match s:
    case SNil{}:
      Failed{M.BadStatusLine{}}
    case SCon{c, t}:
      status.sp(stops(AtSp{}, c), v, t)

def status.version(r10: Maybe<&2, String>, r11: Maybe<&2, String>,
  any: Maybe<&2, String>) -> Phase:
  match r10 r11 any:
    case Some{s} _ _:
      status.rest(M.Http10{}, s)
    case None{} Some{s} _:
      status.rest(M.Http11{}, s)
    case None{} None{} Some{s}:
      Failed{M.BadVersion{}}
    case _ _ _:
      Failed{M.BadStatusLine{}}

# `"HTTP/1." ("0"|"1") SP 3DIGIT [SP reason]`. Another "HTTP/..." version is
# BadVersion; anything else BadStatusLine.
def status_line(+text: String) -> Phase:
  status.version(strip("HTTP/1.0", text), strip("HTTP/1.1", text), strip("HTTP/", text))

# Field lines and trailers
# ------------------------

# One more field line, if the head has room for it.
def field_room(v: M.Version, s: Nat, rs: String, hs: List<&2, M.Header>, room: Nat) -> Phase:
  match room:
    case 0n:
      Failed{M.TooLarge{}}
    case 1n+p:
      line(KField{Head{v, s, rs, hs, p}})

def field_add(head: Head, f: Maybe<&2, M.Header>) -> Phase:
  match head f:
    case Head{v, s, rs, hs, room} Some{h}:
      field_room(v, s, rs, h <> hs, room)
    case _ _:
      Failed{M.BadHeader{}}

# A finished line of the head: the empty line ends it.
def field_end(m: M.Method, +k: Nat, head: Head, text: String) -> Phase:
  match text:
    case SNil{}:
      head_end(m, k, head)
    case SCon{c, t}:
      field_add(head, parse_field(SCon{c, t}))

def trailer_room(r: M.Response, body: List<&2, U32>, room: Nat) -> Phase:
  match room:
    case 0n:
      Failed{M.TooLarge{}}
    case 1n+p:
      line(KTrailer{r, body, p})

def trailer_add(f: Maybe<&2, M.Header>, r: M.Response, body: List<&2, U32>, room: Nat) -> Phase:
  match f:
    case Some{h}:
      trailer_room(r, body, room)
    case None{}:
      Failed{M.BadHeader{}}

# A finished trailer line: parsed like a field line and discarded; the
# empty line ends the message.
def trailer_end(r: M.Response, body: List<&2, U32>, room: Nat, text: String) -> Phase:
  match text:
    case SNil{}:
      Complete{with_body(r, body), Nil{}}
    case SCon{c, t}:
      trailer_add(parse_field(SCon{c, t}), r, body, room)

# Chunk-size lines
# ----------------

def ext_ok(ext: Maybe<&2, String>) -> Bool:
  match ext:
    case None{}:
      True{}
    case Some{e}:
      all_text(e)

# A size that N.hex_read refused: past LIMIT if it is all hex digits.
def size_error(+digits: String) -> M.ParseError:
  Bool.pick(M.ParseError, Bool.not(String.is_empty(digits)) && all_hex(digits),
    M.TooLarge{}, M.BadChunk{})

def chunk.fits(ok: Bool, n: Nat, r: M.Response, body: List<&2, U32>) -> Phase:
  match ok:
    case True{}:
      ChunkData{r, body, n}
    case False{}:
      Failed{M.TooLarge{}}

def size.check(ok: Bool, digits: String, n: Maybe<&2, Nat>, +k: Nat, r: M.Response,
  body: List<&2, U32>) -> Phase:
  match ok n:
    case False{} _:
      Failed{M.BadChunk{}}
    case True{} None{}:
      Failed{size_error(digits)}
    case True{} Some{0n}:
      line(KTrailer{r, body, FIELDS_MAX()})
    case True{} Some{1n+(+p)}:
      chunk.fits(Nat.is_le(1n+p, k), 1n+p, r, body)

# `hexsize [OWS ";" ext]`: the size (N.hex_read) is everything before the
# first ";" less trailing OWS; the extension is text chars, ignored. Size 0
# starts the trailers; a size past the budget fails at once.
def size.parts(+k: Nat, r: M.Response, body: List<&2, U32>, p: String & Maybe<&2, String>) ->
  Phase:
  (before, ext) = p
  +digits = trim_right(before)
  size.check(ext_ok(ext), digits, N.hex_read(digits), k, r, body)

def size_end(+k: Nat, r: M.Response, body: List<&2, U32>, text: String) -> Phase:
  size.parts(k, r, body, split(AtSemi{}, text))

# Lines
# -----

def line_error(kind: LineKind) -> M.ParseError:
  match kind:
    case KStatus{}:
      M.BadStatusLine{}
    case KField{h}:
      M.BadHeader{}
    case KSize{r, b}:
      M.BadChunk{}
    case KTrailer{r, b, n}:
      M.BadHeader{}

# A line has ended (CR LF): what it means depends on its kind.
def line_end(m: M.Method, +k: Nat, kind: LineKind, text: String) -> Phase:
  match kind:
    case KStatus{}:
      status_line(text)
    case KField{head}:
      field_end(m, k, head, text)
    case KSize{r, body}:
      size_end(k, r, body, text)
    case KTrailer{r, body, room}:
      trailer_end(r, body, room, text)

# One more byte of a line, if the line has room for it.
def line_push(kind: LineKind, acc: List<&2, U32>, room: Nat, b: U32) -> Phase:
  match room:
    case 0n:
      Failed{M.TooLarge{}}
    case 1n+p:
      ReadLine{kind, b <> acc, p}

# A byte of a line: CR ends it (LF must follow); a bare LF, or a cell that
# is not a byte, fails; any other byte is kept while the line has room.
def line_byte(kind: LineKind, acc: List<&2, U32>, room: Nat, c: B.Class, b: U32) -> Phase:
  match c:
    case B.Cr{}:
      ReadCr{kind, acc}
    case B.Lf{}:
      Failed{line_error(kind)}
    case B.Invalid{}:
      Failed{line_error(kind)}
    case _:
      line_push(kind, acc, room, b)

# The byte after a line's CR: LF, else the line fails.
def line_cr(m: M.Method, +k: Nat, kind: LineKind, acc: List<&2, U32>, c: B.Class) -> Phase:
  match c:
    case B.Lf{}:
      line_end(m, k, kind, line_text(acc))
    case _:
      Failed{line_error(kind)}

# Bodies
# ------

# A byte of a Content-Length body (left is never 0 here).
def length_byte(r: M.Response, body: List<&2, U32>, left: Nat, b: U32) -> Phase:
  match left:
    case 0n:
      Failed{M.BadLength{}}
    case 1n+p:
      length_next(r, b <> body, p)

def chunk_cr(r: M.Response, body: List<&2, U32>, c: B.Class) -> Phase:
  match c:
    case B.Cr{}:
      ChunkLf{r, body}
    case _:
      Failed{M.BadChunk{}}

# A byte of chunk data, or the CR after it.
def chunk_byte(r: M.Response, body: List<&2, U32>, left: Nat, +b: U32) -> Phase:
  match left:
    case 0n:
      chunk_cr(r, body, B.class(b))
    case 1n+p:
      ChunkData{r, b <> body, p}

# The LF after a chunk's data: the next chunk-size line follows.
def chunk_lf(r: M.Response, body: List<&2, U32>, c: B.Class) -> Phase:
  match c:
    case B.Lf{}:
      line(KSize{r, body})
    case _:
      Failed{M.BadChunk{}}

# The machine
# -----------

# One byte in a consuming phase; k is the budget left after it.
def consume(m: M.Method, +k: Nat, p: Phase, +b: U32) -> Phase:
  match p:
    case ReadLine{kind, acc, room}:
      line_byte(kind, acc, room, B.class(b), b)
    case ReadCr{kind, acc}:
      line_cr(m, k, kind, acc, B.class(b))
    case LengthBody{r, body, left}:
      length_byte(r, body, left, b)
    case CloseBody{r, body}:
      CloseBody{r, b <> body}
    case ChunkData{r, body, left}:
      chunk_byte(r, body, left, b)
    case ChunkLf{r, body}:
      chunk_lf(r, body, B.class(b))
    case Complete{r, rest}:
      Complete{r, rest}
    case Failed{e}:
      Failed{e}

# The one place budget is spent: a byte arriving with budget 0 fails.
def spend(+m: M.Method, k: Nat, p: Phase, b: U32) -> State:
  match k:
    case 0n:
      State{m, 0n, Failed{M.TooLarge{}}}
    case 1n+(+j):
      State{m, j, consume(m, j, p, b)}

# One byte. After a complete message it is leftover (no budget spent); a
# failed state stays failed; any other phase consumes it.
def step(s: State, b: U32) -> State:
  match s:
    case State{m, k, p}:
      match p:
        case Complete{r, rest}:
          State{m, k, Complete{r, b <> rest}}
        case Failed{e}:
          State{m, k, Failed{e}}
        case _:
          spend(m, k, p, b)

# Before the first byte: expecting a status line, with max bytes of budget.
def init(method: M.Method, max: Nat) -> State:
  State{method, max, line(KStatus{})}

# Every byte of xs in order: feed.go(Nil, s) = s and
# feed.go(h <> t, s) = feed.go(t, step(s, h)). The list comes first because
# Bend's termination check reads arguments left to right and s changes.
def feed.go(xs: List<&2, U32>, s: State) -> State:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      feed.go(t, step(s, h))

# feed(s, xs) = feed.go(xs, s); so feed(s, []) = s and
# feed(s, h <> t) = feed(step(s, h), t).
def feed(s: State, xs: List<&2, U32>) -> State:
  feed.go(xs, s)

# The message is complete or has failed: the reader may stop.
def done(s: State) -> Bool:
  match s:
    case State{m, k, p}:
      match p:
        case Complete{r, rest}:
          True{}
        case Failed{e}:
          True{}
        case _:
          False{}

# The body runs to the close: only the end of input ends it (finish then
# completes it). A transport that can tell a clean close from a cut one
# (TLS close_notify) must refuse a cut one in this state (RFC 9112 9.8):
# the body may be truncated. In any other state the framing (or a failure)
# already decides.
def close_delimited(s: State) -> Bool:
  match s:
    case State{m, k, p}:
      match p:
        case CloseBody{r, body}:
          True{}
        case _:
          False{}

# At end of input: a complete message with its leftover; a close-delimited
# body completes here (leftover []); a failure gives its error; anything
# else ended mid-message.
def finish(s: State) -> Result<&2, &2, M.ParseError, M.Decoded>:
  match s:
    case State{m, k, p}:
      match p:
        case Complete{r, rest}:
          Done{M.Decoded{r, rev(U32, rest, Nil{})}}
        case CloseBody{r, body}:
          Done{M.Decoded{with_body(r, body), Nil{}}}
        case Failed{e}:
          Fail{e}
        case _:
          Fail{M.Incomplete{}}

# A whole response read from xs (the bytes up to the close).
def response(method: M.Method, max: Nat, xs: List<&2, U32>) ->
  Result<&2, &2, M.ParseError, M.Decoded>:
  finish(feed(init(method, max), xs))
