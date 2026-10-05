# Laws 9 (feed_split) and 16 (size_bound): the decoder as a fold of D.step.
#
# feed_split: induction on the first list (feed.go(h <> t, s) = feed.go(t, step(s, h))).
#
# size_bound: the measure of a state is budget + body_len(phase), where
# body_len is the length of the body the phase carries (LengthBody, CloseBody,
# ChunkData, ChunkLf, and ReadLine / ReadCr of a KSize or KTrailer line; the
# response body in Complete; 0 otherwise). One step never raises it (a byte
# that spends one unit of budget adds at most one body byte; head_end builds
# the response with an empty body), so neither does feed; init starts it at the
# budget m; and finish reports a body no longer than it (bodies are kept
# reversed, and D.rev keeps the length).
import Base
import ../LAWS.bend as Laws
import ../src/message.bend as M
import ../src/bytes.bend as B
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/spec.bend as S
import ../src/decode.bend as D

# Law 9
# -----

def feed_go_split(a: List<&2, U32>, -b: List<&2, U32>, -s: D.State)
  -> {D.feed.go(b, D.feed.go(a, s)) == D.feed.go(List.append(&2, U32, a, b), s) : D.State}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      feed_go_split(t, b, D.step(s, h))

def Laws.feed_split(s, a, b):
  feed_go_split(a, b, s)

# Nat order
# ---------

def LE(a: Nat, b: Nat) -> Type:
  {Nat.is_le(a, b) == True{} : Bool}

def size_bdisc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def size_false_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : size_bdisc(_)
  Unit{}

def le_zero(x: Nat) -> LE(0n, x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_refl(x: Nat) -> LE(x, x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

def le_succ(x: Nat) -> LE(x, 1n+x):
  match x:
    case 0n:
      {==}
    case 1n+p:
      le_succ(p)

def le_trans(a: Nat, b: Nat, c: Nat) -> LE(a, b) -> LE(b, c) -> LE(a, c):
  match a b c:
    case 0n _ _:
      e1 => e2 => le_zero(c)
    case 1n+ap 0n _:
      e1 => e2 => Empty.absurd(LE(1n+ap, c), size_false_true(e1))
    case 1n+ap 1n+bp 0n:
      e1 => e2 => Empty.absurd(LE(1n+ap, 0n), size_false_true(e2))
    case 1n+ap 1n+bp 1n+cp:
      e1 => e2 => le_trans(ap, bp, cp)(e1, e2)

def le_add_l(j: Nat, -a: Nat, -c: Nat) -> LE(a, c) -> LE(Nat.add(j, a), Nat.add(j, c)):
  match j:
    case 0n:
      e => e
    case 1n+p:
      e => le_add_l(p, a, c)(e)

# y <= k + y
def le_plus(+k: Nat, +y: Nat) -> LE(y, Nat.add(k, y)):
  match k:
    case 0n:
      le_refl(y)
    case 1n+p:
      le_trans(y, Nat.add(p, y), 1n+Nat.add(p, y))(le_plus(p, y), le_succ(Nat.add(p, y)))

def add_succ_r(j: Nat, -y: Nat) -> {Nat.add(j, 1n+y) == 1n+Nat.add(j, y) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %add_succ_r(p, y) : {1n+Nat.add(p, 1n+y) == 1n+_ : Nat}
      {==}

def add_zero_r(j: Nat) -> {Nat.add(j, 0n) == j : Nat}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

# D.rev keeps the length
# ----------------------

def len_rev(+xs: List<&2, U32>, -acc: List<&2, U32>)
  -> {Laws.len(D.rev(U32, xs, acc)) == Nat.add(Laws.len(xs), Laws.len(acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Nat, Laws.len(D.rev(U32, t, h <> acc)), Nat.add(Laws.len(t), 1n+Laws.len(acc)), len_rev(t, h <> acc)) :
        {_ == 1n+Nat.add(Laws.len(t), Laws.len(acc)) : Nat}
      add_succ_r(Laws.len(t), Laws.len(acc))

def len_rev_nil(+xs: List<&2, U32>) -> {Laws.len(xs) == Laws.len(D.rev(U32, xs, Nil{})) : Nat}:
  Equal.sym(Nat, Laws.len(D.rev(U32, xs, Nil{})), Laws.len(xs),
    Equal.trans(Nat, Laws.len(D.rev(U32, xs, Nil{})), Nat.add(Laws.len(xs), 0n), Laws.len(xs),
      len_rev(xs, Nil{}), add_zero_r(Laws.len(xs))))

# The measure
# -----------

def kind_len(k: D.LineKind) -> Nat:
  match k:
    case D.KStatus{}:
      0n
    case D.KField{h}:
      0n
    case D.KSize{r, b}:
      Laws.len(b)
    case D.KTrailer{r, b, n}:
      Laws.len(b)

def body_len(p: D.Phase) -> Nat:
  match p:
    case D.ReadLine{k, a, n}:
      kind_len(k)
    case D.ReadCr{k, a}:
      kind_len(k)
    case D.LengthBody{r, b, l}:
      Laws.len(b)
    case D.CloseBody{r, b}:
      Laws.len(b)
    case D.ChunkData{r, b, l}:
      Laws.len(b)
    case D.ChunkLf{r, b}:
      Laws.len(b)
    case D.Complete{r, rest}:
      Laws.len(S.response_body(r))
    case D.Failed{e}:
      0n

def measure(s: D.State) -> Nat:
  match s:
    case D.State{m, k, p}:
      Nat.add(k, body_len(p))

# The body length of a decoded response (0 for a failure).
def res_len(x: Laws.Res()) -> Nat:
  match x:
    case Done{d}:
      match d:
        case M.Decoded{r, rest}:
          Laws.len(S.response_body(r))
    case Fail{e}:
      0n

# with_body keeps the length of the reversed body.
def with_body_len(r: M.Response, +body: List<&2, U32>)
  -> {Laws.len(body) == Laws.len(S.response_body(D.with_body(r, body))) : Nat}:
  match r:
    case M.Response{v, st, rs, hs, b}:
      len_rev_nil(body)

# Status lines: the next phase carries no body
# --------------------------------------------

def status_head_le(v: M.Version, code: Maybe<&2, Nat>, reason: Maybe<&2, String>, -x: Nat)
  -> LE(body_len(D.status.head(v, code, reason)), 1n+x):
  match code reason:
    case Some{n} Some{rs}:
      {==}
    case Some{n} None{}:
      {==}
    case None{} Some{rs}:
      {==}
    case None{} None{}:
      {==}

def status_parts_le(v: M.Version, r: String & Maybe<&2, String>, -x: Nat)
  -> LE(body_len(D.status.parts(v, r)), 1n+x):
  match r:
    case (code, reason):
      status_head_le(v, D.status_value(code), D.reason_of(reason), x)

def status_sp_le(sp: Bool, v: M.Version, t: String, -x: Nat)
  -> LE(body_len(D.status.sp(sp, v, t)), 1n+x):
  match sp:
    case True{}:
      status_parts_le(v, D.split(D.AtSp{}, t), x)
    case False{}:
      {==}

def status_rest_le(v: M.Version, s: String, -x: Nat)
  -> LE(body_len(D.status.rest(v, s)), 1n+x):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      status_sp_le(D.stops(D.AtSp{}, c), v, t, x)

def status_version_le(r10: Maybe<&2, String>, r11: Maybe<&2, String>, any: Maybe<&2, String>, -x: Nat)
  -> LE(body_len(D.status.version(r10, r11, any)), 1n+x):
  match r10 r11 any:
    case Some{s} Some{s2} Some{s3}:
      status_rest_le(M.Http10{}, s, x)
    case Some{s} Some{s2} None{}:
      status_rest_le(M.Http10{}, s, x)
    case Some{s} None{} Some{s3}:
      status_rest_le(M.Http10{}, s, x)
    case Some{s} None{} None{}:
      status_rest_le(M.Http10{}, s, x)
    case None{} Some{s} Some{s3}:
      status_rest_le(M.Http11{}, s, x)
    case None{} Some{s} None{}:
      status_rest_le(M.Http11{}, s, x)
    case None{} None{} Some{s3}:
      {==}
    case None{} None{} None{}:
      {==}

def status_line_le(+text: String, -x: Nat) -> LE(body_len(D.status_line(text)), 1n+x):
  status_version_le(D.strip("HTTP/1.0", text), D.strip("HTTP/1.1", text), D.strip("HTTP/", text), x)

# The end of the head: the response is built with an empty body
# -------------------------------------------------------------

def length_next_nil_le(v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, n: Nat, -x: Nat)
  -> LE(body_len(D.length_next(M.Response{v, st, rs, hs, Nil{}}, Nil{}, n)), 1n+x):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def cl_fits_le(ok: Bool, n: Nat, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.cl.fits(ok, n, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match ok:
    case True{}:
      length_next_nil_le(v, st, rs, hs, n, x)
    case False{}:
      {==}

def cl_framing_le(k: Nat, cl: Maybe<&2, Nat>, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.cl_framing(k, cl, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match cl:
    case None{}:
      {==}
    case Some{+n}:
      cl_fits_le(Nat.is_le(n, k), n, v, st, rs, hs, x)

def framing_cl_le(cl: List<&2, String>, k: Nat, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.framing.cl(cl, k, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match cl:
    case Nil{}:
      {==}
    case Con{c, t}:
      cl_framing_le(k, D.cl_of(Con{c, t}), v, st, rs, hs, x)

def te_framing_le(conflict: Bool, http10: Bool, chunked: Bool, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.te_framing(conflict, http10, chunked, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match conflict http10 chunked:
    case True{} True{} True{}:
      {==}
    case True{} True{} False{}:
      {==}
    case True{} False{} True{}:
      {==}
    case True{} False{} False{}:
      {==}
    case False{} True{} True{}:
      {==}
    case False{} True{} False{}:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def framing_te_le(fv: M.Version, te: List<&2, String>, +cl: List<&2, String>, k: Nat, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.framing.te(fv, te, cl, k, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match te:
    case Nil{}:
      framing_cl_le(cl, k, v, st, rs, hs, x)
    case Con{c, t}:
      te_framing_le(D.nonempty(cl), D.is_http10(fv), D.chunked_only(Con{c, t}), v, st, rs, hs, x)

def framing_empty_le(e: Bool, fv: M.Version, k: Nat, +fhs: List<&2, M.Header>, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.framing.empty(e, fv, k, fhs, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match e:
    case True{}:
      {==}
    case False{}:
      framing_te_le(fv, H.get_all("transfer-encoding", fhs), H.get_all("content-length", fhs), k, v, st, rs, hs, x)

def framing_interim_le(i: Bool, m: M.Method, fv: M.Version, k: Nat, +fst: Nat, +fhs: List<&2, M.Header>, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.framing.interim(i, m, fv, k, fst, fhs, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match i:
    case True{}:
      {==}
    case False{}:
      framing_empty_le(D.no_body(m, fst), fv, k, fhs, v, st, rs, hs, x)

def framing_upgrade_le(u: Bool, m: M.Method, fv: M.Version, k: Nat, +fst: Nat, +fhs: List<&2, M.Header>, v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, -x: Nat)
  -> LE(body_len(D.framing.upgrade(u, m, fv, k, fst, fhs, M.Response{v, st, rs, hs, Nil{}})), 1n+x):
  match u:
    case True{}:
      {==}
    case False{}:
      framing_interim_le(Nat.is_lt(fst, 200n), m, fv, k, fst, fhs, v, st, rs, hs, x)

def head_end_le(m: M.Method, k: Nat, head: D.Head, -x: Nat) -> LE(body_len(D.head_end(m, k, head)), 1n+x):
  match head:
    case D.Head{+v, +st, rs, hs, n}:
      +h = D.rev(M.Header, hs, Nil{})
      framing_upgrade_le(Nat.is_eq(st, 101n), m, v, k, st, h, v, st, rs, h, x)

# Field lines: the next phase carries no body
# -------------------------------------------

def field_room_le(v: M.Version, s: Nat, rs: String, hs: List<&2, M.Header>, room: Nat, -x: Nat)
  -> LE(body_len(D.field_room(v, s, rs, hs, room)), 1n+x):
  match room:
    case 0n:
      {==}
    case 1n+p:
      {==}

def field_add_le(head: D.Head, f: Maybe<&2, M.Header>, -x: Nat) -> LE(body_len(D.field_add(head, f)), 1n+x):
  match head f:
    case D.Head{v, s, rs, hs, room} Some{h}:
      field_room_le(v, s, rs, h <> hs, room, x)
    case D.Head{v, s, rs, hs, room} None{}:
      {==}

def field_end_le(m: M.Method, k: Nat, head: D.Head, text: String, -x: Nat)
  -> LE(body_len(D.field_end(m, k, head, text)), 1n+x):
  match text:
    case SNil{}:
      head_end_le(m, k, head, x)
    case SCon{c, t}:
      field_add_le(head, D.parse_field(SCon{c, t}), x)

# Chunk-size and trailer lines: the body is carried over
# ------------------------------------------------------

def chunk_fits_le(ok: Bool, n: Nat, r: M.Response, +body: List<&2, U32>)
  -> LE(body_len(D.chunk.fits(ok, n, r, body)), 1n+Laws.len(body)):
  match ok:
    case True{}:
      le_succ(Laws.len(body))
    case False{}:
      {==}

def size_check_le(ok: Bool, digits: String, n: Maybe<&2, Nat>, k: Nat, r: M.Response, +body: List<&2, U32>)
  -> LE(body_len(D.size.check(ok, digits, n, k, r, body)), 1n+Laws.len(body)):
  match ok n:
    case True{} None{}:
      {==}
    case True{} Some{q}:
      match q:
        case 0n:
          le_succ(Laws.len(body))
        case 1n+(+p):
          chunk_fits_le(Nat.is_le(1n+p, k), 1n+p, r, body)
    case False{} None{}:
      {==}
    case False{} Some{q}:
      {==}

def size_parts_le(k: Nat, r: M.Response, +body: List<&2, U32>, p: String & Maybe<&2, String>)
  -> LE(body_len(D.size.parts(k, r, body, p)), 1n+Laws.len(body)):
  match p:
    case (before, ext):
      +digits = D.trim_right(before)
      size_check_le(D.ext_ok(ext), digits, N.hex_read(digits), k, r, body)

def trailer_room_le(r: M.Response, +body: List<&2, U32>, room: Nat)
  -> LE(body_len(D.trailer_room(r, body, room)), 1n+Laws.len(body)):
  match room:
    case 0n:
      {==}
    case 1n+p:
      le_succ(Laws.len(body))

def trailer_add_le(f: Maybe<&2, M.Header>, r: M.Response, +body: List<&2, U32>, room: Nat)
  -> LE(body_len(D.trailer_add(f, r, body, room)), 1n+Laws.len(body)):
  match f:
    case Some{h}:
      trailer_room_le(r, body, room)
    case None{}:
      {==}

# A completed body (with_body reverses it) is as long as the one carried.
def complete_le(r: M.Response, +body: List<&2, U32>, -y: Nat, e: LE(Laws.len(body), y))
  -> LE(Laws.len(S.response_body(D.with_body(r, body))), y):
  %with_body_len(r, body) : {Nat.is_le(_, y) == True{} : Bool}
  e

def trailer_end_le(r: M.Response, +body: List<&2, U32>, room: Nat, text: String)
  -> LE(body_len(D.trailer_end(r, body, room, text)), 1n+Laws.len(body)):
  match text:
    case SNil{}:
      complete_le(r, body, 1n+Laws.len(body), le_succ(Laws.len(body)))
    case SCon{c, t}:
      trailer_add_le(D.parse_field(SCon{c, t}), r, body, room)

# Lines
# -----

def line_end_le(m: M.Method, k: Nat, kind: D.LineKind, +text: String)
  -> LE(body_len(D.line_end(m, k, kind, text)), 1n+kind_len(kind)):
  match kind:
    case D.KStatus{}:
      status_line_le(text, 0n)
    case D.KField{head}:
      field_end_le(m, k, head, text, 0n)
    case D.KSize{r, body}:
      size_parts_le(k, r, body, D.split(D.AtSemi{}, text))
    case D.KTrailer{r, body, room}:
      trailer_end_le(r, body, room, text)


def line_cr_le(m: M.Method, k: Nat, +kind: D.LineKind, acc: List<&2, U32>, c: B.Class)
  -> LE(body_len(D.line_cr(m, k, kind, acc, c)), 1n+kind_len(kind)):
  match c:
    case B.Digit{d}:
      {==}
    case B.HexLetter{d}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      {==}
    case B.Lf{}:
      line_end_le(m, k, kind, D.line_text(acc))
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def line_push_le(+kind: D.LineKind, acc: List<&2, U32>, room: Nat, b: U32)
  -> LE(body_len(D.line_push(kind, acc, room, b)), 1n+kind_len(kind)):
  match room:
    case 0n:
      {==}
    case 1n+p:
      le_succ(kind_len(kind))

def line_byte_le(+kind: D.LineKind, acc: List<&2, U32>, room: Nat, c: B.Class, b: U32)
  -> LE(body_len(D.line_byte(kind, acc, room, c, b)), 1n+kind_len(kind)):
  match c:
    case B.Digit{d}:
      line_push_le(kind, acc, room, b)
    case B.HexLetter{d}:
      line_push_le(kind, acc, room, b)
    case B.Letter{}:
      line_push_le(kind, acc, room, b)
    case B.Tchar{}:
      line_push_le(kind, acc, room, b)
    case B.Colon{}:
      line_push_le(kind, acc, room, b)
    case B.Semi{}:
      line_push_le(kind, acc, room, b)
    case B.Slash{}:
      line_push_le(kind, acc, room, b)
    case B.Sp{}:
      line_push_le(kind, acc, room, b)
    case B.Htab{}:
      line_push_le(kind, acc, room, b)
    case B.Cr{}:
      le_succ(kind_len(kind))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      line_push_le(kind, acc, room, b)
    case B.Ctl{}:
      line_push_le(kind, acc, room, b)
    case B.High{}:
      line_push_le(kind, acc, room, b)
    case B.Invalid{}:
      {==}

# Bodies
# ------

def chunk_cr_le(r: M.Response, +body: List<&2, U32>, c: B.Class)
  -> LE(body_len(D.chunk_cr(r, body, c)), 1n+Laws.len(body)):
  match c:
    case B.Digit{d}:
      {==}
    case B.HexLetter{d}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      le_succ(Laws.len(body))
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def chunk_lf_le(r: M.Response, +body: List<&2, U32>, c: B.Class)
  -> LE(body_len(D.chunk_lf(r, body, c)), 1n+Laws.len(body)):
  match c:
    case B.Digit{d}:
      {==}
    case B.HexLetter{d}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      {==}
    case B.Lf{}:
      le_succ(Laws.len(body))
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

def chunk_byte_le(r: M.Response, +body: List<&2, U32>, left: Nat, +b: U32)
  -> LE(body_len(D.chunk_byte(r, body, left, b)), 1n+Laws.len(body)):
  match left:
    case 0n:
      chunk_cr_le(r, body, B.class(b))
    case 1n+p:
      le_refl(Laws.len(body))

def length_byte_le(r: M.Response, +body: List<&2, U32>, left: Nat, +b: U32)
  -> LE(body_len(D.length_byte(r, body, left, b)), 1n+Laws.len(body)):
  match left:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          complete_le(r, b <> body, 1n+Laws.len(body), le_refl(Laws.len(body)))
        case 1n+q:
          le_refl(Laws.len(body))

# One step
# --------

def consume_le(m: M.Method, k: Nat, p: D.Phase, +b: U32)
  -> LE(body_len(D.consume(m, k, p, b)), 1n+body_len(p)):
  match p:
    case D.ReadLine{kind, acc, room}:
      line_byte_le(kind, acc, room, B.class(b), b)
    case D.ReadCr{kind, acc}:
      line_cr_le(m, k, kind, acc, B.class(b))
    case D.LengthBody{r, body, left}:
      length_byte_le(r, body, left, b)
    case D.CloseBody{r, body}:
      le_refl(Laws.len(body))
    case D.ChunkData{r, body, left}:
      chunk_byte_le(r, body, left, b)
    case D.ChunkLf{r, body}:
      chunk_lf_le(r, body, B.class(b))
    case D.Complete{r, rest}:
      le_succ(Laws.len(S.response_body(r)))
    case D.Failed{e}:
      {==}

def spend_le(m: M.Method, k: Nat, +p: D.Phase, b: U32)
  -> LE(measure(D.spend(m, k, p, b)), Nat.add(k, body_len(p))):
  match k:
    case 0n:
      le_zero(body_len(p))
    case 1n+(+j):
      %add_succ_r(j, body_len(p)) : {Nat.is_le(Nat.add(j, body_len(D.consume(m, j, p, b))), _) == True{} : Bool}
      le_add_l(j, body_len(D.consume(m, j, p, b)), 1n+body_len(p))(consume_le(m, j, p, b))

def step_le(s: D.State, b: U32) -> LE(measure(D.step(s, b)), measure(s)):
  match s:
    case D.State{m, +k, p}:
      match p:
        case D.ReadLine{kind, acc, room}:
          spend_le(m, k, D.ReadLine{kind, acc, room}, b)
        case D.ReadCr{kind, acc}:
          spend_le(m, k, D.ReadCr{kind, acc}, b)
        case D.LengthBody{r, body, left}:
          spend_le(m, k, D.LengthBody{r, body, left}, b)
        case D.CloseBody{r, body}:
          spend_le(m, k, D.CloseBody{r, body}, b)
        case D.ChunkData{r, body, left}:
          spend_le(m, k, D.ChunkData{r, body, left}, b)
        case D.ChunkLf{r, body}:
          spend_le(m, k, D.ChunkLf{r, body}, b)
        case D.Complete{r, rest}:
          le_refl(Nat.add(k, Laws.len(S.response_body(r))))
        case D.Failed{e}:
          le_refl(Nat.add(k, 0n))

def feed_le(+xs: List<&2, U32>, +s: D.State) -> LE(measure(D.feed.go(xs, s)), measure(s)):
  match xs:
    case Nil{}:
      le_refl(measure(s))
    case Con{h, t}:
      le_trans(measure(D.feed.go(t, D.step(s, h))), measure(D.step(s, h)), measure(s))(
        feed_le(t, D.step(s, h)), step_le(s, h))

# The end
# -------

def finish_le(s: D.State) -> LE(res_len(D.finish(s)), measure(s)):
  match s:
    case D.State{m, +k, p}:
      match p:
        case D.ReadLine{kind, acc, room}:
          le_zero(Nat.add(k, kind_len(kind)))
        case D.ReadCr{kind, acc}:
          le_zero(Nat.add(k, kind_len(kind)))
        case D.LengthBody{r, body, left}:
          le_zero(Nat.add(k, Laws.len(body)))
        case D.CloseBody{r, +body}:
          complete_le(r, body, Nat.add(k, Laws.len(body)), le_plus(k, Laws.len(body)))
        case D.ChunkData{r, body, left}:
          le_zero(Nat.add(k, Laws.len(body)))
        case D.ChunkLf{r, body}:
          le_zero(Nat.add(k, Laws.len(body)))
        case D.Complete{+r, rest}:
          le_plus(k, Laws.len(S.response_body(r)))
        case D.Failed{e}:
          le_zero(Nat.add(k, 0n))

# res_len(D.response(meth, m, x)) is the length of r's body (by e); it is at
# most the measure after feeding x (finish_le), which is at most the measure
# of init(meth, m), that is m + 0 (feed_le).
def Laws.size_bound(meth, m, x, r, rest, e):
  %Equal.cong(Laws.Res(), Nat, res_len, D.response(meth, m, x), Done{M.Decoded{r, rest}}, e) :
    {Nat.is_le(_, m) == True{} : Bool}
  %add_zero_r(m) : {Nat.is_le(res_len(D.response(meth, m, x)), _) == True{} : Bool}
  le_trans(res_len(D.response(meth, m, x)), measure(D.feed(D.init(meth, m), x)), Nat.add(m, 0n))(
    finish_le(D.feed(D.init(meth, m), x)), feed_le(x, D.init(meth, m)))
