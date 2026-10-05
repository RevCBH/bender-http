# Laws 1, 4, 5, 6 and 8: ASCII bytes and the request encoder.
#
# The loops each law meets (B.is_ascii, B.all_bytes, B.from_ascii,
# E.none_reserved, H.get_all, the header list built by B.rev twice) are
# first tied to their .spec forms by the equations their file headers
# document; the laws are then proven on the specs by induction.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/headers.bend as H
import ../src/url.bend as U
import ../src/encode.bend as E

# Bool facts
# ----------

def enc_bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def enc_false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : enc_bool_disc(_)
  Unit{}

def enc_and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{} : Bool}, enc_false_ne_true(e))

def enc_and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Empty.absurd({b == True{} : Bool}, enc_false_ne_true(e))

def enc_not_true(+a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, enc_false_ne_true(e))

def enc_or_false_l(+a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{} : Bool}, enc_false_ne_true(Equal.sym(Bool, True{}, False{}, e)))

def enc_and_true(+a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def enc_and_assoc(+a: Bool, -b: Bool, -c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Result facts
# ------------

def enc_res_disc(x: Laws.ReqRes()) -> Type:
  match x:
    case Done{v}:
      Empty
    case Fail{f}:
      Unit

def enc_fail_ne_done(-f: M.Error, -v: List<&2, U32>, e: {Fail{f} == Done{v} : Laws.ReqRes()}) -> Empty:
  %e : enc_res_disc(_)
  Unit{}

def enc_done_val(x: Laws.ReqRes()) -> List<&2, U32>:
  match x:
    case Done{v}:
      v
    case Fail{f}:
      []

def enc_done_inj(-a: List<&2, U32>, -b: List<&2, U32>, e: {Done{a} == Done{b} : Laws.ReqRes()}) -> {a == b : List<&2, U32>}:
  Equal.cong(Laws.ReqRes(), List<&2, U32>, x => enc_done_val(x), Done{a}, Done{b}, e)

# Classes
# -------

def enc_ascii_is_byte(+k: B.Class, e: {B.Class.is_ascii(k) == True{} : Bool}) -> {B.Class.is_byte(k) == True{} : Bool}:
  match k:
    case B.Digit{v}:
      {==}
    case B.HexLetter{v}:
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
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      Empty.absurd({False{} == True{} : Bool}, enc_false_ne_true(e))

# Loop equations (bytes.bend)
# ---------------------------

# all_bytes.go(xs, ok) == Bool.and(ok, all_bytes.spec(xs))
def enc_all_bytes_go(+xs: List<&2, U32>, +ok: Bool)
  -> {B.all_bytes.go(xs, ok) == Bool.and(ok, B.all_bytes.spec(xs)) : Bool}:
  match xs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, enc_and_true(ok))
    case Con{+h, +t}:
      Equal.trans(Bool,
        B.all_bytes.go(t, Bool.and(ok, B.Class.is_byte(B.class(h)))),
        Bool.and(Bool.and(ok, B.Class.is_byte(B.class(h))), B.all_bytes.spec(t)),
        Bool.and(ok, Bool.and(B.Class.is_byte(B.class(h)), B.all_bytes.spec(t))),
        enc_all_bytes_go(t, Bool.and(ok, B.Class.is_byte(B.class(h)))),
        enc_and_assoc(ok, B.Class.is_byte(B.class(h)), B.all_bytes.spec(t)))

# all_bytes(xs) == all_bytes.spec(xs)
def enc_all_bytes_spec(+xs: List<&2, U32>) -> {B.all_bytes(xs) == B.all_bytes.spec(xs) : Bool}:
  enc_all_bytes_go(xs, True{})

# is_ascii.go(s, ok) == Bool.and(ok, is_ascii.spec(s))
def enc_is_ascii_go(+s: String, +ok: Bool)
  -> {B.is_ascii.go(s, ok) == Bool.and(ok, B.is_ascii.spec(s)) : Bool}:
  match s:
    case SNil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, enc_and_true(ok))
    case SCon{+c, +t}:
      Equal.trans(Bool,
        B.is_ascii.go(t, Bool.and(ok, B.Class.is_ascii(B.char_class(c)))),
        Bool.and(Bool.and(ok, B.Class.is_ascii(B.char_class(c))), B.is_ascii.spec(t)),
        Bool.and(ok, Bool.and(B.Class.is_ascii(B.char_class(c)), B.is_ascii.spec(t))),
        enc_is_ascii_go(t, Bool.and(ok, B.Class.is_ascii(B.char_class(c)))),
        enc_and_assoc(ok, B.Class.is_ascii(B.char_class(c)), B.is_ascii.spec(t)))

# is_ascii(s) == is_ascii.spec(s)
def enc_is_ascii_spec(+s: String) -> {B.is_ascii(s) == B.is_ascii.spec(s) : Bool}:
  enc_is_ascii_go(s, True{})

# rev(from_ascii.rev(s, acc), ys) == rev(acc, from_ascii.spec(s) ++ ys)
def enc_from_ascii_rev(+s: String, +acc: List<&2, U32>, +ys: List<&2, U32>)
  -> {B.rev(U32, B.from_ascii.rev(s, acc), ys)
      == B.rev(U32, acc, List.append(&2, U32, B.from_ascii.spec(s), ys)) : List<&2, U32>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      enc_from_ascii_rev(t, Char.to_u32(c) <> acc, ys)

# from_ascii_onto(s, ys) == from_ascii.spec(s) ++ ys
def enc_from_ascii_onto(+s: String, +ys: List<&2, U32>)
  -> {B.from_ascii_onto(s, ys) == List.append(&2, U32, B.from_ascii.spec(s), ys) : List<&2, U32>}:
  enc_from_ascii_rev(s, Nil{}, ys)

def enc_append_nil(+xs: List<&2, U32>) -> {List.append(&2, U32, xs, Nil{}) == xs : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %enc_append_nil(t) : {h <> List.append(&2, U32, t, Nil{}) == h <> _ : List<&2, U32>}
      {==}

# from_ascii(s) == from_ascii.spec(s)
def enc_from_ascii(+s: String) -> {B.from_ascii(s) == B.from_ascii.spec(s) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.from_ascii(s),
    List.append(&2, U32, B.from_ascii.spec(s), Nil{}), B.from_ascii.spec(s),
    enc_from_ascii_onto(s, Nil{}), enc_append_nil(B.from_ascii.spec(s)))

# Law 1
# -----

def enc_to_ascii_spec(+s: String, +e: {B.is_ascii.spec(s) == True{} : Bool})
  -> {B.to_ascii(B.from_ascii.spec(s)) == Some{s} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      match c:
        case Chr{+x}:
          a = enc_and_l(B.Class.is_ascii(B.class(x)), B.is_ascii.spec(t), e)
          r = enc_and_r(B.Class.is_ascii(B.class(x)), B.is_ascii.spec(t), e)
          %Equal.sym(Bool, B.Class.is_ascii(B.class(x)), True{}, a) : {B.to_ascii.con(_, x, B.to_ascii(B.from_ascii.spec(t))) == Some{SCon{Chr{x}, t}} : Maybe<&2, String>}
          %Equal.sym(Maybe<&2, String>, B.to_ascii(B.from_ascii.spec(t)), Some{t}, enc_to_ascii_spec(t, r)) : {B.to_ascii.con(True{}, x, _) == Some{SCon{Chr{x}, t}} : Maybe<&2, String>}
          {==}

def Laws.ascii_roundtrip(s, e):
  es = Equal.trans(Bool, B.is_ascii.spec(s), B.is_ascii(s), True{},
    Equal.sym(Bool, B.is_ascii(s), B.is_ascii.spec(s), enc_is_ascii_spec(s)), e)
  %Equal.sym(List<&2, U32>, B.from_ascii(s), B.from_ascii.spec(s), enc_from_ascii(s)) : {B.to_ascii(_) == Some{s} : Maybe<&2, String>}
  enc_to_ascii_spec(s, es)

# Law 5
# -----

def Laws.encode_total(r, e):
  %Equal.sym(Bool, E.request_ok(r), True{}, e) : {E.request.pick(_, r) == Done{E.request_bytes(r)} : Laws.ReqRes()}
  {==}

# Law 6
# -----

def enc_reject(+m: M.Method, +u: M.Url, +hs: List<&2, M.Header>, +body: List<&2, U32>, +e: {H.headers_ok(hs) == False{} : Bool})
  -> {E.request(M.Request{m, u, hs, body}) == Fail{M.BadRequest{"invalid header name or value"}} : Laws.ReqRes()}:
  %Equal.sym(Bool, H.headers_ok(hs), False{}, e) : {E.request.pick(Bool.and(Bool.and(_, Bool.and(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(u), B.all_bytes(body))))), B.is_ascii(E.head_of(m, u, hs, body))), M.Request{m, u, hs, body}) == Fail{M.BadRequest{"invalid header name or value"}} : Laws.ReqRes()}
  %Equal.sym(Bool, H.headers_ok(hs), False{}, e) : {Fail{M.BadRequest{E.why.pick(_, E.none_reserved(hs), E.method_ok(m), U.ok(u))}} == Fail{M.BadRequest{"invalid header name or value"}} : Laws.ReqRes()}
  {==}

def Laws.encode_rejects_bad_headers(m, u, hs, body, e):
  enc_reject(m, u, hs, body, e)

# Law 4
# -----

# Every cell of from_ascii.spec(s) ++ ys is a byte when s is ASCII and ys are bytes.
def enc_ascii_bytes(+s: String, +ys: List<&2, U32>,
  +ea: {B.is_ascii.spec(s) == True{} : Bool}, +eb: {B.all_bytes.spec(ys) == True{} : Bool})
  -> {B.all_bytes.spec(List.append(&2, U32, B.from_ascii.spec(s), ys)) == True{} : Bool}:
  match s:
    case SNil{}:
      eb
    case SCon{+c, +t}:
      a = enc_and_l(B.Class.is_ascii(B.char_class(c)), B.is_ascii.spec(t), ea)
      r = enc_and_r(B.Class.is_ascii(B.char_class(c)), B.is_ascii.spec(t), ea)
      bt = enc_ascii_is_byte(B.char_class(c), a)
      %Equal.sym(Bool, B.Class.is_byte(B.char_class(c)), True{}, bt) : {Bool.and(_, B.all_bytes.spec(List.append(&2, U32, B.from_ascii.spec(t), ys))) == True{} : Bool}
      enc_ascii_bytes(t, ys, r, eb)

def enc_bytes_of_ok(+r: M.Request, +e: {E.request_ok(r) == True{} : Bool})
  -> {B.all_bytes(E.request_bytes(r)) == True{} : Bool}:
  match r:
    case M.Request{+m, +u, +hs, +body}:
      ef = enc_and_l(E.fields_ok(m, u, hs, body), B.is_ascii(E.head_of(m, u, hs, body)), e)
      eh = enc_and_r(E.fields_ok(m, u, hs, body), B.is_ascii(E.head_of(m, u, hs, body)), e)
      e1 = enc_and_r(H.headers_ok(hs), Bool.and(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(u), B.all_bytes(body)))), ef)
      e2 = enc_and_r(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(u), B.all_bytes(body))), e1)
      e3 = enc_and_r(E.method_ok(m), Bool.and(U.ok(u), B.all_bytes(body)), e2)
      e4 = enc_and_r(U.ok(u), B.all_bytes(body), e3)
      eb = Equal.trans(Bool, B.all_bytes.spec(body), B.all_bytes(body), True{},
        Equal.sym(Bool, B.all_bytes(body), B.all_bytes.spec(body), enc_all_bytes_spec(body)), e4)
      ea = Equal.trans(Bool, B.is_ascii.spec(E.head_of(m, u, hs, body)), B.is_ascii(E.head_of(m, u, hs, body)), True{},
        Equal.sym(Bool, B.is_ascii(E.head_of(m, u, hs, body)), B.is_ascii.spec(E.head_of(m, u, hs, body)), enc_is_ascii_spec(E.head_of(m, u, hs, body))), eh)
      %Equal.sym(Bool, B.all_bytes(E.request_bytes(M.Request{m, u, hs, body})), B.all_bytes.spec(E.request_bytes(M.Request{m, u, hs, body})), enc_all_bytes_spec(E.request_bytes(M.Request{m, u, hs, body}))) : {_ == True{} : Bool}
      %Equal.sym(List<&2, U32>, B.from_ascii_onto(E.head_of(m, u, hs, body), body), List.append(&2, U32, B.from_ascii.spec(E.head_of(m, u, hs, body)), body), enc_from_ascii_onto(E.head_of(m, u, hs, body), body)) : {B.all_bytes.spec(_) == True{} : Bool}
      enc_ascii_bytes(E.head_of(m, u, hs, body), body, ea, eb)

def enc_bytes_pick(+k: Bool, +r: M.Request, -b: List<&2, U32>,
  +ek: {E.request_ok(r) == k : Bool}, +e: {E.request.pick(k, r) == Done{b} : Laws.ReqRes()})
  -> {B.all_bytes(b) == True{} : Bool}:
  match k:
    case True{}:
      %enc_done_inj(E.request_bytes(r), b, e) : {B.all_bytes(_) == True{} : Bool}
      enc_bytes_of_ok(r, ek)
    case False{}:
      Empty.absurd({B.all_bytes(b) == True{} : Bool}, enc_fail_ne_done(M.BadRequest{E.why(r)}, b, e))

def Laws.encode_bytes_in_range(r, b, e):
  enc_bytes_pick(E.request_ok(r), r, b, {==}, e)

# Law 8
# -----

def enc_none_reserved_go(+hs: List<&2, M.Header>, +ok: Bool)
  -> {E.none_reserved.go(hs, ok) == Bool.and(ok, E.none_reserved.spec(hs)) : Bool}:
  match hs:
    case Nil{}:
      Equal.sym(Bool, Bool.and(ok, True{}), ok, enc_and_true(ok))
    case Con{+h, +t}:
      match h:
        case M.Header{+n, +v}:
          Equal.trans(Bool,
            E.none_reserved.go(t, Bool.and(ok, Bool.not(E.is_reserved(n)))),
            Bool.and(Bool.and(ok, Bool.not(E.is_reserved(n))), E.none_reserved.spec(t)),
            Bool.and(ok, Bool.and(Bool.not(E.is_reserved(n)), E.none_reserved.spec(t))),
            enc_none_reserved_go(t, Bool.and(ok, Bool.not(E.is_reserved(n)))),
            enc_and_assoc(ok, Bool.not(E.is_reserved(n)), E.none_reserved.spec(t)))

def enc_get_all_pick_rev(+hit: Bool, +v: String, +acc: List<&2, String>, +rest: List<&2, String>)
  -> {B.rev(String, H.get_all.pick(hit, v, acc), rest) == B.rev(String, acc, H.get_all.pick(hit, v, rest)) : List<&2, String>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

# get_all.go(l, hs, acc) == rev(acc, get_all.spec(l, hs))
def enc_get_all_go(+l: String, +hs: List<&2, M.Header>, +acc: List<&2, String>)
  -> {H.get_all.go(l, hs, acc) == B.rev(String, acc, H.get_all.spec(l, hs)) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match h:
        case M.Header{+n, +v}:
          Equal.trans(List<&2, String>,
            H.get_all.go(l, t, H.get_all.pick(String.eq(l, H.lower(n)), v, acc)),
            B.rev(String, H.get_all.pick(String.eq(l, H.lower(n)), v, acc), H.get_all.spec(l, t)),
            B.rev(String, acc, H.get_all.pick(String.eq(l, H.lower(n)), v, H.get_all.spec(l, t))),
            enc_get_all_go(l, t, H.get_all.pick(String.eq(l, H.lower(n)), v, acc)),
            enc_get_all_pick_rev(String.eq(l, H.lower(n)), v, acc, H.get_all.spec(l, t)))

# rev(rev(hs, acc), ys) == rev(acc, hs ++ ys)
def enc_rev_rev(+hs: List<&2, M.Header>, +acc: List<&2, M.Header>, +ys: List<&2, M.Header>)
  -> {B.rev(M.Header, B.rev(M.Header, hs, acc), ys) == B.rev(M.Header, acc, List.append(&2, M.Header, hs, ys)) : List<&2, M.Header>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      enc_rev_rev(t, h <> acc, ys)

# No header of hs is named Host (any case): get_all.spec skips them.
def enc_skip_unreserved(+hs: List<&2, M.Header>, +ys: List<&2, M.Header>, +e: {E.none_reserved.spec(hs) == True{} : Bool})
  -> {H.get_all.spec(H.lower("host"), List.append(&2, M.Header, hs, ys)) == H.get_all.spec(H.lower("host"), ys) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      match h:
        case M.Header{+n, +v}:
          a = enc_and_l(Bool.not(E.is_reserved(n)), E.none_reserved.spec(t), e)
          b = enc_and_r(Bool.not(E.is_reserved(n)), E.none_reserved.spec(t), e)
          nr = enc_not_true(E.is_reserved(n), a)
          nh = enc_or_false_l(H.name_eq("host", n), Bool.or(H.name_eq("content-length", n), Bool.or(H.name_eq("transfer-encoding", n), H.name_eq("connection", n))), nr)
          %Equal.sym(Bool, H.name_eq("host", n), False{}, nh) : {H.get_all.pick(_, v, H.get_all.spec(H.lower("host"), List.append(&2, M.Header, t, ys))) == H.get_all.spec(H.lower("host"), ys) : List<&2, String>}
          enc_skip_unreserved(t, ys, b)

# The headers after the caller's carry no Host.
def enc_tail_no_host(+w: Bool, +body: List<&2, U32>)
  -> {H.get_all.spec(H.lower("host"), List.append(&2, M.Header, E.length_header.pick(w, body), [M.Header{"Connection", "close"}])) == [] : List<&2, String>}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.host_once(r, e):
  match r:
    case M.Request{+m, +u, +hs, +body}:
      ef = enc_and_l(E.fields_ok(m, u, hs, body), B.is_ascii(E.head_of(m, u, hs, body)), e)
      e1 = enc_and_r(H.headers_ok(hs), Bool.and(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(u), B.all_bytes(body)))), ef)
      e2 = enc_and_l(E.none_reserved(hs), Bool.and(E.method_ok(m), Bool.and(U.ok(u), B.all_bytes(body))), e1)
      en = Equal.trans(Bool, E.none_reserved.spec(hs), E.none_reserved(hs), True{},
        Equal.sym(Bool, E.none_reserved(hs), E.none_reserved.spec(hs), enc_none_reserved_go(hs, True{})), e2)
      +tl = E.tail_headers(m, body)
      +rest = B.rev(M.Header, B.rev(M.Header, hs, Nil{}), tl)
      %Equal.sym(List<&2, String>, H.get_all.go(H.lower("host"), rest, [U.host_header(u)]), B.rev(String, [U.host_header(u)], H.get_all.spec(H.lower("host"), rest)), enc_get_all_go(H.lower("host"), rest, [U.host_header(u)])) : {List.length(&2, String, _) == 1n : Nat}
      %Equal.sym(List<&2, M.Header>, rest, List.append(&2, M.Header, hs, tl), enc_rev_rev(hs, Nil{}, tl)) : {1n+List.length(&2, String, H.get_all.spec(H.lower("host"), _)) == 1n : Nat}
      %Equal.sym(List<&2, String>, H.get_all.spec(H.lower("host"), List.append(&2, M.Header, hs, tl)), H.get_all.spec(H.lower("host"), tl), enc_skip_unreserved(hs, tl, en)) : {1n+List.length(&2, String, _) == 1n : Nat}
      %Equal.sym(List<&2, String>, H.get_all.spec(H.lower("host"), tl), [], enc_tail_no_host(E.wants_length(m, body), body)) : {1n+List.length(&2, String, _) == 1n : Nat}
      {==}
