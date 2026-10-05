# The decoder lemma library: what feeding an encoded head does.
#
# Laws 10-15 all start the same way: the decoder reads S.encode_head(r) and
# reaches the phase D.head_end builds for r's version, status, reason and
# headers. This file proves that once, for any method and any budget, and
# exports the pieces for the laws built on it. Import it as
#   import ../proofs/decode_lemmas.bend as DL
# (it imports proofs/num.bend for Laws.dec_roundtrip). Every lemma below has
# a comment where it is defined; hypotheses are explicit arguments.
#
# Budgets. charge(m, n, b, f) is the state after n bytes that each cost one
# unit of budget, from budget b, f(k) being the phase reached with k left:
# State{m, b - n, f(b - n)} if b >= n, else State{m, 0, Failed{TooLarge}}
# (a byte arrived with budget 0). A run of n consuming bytes is stated as
#   feed(State{m, b, p}, xs) == charge(m, len(xs), b, f)    for every b,
# so one lemma covers a budget that suffices and one that does not:
#   charge_exact(m, n, k, f)   charge(m, n, n + k, f) == State{m, k, f(k)}
#   charge_seq / seg_seq       two runs glued (xs then ys: n1 + n2 bytes)
#   charge_fail_feed           every f(k) a failure: finish(feed(charge(..), ys)) is a Fail
#
# The head (r any response, m any method):
#   head_phase(m, k, r)        = framing.upgrade(is_eq(st, 101), m, v, k, st, hs, Response{v, st, rs, hs, []})
#                                (what D.head_end gives for r's head, k budget left)
#   head_feed(m, r, b, e_sv, e_ok)
#       feed(init(m, b), encode_head(r)) == charge(m, len(encode_head(r)), b, k => head_phase(m, k, r))
#   head_charge(m, r, b, ys, e_sv, e_ok)
#       feed(init(m, b), encode_head(r) ++ ys) == feed(charge(m, len(encode_head(r)), b, k => head_phase(m, k, r)), ys)
#   head_at(m, r, K, ys, e_sv, e_ok)                                 (THE HEAD LEMMA)
#       feed(init(m, len(encode_head(r)) + K), encode_head(r) ++ ys) == feed(State{m, K, head_phase(m, K, r)}, ys)
#   with e_sv : status_value(N.show(response_status(r))) == Some{response_status(r)}
#        e_ok : S.head_ok(r) == True
#   status_value_show(st, 100 <= st, st <= 999) gives e_sv.
#   init(m, K) is State{m, K, line(KStatus)}: a second head (law 14) starts
#   from head_phase_interim's line(KStatus) with head_at again.
#
# The phase after the head (over r = Response{v, st, rs, hs, body}):
#   head_phase_complete(.., st != 101, not st < 200, no_body(m, st))  == Complete{Response{v, st, rs, hs, []}, []}
#   head_phase_interim(.., st != 101, st < 200)                       == line(KStatus)
#   head_phase_body(.., st != 101, not st < 200, not no_body(m, st))
#       == framing.te(v, get_all("transfer-encoding", hs), get_all("content-length", hs), k, Response{v, st, rs, hs, []})
#   head_phase_conflict(.., + has content-length, has transfer-encoding) == Failed{ConflictingFraming}
#   te_conflict, has_get_all (has(n, hs) => nonempty(get_all(n, hs))), no_body_false,
#   final_not_101 / final_not_lt (from 200 <= st), bs_100 .. bs_304 (S.body_status_ok
#   taken apart), response_ok_status / response_ok_head, head_ok_* / head_fits_*.
#
# The machine: feed_cat (law 9 again), feed_failed, feed_complete (leftover
# kept reversed), rev_rev (finish reverses it back), cat_assoc, len_cat,
# from_ascii_eq (B.from_ascii == from_ascii.spec), FA = from_ascii.spec, fa_app.
#
# The pieces of the head lemma, for other line-shaped input:
#   line_feed_text  a fresh line s (plain chars, len(s) <= room) then CR LF:
#                   feed(State{m, b, ReadLine{kind, [], room}}, line_bytes(s)) == charge(m, len(line_bytes(s)), b, end_k(m, kind, s))
#   status_end      the status line of r ends in line(KField{Head{v, st, rs, [], FIELDS_MAX}})
#   field_line_end  a field line "n: v" adds Header{n, v} to the head (room - 1)
#   fields_feed     all field lines of hs then the empty line end the head (fields_end)
#   split_con, trim_value, field_parse, status_line_parse: the line parsers on encoded text
#   all_text_go, all_tchar_go, all_field_char_go, headers_ok_go: the loop equations
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/decode.bend as D
import ../src/spec.bend as S
import ../proofs/num.bend as NP

# Bool facts
# ----------

def bool_disc(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

# False is not True.
def false_ne_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : bool_disc(_)
  Unit{}

# Anything from {False == True}.
def absurd_ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, false_ne_true(e))

# a && b is True: so is a.
def and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      absurd_ft({False{} == True{} : Bool}, e)

# a && b is True: so is b.
def and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      absurd_ft({b == True{} : Bool}, e)

# Both True: a && b is True.
def and_intro(a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      absurd_ft({Bool.and(False{}, b) == True{} : Bool}, ea)

# not(a) is True: a is False.
def not_true(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      absurd_ft({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# a is True and False: anything.
def true_false(-A: Type, a: Bool, e1: {a == True{} : Bool}, e2: {a == False{} : Bool}) -> A:
  match a:
    case True{}:
      absurd_ft(A, Equal.sym(Bool, True{}, False{}, e2))
    case False{}:
      absurd_ft(A, e1)

# Nat facts
# ---------

def add_zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def le_zero_l(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def le_trans(a: Nat, b: Nat, c: Nat, e1: {Nat.is_le(a, b) == True{} : Bool}, e2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      le_zero_l(c)
    case 1n+ap 0n _:
      absurd_ft({Nat.is_le(1n+ap, c) == True{} : Bool}, e1)
    case 1n+ap 1n+bp 0n:
      absurd_ft({Nat.is_le(1n+ap, 0n) == True{} : Bool}, e2)
    case 1n+ap 1n+bp 1n+cp:
      le_trans(ap, bp, cp, e1, e2)

# a < b: b is not a.
def le_ne(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      absurd_ft({Nat.is_eq(0n, 0n) == False{} : Bool}, e)
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      absurd_ft({Nat.is_eq(0n, 1n+ap) == False{} : Bool}, e)
    case 1n+ap 1n+bp:
      le_ne(ap, bp, e)

# a <= b: b is not below a.
def le_not_lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      {==}
    case 1n+ap 0n:
      absurd_ft({Nat.is_lt(0n, 1n+ap) == False{} : Bool}, e)
    case 1n+ap 1n+bp:
      le_not_lt(ap, bp, e)

# Lists
# -----

def cat_nil(-A: Data, xs: List<&2, A>) -> {List.append(&2, A, xs, Nil{}) == xs : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_nil(A, t) : {Con{h, List.append(&2, A, t, Nil{})} == Con{h, _} : List<&2, A>}
      {==}

def cat_assoc(xs: List<&2, U32>, -ys: List<&2, U32>, -zs: List<&2, U32>)
  -> {Laws.cat(Laws.cat(xs, ys), zs) == Laws.cat(xs, Laws.cat(ys, zs)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %cat_assoc(t, ys, zs) : {Con{h, Laws.cat(Laws.cat(t, ys), zs)} == Con{h, _} : List<&2, U32>}
      {==}

def len_cat(xs: List<&2, U32>, -ys: List<&2, U32>)
  -> {Laws.len(Laws.cat(xs, ys)) == Nat.add(Laws.len(xs), Laws.len(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %len_cat(t, ys) : {1n+Laws.len(Laws.cat(t, ys)) == 1n+_ : Nat}
      {==}

# D.rev(xs, acc) is reverse(xs) ++ acc, so reversing it onto ys gives acc
# reversed onto xs ++ ys.
def rev_rev_onto(-A: Data, xs: List<&2, A>, acc: List<&2, A>, -ys: List<&2, A>)
  -> {D.rev(A, D.rev(A, xs, acc), ys) == D.rev(A, acc, List.append(&2, A, xs, ys)) : List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_rev_onto(A, t, h <> acc, ys)

# Reversing twice is the identity.
def rev_rev(-A: Data, +xs: List<&2, A>) -> {D.rev(A, D.rev(A, xs, Nil{}), Nil{}) == xs : List<&2, A>}:
  Equal.trans(List<&2, A>, D.rev(A, D.rev(A, xs, Nil{}), Nil{}), List.append(&2, A, xs, Nil{}), xs,
    rev_rev_onto(A, xs, Nil{}, Nil{}), cat_nil(A, xs))

# Strings
# -------

def sapp_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %sapp_nil(t) : {SCon{c, String.append(t, SNil{})} == SCon{c, _} : String}
      {==}

# String.reverse.go(a, acc) is reverse(a) ++ acc.
def rgo_app(a: String, acc: String, -y: String)
  -> {String.reverse.go(a, String.append(acc, y)) == String.append(String.reverse.go(a, acc), y) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rgo_app(t, SCon{h, acc}, y)

# Reversing reverse(a) ++ acc onto y gives reverse(acc) ++ a ++ y.
def rgo_rgo(a: String, acc: String, -y: String)
  -> {String.reverse.go(String.reverse.go(a, acc), y) == String.reverse.go(acc, String.append(a, y)) : String}:
  match a:
    case SNil{}:
      {==}
    case SCon{h, t}:
      rgo_rgo(t, SCon{h, acc}, y)

# The chars x, a in reverse, reversed back: x then a.
def rev_single(+a: String, x: Char)
  -> {String.reverse(String.reverse.go(a, SCon{x, SNil{}})) == SCon{x, a} : String}:
  Equal.trans(String, String.reverse(String.reverse.go(a, SCon{x, SNil{}})), SCon{x, String.append(a, SNil{})}, SCon{x, a},
    rgo_rgo(a, SCon{x, SNil{}}, SNil{}),
    Equal.cong(String, String, y => SCon{x, y}, String.append(a, SNil{}), a, sapp_nil(a)))

# Reversing twice is the identity.
def srev_rev(+s: String) -> {String.reverse(String.reverse(s)) == s : String}:
  Equal.trans(String, String.reverse(String.reverse(s)), String.append(s, SNil{}), s,
    rgo_rgo(s, SNil{}, SNil{}), sapp_nil(s))

# Bytes from text
# ---------------

def FA(s: String) -> List<&2, U32>:
  B.from_ascii.spec(s)

# The bytes of a ++ b.
def fa_app(a: String, -b: String) -> {FA(String.append(a, b)) == Laws.cat(FA(a), FA(b)) : List<&2, U32>}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %fa_app(t, b) : {Con{Char.to_u32(c), FA(String.append(t, b))} == Con{Char.to_u32(c), _} : List<&2, U32>}
      {==}

# The loop equation of from_ascii (bytes.bend).
def from_ascii_rev(s: String, acc: List<&2, U32>, -ys: List<&2, U32>)
  -> {B.rev(U32, B.from_ascii.rev(s, acc), ys) == B.rev(U32, acc, Laws.cat(FA(s), ys)) : List<&2, U32>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      from_ascii_rev(t, Char.to_u32(c) <> acc, ys)

# from_ascii is from_ascii.spec.
def from_ascii_eq(+s: String) -> {B.from_ascii(s) == FA(s) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.from_ascii(s), Laws.cat(FA(s), Nil{}), FA(s),
    from_ascii_rev(s, Nil{}, Nil{}), cat_nil(U32, FA(s)))

# A line's bytes: its text, then CR LF.
def line_bytes(s: String) -> List<&2, U32>:
  Laws.cat(FA(s), [13, 10])

# The bytes of s ++ CRLF are line_bytes(s).
def line_bytes_eq(+s: String) -> {B.from_ascii(String.append(s, "\r\n")) == line_bytes(s) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, B.from_ascii(String.append(s, "\r\n")), FA(String.append(s, "\r\n")), line_bytes(s),
    from_ascii_eq(String.append(s, "\r\n")), fa_app(s, "\r\n"))

# Reading the bytes of s back (latin1_onto over the reversed line) gives s:
# Char.from_u32(Char.to_u32(c)) == c by a case on c.
def latin1_fa(s: String, acc: List<&2, U32>, -x: String)
  -> {B.latin1_onto(B.from_ascii.rev(s, acc), x) == B.latin1_onto(acc, String.append(s, x)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{u}:
          latin1_fa(t, u <> acc, x)

# The text the decoder reads off the line s.
def text_of(+s: String) -> {D.line_text(B.from_ascii.rev(s, Nil{})) == s : String}:
  Equal.trans(String, D.line_text(B.from_ascii.rev(s, Nil{})), String.append(s, SNil{}), s,
    latin1_fa(s, Nil{}, SNil{}), sapp_nil(s))

# The machine
# -----------

# feed is a fold of step: feed(feed(s, a), b) == feed(s, a ++ b).
def feed_go_cat(a: List<&2, U32>, -b: List<&2, U32>, -s: D.State)
  -> {D.feed.go(b, D.feed.go(a, s)) == D.feed.go(Laws.cat(a, b), s) : D.State}:
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      feed_go_cat(t, b, D.step(s, h))

def feed_cat(-s: D.State, a: List<&2, U32>, -b: List<&2, U32>)
  -> {D.feed(D.feed(s, a), b) == D.feed(s, Laws.cat(a, b)) : D.State}:
  feed_go_cat(a, b, s)

# A failed state ignores every byte.
def feed_failed(-m: M.Method, -k: Nat, -e: M.ParseError, xs: List<&2, U32>)
  -> {D.feed(D.State{m, k, D.Failed{e}}, xs) == D.State{m, k, D.Failed{e}} : D.State}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      feed_failed(m, k, e, t)

# A complete state keeps every byte as leftover (reversed), spending nothing.
def feed_complete(-m: M.Method, -k: Nat, -r: M.Response, xs: List<&2, U32>, acc: List<&2, U32>)
  -> {D.feed(D.State{m, k, D.Complete{r, acc}}, xs) == D.State{m, k, D.Complete{r, D.rev(U32, xs, acc)}} : D.State}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      feed_complete(m, k, r, t, h <> acc)

# Budgets
# -------

# The state after n one-unit bytes from budget b, f(k) being the phase
# reached with budget k left: State{m, b - n, f(b - n)}, or TooLarge when a
# byte arrives with budget 0.
def charge(m: M.Method, n: Nat, b: Nat, f: Nat -> D.Phase) -> D.State:
  match n b:
    case 0n +k:
      D.State{m, k, f(k)}
    case 1n+p 0n:
      D.State{m, 0n, D.Failed{M.TooLarge{}}}
    case 1n+p 1n+c:
      charge(m, p, c, f)

# A budget of n + k: the run reaches f(k) with k left.
def charge_exact(-m: M.Method, n: Nat, -k: Nat, -f: Nat -> D.Phase)
  -> {charge(m, n, Nat.add(n, k), f) == D.State{m, k, f(k)} : D.State}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      charge_exact(m, p, k, f)

# Runs compose: if every f(k) followed by ys is a run of n2 bytes ending in
# g, then charge(.., n1, .., f) followed by ys is a run of n1 + n2 bytes.
def charge_seq(-m: M.Method, n1: Nat, b: Nat, -n2: Nat, -f: Nat -> D.Phase, -g: Nat -> D.Phase, ys: List<&2, U32>,
  h: @k: Nat -> {D.feed(D.State{m, k, f(k)}, ys) == charge(m, n2, k, g) : D.State})
  -> {D.feed(charge(m, n1, b, f), ys) == charge(m, Nat.add(n1, n2), b, g) : D.State}:
  match n1 b:
    case 0n b0:
      h(b0)
    case 1n+p 0n:
      feed_failed(m, 0n, M.TooLarge{}, ys)
    case 1n+p 1n+c:
      charge_seq(m, p, c, n2, f, g, ys, h)

# Two runs glued: xs then ys.
def seg_seq(-m: M.Method, +b: Nat, -p: D.Phase, +xs: List<&2, U32>, +ys: List<&2, U32>, -f: Nat -> D.Phase, -g: Nat -> D.Phase,
  h1: {D.feed(D.State{m, b, p}, xs) == charge(m, Laws.len(xs), b, f) : D.State},
  h2: @k: Nat -> {D.feed(D.State{m, k, f(k)}, ys) == charge(m, Laws.len(ys), k, g) : D.State})
  -> {D.feed(D.State{m, b, p}, Laws.cat(xs, ys)) == charge(m, Laws.len(Laws.cat(xs, ys)), b, g) : D.State}:
  %feed_cat(D.State{m, b, p}, xs, ys) : {_ == charge(m, Laws.len(Laws.cat(xs, ys)), b, g) : D.State}
  %Equal.sym(D.State, D.feed(D.State{m, b, p}, xs), charge(m, Laws.len(xs), b, f), h1) :
    {D.feed(_, ys) == charge(m, Laws.len(Laws.cat(xs, ys)), b, g) : D.State}
  %Equal.sym(Nat, Laws.len(Laws.cat(xs, ys)), Nat.add(Laws.len(xs), Laws.len(ys)), len_cat(xs, ys)) :
    {D.feed(charge(m, Laws.len(xs), b, f), ys) == charge(m, _, b, g) : D.State}
  charge_seq(m, Laws.len(xs), b, Laws.len(ys), f, g, ys, h2)

# Lines
# -----

# A byte class the line reader keeps: not CR, LF, or a cell past 255.
def plain(k: B.Class) -> Bool:
  match k:
    case B.Cr{}:
      False{}
    case B.Lf{}:
      False{}
    case B.Invalid{}:
      False{}
    case _:
      True{}

# Every char of s has a plain class.
def plain_str(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(plain(B.char_class(c)), plain_str(t))

# The classes of the digit chars N.digit_char writes ('?' is Delim).
def dclass(k: B.Class) -> Bool:
  match k:
    case B.Digit{v}:
      True{}
    case B.HexLetter{v}:
      True{}
    case B.Delim{}:
      True{}
    case _:
      False{}

def nz_digit(d: Nat) -> Bool:
  match d:
    case 0n:
      False{}
    case 1n+p:
      True{}

# Not the class of '0' (what status_value.lead refuses).
def notzero(k: B.Class) -> Bool:
  match k:
    case B.Digit{v}:
      nz_digit(v)
    case _:
      True{}

# A byte of a plain class is pushed onto the line.
def line_byte_plain(-kind: D.LineKind, -acc: List<&2, U32>, -room: Nat, k: B.Class, -x: U32, e: {plain(k) == True{} : Bool})
  -> {D.line_byte(kind, acc, room, k, x) == D.line_push(kind, acc, room, x) : D.Phase}:
  match k:
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
      absurd_ft({D.line_byte(kind, acc, room, B.Cr{}, x) == D.line_push(kind, acc, room, x) : D.Phase}, e)
    case B.Lf{}:
      absurd_ft({D.line_byte(kind, acc, room, B.Lf{}, x) == D.line_push(kind, acc, room, x) : D.Phase}, e)
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      absurd_ft({D.line_byte(kind, acc, room, B.Invalid{}, x) == D.line_push(kind, acc, room, x) : D.Phase}, e)

# The phase a line of this kind reaches when it ends with the text, budget k left.
def end_k(m: M.Method, kind: D.LineKind, text: String) -> Nat -> D.Phase:
  k => D.line_end(m, k, kind, text)

def line_feed_nil(-m: M.Method, -kind: D.LineKind, -acc: List<&2, U32>, -room: Nat, b: Nat)
  -> {D.feed(D.State{m, b, D.ReadLine{kind, acc, room}}, line_bytes(SNil{}))
      == charge(m, Laws.len(line_bytes(SNil{})), b, end_k(m, kind, D.line_text(B.from_ascii.rev(SNil{}, acc)))) : D.State}:
  match b:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+c:
      {==}

# The line lemma (general form): reading s (plain chars, at most room of
# them) then CR LF in a ReadLine phase, the line ends with the text of the
# bytes read (acc, then s); every byte costs one unit.
def line_feed(-m: M.Method, -kind: D.LineKind, s: String, -acc: List<&2, U32>, room: Nat, b: Nat,
  +ep: {plain_str(s) == True{} : Bool}, er: {Nat.is_le(String.length(s), room) == True{} : Bool})
  -> {D.feed(D.State{m, b, D.ReadLine{kind, acc, room}}, line_bytes(s))
      == charge(m, Laws.len(line_bytes(s)), b, end_k(m, kind, D.line_text(B.from_ascii.rev(s, acc)))) : D.State}:
  match s room b:
    case SNil{} r0 b0:
      line_feed_nil(m, kind, acc, r0, b0)
    case SCon{+c, t} 0n b0:
      absurd_ft({D.feed(D.State{m, b0, D.ReadLine{kind, acc, 0n}}, line_bytes(SCon{c, t}))
        == charge(m, Laws.len(line_bytes(SCon{c, t})), b0, end_k(m, kind, D.line_text(B.from_ascii.rev(SCon{c, t}, acc)))) : D.State}, er)
    case SCon{+c, t} 1n+q 0n:
      feed_failed(m, 0n, M.TooLarge{}, line_bytes(t))
    case SCon{+c, t} 1n+q 1n+b1:
      %Equal.sym(D.Phase, D.line_byte(kind, acc, 1n+q, B.char_class(c), Char.to_u32(c)), D.line_push(kind, acc, 1n+q, Char.to_u32(c)),
        line_byte_plain(kind, acc, 1n+q, B.char_class(c), Char.to_u32(c), and_l(plain(B.char_class(c)), plain_str(t), ep))) :
        {D.feed(D.State{m, b1, _}, line_bytes(t))
          == charge(m, Laws.len(line_bytes(t)), b1, end_k(m, kind, D.line_text(B.from_ascii.rev(t, Char.to_u32(c) <> acc)))) : D.State}
      line_feed(m, kind, t, Char.to_u32(c) <> acc, q, b1, and_r(plain(B.char_class(c)), plain_str(t), ep), er)

# The line lemma: a fresh line s (plain chars, at most room of them) then
# CR LF ends with the text s.
def line_feed_text(-m: M.Method, -kind: D.LineKind, +s: String, room: Nat, b: Nat,
  +ep: {plain_str(s) == True{} : Bool}, er: {Nat.is_le(String.length(s), room) == True{} : Bool})
  -> {D.feed(D.State{m, b, D.ReadLine{kind, Nil{}, room}}, line_bytes(s))
      == charge(m, Laws.len(line_bytes(s)), b, end_k(m, kind, s)) : D.State}:
  %text_of(s) : {D.feed(D.State{m, b, D.ReadLine{kind, Nil{}, room}}, line_bytes(s))
      == charge(m, Laws.len(line_bytes(s)), b, end_k(m, kind, _)) : D.State}
  line_feed(m, kind, s, Nil{}, room, b, ep, er)

# s ++ CRLF is at least two chars long.
def crlf_len(t: String) -> {Nat.is_le(String.length(String.append(t, "\r\n")), 1n) == False{} : Bool}:
  match t:
    case SNil{}:
      {==}
    case SCon{c, u}:
      match u:
        case SNil{}:
          {==}
        case SCon{d, w}:
          {==}

# A line that fits 2 + mm with its CRLF fits mm without it (S.line_fits).
def fits_crlf(s: String, mm: Nat, e: {Nat.is_le(String.length(String.append(s, "\r\n")), Nat.add(2n, mm)) == True{} : Bool})
  -> {Nat.is_le(String.length(s), mm) == True{} : Bool}:
  match s mm:
    case SNil{} m0:
      le_zero_l(m0)
    case SCon{c, +t} 0n:
      true_false({Nat.is_le(String.length(SCon{c, t}), 0n) == True{} : Bool},
        Nat.is_le(String.length(String.append(t, "\r\n")), 1n), e, crlf_len(t))
    case SCon{c, t} 1n+mp:
      fits_crlf(t, mp, e)

# Char classes
# ------------

# A field char (VCHAR, SP, HTAB) is kept by the line reader.
def field_plain(k: B.Class, e: {B.Class.is_field_char(k) == True{} : Bool}) -> {plain(k) == True{} : Bool}:
  match k:
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
      absurd_ft({plain(B.Cr{}) == True{} : Bool}, e)
    case B.Lf{}:
      absurd_ft({plain(B.Lf{}) == True{} : Bool}, e)
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      absurd_ft({plain(B.Invalid{}) == True{} : Bool}, e)

# A tchar is kept by the line reader.
def tchar_plain(k: B.Class, e: {B.Class.is_tchar(k) == True{} : Bool}) -> {plain(k) == True{} : Bool}:
  match k:
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
      absurd_ft({plain(B.Cr{}) == True{} : Bool}, e)
    case B.Lf{}:
      absurd_ft({plain(B.Lf{}) == True{} : Bool}, e)
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      absurd_ft({plain(B.Invalid{}) == True{} : Bool}, e)

# A tchar does not stop a split at ':'.
def tchar_nocolon(k: B.Class, e: {B.Class.is_tchar(k) == True{} : Bool}) -> {Bool.not(D.stop_class(D.AtColon{}, k)) == True{} : Bool}:
  match k:
    case B.Digit{d}:
      {==}
    case B.HexLetter{d}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      absurd_ft({Bool.not(D.stop_class(D.AtColon{}, B.Colon{})) == True{} : Bool}, e)
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
      {==}

# A field char is a text char (reason phrases, field values).
def field_text_class(k: B.Class, e: {B.Class.is_field_char(k) == True{} : Bool}) -> {D.text_class(k) == True{} : Bool}:
  match k:
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
      absurd_ft({D.text_class(B.Cr{}) == True{} : Bool}, e)
    case B.Lf{}:
      absurd_ft({D.text_class(B.Lf{}) == True{} : Bool}, e)
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      absurd_ft({D.text_class(B.Ctl{}) == True{} : Bool}, e)
    case B.High{}:
      {==}
    case B.Invalid{}:
      absurd_ft({D.text_class(B.Invalid{}) == True{} : Bool}, e)

# A digit char's class is kept by the line reader.
def dclass_plain(k: B.Class, e: {dclass(k) == True{} : Bool}) -> {plain(k) == True{} : Bool}:
  match k:
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
      absurd_ft({plain(B.Cr{}) == True{} : Bool}, e)
    case B.Lf{}:
      absurd_ft({plain(B.Lf{}) == True{} : Bool}, e)
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      absurd_ft({plain(B.Invalid{}) == True{} : Bool}, e)

# A digit char's class does not stop a split at SP.
def dclass_nosp(k: B.Class, e: {dclass(k) == True{} : Bool}) -> {Bool.not(D.stop_class(D.AtSp{}, k)) == True{} : Bool}:
  match k:
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
      absurd_ft({Bool.not(D.stop_class(D.AtSp{}, B.Sp{})) == True{} : Bool}, e)
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
      {==}


# Every digit char (0..15, and '?' past 15) has a digit-ish class.
def dc(d: Nat) -> {dclass(B.char_class(N.digit_char(d))) == True{} : Bool}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n+p:
      {==}

# A nonzero digit's char does not have the class Digit{0}.
def dc_nz(d: Nat, e: {nz_digit(d) == True{} : Bool}) -> {notzero(B.char_class(N.digit_char(d))) == True{} : Bool}:
  match d:
    case 0n:
      absurd_ft({notzero(B.char_class(N.digit_char(0n))) == True{} : Bool}, e)
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n:
      {==}
    case 11n:
      {==}
    case 12n:
      {==}
    case 13n:
      {==}
    case 14n:
      {==}
    case 15n:
      {==}
    case 16n+p:
      {==}

# A leading char of any class but Digit{0}: status_value reads the number.
def lead_ok(k: B.Class, -t: String, e: {notzero(k) == True{} : Bool})
  -> {D.status_value.lead(k, t) == D.status_value.of(N.read(t)) : Maybe<&2, Nat>}:
  match k:
    case B.Digit{v}:
      match v:
        case 0n:
          absurd_ft({D.status_value.lead(B.Digit{0n}, t) == D.status_value.of(N.read(t)) : Maybe<&2, Nat>}, e)
        case 1n+p:
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
      {==}

# String predicates and the loops of bytes / headers / decode
# -----------------------------------------------------------

# No char of s stops a split at stop.
def nostop(+stop: D.Stop, s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, t}:
      Bool.and(Bool.not(D.stops(stop, c)), nostop(stop, t))

def plain_app(a: String, -b: String, +ea: {plain_str(a) == True{} : Bool}, eb: {plain_str(b) == True{} : Bool})
  -> {plain_str(String.append(a, b)) == True{} : Bool}:
  match a:
    case SNil{}:
      eb
    case SCon{+c, t}:
      and_intro(plain(B.char_class(c)), plain_str(String.append(t, b)),
        and_l(plain(B.char_class(c)), plain_str(t), ea),
        plain_app(t, b, and_r(plain(B.char_class(c)), plain_str(t), ea), eb))

# The loop equations (decode.bend, headers.bend headers): go(s, ok) == ok && spec(s).
def all_text_go(s: String, ok: Bool) -> {D.all_text.go(s, ok) == Bool.and(ok, D.all_text.spec(s)) : Bool}:
  match s ok:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+c, t} True{}:
      all_text_go(t, D.text_class(B.char_class(c)))
    case SCon{c, t} False{}:
      all_text_go(t, False{})

def all_tchar_go(s: String, ok: Bool) -> {H.all_tchar.go(s, ok) == Bool.and(ok, H.all_tchar.spec(s)) : Bool}:
  match s ok:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+c, t} True{}:
      all_tchar_go(t, B.Class.is_tchar(B.char_class(c)))
    case SCon{c, t} False{}:
      all_tchar_go(t, False{})

def all_field_char_go(s: String, ok: Bool) -> {H.all_field_char.go(s, ok) == Bool.and(ok, H.all_field_char.spec(s)) : Bool}:
  match s ok:
    case SNil{} True{}:
      {==}
    case SNil{} False{}:
      {==}
    case SCon{+c, t} True{}:
      all_field_char_go(t, B.Class.is_field_char(B.char_class(c)))
    case SCon{c, t} False{}:
      all_field_char_go(t, False{})

def headers_ok_go(hs: List<&2, M.Header>, ok: Bool) -> {H.headers_ok.go(hs, ok) == Bool.and(ok, H.headers_ok.spec(hs)) : Bool}:
  match hs ok:
    case Nil{} True{}:
      {==}
    case Nil{} False{}:
      {==}
    case Con{+h, t} True{}:
      headers_ok_go(t, H.header_ok(h))
    case Con{h, t} False{}:
      headers_ok_go(t, False{})

def field_chars_plain(s: String, +e: {H.all_field_char.spec(s) == True{} : Bool}) -> {plain_str(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      and_intro(plain(B.char_class(c)), plain_str(t),
        field_plain(B.char_class(c), and_l(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t), e)),
        field_chars_plain(t, and_r(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t), e)))

def field_chars_text(s: String, +e: {H.all_field_char.spec(s) == True{} : Bool}) -> {D.all_text.spec(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      and_intro(D.text_class(B.char_class(c)), D.all_text.spec(t),
        field_text_class(B.char_class(c), and_l(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t), e)),
        field_chars_text(t, and_r(B.Class.is_field_char(B.char_class(c)), H.all_field_char.spec(t), e)))

def reason_plain(s: String, +e: {S.all_reason_char(s) == True{} : Bool}) -> {plain_str(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      and_intro(plain(B.char_class(c)), plain_str(t),
        field_plain(B.char_class(c), and_l(B.Class.is_field_char(B.char_class(c)), S.all_reason_char(t), e)),
        reason_plain(t, and_r(B.Class.is_field_char(B.char_class(c)), S.all_reason_char(t), e)))

def reason_text(s: String, +e: {S.all_reason_char(s) == True{} : Bool}) -> {D.all_text.spec(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      and_intro(D.text_class(B.char_class(c)), D.all_text.spec(t),
        field_text_class(B.char_class(c), and_l(B.Class.is_field_char(B.char_class(c)), S.all_reason_char(t), e)),
        reason_text(t, and_r(B.Class.is_field_char(B.char_class(c)), S.all_reason_char(t), e)))

def tchars_plain(s: String, +e: {H.all_tchar.spec(s) == True{} : Bool}) -> {plain_str(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      and_intro(plain(B.char_class(c)), plain_str(t),
        tchar_plain(B.char_class(c), and_l(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)),
        tchars_plain(t, and_r(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)))

def tchars_nocolon(s: String, +e: {H.all_tchar.spec(s) == True{} : Bool}) -> {nostop(D.AtColon{}, s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      and_intro(Bool.not(D.stops(D.AtColon{}, c)), nostop(D.AtColon{}, t),
        tchar_nocolon(B.char_class(c), and_l(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)),
        tchars_nocolon(t, and_r(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), e)))

# Decimal text
# ------------

# The digit chars of ds prepended to acc are plain, as acc is.
def dt_plain(ds: List<&2, Nat>, -acc: String, e: {plain_str(acc) == True{} : Bool})
  -> {plain_str(N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      e
    case Con{+d, t}:
      dt_plain(t, SCon{N.digit_char(d), acc},
        and_intro(plain(B.char_class(N.digit_char(d))), plain_str(acc),
          dclass_plain(B.char_class(N.digit_char(d)), dc(d)), e))

# ... and do not stop a split at SP.
def dt_nosp(ds: List<&2, Nat>, -acc: String, e: {nostop(D.AtSp{}, acc) == True{} : Bool})
  -> {nostop(D.AtSp{}, N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      e
    case Con{+d, t}:
      dt_nosp(t, SCon{N.digit_char(d), acc},
        and_intro(Bool.not(D.stops(D.AtSp{}, N.digit_char(d))), nostop(D.AtSp{}, acc),
          dclass_nosp(B.char_class(N.digit_char(d)), dc(d)), e))

# N.show(n) is plain and has no SP.
def show_plain(+n: Nat) -> {plain_str(N.show(n)) == True{} : Bool}:
  dt_plain(N.dec_digits(n), SNil{}, {==})

def show_nosp(+n: Nat) -> {nostop(D.AtSp{}, N.show(n)) == True{} : Bool}:
  dt_nosp(N.dec_digits(n), SNil{}, {==})

# The last (most significant) digit of the digit list t, after d.
def last_d(t: List<&2, Nat>, d: Nat) -> Nat:
  match t:
    case Nil{}:
      d
    case Con{d2, t2}:
      last_d(t2, d2)

# The text after the first char of digits_text(d <> t, acc).
def dt_rest(t: List<&2, Nat>, d: Nat, acc: String) -> String:
  match t:
    case Nil{}:
      acc
    case Con{d2, t2}:
      dt_rest(t2, d2, SCon{N.digit_char(d), acc})

# digits_text(d <> t, acc) starts with the char of the last digit.
def dt_head(t: List<&2, Nat>, d: Nat, -acc: String)
  -> {N.digits_text(Con{d, t}, acc) == SCon{N.digit_char(last_d(t, d)), dt_rest(t, d, acc)} : String}:
  match t:
    case Nil{}:
      {==}
    case Con{d2, t2}:
      dt_head(t2, d2, SCon{N.digit_char(d), acc})

# The last digit of d <> t is nonzero.
def nzl(t: List<&2, Nat>, d: Nat) -> Bool:
  match t:
    case Nil{}:
      nz_digit(d)
    case Con{d2, t2}:
      nzl(t2, d2)

# A digit list whose last (most significant) digit is nonzero.
def nz(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      nzl(t, d)

def nzl_last(t: List<&2, Nat>, d: Nat, e: {nzl(t, d) == True{} : Bool}) -> {nz_digit(last_d(t, d)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Con{d2, t2}:
      nzl_last(t2, d2, e)

def nzl_succ(t: List<&2, Nat>, -d: Nat, e: {nzl(t, d) == True{} : Bool}) -> {nzl(t, 1n+d) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{d2, t2}:
      e

def nzl_con(ds: List<&2, Nat>, -d: Nat, e: {nz(ds) == True{} : Bool}) -> {nzl(ds, d) == True{} : Bool}:
  match ds:
    case Nil{}:
      absurd_ft({nzl(Nil{}, d) == True{} : Bool}, e)
    case Con{y, z}:
      e

# A 9 that carries: the digits after it, counted up, have a nonzero lead.
def inc_nz_nine(t: List<&2, Nat>, e: {nzl(t, 9n) == True{} : Bool},
  ih: {nz(t) == True{} : Bool} -> {nz(N.dec_inc(t)) == True{} : Bool})
  -> {nzl(N.dec_inc(t), 0n) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{d2, t2}:
      nzl_con(N.dec_inc(Con{d2, t2}), 0n, ih(e))

# Counting up keeps the leading digit nonzero.
def inc_nz(ds: List<&2, Nat>, e: {nz(ds) == True{} : Bool}) -> {nz(N.dec_inc(ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      match d:
        case 0n:
          nzl_succ(t, 0n, e)
        case 1n:
          nzl_succ(t, 1n, e)
        case 2n:
          nzl_succ(t, 2n, e)
        case 3n:
          nzl_succ(t, 3n, e)
        case 4n:
          nzl_succ(t, 4n, e)
        case 5n:
          nzl_succ(t, 5n, e)
        case 6n:
          nzl_succ(t, 6n, e)
        case 7n:
          nzl_succ(t, 7n, e)
        case 8n:
          nzl_succ(t, 8n, e)
        case 9n:
          inc_nz_nine(t, e, x => inc_nz(t, x))
        case 10n+p:
          nzl_succ(t, 10n+p, e)

def count_nz(n: Nat, +ds: List<&2, Nat>, e: {nz(ds) == True{} : Bool}) -> {nz(N.dec_count(n, ds)) == True{} : Bool}:
  match n:
    case 0n:
      e
    case 1n+p:
      count_nz(p, N.dec_inc(ds), inc_nz(ds, e))

# The text of a digit list with a nonzero leading digit does not start with
# '0': status_value reads it as a number.
def status_value_lead(ds: List<&2, Nat>, e: {nz(ds) == True{} : Bool})
  -> {D.status_value(N.digits_text(ds, SNil{})) == D.status_value.of(N.read(N.digits_text(ds, SNil{}))) : Maybe<&2, Nat>}:
  match ds:
    case Nil{}:
      absurd_ft({D.status_value(N.digits_text(Nil{}, SNil{})) == D.status_value.of(N.read(N.digits_text(Nil{}, SNil{}))) : Maybe<&2, Nat>}, e)
    case Con{+d, +t}:
      %Equal.sym(String, N.digits_text(Con{d, t}, SNil{}), SCon{N.digit_char(last_d(t, d)), dt_rest(t, d, SNil{})}, dt_head(t, d, SNil{})) :
        {D.status_value(_) == D.status_value.of(N.read(_)) : Maybe<&2, Nat>}
      lead_ok(B.char_class(N.digit_char(last_d(t, d))), SCon{N.digit_char(last_d(t, d)), dt_rest(t, d, SNil{})},
        dc_nz(last_d(t, d), nzl_last(t, d, e)))

def sv_pick(-n: Nat, a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool})
  -> {D.status_value.pick(Bool.and(a, b), n) == Some{n} : Maybe<&2, Nat>}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd_ft({D.status_value.pick(False{}, n) == Some{n} : Maybe<&2, Nat>}, eb)
    case False{} y:
      absurd_ft({D.status_value.pick(False{}, n) == Some{n} : Maybe<&2, Nat>}, ea)

# A status 100..999 reads back from its decimal text (law 2, proofs/num.bend).
def status_value_show(st: Nat, e1: {Nat.is_le(100n, st) == True{} : Bool}, +e2: {Nat.is_le(st, 999n) == True{} : Bool})
  -> {D.status_value(N.show(st)) == Some{st} : Maybe<&2, Nat>}:
  match st:
    case 0n:
      absurd_ft({D.status_value(N.show(0n)) == Some{0n} : Maybe<&2, Nat>}, e1)
    case 1n+(+p):
      %Equal.sym(Maybe<&2, Nat>, D.status_value(N.show(1n+p)), D.status_value.of(N.read(N.show(1n+p))),
        status_value_lead(N.dec_count(p, [1n]), count_nz(p, [1n], {==}))) :
        {_ == Some{1n+p} : Maybe<&2, Nat>}
      %Equal.sym(Maybe<&2, Nat>, N.read(N.show(1n+p)), Some{1n+p},
        Laws.dec_roundtrip(1n+p, le_trans(1n+p, 999n, N.LIMIT(), e2, {==}))) :
        {D.status_value.of(_) == Some{1n+p} : Maybe<&2, Nat>}
      sv_pick(1n+p, Nat.is_le(100n, 1n+p), Nat.is_le(1n+p, 999n), e1, e2)

# Splits
# ------

# The char at hand stops the split: before it acc (reversed), after it b.
def split_hit(b: String, hit: Bool, -x: Char, -acc: String, -stop: D.Stop, e: {hit == True{} : Bool})
  -> {D.split.go(b, hit, x, acc, stop) == (String.reverse(acc), Some{b}) : String & Maybe<&2, String>}:
  match b hit:
    case SNil{} True{}:
      {==}
    case SCon{y, z} True{}:
      {==}
    case SNil{} False{}:
      absurd_ft({D.split.go(SNil{}, False{}, x, acc, stop) == (String.reverse(acc), Some{SNil{}}) : String & Maybe<&2, String>}, e)
    case SCon{y, z} False{}:
      absurd_ft({D.split.go(SCon{y, z}, False{}, x, acc, stop) == (String.reverse(acc), Some{SCon{y, z}}) : String & Maybe<&2, String>}, e)

# No char of a stops the split and d does: the split is at d.
def split_run(a: String, hit: Bool, x: Char, -acc: String, +stop: D.Stop, +d: Char, rest: String,
  eh: {hit == False{} : Bool}, +ea: {nostop(stop, a) == True{} : Bool}, ed: {D.stops(stop, d) == True{} : Bool})
  -> {D.split.go(String.append(a, SCon{d, rest}), hit, x, acc, stop)
      == (String.reverse(String.reverse.go(a, SCon{x, acc})), Some{rest}) : String & Maybe<&2, String>}:
  match a hit:
    case SNil{} True{}:
      absurd_ft({D.split.go(SCon{d, rest}, True{}, x, acc, stop)
        == (String.reverse(SCon{x, acc}), Some{rest}) : String & Maybe<&2, String>}, Equal.sym(Bool, True{}, False{}, eh))
    case SNil{} False{}:
      split_hit(rest, D.stops(stop, d), d, SCon{x, acc}, stop, ed)
    case SCon{+a1, a2} True{}:
      absurd_ft({D.split.go(SCon{a1, String.append(a2, SCon{d, rest})}, True{}, x, acc, stop)
        == (String.reverse(String.reverse.go(SCon{a1, a2}, SCon{x, acc})), Some{rest}) : String & Maybe<&2, String>}, Equal.sym(Bool, True{}, False{}, eh))
    case SCon{+a1, a2} False{}:
      split_run(a2, D.stops(stop, a1), a1, SCon{x, acc}, stop, d, rest,
        not_true(D.stops(stop, a1), and_l(Bool.not(D.stops(stop, a1)), nostop(stop, a2), ea)),
        and_r(Bool.not(D.stops(stop, a1)), nostop(stop, a2), ea), ed)

# split(stop, x a2 d rest) == (x a2, Some{rest}) when no char of x a2 stops it and d does.
def split_con(+x: Char, +a2: String, +stop: D.Stop, +d: Char, +rest: String,
  ex: {D.stops(stop, x) == False{} : Bool}, ea: {nostop(stop, a2) == True{} : Bool}, ed: {D.stops(stop, d) == True{} : Bool})
  -> {D.split(stop, SCon{x, String.append(a2, SCon{d, rest})}) == (SCon{x, a2}, Some{rest}) : String & Maybe<&2, String>}:
  Equal.trans(String & Maybe<&2, String>, D.split(stop, SCon{x, String.append(a2, SCon{d, rest})}),
    (String.reverse(String.reverse.go(a2, SCon{x, SNil{}})), Some{rest}), (SCon{x, a2}, Some{rest}),
    split_run(a2, D.stops(stop, x), x, SNil{}, stop, d, rest, ex, ea, ed),
    Equal.cong(String, String & Maybe<&2, String>, y => (y, Some{rest}),
      String.reverse(String.reverse.go(a2, SCon{x, SNil{}})), SCon{x, a2}, rev_single(a2, x)))

# Trims
# -----

def tl_go_false(t: String, ows: Bool, -c: Char, e: {ows == False{} : Bool}) -> {D.trim_left.go(t, ows, c) == SCon{c, t} : String}:
  match t ows:
    case SNil{} False{}:
      {==}
    case SCon{x, y} False{}:
      {==}
    case SNil{} True{}:
      absurd_ft({D.trim_left.go(SNil{}, True{}, c) == SCon{c, SNil{}} : String}, Equal.sym(Bool, True{}, False{}, e))
    case SCon{x, y} True{}:
      absurd_ft({D.trim_left.go(SCon{x, y}, True{}, c) == SCon{c, SCon{x, y}} : String}, Equal.sym(Bool, True{}, False{}, e))

# No leading OWS: trim_left keeps s.
def trim_left_id(s: String, e: {H.first_not_ows(s) == True{} : Bool}) -> {D.trim_left(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      tl_go_false(t, D.is_ows_char(c), c, not_true(D.is_ows_char(c), e))

# trim_left drops the SP after a field's ":" and stops at the value.
def trim_left_sp(v: String, e: {H.first_not_ows(v) == True{} : Bool}) -> {D.trim_left(SCon{' ', v}) == v : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{+x, y}:
      tl_go_false(y, D.is_ows_char(x), x, not_true(D.is_ows_char(x), e))

# The last char of c t, first after reversing.
def last_first(t: String, c: Char, -acc: String, e: {H.last_not_ows(SCon{c, t}) == True{} : Bool})
  -> {H.first_not_ows(String.reverse.go(t, SCon{c, acc})) == True{} : Bool}:
  match t:
    case SNil{}:
      e
    case SCon{d, u}:
      last_first(u, d, SCon{c, acc}, e)

# No trailing OWS: trim_right keeps v.
def trim_right_id(v: String, e: {H.last_not_ows(v) == True{} : Bool}) -> {D.trim_right(v) == v : String}:
  match v:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, D.trim_left(String.reverse.go(t, SCon{c, SNil{}})), String.reverse.go(t, SCon{c, SNil{}}),
        trim_left_id(String.reverse.go(t, SCon{c, SNil{}}), last_first(t, c, SNil{}, e))) :
        {String.reverse(_) == SCon{c, t} : String}
      rev_single(t, c)

# A sendable value after ": " is read back as it is.
def trim_value(+v: String, e1: {H.first_not_ows(v) == True{} : Bool}, e2: {H.last_not_ows(v) == True{} : Bool})
  -> {D.trim(SCon{' ', v}) == v : String}:
  %Equal.sym(String, D.trim_left(SCon{' ', v}), v, trim_left_sp(v, e1)) : {D.trim_right(_) == v : String}
  trim_right_id(v, e2)

# Status lines
# ------------

def mdisc(x: Maybe<&2, Nat>) -> Type:
  match x:
    case None{}:
      Unit
    case Some{n}:
      Empty

def none_ne_some(-n: Nat, e: {None{} == Some{n} : Maybe<&2, Nat>}) -> Empty:
  %e : mdisc(_)
  Unit{}

# After "HTTP/1.x": SP, the code x a2, SP, the reason rs.
def status_rest_parse(-v: M.Version, +x: Char, +a2: String, +rs: String, -n: Nat,
  e_sv: {D.status_value(SCon{x, a2}) == Some{n} : Maybe<&2, Nat>},
  +e_ns: {nostop(D.AtSp{}, SCon{x, a2}) == True{} : Bool},
  e_rs: {D.all_text.spec(rs) == True{} : Bool})
  -> {D.status.rest(v, SCon{' ', SCon{x, String.append(a2, SCon{' ', rs})}}) == D.line(D.KField{D.Head{v, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}:
  %Equal.sym(String & Maybe<&2, String>, D.split(D.AtSp{}, SCon{x, String.append(a2, SCon{' ', rs})}), (SCon{x, a2}, Some{rs}),
    split_con(x, a2, D.AtSp{}, ' ', rs,
      not_true(D.stops(D.AtSp{}, x), and_l(Bool.not(D.stops(D.AtSp{}, x)), nostop(D.AtSp{}, a2), e_ns)),
      and_r(Bool.not(D.stops(D.AtSp{}, x)), nostop(D.AtSp{}, a2), e_ns), {==})) :
    {D.status.parts(v, _) == D.line(D.KField{D.Head{v, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}
  %Equal.sym(Maybe<&2, Nat>, D.status_value(SCon{x, a2}), Some{n}, e_sv) :
    {D.status.head(v, _, D.reason_of.pick(D.all_text(rs), rs)) == D.line(D.KField{D.Head{v, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}
  %Equal.sym(Bool, D.all_text(rs), True{},
    Equal.trans(Bool, D.all_text(rs), Bool.and(True{}, D.all_text.spec(rs)), True{}, all_text_go(rs, True{}), e_rs)) :
    {D.status.head(v, Some{n}, D.reason_of.pick(_, rs)) == D.line(D.KField{D.Head{v, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}
  {==}

# The status line "HTTP/1.x SP a SP rs" reads back as version v, status n
# (the value of a) and reason rs, and the field lines follow.
def status_line_parse(v: M.Version, a: String, +rs: String, -n: Nat,
  e_sv: {D.status_value(a) == Some{n} : Maybe<&2, Nat>}, e_ns: {nostop(D.AtSp{}, a) == True{} : Bool},
  e_rs: {D.all_text.spec(rs) == True{} : Bool})
  -> {D.status_line(String.append(S.version_text(v), String.append(" ", String.append(a, String.append(" ", rs)))))
      == D.line(D.KField{D.Head{v, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}:
  match v a:
    case M.Http10{} SNil{}:
      Empty.absurd({D.status_line(String.append(S.version_text(M.Http10{}), String.append(" ", String.append(SNil{}, String.append(" ", rs)))))
        == D.line(D.KField{D.Head{M.Http10{}, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}, none_ne_some(n, e_sv))
    case M.Http10{} SCon{x, a2}:
      status_rest_parse(M.Http10{}, x, a2, rs, n, e_sv, e_ns, e_rs)
    case M.Http11{} SNil{}:
      Empty.absurd({D.status_line(String.append(S.version_text(M.Http11{}), String.append(" ", String.append(SNil{}, String.append(" ", rs)))))
        == D.line(D.KField{D.Head{M.Http11{}, n, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}, none_ne_some(n, e_sv))
    case M.Http11{} SCon{x, a2}:
      status_rest_parse(M.Http11{}, x, a2, rs, n, e_sv, e_ns, e_rs)

# The status line of a response, as the decoder reads it: its version,
# status and reason, then the field lines.
def status_end(-m: M.Method, -k: Nat, v: M.Version, +st: Nat, +rs: String, -hs: List<&2, M.Header>, -body: List<&2, U32>,
  e_sv: {D.status_value(N.show(st)) == Some{st} : Maybe<&2, Nat>}, e_rs: {S.all_reason_char(rs) == True{} : Bool})
  -> {D.line_end(m, k, D.KStatus{}, S.status_text(M.Response{v, st, rs, hs, body}))
      == D.line(D.KField{D.Head{v, st, rs, Nil{}, D.FIELDS_MAX()}}) : D.Phase}:
  status_line_parse(v, N.show(st), rs, st, e_sv, show_nosp(st), reason_text(rs, e_rs))

def version_plain(v: M.Version) -> {plain_str(S.version_text(v)) == True{} : Bool}:
  match v:
    case M.Http10{}:
      {==}
    case M.Http11{}:
      {==}

def status_plain(+v: M.Version, +st: Nat, +rs: String, -hs: List<&2, M.Header>, -body: List<&2, U32>,
  e_rs: {S.all_reason_char(rs) == True{} : Bool})
  -> {plain_str(S.status_text(M.Response{v, st, rs, hs, body})) == True{} : Bool}:
  plain_app(S.version_text(v), String.append(" ", String.append(N.show(st), String.append(" ", rs))), version_plain(v),
    plain_app(N.show(st), String.append(" ", rs), show_plain(st), reason_plain(rs, e_rs)))

# Field lines
# -----------

def tok_spec(+c: Char, +t: String, e: {H.is_token(SCon{c, t}) == True{} : Bool})
  -> {Bool.and(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t)) == True{} : Bool}:
  Equal.trans(Bool, Bool.and(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t)), H.all_tchar.go(t, B.Class.is_tchar(B.char_class(c))), True{},
    Equal.sym(Bool, H.all_tchar.go(t, B.Class.is_tchar(B.char_class(c))), Bool.and(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t)),
      all_tchar_go(t, B.Class.is_tchar(B.char_class(c)))), e)

def tok_plain(n: String, +e: {H.is_token(n) == True{} : Bool}) -> {plain_str(n) == True{} : Bool}:
  match n:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      and_intro(plain(B.char_class(c)), plain_str(t),
        tchar_plain(B.char_class(c), and_l(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), tok_spec(c, t, e))),
        tchars_plain(t, and_r(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), tok_spec(c, t, e))))

# H.is_value(v), taken apart.
def value_chars(+v: String, e: {H.is_value(v) == True{} : Bool}) -> {H.all_field_char.spec(v) == True{} : Bool}:
  Equal.trans(Bool, H.all_field_char.spec(v), H.all_field_char.go(v, True{}), True{},
    Equal.sym(Bool, H.all_field_char.go(v, True{}), Bool.and(True{}, H.all_field_char.spec(v)), all_field_char_go(v, True{})),
    and_l(H.all_field_char(v), H.first_not_ows(v), and_l(Bool.and(H.all_field_char(v), H.first_not_ows(v)), H.last_not_ows(v), e)))

def value_first(+v: String, e: {H.is_value(v) == True{} : Bool}) -> {H.first_not_ows(v) == True{} : Bool}:
  and_r(H.all_field_char(v), H.first_not_ows(v), and_l(Bool.and(H.all_field_char(v), H.first_not_ows(v)), H.last_not_ows(v), e))

def value_last(+v: String, e: {H.is_value(v) == True{} : Bool}) -> {H.last_not_ows(v) == True{} : Bool}:
  and_r(Bool.and(H.all_field_char(v), H.first_not_ows(v)), H.last_not_ows(v), e)

def value_text(+v: String, e: {H.is_value(v) == True{} : Bool}) -> {D.all_text(v) == True{} : Bool}:
  Equal.trans(Bool, D.all_text(v), Bool.and(True{}, D.all_text.spec(v)), True{}, all_text_go(v, True{}),
    field_chars_text(v, value_chars(v, e)))

def field_of_ok(-name: String, -value: String, a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool})
  -> {D.field.of(Bool.and(a, b), name, value) == Some{M.Header{name, value}} : Maybe<&2, M.Header>}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd_ft({D.field.of(False{}, name, value) == Some{M.Header{name, value}} : Maybe<&2, M.Header>}, eb)
    case False{} y:
      absurd_ft({D.field.of(False{}, name, value) == Some{M.Header{name, value}} : Maybe<&2, M.Header>}, ea)

# A header with a token name and a sendable value parses back from its
# field line's text.
def field_parse(n: String, +v: String, +e_tok: {H.is_token(n) == True{} : Bool}, +e_val: {H.is_value(v) == True{} : Bool})
  -> {D.parse_field(String.append(n, String.append(": ", v))) == Some{M.Header{n, v}} : Maybe<&2, M.Header>}:
  match n:
    case SNil{}:
      absurd_ft({D.parse_field(String.append(SNil{}, String.append(": ", v))) == Some{M.Header{SNil{}, v}} : Maybe<&2, M.Header>}, e_tok)
    case SCon{+c, +t}:
      %Equal.sym(String & Maybe<&2, String>, D.split(D.AtColon{}, SCon{c, String.append(t, SCon{':', SCon{' ', v}})}),
        (SCon{c, t}, Some{SCon{' ', v}}),
        split_con(c, t, D.AtColon{}, ':', SCon{' ', v},
          not_true(D.stops(D.AtColon{}, c),
            tchar_nocolon(B.char_class(c), and_l(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), tok_spec(c, t, e_tok)))),
          tchars_nocolon(t, and_r(B.Class.is_tchar(B.char_class(c)), H.all_tchar.spec(t), tok_spec(c, t, e_tok))),
          {==})) :
        {D.field.parts(_) == Some{M.Header{SCon{c, t}, v}} : Maybe<&2, M.Header>}
      %Equal.sym(String, D.trim(SCon{' ', v}), v, trim_value(v, value_first(v, e_val), value_last(v, e_val))) :
        {D.field.of(Bool.and(H.is_token(SCon{c, t}), D.all_text(_)), SCon{c, t}, _) == Some{M.Header{SCon{c, t}, v}} : Maybe<&2, M.Header>}
      field_of_ok(SCon{c, t}, v, H.is_token(SCon{c, t}), D.all_text(v), e_tok, value_text(v, e_val))

# A field line's end: the header joins the head (newest first), one less room.
def field_line_end(-m: M.Method, -k: Nat, -v: M.Version, -st: Nat, -rs: String, -acc: List<&2, M.Header>, -q: Nat,
  n: String, +val: String, e_tok: {H.is_token(n) == True{} : Bool}, e_val: {H.is_value(val) == True{} : Bool})
  -> {D.line_end(m, k, D.KField{D.Head{v, st, rs, acc, 1n+q}}, String.append(n, String.append(": ", val)))
      == D.line(D.KField{D.Head{v, st, rs, M.Header{n, val} <> acc, q}}) : D.Phase}:
  match n:
    case SNil{}:
      absurd_ft({D.line_end(m, k, D.KField{D.Head{v, st, rs, acc, 1n+q}}, String.append(SNil{}, String.append(": ", val)))
        == D.line(D.KField{D.Head{v, st, rs, M.Header{SNil{}, val} <> acc, q}}) : D.Phase}, e_tok)
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, M.Header>, D.parse_field(String.append(SCon{c, t}, String.append(": ", val))), Some{M.Header{SCon{c, t}, val}},
        field_parse(SCon{c, t}, val, e_tok, e_val)) :
        {D.field_add(D.Head{v, st, rs, acc, 1n+q}, _) == D.line(D.KField{D.Head{v, st, rs, M.Header{SCon{c, t}, val} <> acc, q}}) : D.Phase}
      {==}

def field_text_plain(+n: String, +val: String, e_tok: {H.is_token(n) == True{} : Bool}, e_val: {H.is_value(val) == True{} : Bool})
  -> {plain_str(S.field_text(M.Header{n, val})) == True{} : Bool}:
  plain_app(n, String.append(": ", val), tok_plain(n, e_tok), field_chars_plain(val, value_chars(val, e_val)))

# The phase when the head's last line (the empty one) ends, budget k left;
# hsr are the headers newest first.
def fields_end(m: M.Method, v: M.Version, st: Nat, rs: String, hsr: List<&2, M.Header>) -> Nat -> D.Phase:
  k => D.head_end(m, k, D.Head{v, st, rs, hsr, 0n})

def fields_nil(-m: M.Method, -v: M.Version, -st: Nat, -rs: String, -acc: List<&2, M.Header>, -room: Nat, b: Nat)
  -> {D.feed(D.State{m, b, D.line(D.KField{D.Head{v, st, rs, acc, room}})}, Laws.cat(S.field_bytes(Nil{}), [13, 10]))
      == charge(m, Laws.len(Laws.cat(S.field_bytes(Nil{}), [13, 10])), b, fields_end(m, v, st, rs, D.rev(M.Header, Nil{}, acc))) : D.State}:
  match b:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+c:
      {==}

def fields_bytes_eq(+h: M.Header, +t: List<&2, M.Header>)
  -> {Laws.cat(S.field_bytes(Con{h, t}), [13, 10]) == Laws.cat(line_bytes(S.field_text(h)), Laws.cat(S.field_bytes(t), [13, 10])) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, Laws.cat(S.field_bytes(Con{h, t}), [13, 10]),
    Laws.cat(B.from_ascii(S.field_line(h)), Laws.cat(S.field_bytes(t), [13, 10])),
    Laws.cat(line_bytes(S.field_text(h)), Laws.cat(S.field_bytes(t), [13, 10])),
    cat_assoc(B.from_ascii(S.field_line(h)), S.field_bytes(t), [13, 10]),
    Equal.cong(List<&2, U32>, List<&2, U32>, x => Laws.cat(x, Laws.cat(S.field_bytes(t), [13, 10])),
      B.from_ascii(S.field_line(h)), line_bytes(S.field_text(h)), line_bytes_eq(S.field_text(h))))

def fields_step(-m: M.Method, -v: M.Version, -st: Nat, -rs: String, -acc: List<&2, M.Header>, -q: Nat, n: String, +val: String,
  -t: List<&2, M.Header>, -k: Nat, e_tok: {H.is_token(n) == True{} : Bool}, e_val: {H.is_value(val) == True{} : Bool},
  ih: {D.feed(D.State{m, k, D.line(D.KField{D.Head{v, st, rs, M.Header{n, val} <> acc, q}})}, Laws.cat(S.field_bytes(t), [13, 10]))
       == charge(m, Laws.len(Laws.cat(S.field_bytes(t), [13, 10])), k, fields_end(m, v, st, rs, D.rev(M.Header, t, M.Header{n, val} <> acc))) : D.State})
  -> {D.feed(D.State{m, k, end_k(m, D.KField{D.Head{v, st, rs, acc, 1n+q}}, S.field_text(M.Header{n, val}))(k)}, Laws.cat(S.field_bytes(t), [13, 10]))
      == charge(m, Laws.len(Laws.cat(S.field_bytes(t), [13, 10])), k, fields_end(m, v, st, rs, D.rev(M.Header, t, M.Header{n, val} <> acc))) : D.State}:
  %Equal.sym(D.Phase, D.line_end(m, k, D.KField{D.Head{v, st, rs, acc, 1n+q}}, String.append(n, String.append(": ", val))),
    D.line(D.KField{D.Head{v, st, rs, M.Header{n, val} <> acc, q}}),
    field_line_end(m, k, v, st, rs, acc, q, n, val, e_tok, e_val)) :
    {D.feed(D.State{m, k, _}, Laws.cat(S.field_bytes(t), [13, 10]))
      == charge(m, Laws.len(Laws.cat(S.field_bytes(t), [13, 10])), k, fields_end(m, v, st, rs, D.rev(M.Header, t, M.Header{n, val} <> acc))) : D.State}
  ih

# The field lines lemma: the field lines of hs (valid, each within the line
# limit, at most room of them) then the empty line, read into a head that
# has acc so far, end the head with acc and hs (newest first).
def fields_feed(-m: M.Method, -v: M.Version, -st: Nat, -rs: String, hs: List<&2, M.Header>, -acc: List<&2, M.Header>, room: Nat, b: Nat,
  +e_ok: {H.headers_ok.spec(hs) == True{} : Bool}, +e_fit: {S.fields_fit(hs) == True{} : Bool},
  e_room: {Nat.is_le(List.length(&2, M.Header, hs), room) == True{} : Bool})
  -> {D.feed(D.State{m, b, D.line(D.KField{D.Head{v, st, rs, acc, room}})}, Laws.cat(S.field_bytes(hs), [13, 10]))
      == charge(m, Laws.len(Laws.cat(S.field_bytes(hs), [13, 10])), b, fields_end(m, v, st, rs, D.rev(M.Header, hs, acc))) : D.State}:
  match hs room b:
    case Nil{} r0 b0:
      fields_nil(m, v, st, rs, acc, r0, b0)
    case Con{h, t} 0n b0:
      absurd_ft({D.feed(D.State{m, b0, D.line(D.KField{D.Head{v, st, rs, acc, 0n}})}, Laws.cat(S.field_bytes(Con{h, t}), [13, 10]))
        == charge(m, Laws.len(Laws.cat(S.field_bytes(Con{h, t}), [13, 10])), b0, fields_end(m, v, st, rs, D.rev(M.Header, Con{h, t}, acc))) : D.State}, e_room)
    case Con{M.Header{+n, +val}, +t} 1n+q +b0:
      %Equal.sym(List<&2, U32>, Laws.cat(S.field_bytes(Con{M.Header{n, val}, t}), [13, 10]),
        Laws.cat(line_bytes(S.field_text(M.Header{n, val})), Laws.cat(S.field_bytes(t), [13, 10])),
        fields_bytes_eq(M.Header{n, val}, t)) :
        {D.feed(D.State{m, b0, D.line(D.KField{D.Head{v, st, rs, acc, 1n+q}})}, _)
          == charge(m, Laws.len(_), b0, fields_end(m, v, st, rs, D.rev(M.Header, Con{M.Header{n, val}, t}, acc))) : D.State}
      seg_seq(m, b0, D.line(D.KField{D.Head{v, st, rs, acc, 1n+q}}), line_bytes(S.field_text(M.Header{n, val})),
        Laws.cat(S.field_bytes(t), [13, 10]),
        end_k(m, D.KField{D.Head{v, st, rs, acc, 1n+q}}, S.field_text(M.Header{n, val})),
        fields_end(m, v, st, rs, D.rev(M.Header, t, M.Header{n, val} <> acc)),
        line_feed_text(m, D.KField{D.Head{v, st, rs, acc, 1n+q}}, S.field_text(M.Header{n, val}), D.LINE_MAX(), b0,
          field_text_plain(n, val,
            and_l(H.is_token(n), H.is_value(val), and_l(H.header_ok(M.Header{n, val}), H.headers_ok.spec(t), e_ok)),
            and_r(H.is_token(n), H.is_value(val), and_l(H.header_ok(M.Header{n, val}), H.headers_ok.spec(t), e_ok))),
          fits_crlf(S.field_text(M.Header{n, val}), D.LINE_MAX(),
            and_l(S.line_fits(S.field_line(M.Header{n, val})), S.fields_fit(t), e_fit))),
        k => fields_step(m, v, st, rs, acc, q, n, val, t, k,
          and_l(H.is_token(n), H.is_value(val), and_l(H.header_ok(M.Header{n, val}), H.headers_ok.spec(t), e_ok)),
          and_r(H.is_token(n), H.is_value(val), and_l(H.header_ok(M.Header{n, val}), H.headers_ok.spec(t), e_ok)),
          fields_feed(m, v, st, rs, t, M.Header{n, val} <> acc, q, k,
            and_r(H.header_ok(M.Header{n, val}), H.headers_ok.spec(t), e_ok),
            and_r(S.line_fits(S.field_line(M.Header{n, val})), S.fields_fit(t), e_fit), e_room)))

# The head
# --------

# The phase the decoder is in right after r's head, with budget k left: what
# D.head_end builds for r's version, status, reason and headers (then the
# framing decides: interim, upgrade, no body, chunked, length, close).
def head_phase(m: M.Method, k: Nat, r: M.Response) -> D.Phase:
  match r:
    case M.Response{+v, +st, rs, +hs, b}:
      D.framing.upgrade(Nat.is_eq(st, 101n), m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}})

def head_bytes_eq(+r: M.Response)
  -> {S.encode_head(r) == Laws.cat(line_bytes(S.status_text(r)), Laws.cat(S.field_bytes(S.response_headers(r)), [13, 10])) : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, x => Laws.cat(x, Laws.cat(S.field_bytes(S.response_headers(r)), [13, 10])),
    B.from_ascii(S.status_line(r)), line_bytes(S.status_text(r)), line_bytes_eq(S.status_text(r)))

def status_step(-m: M.Method, v: M.Version, +st: Nat, +rs: String, -hs: List<&2, M.Header>, -body: List<&2, U32>, -k: Nat,
  e_sv: {D.status_value(N.show(st)) == Some{st} : Maybe<&2, Nat>}, e_rs: {S.all_reason_char(rs) == True{} : Bool},
  ih: {D.feed(D.State{m, k, D.line(D.KField{D.Head{v, st, rs, Nil{}, D.FIELDS_MAX()}})}, Laws.cat(S.field_bytes(hs), [13, 10]))
       == charge(m, Laws.len(Laws.cat(S.field_bytes(hs), [13, 10])), k, fields_end(m, v, st, rs, D.rev(M.Header, hs, Nil{}))) : D.State})
  -> {D.feed(D.State{m, k, end_k(m, D.KStatus{}, S.status_text(M.Response{v, st, rs, hs, body}))(k)}, Laws.cat(S.field_bytes(hs), [13, 10]))
      == charge(m, Laws.len(Laws.cat(S.field_bytes(hs), [13, 10])), k, fields_end(m, v, st, rs, D.rev(M.Header, hs, Nil{}))) : D.State}:
  %Equal.sym(D.Phase, D.line_end(m, k, D.KStatus{}, S.status_text(M.Response{v, st, rs, hs, body})),
    D.line(D.KField{D.Head{v, st, rs, Nil{}, D.FIELDS_MAX()}}), status_end(m, k, v, st, rs, hs, body, e_sv, e_rs)) :
    {D.feed(D.State{m, k, _}, Laws.cat(S.field_bytes(hs), [13, 10]))
      == charge(m, Laws.len(Laws.cat(S.field_bytes(hs), [13, 10])), k, fields_end(m, v, st, rs, D.rev(M.Header, hs, Nil{}))) : D.State}
  ih

# The head lemma, by parts (head_feed below takes S.head_ok whole).
def head_feed_parts(-m: M.Method, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>, +b: Nat,
  e_sv: {D.status_value(N.show(st)) == Some{st} : Maybe<&2, Nat>},
  +e_rs: {S.all_reason_char(rs) == True{} : Bool},
  e_ok: {H.headers_ok.spec(hs) == True{} : Bool},
  e_fs: {S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})) == True{} : Bool},
  e_fit: {S.fields_fit(hs) == True{} : Bool},
  e_cnt: {Nat.is_le(List.length(&2, M.Header, hs), D.FIELDS_MAX()) == True{} : Bool})
  -> {D.feed(D.init(m, b), S.encode_head(M.Response{v, st, rs, hs, body}))
      == charge(m, Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), b, k => head_phase(m, k, M.Response{v, st, rs, hs, body})) : D.State}:
  %Equal.sym(List<&2, U32>, S.encode_head(M.Response{v, st, rs, hs, body}),
    Laws.cat(line_bytes(S.status_text(M.Response{v, st, rs, hs, body})), Laws.cat(S.field_bytes(hs), [13, 10])),
    head_bytes_eq(M.Response{v, st, rs, hs, body})) :
    {D.feed(D.init(m, b), _) == charge(m, Laws.len(_), b, k => head_phase(m, k, M.Response{v, st, rs, hs, body})) : D.State}
  %rev_rev(M.Header, hs) :
    {D.feed(D.init(m, b), Laws.cat(line_bytes(S.status_text(M.Response{v, st, rs, hs, body})), Laws.cat(S.field_bytes(hs), [13, 10])))
      == charge(m, Laws.len(Laws.cat(line_bytes(S.status_text(M.Response{v, st, rs, hs, body})), Laws.cat(S.field_bytes(hs), [13, 10]))), b,
           k => D.framing.upgrade(Nat.is_eq(st, 101n), m, v, k, st, _, M.Response{v, st, rs, _, Nil{}})) : D.State}
  seg_seq(m, b, D.line(D.KStatus{}), line_bytes(S.status_text(M.Response{v, st, rs, hs, body})), Laws.cat(S.field_bytes(hs), [13, 10]),
    end_k(m, D.KStatus{}, S.status_text(M.Response{v, st, rs, hs, body})), fields_end(m, v, st, rs, D.rev(M.Header, hs, Nil{})),
    line_feed_text(m, D.KStatus{}, S.status_text(M.Response{v, st, rs, hs, body}), D.LINE_MAX(), b,
      status_plain(v, st, rs, hs, body, e_rs), fits_crlf(S.status_text(M.Response{v, st, rs, hs, body}), D.LINE_MAX(), e_fs)),
    k => status_step(m, v, st, rs, hs, body, k, e_sv, e_rs, fields_feed(m, v, st, rs, hs, Nil{}, D.FIELDS_MAX(), k, e_ok, e_fit, e_cnt)))

# S.head_ok, taken apart (all_reason_char && headers_ok && head_fits, the
# last being line_fits(status line) && fields_fit && count <= FIELDS_MAX).
def head_ok_reason(+v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  e: {S.head_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool}) -> {S.all_reason_char(rs) == True{} : Bool}:
  and_l(S.all_reason_char(rs), H.headers_ok(hs),
    and_l(Bool.and(S.all_reason_char(rs), H.headers_ok(hs)), S.head_fits(M.Response{v, st, rs, hs, body}), e))

def head_ok_headers(+v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  e: {S.head_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool}) -> {H.headers_ok.spec(hs) == True{} : Bool}:
  Equal.trans(Bool, H.headers_ok.spec(hs), H.headers_ok(hs), True{},
    Equal.sym(Bool, H.headers_ok(hs), Bool.and(True{}, H.headers_ok.spec(hs)), headers_ok_go(hs, True{})),
    and_r(S.all_reason_char(rs), H.headers_ok(hs),
      and_l(Bool.and(S.all_reason_char(rs), H.headers_ok(hs)), S.head_fits(M.Response{v, st, rs, hs, body}), e)))

def head_ok_fits(+v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  e: {S.head_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool}) -> {S.head_fits(M.Response{v, st, rs, hs, body}) == True{} : Bool}:
  and_r(Bool.and(S.all_reason_char(rs), H.headers_ok(hs)), S.head_fits(M.Response{v, st, rs, hs, body}), e)

def head_fits_status(+v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  e: {S.head_fits(M.Response{v, st, rs, hs, body}) == True{} : Bool})
  -> {S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})) == True{} : Bool}:
  and_l(S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})), S.fields_fit(hs),
    and_l(Bool.and(S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})), S.fields_fit(hs)),
      Nat.is_le(List.length(&2, M.Header, hs), D.FIELDS_MAX()), e))

def head_fits_fields(+v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  e: {S.head_fits(M.Response{v, st, rs, hs, body}) == True{} : Bool}) -> {S.fields_fit(hs) == True{} : Bool}:
  and_r(S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})), S.fields_fit(hs),
    and_l(Bool.and(S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})), S.fields_fit(hs)),
      Nat.is_le(List.length(&2, M.Header, hs), D.FIELDS_MAX()), e))

def head_fits_count(+v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  e: {S.head_fits(M.Response{v, st, rs, hs, body}) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, M.Header, hs), D.FIELDS_MAX()) == True{} : Bool}:
  and_r(Bool.and(S.line_fits(S.status_line(M.Response{v, st, rs, hs, body})), S.fields_fit(hs)),
    Nat.is_le(List.length(&2, M.Header, hs), D.FIELDS_MAX()), e)

# THE HEAD LEMMA. For any method m and budget b: if r's status reads back
# from its text (e_sv; status_value_show gives it for 100..999) and its head
# is valid (S.head_ok), feeding S.encode_head(r) to init(m, b) is a run of
# len(head) bytes ending in head_phase(m, k, r) (k the budget left), or in
# TooLarge if b < len(head).
def head_feed(-m: M.Method, r: M.Response, +b: Nat,
  e_sv: {D.status_value(N.show(S.response_status(r))) == Some{S.response_status(r)} : Maybe<&2, Nat>},
  +e_ok: {S.head_ok(r) == True{} : Bool})
  -> {D.feed(D.init(m, b), S.encode_head(r)) == charge(m, Laws.len(S.encode_head(r)), b, k => head_phase(m, k, r)) : D.State}:
  match r:
    case M.Response{+v, +st, +rs, +hs, +body}:
      head_feed_parts(m, v, st, rs, hs, body, b, e_sv,
        head_ok_reason(v, st, rs, hs, body, e_ok), head_ok_headers(v, st, rs, hs, body, e_ok),
        head_fits_status(v, st, rs, hs, body, head_ok_fits(v, st, rs, hs, body, e_ok)),
        head_fits_fields(v, st, rs, hs, body, head_ok_fits(v, st, rs, hs, body, e_ok)),
        head_fits_count(v, st, rs, hs, body, head_ok_fits(v, st, rs, hs, body, e_ok)))

# The head lemma with what follows the head: feeding head ++ ys from init(m, b)
# is feeding ys after the run of the head.
def head_charge(-m: M.Method, +r: M.Response, +b: Nat, +ys: List<&2, U32>,
  e_sv: {D.status_value(N.show(S.response_status(r))) == Some{S.response_status(r)} : Maybe<&2, Nat>},
  e_ok: {S.head_ok(r) == True{} : Bool})
  -> {D.feed(D.init(m, b), Laws.cat(S.encode_head(r), ys))
      == D.feed(charge(m, Laws.len(S.encode_head(r)), b, k => head_phase(m, k, r)), ys) : D.State}:
  Equal.trans(D.State, D.feed(D.init(m, b), Laws.cat(S.encode_head(r), ys)), D.feed(D.feed(D.init(m, b), S.encode_head(r)), ys),
    D.feed(charge(m, Laws.len(S.encode_head(r)), b, k => head_phase(m, k, r)), ys),
    Equal.sym(D.State, D.feed(D.feed(D.init(m, b), S.encode_head(r)), ys), D.feed(D.init(m, b), Laws.cat(S.encode_head(r), ys)),
      feed_cat(D.init(m, b), S.encode_head(r), ys)),
    Equal.cong(D.State, D.State, x => D.feed(x, ys), D.feed(D.init(m, b), S.encode_head(r)),
      charge(m, Laws.len(S.encode_head(r)), b, k => head_phase(m, k, r)), head_feed(m, r, b, e_sv, e_ok)))

# The head lemma with a budget that covers the head: len(head) + K leaves K.
#   feed(init(m, len(head) + K), head ++ ys) == feed(State{m, K, head_phase(m, K, r)}, ys)
def head_at(-m: M.Method, +r: M.Response, +kk: Nat, +ys: List<&2, U32>,
  e_sv: {D.status_value(N.show(S.response_status(r))) == Some{S.response_status(r)} : Maybe<&2, Nat>},
  e_ok: {S.head_ok(r) == True{} : Bool})
  -> {D.feed(D.init(m, Nat.add(Laws.len(S.encode_head(r)), kk)), Laws.cat(S.encode_head(r), ys))
      == D.feed(D.State{m, kk, head_phase(m, kk, r)}, ys) : D.State}:
  %Equal.sym(D.State, D.feed(D.init(m, Nat.add(Laws.len(S.encode_head(r)), kk)), Laws.cat(S.encode_head(r), ys)),
    D.feed(charge(m, Laws.len(S.encode_head(r)), Nat.add(Laws.len(S.encode_head(r)), kk), k => head_phase(m, k, r)), ys),
    head_charge(m, r, Nat.add(Laws.len(S.encode_head(r)), kk), ys, e_sv, e_ok)) :
    {_ == D.feed(D.State{m, kk, head_phase(m, kk, r)}, ys) : D.State}
  %Equal.sym(D.State, charge(m, Laws.len(S.encode_head(r)), Nat.add(Laws.len(S.encode_head(r)), kk), k => head_phase(m, k, r)),
    D.State{m, kk, head_phase(m, kk, r)}, charge_exact(m, Laws.len(S.encode_head(r)), kk, k => head_phase(m, k, r))) :
    {D.feed(_, ys) == D.feed(D.State{m, kk, head_phase(m, kk, r)}, ys) : D.State}
  {==}

# Framing after the head
# ----------------------

# A final status (not 101, not 1xx) with no body (HEAD, 204, 304): complete.
def head_phase_complete(-m: M.Method, -k: Nat, -v: M.Version, +st: Nat, -rs: String, -hs: List<&2, M.Header>, -body: List<&2, U32>,
  e101: {Nat.is_eq(st, 101n) == False{} : Bool}, elt: {Nat.is_lt(st, 200n) == False{} : Bool},
  e_nb: {D.no_body(m, st) == True{} : Bool})
  -> {head_phase(m, k, M.Response{v, st, rs, hs, body}) == D.Complete{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}:
  %Equal.sym(Bool, Nat.is_eq(st, 101n), False{}, e101) :
    {D.framing.upgrade(_, m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}}) == D.Complete{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}
  %Equal.sym(Bool, Nat.is_lt(st, 200n), False{}, elt) :
    {D.framing.interim(_, m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}}) == D.Complete{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}
  %Equal.sym(Bool, D.no_body(m, st), True{}, e_nb) :
    {D.framing.empty(_, v, k, hs, M.Response{v, st, rs, hs, Nil{}}) == D.Complete{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}
  {==}

# An interim status (1xx, not 101): the next status line follows.
def head_phase_interim(-m: M.Method, -k: Nat, -v: M.Version, +st: Nat, -rs: String, -hs: List<&2, M.Header>, -body: List<&2, U32>,
  e101: {Nat.is_eq(st, 101n) == False{} : Bool}, elt: {Nat.is_lt(st, 200n) == True{} : Bool})
  -> {head_phase(m, k, M.Response{v, st, rs, hs, body}) == D.line(D.KStatus{}) : D.Phase}:
  %Equal.sym(Bool, Nat.is_eq(st, 101n), False{}, e101) :
    {D.framing.upgrade(_, m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}}) == D.line(D.KStatus{}) : D.Phase}
  %Equal.sym(Bool, Nat.is_lt(st, 200n), True{}, elt) :
    {D.framing.interim(_, m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}}) == D.line(D.KStatus{}) : D.Phase}
  {==}

# A final status with a body: the framing headers decide (RFC 9112 6.3, 4.-6.).
def head_phase_body(-m: M.Method, -k: Nat, -v: M.Version, +st: Nat, -rs: String, -hs: List<&2, M.Header>, -body: List<&2, U32>,
  e101: {Nat.is_eq(st, 101n) == False{} : Bool}, elt: {Nat.is_lt(st, 200n) == False{} : Bool},
  e_nb: {D.no_body(m, st) == False{} : Bool})
  -> {head_phase(m, k, M.Response{v, st, rs, hs, body})
      == D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}}) : D.Phase}:
  %Equal.sym(Bool, Nat.is_eq(st, 101n), False{}, e101) :
    {D.framing.upgrade(_, m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}})
      == D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}}) : D.Phase}
  %Equal.sym(Bool, Nat.is_lt(st, 200n), False{}, elt) :
    {D.framing.interim(_, m, v, k, st, hs, M.Response{v, st, rs, hs, Nil{}})
      == D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}}) : D.Phase}
  %Equal.sym(Bool, D.no_body(m, st), False{}, e_nb) :
    {D.framing.empty(_, v, k, hs, M.Response{v, st, rs, hs, Nil{}})
      == D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}}) : D.Phase}
  {==}

# Transfer-Encoding with any Content-Length: ConflictingFraming.
def te_conflict(-v: M.Version, te: List<&2, String>, -cl: List<&2, String>, -k: Nat, -r: M.Response,
  e_te: {D.nonempty(te) == True{} : Bool}, e_cl: {D.nonempty(cl) == True{} : Bool})
  -> {D.framing.te(v, te, cl, k, r) == D.Failed{M.ConflictingFraming{}} : D.Phase}:
  match te:
    case Nil{}:
      absurd_ft({D.framing.te(v, Nil{}, cl, k, r) == D.Failed{M.ConflictingFraming{}} : D.Phase}, e_te)
    case Con{x, t}:
      %Equal.sym(Bool, D.nonempty(cl), True{}, e_cl) :
        {D.te_framing(_, D.is_http10(v), D.chunked_only(Con{x, t}), r) == D.Failed{M.ConflictingFraming{}} : D.Phase}
      {==}

# Header lookup
# -------------

def brev_ne(xs: List<&2, String>, -y: String, -ys: List<&2, String>) -> {D.nonempty(B.rev(String, xs, Con{y, ys})) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      brev_ne(t, h, Con{y, ys})

def ga_pick(-l: String, -t: List<&2, M.Header>, hit: Bool, -v: String, -x: String, -xs: List<&2, String>,
  i1: {D.nonempty(H.get_all.go(l, t, Con{v, Con{x, xs}})) == True{} : Bool},
  i2: {D.nonempty(H.get_all.go(l, t, Con{x, xs})) == True{} : Bool})
  -> {D.nonempty(H.get_all.go(l, t, H.get_all.pick(hit, v, Con{x, xs}))) == True{} : Bool}:
  match hit:
    case True{}:
      i1
    case False{}:
      i2

# Once a value is found, get_all finds at least one.
def ga_ne(+l: String, hs: List<&2, M.Header>, +x: String, +xs: List<&2, String>)
  -> {D.nonempty(H.get_all.go(l, hs, Con{x, xs})) == True{} : Bool}:
  match hs:
    case Nil{}:
      brev_ne(xs, x, Nil{})
    case Con{M.Header{+n, +v}, +t}:
      ga_pick(l, t, String.eq(l, H.lower(n)), v, x, xs, ga_ne(l, t, v, Con{x, xs}), ga_ne(l, t, x, xs))

def hb_pick(-l: String, -t: List<&2, M.Header>, hit: Bool, -v: String, e: {H.has.go(l, t, hit) == True{} : Bool},
  ih: {H.has.go(l, t, False{}) == True{} : Bool} -> {D.nonempty(H.get_all.go(l, t, Nil{})) == True{} : Bool},
  ne: {D.nonempty(H.get_all.go(l, t, Con{v, Nil{}})) == True{} : Bool})
  -> {D.nonempty(H.get_all.go(l, t, H.get_all.pick(hit, v, Nil{}))) == True{} : Bool}:
  match hit:
    case True{}:
      ne
    case False{}:
      ih(e)

def has_ne(+l: String, hs: List<&2, M.Header>, e: {H.has.go(l, hs, False{}) == True{} : Bool})
  -> {D.nonempty(H.get_all.go(l, hs, Nil{})) == True{} : Bool}:
  match hs:
    case Nil{}:
      absurd_ft({D.nonempty(H.get_all.go(l, Nil{}, Nil{})) == True{} : Bool}, e)
    case Con{M.Header{+n, +v}, +t}:
      hb_pick(l, t, String.eq(l, H.lower(n)), v, e, x => has_ne(l, t, x), ga_ne(l, t, v, Nil{}))

# H.has(name, hs): get_all(name, hs) is not empty.
def has_get_all(+name: String, hs: List<&2, M.Header>, e: {H.has(name, hs) == True{} : Bool})
  -> {D.nonempty(H.get_all(name, hs)) == True{} : Bool}:
  has_ne(H.lower(name), hs, e)

# Content-Length with Transfer-Encoding, after a final head with a body: conflict.
def head_phase_conflict(-m: M.Method, +k: Nat, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, -body: List<&2, U32>,
  e101: {Nat.is_eq(st, 101n) == False{} : Bool}, elt: {Nat.is_lt(st, 200n) == False{} : Bool},
  e_nb: {D.no_body(m, st) == False{} : Bool},
  e_cl: {H.has("content-length", hs) == True{} : Bool}, e_te: {H.has("transfer-encoding", hs) == True{} : Bool})
  -> {head_phase(m, k, M.Response{v, st, rs, hs, body}) == D.Failed{M.ConflictingFraming{}} : D.Phase}:
  Equal.trans(D.Phase, head_phase(m, k, M.Response{v, st, rs, hs, body}),
    D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}}),
    D.Failed{M.ConflictingFraming{}},
    head_phase_body(m, k, v, st, rs, hs, body, e101, elt, e_nb),
    te_conflict(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}},
      has_get_all("transfer-encoding", hs, e_te), has_get_all("content-length", hs, e_cl)))

# Statuses
# --------

def absurd_tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  absurd_ft(A, Equal.sym(Bool, True{}, False{}, e))

def or3_false(a: Bool, b: Bool, c: Bool, ea: {a == False{} : Bool}, eb: {b == False{} : Bool}, ec: {c == False{} : Bool})
  -> {Bool.or(Bool.or(a, b), c) == False{} : Bool}:
  match a b c:
    case False{} False{} False{}:
      {==}
    case False{} False{} True{}:
      absurd_tf({True{} == False{} : Bool}, ec)
    case False{} True{} z:
      absurd_tf({Bool.or(True{}, z) == False{} : Bool}, eb)
    case True{} y z:
      absurd_tf({Bool.or(True{}, z) == False{} : Bool}, ea)

# Not HEAD, not 204, not 304: the response has a body.
def no_body_false(+m: M.Method, +st: Nat, eh: {D.is_head(m) == False{} : Bool},
  e204: {Nat.is_eq(st, 204n) == False{} : Bool}, e304: {Nat.is_eq(st, 304n) == False{} : Bool})
  -> {D.no_body(m, st) == False{} : Bool}:
  or3_false(D.is_head(m), Nat.is_eq(st, 204n), Nat.is_eq(st, 304n), eh, e204, e304)

# 200 <= st: not 101, not 1xx.
def final_not_101(+st: Nat, e: {Nat.is_le(200n, st) == True{} : Bool}) -> {Nat.is_eq(st, 101n) == False{} : Bool}:
  le_ne(101n, st, le_trans(102n, 200n, st, {==}, e))

def final_not_lt(+st: Nat, e: {Nat.is_le(200n, st) == True{} : Bool}) -> {Nat.is_lt(st, 200n) == False{} : Bool}:
  le_not_lt(200n, st, e)

# S.body_status_ok(st), taken apart (100 <= st, st <= 999, not 101, not
# below 200, not 204, not 304, nested to the left).
def bs1(+st: Nat) -> Bool:
  Bool.and(Nat.is_le(100n, st), Nat.is_le(st, 999n))

def bs2(+st: Nat) -> Bool:
  Bool.and(bs1(st), Bool.not(Nat.is_eq(st, 101n)))

def bs3(+st: Nat) -> Bool:
  Bool.and(bs2(st), Bool.not(Nat.is_lt(st, 200n)))

def bs4(+st: Nat) -> Bool:
  Bool.and(bs3(st), Bool.not(Nat.is_eq(st, 204n)))

def bs_100(+st: Nat, e: {S.body_status_ok(st) == True{} : Bool}) -> {Nat.is_le(100n, st) == True{} : Bool}:
  and_l(Nat.is_le(100n, st), Nat.is_le(st, 999n), and_l(bs1(st), Bool.not(Nat.is_eq(st, 101n)),
    and_l(bs2(st), Bool.not(Nat.is_lt(st, 200n)), and_l(bs3(st), Bool.not(Nat.is_eq(st, 204n)),
      and_l(bs4(st), Bool.not(Nat.is_eq(st, 304n)), e)))))

def bs_999(+st: Nat, e: {S.body_status_ok(st) == True{} : Bool}) -> {Nat.is_le(st, 999n) == True{} : Bool}:
  and_r(Nat.is_le(100n, st), Nat.is_le(st, 999n), and_l(bs1(st), Bool.not(Nat.is_eq(st, 101n)),
    and_l(bs2(st), Bool.not(Nat.is_lt(st, 200n)), and_l(bs3(st), Bool.not(Nat.is_eq(st, 204n)),
      and_l(bs4(st), Bool.not(Nat.is_eq(st, 304n)), e)))))

def bs_101(+st: Nat, e: {S.body_status_ok(st) == True{} : Bool}) -> {Nat.is_eq(st, 101n) == False{} : Bool}:
  not_true(Nat.is_eq(st, 101n), and_r(bs1(st), Bool.not(Nat.is_eq(st, 101n)),
    and_l(bs2(st), Bool.not(Nat.is_lt(st, 200n)), and_l(bs3(st), Bool.not(Nat.is_eq(st, 204n)),
      and_l(bs4(st), Bool.not(Nat.is_eq(st, 304n)), e)))))

def bs_200(+st: Nat, e: {S.body_status_ok(st) == True{} : Bool}) -> {Nat.is_lt(st, 200n) == False{} : Bool}:
  not_true(Nat.is_lt(st, 200n), and_r(bs2(st), Bool.not(Nat.is_lt(st, 200n)),
    and_l(bs3(st), Bool.not(Nat.is_eq(st, 204n)), and_l(bs4(st), Bool.not(Nat.is_eq(st, 304n)), e))))

def bs_204(+st: Nat, e: {S.body_status_ok(st) == True{} : Bool}) -> {Nat.is_eq(st, 204n) == False{} : Bool}:
  not_true(Nat.is_eq(st, 204n), and_r(bs3(st), Bool.not(Nat.is_eq(st, 204n)),
    and_l(bs4(st), Bool.not(Nat.is_eq(st, 304n)), e)))

def bs_304(+st: Nat, e: {S.body_status_ok(st) == True{} : Bool}) -> {Nat.is_eq(st, 304n) == False{} : Bool}:
  not_true(Nat.is_eq(st, 304n), and_r(bs4(st), Bool.not(Nat.is_eq(st, 304n)), e))

# S.response_ok(r), taken apart.
def response_ok_status(+r: M.Response, e: {S.response_ok(r) == True{} : Bool})
  -> {S.body_status_ok(S.response_status(r)) == True{} : Bool}:
  and_l(S.body_status_ok(S.response_status(r)), S.head_ok(r), e)

def response_ok_head(+r: M.Response, e: {S.response_ok(r) == True{} : Bool}) -> {S.head_ok(r) == True{} : Bool}:
  and_r(S.body_status_ok(S.response_status(r)), S.head_ok(r), e)

# The end of input
# ----------------

# A run whose every end is the failure e fails, whatever the budget (a short
# budget fails with TooLarge).
def charge_fail_feed(-m: M.Method, n: Nat, b: Nat, -f: Nat -> D.Phase, -e: M.ParseError, ys: List<&2, U32>,
  hf: @k: Nat -> {f(k) == D.Failed{e} : D.Phase})
  -> {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.finish(D.feed(charge(m, n, b, f), ys))) == True{} : Bool}:
  match n b:
    case 0n b0:
      %Equal.sym(D.Phase, f(b0), D.Failed{e}, hf(b0)) :
        {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.finish(D.feed(D.State{m, b0, _}, ys))) == True{} : Bool}
      %Equal.sym(D.State, D.feed(D.State{m, b0, D.Failed{e}}, ys), D.State{m, b0, D.Failed{e}}, feed_failed(m, b0, e, ys)) :
        {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.finish(_)) == True{} : Bool}
      {==}
    case 1n+p 0n:
      %Equal.sym(D.State, D.feed(D.State{m, 0n, D.Failed{M.TooLarge{}}}, ys), D.State{m, 0n, D.Failed{M.TooLarge{}}},
        feed_failed(m, 0n, M.TooLarge{}, ys)) :
        {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.finish(_)) == True{} : Bool}
      {==}
    case 1n+p 1n+c:
      charge_fail_feed(m, p, c, f, e, ys, hf)
