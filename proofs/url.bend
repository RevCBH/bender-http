# Law 17: a valid URL shows and parses back to itself.
#
# show(Url{s, h, p, t}) is scheme "://" h pt t, with pt = port_text(s, p)
# ("" or ":" digits). parse computes through the scheme and "://" (concrete
# chars), then meets cut_auth(h ++ (pt ++ t)). The proof:
#   - per-char facts on the UClass: a host char (Lower, Num, Dash, Dot) and a
#     port char (Num, Colon) are "plain": not '/', '?', '#', '@' or a bracket;
#     a host char is not ':' either, and is not uppercase, so lower leaves it;
#   - cut_auth(x ++ r) == Cut{x ++ a, b} when cut_auth(r) == Cut{a, b} and x is
#     plain (cut_colon likewise for a host x); t starts with '/', so
#     cut_auth(t) == Cut{"", t}, and the authority is h ++ pt;
#   - the authority has no '@' or bracket; cut at ':' it is h and pt;
#   - host_of(h) == Done{h} (lower(h) == h, host_ok(h) by hypothesis);
#     port_of gives p back: from Nat.is_eq(p, default) for "", and from
#     read(show(p)) == Some{p} (law 2, p <= 65535 <= LIMIT) for ":" digits;
#   - target_of(t) == Done{t}: t starts with '/' and holds no '#', so
#     before_hash leaves it.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/url.bend as U
import ../proofs/num.bend as NP

def SRes() -> Type:
  Result<&2, &2, M.Error, String>

def PRes() -> Type:
  Result<&2, &2, M.Error, Nat>

# Small facts
# -----------

def url_no(-A: Type, +e: {False{} == True{} : Bool}) -> A:
  Empty.absurd(A, NP.false_true(e))

def url_and_intro(a: Bool, -b: Bool, +ea: {a == True{} : Bool}, +eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      eb
    case False{}:
      url_no({Bool.and(False{}, b) == True{} : Bool}, ea)

def url_maybe_disc(m: Maybe<&2, Nat>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      Empty

def url_none_some(-p: Nat, +e: {None{} == Some{p} : Maybe<&2, Nat>}) -> Empty:
  %e : url_maybe_disc(_)
  Unit{}

def url_is_eq(a: Nat, +b: Nat, +e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          url_no({0n == 1n+q : Nat}, e)
    case 1n+k:
      match b:
        case 0n:
          url_no({1n+k == 0n : Nat}, e)
        case 1n+q:
          %url_is_eq(k, q, e) : {1n+k == 1n+_ : Nat}
          {==}

def url_append_nil(s: String) -> {String.append(s, SNil{}) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %url_append_nil(t) : {SCon{c, String.append(t, SNil{})} == SCon{c, _} : String}
      {==}

# Per-char facts on the URL class
# -------------------------------

# A char a host or a port may hold: lowercase letters, digits, '-', '.', ':'.
def plain(k: U.UClass) -> Bool:
  match k:
    case U.Lower{}:
      True{}
    case U.Num{}:
      True{}
    case U.Dash{}:
      True{}
    case U.Dot{}:
      True{}
    case U.Colon{}:
      True{}
    case _:
      False{}

def all_plain(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(plain(U.uclass(c)), all_plain(t))

def host_plain(k: U.UClass, +e: {U.UClass.is_host(k) == True{} : Bool}) -> {plain(k) == True{} : Bool}:
  match k:
    case U.Lower{}:
      {==}
    case U.Upper{}:
      url_no({plain(U.Upper{}) == True{} : Bool}, e)
    case U.Num{}:
      {==}
    case U.Dash{}:
      {==}
    case U.Dot{}:
      {==}
    case U.Colon{}:
      {==}
    case U.Slash{}:
      url_no({plain(U.Slash{}) == True{} : Bool}, e)
    case U.Query{}:
      url_no({plain(U.Query{}) == True{} : Bool}, e)
    case U.Hash{}:
      url_no({plain(U.Hash{}) == True{} : Bool}, e)
    case U.At{}:
      url_no({plain(U.At{}) == True{} : Bool}, e)
    case U.Bracket{}:
      url_no({plain(U.Bracket{}) == True{} : Bool}, e)
    case U.Other{}:
      url_no({plain(U.Other{}) == True{} : Bool}, e)
    case U.Bad{}:
      url_no({plain(U.Bad{}) == True{} : Bool}, e)

def host_not_colon(k: U.UClass, +e: {U.UClass.is_host(k) == True{} : Bool}) -> {U.UClass.is_colon(k) == False{} : Bool}:
  match k:
    case U.Lower{}:
      {==}
    case U.Upper{}:
      {==}
    case U.Num{}:
      {==}
    case U.Dash{}:
      {==}
    case U.Dot{}:
      {==}
    case U.Colon{}:
      url_no({U.UClass.is_colon(U.Colon{}) == False{} : Bool}, e)
    case U.Slash{}:
      {==}
    case U.Query{}:
      {==}
    case U.Hash{}:
      {==}
    case U.At{}:
      {==}
    case U.Bracket{}:
      {==}
    case U.Other{}:
      {==}
    case U.Bad{}:
      {==}

def plain_not_auth_end(k: U.UClass, +e: {plain(k) == True{} : Bool}) -> {U.UClass.is_auth_end(k) == False{} : Bool}:
  match k:
    case U.Lower{}:
      {==}
    case U.Upper{}:
      {==}
    case U.Num{}:
      {==}
    case U.Dash{}:
      {==}
    case U.Dot{}:
      {==}
    case U.Colon{}:
      {==}
    case U.Slash{}:
      url_no({U.UClass.is_auth_end(U.Slash{}) == False{} : Bool}, e)
    case U.Query{}:
      url_no({U.UClass.is_auth_end(U.Query{}) == False{} : Bool}, e)
    case U.Hash{}:
      url_no({U.UClass.is_auth_end(U.Hash{}) == False{} : Bool}, e)
    case U.At{}:
      {==}
    case U.Bracket{}:
      {==}
    case U.Other{}:
      {==}
    case U.Bad{}:
      {==}

def plain_not_at(k: U.UClass, +e: {plain(k) == True{} : Bool}) -> {U.UClass.is_at(k) == False{} : Bool}:
  match k:
    case U.Lower{}:
      {==}
    case U.Upper{}:
      {==}
    case U.Num{}:
      {==}
    case U.Dash{}:
      {==}
    case U.Dot{}:
      {==}
    case U.Colon{}:
      {==}
    case U.Slash{}:
      {==}
    case U.Query{}:
      {==}
    case U.Hash{}:
      {==}
    case U.At{}:
      url_no({U.UClass.is_at(U.At{}) == False{} : Bool}, e)
    case U.Bracket{}:
      {==}
    case U.Other{}:
      {==}
    case U.Bad{}:
      {==}

def plain_not_bracket(k: U.UClass, +e: {plain(k) == True{} : Bool}) -> {U.UClass.is_bracket(k) == False{} : Bool}:
  match k:
    case U.Lower{}:
      {==}
    case U.Upper{}:
      {==}
    case U.Num{}:
      {==}
    case U.Dash{}:
      {==}
    case U.Dot{}:
      {==}
    case U.Colon{}:
      {==}
    case U.Slash{}:
      {==}
    case U.Query{}:
      {==}
    case U.Hash{}:
      {==}
    case U.At{}:
      {==}
    case U.Bracket{}:
      url_no({U.UClass.is_bracket(U.Bracket{}) == False{} : Bool}, e)
    case U.Other{}:
      {==}
    case U.Bad{}:
      {==}

def target_not_hash(k: U.UClass, +e: {U.UClass.is_target(k) == True{} : Bool}) -> {U.UClass.is_hash(k) == False{} : Bool}:
  match k:
    case U.Lower{}:
      {==}
    case U.Upper{}:
      {==}
    case U.Num{}:
      {==}
    case U.Dash{}:
      {==}
    case U.Dot{}:
      {==}
    case U.Colon{}:
      {==}
    case U.Slash{}:
      {==}
    case U.Query{}:
      {==}
    case U.Hash{}:
      url_no({U.UClass.is_hash(U.Hash{}) == False{} : Bool}, e)
    case U.At{}:
      {==}
    case U.Bracket{}:
      {==}
    case U.Other{}:
      {==}
    case U.Bad{}:
      {==}

def slash_eq(k: U.UClass, +e: {U.UClass.is_slash(k) == True{} : Bool}) -> {k == U.Slash{} : U.UClass}:
  match k:
    case U.Lower{}:
      url_no({U.Lower{} == U.Slash{} : U.UClass}, e)
    case U.Upper{}:
      url_no({U.Upper{} == U.Slash{} : U.UClass}, e)
    case U.Num{}:
      url_no({U.Num{} == U.Slash{} : U.UClass}, e)
    case U.Dash{}:
      url_no({U.Dash{} == U.Slash{} : U.UClass}, e)
    case U.Dot{}:
      url_no({U.Dot{} == U.Slash{} : U.UClass}, e)
    case U.Colon{}:
      url_no({U.Colon{} == U.Slash{} : U.UClass}, e)
    case U.Slash{}:
      {==}
    case U.Query{}:
      url_no({U.Query{} == U.Slash{} : U.UClass}, e)
    case U.Hash{}:
      url_no({U.Hash{} == U.Slash{} : U.UClass}, e)
    case U.At{}:
      url_no({U.At{} == U.Slash{} : U.UClass}, e)
    case U.Bracket{}:
      url_no({U.Bracket{} == U.Slash{} : U.UClass}, e)
    case U.Other{}:
      url_no({U.Other{} == U.Slash{} : U.UClass}, e)
    case U.Bad{}:
      url_no({U.Bad{} == U.Slash{} : U.UClass}, e)

# Host chars are not uppercase
# ----------------------------

def upper_b(+c: Char) -> Bool:
  H.is_letter(B.class(H.up32(Char.to_u32(c))))

def upper_c(+c: Char) -> Bool:
  Bool.not(H.is_letter(B.class(H.up32(H.up32(Char.to_u32(c))))))

# A char whose class is not a letter is not uppercase.
def upper_of_nonletter(+c: Char, +k: B.Class, +ek: {B.char_class(c) == k : B.Class}, +nl: {H.is_letter(k) == False{} : Bool})
  -> {H.is_upper(c) == False{} : Bool}:
  %Equal.sym(B.Class, B.char_class(c), k, ek) : {Bool.and(Bool.and(H.is_letter(_), upper_b(c)), upper_c(c)) == False{} : Bool}
  %Equal.sym(Bool, H.is_letter(k), False{}, nl) : {Bool.and(Bool.and(_, upper_b(c)), upper_c(c)) == False{} : Bool}
  {==}

def letter_host(b: Bool, +e: {U.UClass.is_host(U.letter_class(b)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      url_no({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def host_not_upper(+c: Char, k: B.Class, +ek: {B.char_class(c) == k : B.Class}, +h: {U.UClass.is_host(U.uclass.of(k, c)) == True{} : Bool})
  -> {H.is_upper(c) == False{} : Bool}:
  match k:
    case B.Digit{v}:
      upper_of_nonletter(c, B.Digit{v}, ek, {==})
    case B.HexLetter{v}:
      letter_host(H.is_upper(c), h)
    case B.Letter{}:
      letter_host(H.is_upper(c), h)
    case B.Tchar{}:
      upper_of_nonletter(c, B.Tchar{}, ek, {==})
    case B.Colon{}:
      upper_of_nonletter(c, B.Colon{}, ek, {==})
    case B.Semi{}:
      upper_of_nonletter(c, B.Semi{}, ek, {==})
    case B.Slash{}:
      upper_of_nonletter(c, B.Slash{}, ek, {==})
    case B.Sp{}:
      upper_of_nonletter(c, B.Sp{}, ek, {==})
    case B.Htab{}:
      upper_of_nonletter(c, B.Htab{}, ek, {==})
    case B.Cr{}:
      upper_of_nonletter(c, B.Cr{}, ek, {==})
    case B.Lf{}:
      upper_of_nonletter(c, B.Lf{}, ek, {==})
    case B.Delim{}:
      upper_of_nonletter(c, B.Delim{}, ek, {==})
    case B.Ctl{}:
      upper_of_nonletter(c, B.Ctl{}, ek, {==})
    case B.High{}:
      upper_of_nonletter(c, B.High{}, ek, {==})
    case B.Invalid{}:
      upper_of_nonletter(c, B.Invalid{}, ek, {==})

# String facts
# ------------

def host_all_plain(s: String, +e: {U.all_host(s) == True{} : Bool}) -> {all_plain(s) == True{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      hk = NP.and_l(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)
      ht = NP.and_r(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)
      url_and_intro(plain(U.uclass(c)), all_plain(t), host_plain(U.uclass(c), hk), host_all_plain(t, ht))

def plain_append(x: String, +y: String, +ex: {all_plain(x) == True{} : Bool}, +ey: {all_plain(y) == True{} : Bool})
  -> {all_plain(String.append(x, y)) == True{} : Bool}:
  match x:
    case SNil{}:
      ey
    case SCon{+c, +t}:
      hk = NP.and_l(plain(U.uclass(c)), all_plain(t), ex)
      ht = NP.and_r(plain(U.uclass(c)), all_plain(t), ex)
      url_and_intro(plain(U.uclass(c)), all_plain(String.append(t, y)), hk, plain_append(t, y, ht, ey))

def plain_no_at(s: String, +e: {all_plain(s) == True{} : Bool}) -> {U.has_at(s) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      hk = NP.and_l(plain(U.uclass(c)), all_plain(t), e)
      ht = NP.and_r(plain(U.uclass(c)), all_plain(t), e)
      %Equal.sym(Bool, U.UClass.is_at(U.uclass(c)), False{}, plain_not_at(U.uclass(c), hk)) : {Bool.or(_, U.has_at(t)) == False{} : Bool}
      plain_no_at(t, ht)

def plain_no_bracket(s: String, +e: {all_plain(s) == True{} : Bool}) -> {U.has_bracket(s) == False{} : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      hk = NP.and_l(plain(U.uclass(c)), all_plain(t), e)
      ht = NP.and_r(plain(U.uclass(c)), all_plain(t), e)
      %Equal.sym(Bool, U.UClass.is_bracket(U.uclass(c)), False{}, plain_not_bracket(U.uclass(c), hk)) : {Bool.or(_, U.has_bracket(t)) == False{} : Bool}
      plain_no_bracket(t, ht)

# lower == lower.spec, and lower.spec leaves a host unchanged.
def lower_go(s: String, +acc: String) -> {H.lower.go(s, acc) == String.reverse.go(acc, H.lower.spec(s)) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      lower_go(t, SCon{H.lower_char(c), acc})

def lower_spec_host(s: String, +e: {U.all_host(s) == True{} : Bool}) -> {H.lower.spec(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      hk = NP.and_l(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)
      ht = NP.and_r(U.UClass.is_host(U.uclass(c)), U.all_host(t), e)
      %Equal.sym(Bool, H.is_upper(c), False{}, host_not_upper(c, B.char_class(c), {==}, hk)) : {SCon{H.lower_char.pick(_, c), H.lower.spec(t)} == SCon{c, t} : String}
      %Equal.sym(String, H.lower.spec(t), t, lower_spec_host(t, ht)) : {SCon{c, _} == SCon{c, t} : String}
      {==}

def before_hash_target(s: String, +e: {U.all_target(s) == True{} : Bool}) -> {U.before_hash(s) == s : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      hk = NP.and_l(U.UClass.is_target(U.uclass(c)), U.all_target(t), e)
      ht = NP.and_r(U.UClass.is_target(U.uclass(c)), U.all_target(t), e)
      %Equal.sym(Bool, U.UClass.is_hash(U.uclass(c)), False{}, target_not_hash(U.uclass(c), hk)) : {U.before_hash.pick(_, c, U.before_hash(t)) == SCon{c, t} : String}
      %Equal.sym(String, U.before_hash(t), t, before_hash_target(t, ht)) : {SCon{c, _} == SCon{c, t} : String}
      {==}

# Cuts
# ----

def cut_auth_append(x: String, +r: String, -a: String, -b: String,
  +er: {U.cut_auth(r) == U.Cut{a, b} : U.Cut}, +ex: {all_plain(x) == True{} : Bool})
  -> {U.cut_auth(String.append(x, r)) == U.Cut{String.append(x, a), b} : U.Cut}:
  match x:
    case SNil{}:
      er
    case SCon{+c, +t}:
      hk = NP.and_l(plain(U.uclass(c)), all_plain(t), ex)
      ht = NP.and_r(plain(U.uclass(c)), all_plain(t), ex)
      %Equal.sym(Bool, U.UClass.is_auth_end(U.uclass(c)), False{}, plain_not_auth_end(U.uclass(c), hk)) : {U.cut.pick(_, c, String.append(t, r), U.cut_auth(String.append(t, r))) == U.Cut{SCon{c, String.append(t, a)}, b} : U.Cut}
      %Equal.sym(U.Cut, U.cut_auth(String.append(t, r)), U.Cut{String.append(t, a), b}, cut_auth_append(t, r, a, b, er, ht)) : {U.cut.con(c, _) == U.Cut{SCon{c, String.append(t, a)}, b} : U.Cut}
      {==}

def cut_colon_append(x: String, +r: String, -a: String, -b: String,
  +er: {U.cut_colon(r) == U.Cut{a, b} : U.Cut}, +ex: {U.all_host(x) == True{} : Bool})
  -> {U.cut_colon(String.append(x, r)) == U.Cut{String.append(x, a), b} : U.Cut}:
  match x:
    case SNil{}:
      er
    case SCon{+c, +t}:
      hk = NP.and_l(U.UClass.is_host(U.uclass(c)), U.all_host(t), ex)
      ht = NP.and_r(U.UClass.is_host(U.uclass(c)), U.all_host(t), ex)
      %Equal.sym(Bool, U.UClass.is_colon(U.uclass(c)), False{}, host_not_colon(U.uclass(c), hk)) : {U.cut.pick(_, c, String.append(t, r), U.cut_colon(String.append(t, r))) == U.Cut{SCon{c, String.append(t, a)}, b} : U.Cut}
      %Equal.sym(U.Cut, U.cut_colon(String.append(t, r)), U.Cut{String.append(t, a), b}, cut_colon_append(t, r, a, b, er, ht)) : {U.cut.con(c, _) == U.Cut{SCon{c, String.append(t, a)}, b} : U.Cut}
      {==}

# A target starts with '/', which ends the authority.
def cut_auth_target(t: String, +e: {U.target_ok(t) == True{} : Bool}) -> {U.cut_auth(t) == U.Cut{SNil{}, t} : U.Cut}:
  match t:
    case SNil{}:
      url_no({U.cut_auth(SNil{}) == U.Cut{SNil{}, SNil{}} : U.Cut}, e)
    case SCon{+c, +r}:
      hs = NP.and_l(U.UClass.is_slash(U.uclass(c)), U.all_target(r), e)
      %Equal.sym(U.UClass, U.uclass(c), U.Slash{}, slash_eq(U.uclass(c), hs)) : {U.cut.pick(U.UClass.is_auth_end(_), c, r, U.cut_auth(r)) == U.Cut{SNil{}, SCon{c, r}} : U.Cut}
      {==}

# Parts
# -----

def host_chars_all(h: String, +e: {U.host_chars(h) == True{} : Bool}) -> {U.all_host(h) == True{} : Bool}:
  match h:
    case SNil{}:
      url_no({U.all_host(SNil{}) == True{} : Bool}, e)
    case SCon{c, t}:
      e

def host_of_ok(h: String, +ah: {U.all_host(h) == True{} : Bool}, +eh: {U.host_ok(h) == True{} : Bool})
  -> {U.host_of(h) == Done{h} : SRes()}:
  match h:
    case SNil{}:
      url_no({U.host_of(SNil{}) == Done{SNil{}} : SRes()}, eh)
    case SCon{+c, +t}:
      lw = Equal.trans(String, H.lower(SCon{c, t}), H.lower.spec(SCon{c, t}), SCon{c, t}, lower_go(SCon{c, t}, SNil{}), lower_spec_host(SCon{c, t}, ah))
      %Equal.sym(String, H.lower(SCon{c, t}), SCon{c, t}, lw) : {U.host_of.check(U.host_ok(_), _) == Done{SCon{c, t}} : SRes()}
      %Equal.sym(Bool, U.host_ok(SCon{c, t}), True{}, eh) : {U.host_of.check(_, SCon{c, t}) == Done{SCon{c, t}} : SRes()}
      {==}

def target_of_ok(t: String, +e: {U.target_ok(t) == True{} : Bool}) -> {U.target_of(t) == Done{t} : SRes()}:
  match t:
    case SNil{}:
      url_no({U.target_of(SNil{}) == Done{SNil{}} : SRes()}, e)
    case SCon{+c, +r}:
      hs = NP.and_l(U.UClass.is_slash(U.uclass(c)), U.all_target(r), e)
      ht = NP.and_r(U.UClass.is_slash(U.uclass(c)), U.all_target(r), e)
      %Equal.sym(U.UClass, U.uclass(c), U.Slash{}, slash_eq(U.uclass(c), hs)) : {U.target_of.check(U.target_ok(U.target_raw.of(_, c, r)), U.target_raw.of(_, c, r)) == Done{SCon{c, r}} : SRes()}
      %Equal.sym(String, U.before_hash(r), r, before_hash_target(r, ht)) : {U.target_of.check(U.target_ok(SCon{c, _}), SCon{c, _}) == Done{SCon{c, r}} : SRes()}
      %Equal.sym(Bool, U.target_ok(SCon{c, r}), True{}, e) : {U.target_of.check(_, SCon{c, r}) == Done{SCon{c, r}} : SRes()}
      {==}

# The digits of show(p) are plain.
def digit_plain(d: Nat, +e: {Nat.is_le(d, 9n) == True{} : Bool}) -> {plain(U.uclass(N.digit_char(d))) == True{} : Bool}:
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
    case 10n+k:
      url_no({plain(U.uclass(N.digit_char(10n+k))) == True{} : Bool}, e)

def digits_text_plain(ds: List<&2, Nat>, +acc: String, +ok: {NP.digits_ok(9n, ds) == True{} : Bool}, +ea: {all_plain(acc) == True{} : Bool})
  -> {all_plain(N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      ea
    case Con{+d, +t}:
      okd = NP.and_l(Nat.is_le(d, 9n), NP.digits_ok(9n, t), ok)
      okt = NP.and_r(Nat.is_le(d, 9n), NP.digits_ok(9n, t), ok)
      digits_text_plain(t, SCon{N.digit_char(d), acc}, okt, url_and_intro(plain(U.uclass(N.digit_char(d))), all_plain(acc), digit_plain(d, okd), ea))

def show_plain(+p: Nat) -> {all_plain(N.show(p)) == True{} : Bool}:
  digits_text_plain(N.dec_count(p, [0n]), SNil{}, NP.dec_count_ok(p, [0n], {==}), {==})

def port_text_plain(d: Bool, +p: Nat) -> {all_plain(U.port_text.pick(d, p)) == True{} : Bool}:
  match d:
    case True{}:
      {==}
    case False{}:
      show_plain(p)

# A port that reads back is accepted.
def port_digits(sd: String, +p: Nat, +er: {N.read(sd) == Some{p} : Maybe<&2, Nat>}, +ep: {U.port_ok(p) == True{} : Bool})
  -> {U.port_of.digits(sd) == Done{p} : PRes()}:
  match sd:
    case SNil{}:
      Empty.absurd({U.port_of.digits(SNil{}) == Done{p} : PRes()}, url_none_some(p, er))
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Nat>, N.read(SCon{c, t}), Some{p}, er) : {U.port_of.num(_, SCon{c, t}) == Done{p} : PRes()}
      %Equal.sym(Bool, U.port_ok(p), True{}, ep) : {U.port_of.range(_, p) == Done{p} : PRes()}
      {==}

def port_show(+p: Nat, +ep: {U.port_ok(p) == True{} : Bool}) -> {U.port_of.digits(N.show(p)) == Done{p} : PRes()}:
  +hi = NP.and_r(Nat.is_le(1n, p), Nat.is_le(p, 65535n), ep)
  +lim = NP.le_trans(p, 65535n, N.LIMIT(), hi, {==})
  port_digits(N.show(p), p, Laws.dec_roundtrip(p, lim), ep)

# Steps 4-6
# ---------

def hostport_ok(d: Bool, +s: M.Scheme, +h: String, +p: Nat, +t: String,
  +ed: {Nat.is_eq(p, U.default_port(s)) == d : Bool},
  +ah: {U.all_host(h) == True{} : Bool},
  +eh: {U.host_ok(h) == True{} : Bool},
  +ep: {U.port_ok(p) == True{} : Bool},
  +et: {U.target_ok(t) == True{} : Bool})
  -> {U.parse.hostport(s, U.cut_colon(String.append(h, U.port_text.pick(d, p))), t) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}:
  match d:
    case True{}:
      %Equal.sym(U.Cut, U.cut_colon(String.append(h, SNil{})), U.Cut{String.append(h, SNil{}), SNil{}}, cut_colon_append(h, SNil{}, SNil{}, SNil{}, {==}, ah)) : {U.parse.hostport(s, _, t) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(String, String.append(h, SNil{}), h, url_append_nil(h)) : {U.make(s, U.host_of(_), U.port_of(s, SNil{}), U.target_of(t)) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(SRes(), U.host_of(h), Done{h}, host_of_ok(h, ah, eh)) : {U.make(s, _, U.port_of(s, SNil{}), U.target_of(t)) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(SRes(), U.target_of(t), Done{t}, target_of_ok(t, et)) : {U.make(s, Done{h}, U.port_of(s, SNil{}), _) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %url_is_eq(p, U.default_port(s), ed) : {U.make(s, Done{h}, Done{_}, Done{t}) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      {==}
    case False{}:
      %Equal.sym(U.Cut, U.cut_colon(String.append(h, SCon{':', N.show(p)})), U.Cut{String.append(h, SNil{}), SCon{':', N.show(p)}}, cut_colon_append(h, SCon{':', N.show(p)}, SNil{}, SCon{':', N.show(p)}, {==}, ah)) : {U.parse.hostport(s, _, t) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(String, String.append(h, SNil{}), h, url_append_nil(h)) : {U.make(s, U.host_of(_), U.port_of(s, SCon{':', N.show(p)}), U.target_of(t)) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(SRes(), U.host_of(h), Done{h}, host_of_ok(h, ah, eh)) : {U.make(s, _, U.port_of(s, SCon{':', N.show(p)}), U.target_of(t)) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(SRes(), U.target_of(t), Done{t}, target_of_ok(t, et)) : {U.make(s, Done{h}, U.port_of(s, SCon{':', N.show(p)}), _) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      %Equal.sym(PRes(), U.port_of.digits(N.show(p)), Done{p}, port_show(p, ep)) : {U.make(s, Done{h}, _, Done{t}) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
      {==}

def auth_ok(+s: M.Scheme, +h: String, +p: Nat, +t: String,
  +eh: {U.host_ok(h) == True{} : Bool},
  +ep: {U.port_ok(p) == True{} : Bool},
  +et: {U.target_ok(t) == True{} : Bool})
  -> {U.parse.auth(s, U.cut_auth(String.append(h, String.append(U.port_text(s, p), t)))) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}:
  +pt = U.port_text(s, p)
  +ah = host_chars_all(h, NP.and_l(U.host_chars(h), U.numeric_ok(h), eh))
  +ph = host_all_plain(h, ah)
  +ppt = port_text_plain(Nat.is_eq(p, U.default_port(s)), p)
  +c1 = cut_auth_append(pt, t, SNil{}, t, cut_auth_target(t, et), ppt)
  +c2 = cut_auth_append(h, String.append(pt, t), String.append(pt, SNil{}), t, c1, ph)
  +pa = plain_append(h, pt, ph, ppt)
  %Equal.sym(U.Cut, U.cut_auth(String.append(h, String.append(pt, t))), U.Cut{String.append(h, String.append(pt, SNil{})), t}, c2) : {U.parse.auth(s, _) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
  %Equal.sym(String, String.append(pt, SNil{}), pt, url_append_nil(pt)) : {U.parse.auth(s, U.Cut{String.append(h, _), t}) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
  %Equal.sym(Bool, U.has_at(String.append(h, pt)), False{}, plain_no_at(String.append(h, pt), pa)) : {U.parse.auth.pick(_, U.has_bracket(String.append(h, pt)), s, String.append(h, pt), t) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
  %Equal.sym(Bool, U.has_bracket(String.append(h, pt)), False{}, plain_no_bracket(String.append(h, pt), pa)) : {U.parse.auth.pick(False{}, _, s, String.append(h, pt), t) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}
  hostport_ok(Nat.is_eq(p, U.default_port(s)), s, h, p, t, {==}, ah, eh, ep, et)

def scheme_ok(s: M.Scheme, +h: String, +p: Nat, +t: String,
  +eh: {U.host_ok(h) == True{} : Bool},
  +ep: {U.port_ok(p) == True{} : Bool},
  +et: {U.target_ok(t) == True{} : Bool})
  -> {U.parse(U.show(M.Url{s, h, p, t})) == Done{M.Url{s, h, p, t}} : Laws.UrlRes()}:
  match s:
    case M.Http{}:
      auth_ok(M.Http{}, h, p, t, eh, ep, et)
    case M.Https{}:
      auth_ok(M.Https{}, h, p, t, eh, ep, et)

def url_rt(u: M.Url, +e: {U.ok(u) == True{} : Bool}) -> {U.parse(U.show(u)) == Done{u} : Laws.UrlRes()}:
  match u:
    case M.Url{+s, +h, +p, +t}:
      +ehp = NP.and_l(Bool.and(U.host_ok(h), U.port_ok(p)), U.target_ok(t), e)
      et = NP.and_r(Bool.and(U.host_ok(h), U.port_ok(p)), U.target_ok(t), e)
      eh = NP.and_l(U.host_ok(h), U.port_ok(p), ehp)
      ep = NP.and_r(U.host_ok(h), U.port_ok(p), ehp)
      scheme_ok(s, h, p, t, eh, ep, et)

# Law 17
# ------

def Laws.url_roundtrip(u, e):
  url_rt(u, e)
