import Base
import ./bytes.bend as B
import ./message.bend as M

# Header names and values: validation (what the encoder accepts) and
# case-insensitive lookup (how a name is found in a header list).
#
# NOTE (loops and specs): as in bytes.bend, every def here that walks a
# caller- or network-sized string or header list is a loop (direct tail
# calls only), because the JS lane's stack overflows near 20-40k nested
# calls. The structural recursion each loop computes stays beside it as
# `<name>.spec`, for the law proofs only; one lemma per pair, by induction
# with the accumulator generalized (all steps definitional, plus a case
# split on `ok` / the hit test):
#   all_tchar.go(s, ok) == Bool.and(ok, all_tchar.spec(s))
#   all_field_char.go(s, ok) == Bool.and(ok, all_field_char.spec(s))
#   headers_ok.go(hs, ok) == Bool.and(ok, headers_ok.spec(hs))
#   lower.go(s, acc) == String.reverse.go(acc, lower.spec(s))
#   get_all.go(l, hs, acc) == B.rev(String, acc, get_all.spec(l, hs))
#   get.go(l, hs, None{}) == List.head(&2, String, get_all.spec(l, hs))
#   has.go(l, hs, False{}) == Bool.not(List.is_empty(&2, String, get_all.spec(l, hs)))
# Corollaries (acc = True{} / SNil{} / Nil{}): all_tchar == all_tchar.spec,
# is_token(SCon{c, t}) == Bool.and(is_tchar(c), all_tchar.spec(t)),
# all_field_char == all_field_char.spec, headers_ok == headers_ok.spec,
# lower == lower.spec, get_all(n, hs) == get_all.spec(lower(n), hs),
# get(n, hs) == List.head(get_all(n, hs)), has(n, hs) == not(is_empty(get_all(n, hs))).

# Validation
# ----------

def all_tchar.spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      B.Class.is_tchar(B.char_class(c)) && all_tchar.spec(t)

def all_tchar.go(s: String, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{c, t}:
      all_tchar.go(t, ok && B.Class.is_tchar(B.char_class(c)))

# Every char is a tchar.
def all_tchar(s: String) -> Bool:
  all_tchar.go(s, True{})

# A token (RFC 9110): one or more tchars. Header names and methods.
def is_token(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      all_tchar.go(t, B.Class.is_tchar(B.char_class(c)))

def all_field_char.spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      B.Class.is_field_char(B.char_class(c)) && all_field_char.spec(t)

def all_field_char.go(s: String, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{c, t}:
      all_field_char.go(t, ok && B.Class.is_field_char(B.char_class(c)))

# Every char may sit inside a field value (VCHAR, SP, HTAB).
def all_field_char(s: String) -> Bool:
  all_field_char.go(s, True{})

# The first char, if any, is not OWS.
def first_not_ows(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.not(B.Class.is_ows(B.char_class(c)))

# The last char, if any, is not OWS (a loop: the recursive call is a tail call).
def last_not_ows(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      match t:
        case SNil{}:
          Bool.not(B.Class.is_ows(B.char_class(c)))
        case SCon{d, u}:
          last_not_ows(SCon{d, u})

# A field value the encoder may send: field chars only, and no SP/HTAB at
# either end. Empty is allowed.
def is_value(+s: String) -> Bool:
  all_field_char(s) && first_not_ows(s) && last_not_ows(s)

def header_ok(h: M.Header) -> Bool:
  match h:
    case M.Header{n, v}:
      is_token(n) && is_value(v)

def headers_ok.spec(hs: List<&2, M.Header>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, t}:
      header_ok(h) && headers_ok.spec(t)

def headers_ok.go(hs: List<&2, M.Header>, ok: Bool) -> Bool:
  match hs:
    case Nil{}:
      ok
    case Con{h, t}:
      headers_ok.go(t, ok && header_ok(h))

# Every header has a token name and a sendable value.
def headers_ok(hs: List<&2, M.Header>) -> Bool:
  headers_ok.go(hs, True{})

# Case folding
# ------------
#
# NOTE (classifier use): bytes.bend's Class has no upper/lower distinction,
# and no module may compare a char code itself. A char is an uppercase ASCII
# letter exactly when
#   class(c) is a letter, class(c + 32) is a letter, class(c + 64) is not,
# with c + 64 written as (c + 32) + 32. For 'A'..'Z', c + 32 is 'a'..'z' and
# c + 64 is 0x81..0x9A (High). For 'a'..'z', c + 32 is High. Any other char
# fails the first test, so this decides 'A'..'Z' with the classifier alone,
# and lowering adds 32. Writing c + 64 as (c + 32) + 32 makes lowering
# idempotent by definition: after c becomes c + 32, the test on the new char
# asks class((c + 32) + 32), the very term the first test found not a letter.
# So lower_char(lower_char(c)) == lower_char(c), hence (with lower ==
# lower.spec) lower(lower(s)) == lower(s): the one lemma law 18 needs.

# Letter or HexLetter: an ASCII letter of either case.
def is_letter(k: B.Class) -> Bool:
  match k:
    case B.HexLetter{v}:
      True{}
    case B.Letter{}:
      True{}
    case _:
      False{}

# The code 32 places up: the same letter in lowercase, for 'A'..'Z'.
def up32(x: U32) -> U32:
  (x + 32 : U32)

# 'A'..'Z' (see the note above).
def is_upper(+c: Char) -> Bool:
  +x = Char.to_u32(c)
  is_letter(B.class(x)) && is_letter(B.class(up32(x)))
    && Bool.not(is_letter(B.class(up32(up32(x)))))

def lower_char.pick(up: Bool, +c: Char) -> Char:
  match up:
    case True{}:
      Char.from_u32(up32(Char.to_u32(c)))
    case False{}:
      c

# 'A'..'Z' to 'a'..'z'; every other char unchanged.
def lower_char(+c: Char) -> Char:
  lower_char.pick(is_upper(c), c)

def lower.spec(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{lower_char(c), lower.spec(t)}

# The lowered chars of s, consed onto acc in reverse; at the end the whole
# reversed accumulator is turned around once.
def lower.go(s: String, acc: String) -> String:
  match s:
    case SNil{}:
      String.reverse(acc)
    case SCon{c, t}:
      lower.go(t, SCon{lower_char(c), acc})

# ASCII letters to lowercase; everything else unchanged.
def lower(s: String) -> String:
  lower.go(s, SNil{})

# Header names are equal ignoring ASCII case. (String.eq nests one call
# per char of the common prefix: callers compare against a short name.)
def name_eq(a: String, b: String) -> Bool:
  String.eq(lower(a), lower(b))

# Lookup
# ------
#
# Every lookup lowers the query name once and compares it with each
# header's lowered name: String.eq(l, lower(n)) with l = lower(name) is
# name_eq(name, n) by definition, without lowering the query per header.

def get_all.pick(hit: Bool, v: String, rest: List<&2, String>) -> List<&2, String>:
  match hit:
    case True{}:
      v <> rest
    case False{}:
      rest

# The values of every header whose name lowers to l (l already lowered), in order.
def get_all.spec(+l: String, hs: List<&2, M.Header>) -> List<&2, String>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case M.Header{n, v}:
          get_all.pick(String.eq(l, lower(n)), v, get_all.spec(l, t))

# The same as a loop: matches consed onto acc, reversed once at the end.
def get_all.go(+l: String, hs: List<&2, M.Header>, acc: List<&2, String>) -> List<&2, String>:
  match hs:
    case Nil{}:
      B.rev(String, acc, Nil{})
    case Con{h, t}:
      match h:
        case M.Header{n, v}:
          get_all.go(l, t, get_all.pick(String.eq(l, lower(n)), v, acc))

# The values of every header whose name matches, in order.
def get_all(name: String, hs: List<&2, M.Header>) -> List<&2, String>:
  get_all.go(lower(name), hs, Nil{})

def get.hit(hit: Bool, v: String) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{v}
    case False{}:
      None{}

# Some{v} if the header's name lowers to l, else None.
def get.test(+l: String, h: M.Header) -> Maybe<&2, String>:
  match h:
    case M.Header{n, v}:
      get.hit(String.eq(l, lower(n)), v)

# The first value whose name lowers to l: stops at the first match.
def get.go(+l: String, hs: List<&2, M.Header>, found: Maybe<&2, String>) -> Maybe<&2, String>:
  match hs found:
    case Nil{} Some{v}:
      Some{v}
    case Con{h, t} Some{v}:
      Some{v}
    case Nil{} None{}:
      None{}
    case Con{h, t} None{}:
      get.go(l, t, get.test(l, h))

# The value of the first header whose name matches.
def get(name: String, hs: List<&2, M.Header>) -> Maybe<&2, String>:
  get.go(lower(name), hs, None{})

# Whether the header's name lowers to l.
def has.test(+l: String, h: M.Header) -> Bool:
  match h:
    case M.Header{n, v}:
      String.eq(l, lower(n))

# Whether a header's name lowers to l: stops at the first match.
def has.go(+l: String, hs: List<&2, M.Header>, found: Bool) -> Bool:
  match hs found:
    case Nil{} True{}:
      True{}
    case Con{h, t} True{}:
      True{}
    case Nil{} False{}:
      False{}
    case Con{h, t} False{}:
      has.go(l, t, has.test(l, h))

def has(name: String, hs: List<&2, M.Header>) -> Bool:
  has.go(lower(name), hs, False{})

# How many headers have this name. Law-facing (law 8) and called by nothing
# at runtime; Base's List.length nests one call per match.
def count(name: String, hs: List<&2, M.Header>) -> Nat:
  List.length(&2, String, get_all(name, hs))

# The headers the client sets itself; a request carrying one is refused.
def reserved(name: String) -> Bool:
  +l = lower(name)
  String.eq(l, "host") || String.eq(l, "content-length")
    || String.eq(l, "transfer-encoding") || String.eq(l, "connection")
