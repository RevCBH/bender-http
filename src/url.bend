import Base
import ./bytes.bend as B
import ./message.bend as M
import ./num.bend as N
import ./headers.bend as H

# Absolute http(s) URLs: parse, show, validity.
#
#   parse(s) = scheme "://" host [":" port] [target]
#
# parse is a chain of small total steps, each a plain structural recursion
# or a match on the previous step's result:
#   1. cut the string at the first ':'            (the scheme before it)
#   2. expect "://" there                          (the rest after it)
#   3. cut the rest at the first '/', '?' or '#'   (the authority before it)
#   4. refuse '@' (userinfo) and '[' / ']' (IPv6) in the authority
#   5. cut the authority at the first ':'          (host, then the port)
#   6. lowercase and check the host (refusing a numeric host that is not a
#      canonical dotted quad); read and range-check the port;
#      build the target from what follows the authority (fragment dropped)
# so that the law
#   ok(u) => parse(show(u)) == Done{u}
# follows from per-char facts: no host, port or target char is a cut char.

# The URL char classifier
# -----------------------
#
# Every char is classified once, by `uclass`, and every URL predicate and
# cut dispatches on the UClass. A proof reasons from {uclass(c) == K : UClass}
# exactly as other modules reason from {B.char_class(c) == K : B.Class}.
#
# NOTE (classifier use): uclass refines B.char_class. Most kinds come straight
# from the B.Class (digits, ':' and '/' have classes of their own; letters
# split into cases with H.is_upper, itself classifier-only). URL syntax also
# needs a few chars that share a B.Class with others: '-', '.' and '#' (all
# Tchar) and '?', '@', '[' and ']' (all Delim). Only inside those two class
# branches is the char compared with a literal (Char.is_eq), and in is_x
# (the 'x' of a "0x" host label, see Numeric hosts), and nowhere else.
type UClass is Data:
  Lower{}       # a-z
  Upper{}       # A-Z
  Num{}         # 0-9
  Dash{}        # -
  Dot{}         # .
  Colon{}       # :
  Slash{}       # /
  Query{}       # ?
  Hash{}        # #
  At{}          # @
  Bracket{}     # [ ]
  Other{}       # any other VCHAR
  Bad{}         # not a VCHAR: SP, controls, non-ASCII

def letter_class(up: Bool) -> UClass:
  match up:
    case True{}:
      Upper{}
    case False{}:
      Lower{}

# A Tchar is '-', '.', '#' or one of the other marks.
def tchar_class(+c: Char) -> UClass:
  Bool.pick(UClass, Char.is_eq(c, '-'), Dash{},
  Bool.pick(UClass, Char.is_eq(c, '.'), Dot{},
  Bool.pick(UClass, Char.is_eq(c, '#'), Hash{},
  Other{})))

# A Delim is '?', '@', '[', ']' or one of the other delimiters.
def delim_class(+c: Char) -> UClass:
  Bool.pick(UClass, Char.is_eq(c, '?'), Query{},
  Bool.pick(UClass, Char.is_eq(c, '@'), At{},
  Bool.pick(UClass, Char.is_eq(c, '[') || Char.is_eq(c, ']'), Bracket{},
  Other{})))

def uclass.of(k: B.Class, +c: Char) -> UClass:
  match k:
    case B.Digit{v}:
      Num{}
    case B.HexLetter{v}:
      letter_class(H.is_upper(c))
    case B.Letter{}:
      letter_class(H.is_upper(c))
    case B.Tchar{}:
      tchar_class(c)
    case B.Colon{}:
      Colon{}
    case B.Semi{}:
      Other{}
    case B.Slash{}:
      Slash{}
    case B.Delim{}:
      delim_class(c)
    case _:
      Bad{}

# The URL class of a char.
def uclass(+c: Char) -> UClass:
  uclass.of(B.char_class(c), c)

# UClass predicates
# -----------------

# A char a host may hold: lowercase letters, digits, '-', '.'.
def UClass.is_host(k: UClass) -> Bool:
  match k:
    case Lower{}:
      True{}
    case Num{}:
      True{}
    case Dash{}:
      True{}
    case Dot{}:
      True{}
    case _:
      False{}

# A char that ends the authority: '/', '?', '#'.
def UClass.is_auth_end(k: UClass) -> Bool:
  match k:
    case Slash{}:
      True{}
    case Query{}:
      True{}
    case Hash{}:
      True{}
    case _:
      False{}

# A char a target may hold: every VCHAR except '#'.
def UClass.is_target(k: UClass) -> Bool:
  match k:
    case Hash{}:
      False{}
    case Bad{}:
      False{}
    case _:
      True{}

def UClass.is_colon(k: UClass) -> Bool:
  match k:
    case Colon{}:
      True{}
    case _:
      False{}

def UClass.is_slash(k: UClass) -> Bool:
  match k:
    case Slash{}:
      True{}
    case _:
      False{}

def UClass.is_num(k: UClass) -> Bool:
  match k:
    case Num{}:
      True{}
    case _:
      False{}

def UClass.is_dot(k: UClass) -> Bool:
  match k:
    case Dot{}:
      True{}
    case _:
      False{}

def UClass.is_hash(k: UClass) -> Bool:
  match k:
    case Hash{}:
      True{}
    case _:
      False{}

def UClass.is_at(k: UClass) -> Bool:
  match k:
    case At{}:
      True{}
    case _:
      False{}

def UClass.is_bracket(k: UClass) -> Bool:
  match k:
    case Bracket{}:
      True{}
    case _:
      False{}

# Ports
# -----

def default_port(s: M.Scheme) -> Nat:
  match s:
    case M.Http{}:
      80n
    case M.Https{}:
      443n

# 1 <= p <= 65535.
def port_ok(+p: Nat) -> Bool:
  Nat.is_le(1n, p) && Nat.is_le(p, 65535n)

# IPv4 literals
# -------------

# The pieces of s between dots: [""] for "", ["a", "b"] for "a.b".
def dot_pieces.con(c: Char, ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      [SCon{c, SNil{}}]
    case Con{p, rest}:
      SCon{c, p} <> rest

def dot_pieces.pick(dot: Bool, c: Char, ps: List<&2, String>) -> List<&2, String>:
  match dot:
    case True{}:
      SNil{} <> ps
    case False{}:
      dot_pieces.con(c, ps)

def dot_pieces(s: String) -> List<&2, String>:
  match s:
    case SNil{}:
      [SNil{}]
    case SCon{+c, t}:
      dot_pieces.pick(UClass.is_dot(uclass(c)), c, dot_pieces(t))

# The digit '0'.
def is_zero(k: B.Class) -> Bool:
  match k:
    case B.Digit{v}:
      Nat.is_eq(v, 0n)
    case _:
      False{}

# No leading zero: one char, or a first char other than '0'.
def no_lead_zero(s: String) -> Bool:
  match s:
    case SCon{c, SCon{d, r}}:
      Bool.not(is_zero(B.char_class(c)))
    case _:
      True{}

def octet_value(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case Some{v}:
      Nat.is_le(v, 255n)
    case None{}:
      False{}

# A decimal number 0..255 written without leading zeros.
def octet_ok(+s: String) -> Bool:
  octet_value(N.read(s)) && no_lead_zero(s)

def octets4(ps: List<&2, String>) -> Bool:
  match ps:
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      octet_ok(a) && octet_ok(b) && octet_ok(c) && octet_ok(d)
    case _:
      False{}

# Four decimal octets 0..255 separated by dots (no leading zeros).
def is_ipv4(host: String) -> Bool:
  octets4(dot_pieces(host))

# Validity
# --------

def all_host(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      UClass.is_host(uclass(c)) && all_host(t)

# Nonempty; lowercase letters, digits, '-', '.' only.
def host_chars(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      UClass.is_host(uclass(c)) && all_host(t)

# Numeric hosts
# -------------
#
# A host whose last dot-separated label is a number (the WHATWG "ends in a
# number" rule) is an IPv4 address to the OS: getaddrinfo / inet_aton read
# "2130706433", "127.1", "0x7f.1" and "010.0.0.1" (octal: 8.0.0.1) as
# addresses. Such a host is allowed only as a canonical dotted quad (is_ipv4),
# so a URL's host string always says which address it means. A host ending
# in '.' (last label "") is a name, which the resolver does not reinterpret.

def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      UClass.is_num(uclass(c)) && all_digits(t)

def is_hex_class(k: B.Class) -> Bool:
  match k:
    case B.Digit{v}:
      True{}
    case B.HexLetter{v}:
      True{}
    case _:
      False{}

def all_hex(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      is_hex_class(B.char_class(c)) && all_hex(t)

# NOTE (classifier use): 'x' is a plain Lower letter to uclass, so the "0x"
# prefix is the one other place a char is compared with a literal.
def is_x(c: Char) -> Bool:
  Char.is_eq(c, 'x')

# "x" then zero or more hex digits (what follows a leading '0').
def hex_tail(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      is_x(c) && all_hex(t)

# A label inet_aton could read as a number: one or more decimal digits, or
# "0x" then zero or more hex digits. (The host is lowercase, so no "0X".)
def is_number(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      UClass.is_num(uclass(c)) && (all_digits(t) || (is_zero(B.char_class(c)) && hex_tail(t)))

# The last of p <> ps (a loop; structural on ps).
def last_piece.go(ps: List<&2, String>, p: String) -> String:
  match ps:
    case Nil{}:
      p
    case Con{q, rest}:
      last_piece.go(rest, q)

def last_piece(ps: List<&2, String>) -> String:
  match ps:
    case Nil{}:
      SNil{}
    case Con{p, rest}:
      last_piece.go(rest, p)

# The last dot-separated label is a number.
def ends_in_number(s: String) -> Bool:
  is_number(last_piece(dot_pieces(s)))

def numeric_ok.pick(num: Bool, s: String) -> Bool:
  match num:
    case True{}:
      is_ipv4(s)
    case False{}:
      True{}

# Not ambiguous: a host ending in a number is a canonical dotted quad.
def numeric_ok(+s: String) -> Bool:
  numeric_ok.pick(ends_in_number(s), s)

# Nonempty; lowercase letters, digits, '-', '.' only; and a host whose last
# label is a number must be a canonical dotted quad (is_ipv4).
def host_ok(+s: String) -> Bool:
  host_chars(s) && numeric_ok(s)

def all_target(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      UClass.is_target(uclass(c)) && all_target(t)

# Starts with '/'; every char a VCHAR other than '#'.
def target_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      UClass.is_slash(uclass(c)) && all_target(t)

def ok(u: M.Url) -> Bool:
  match u:
    case M.Url{s, h, p, t}:
      host_ok(h) && port_ok(p) && target_ok(t)

# Showing
# -------

def scheme_text(s: M.Scheme) -> String:
  match s:
    case M.Http{}:
      "http"
    case M.Https{}:
      "https"

def port_text.pick(dflt: Bool, p: Nat) -> String:
  match dflt:
    case True{}:
      ""
    case False{}:
      ":" ++ N.show(p)

# "" for the scheme's default port, else ":port".
def port_text(s: M.Scheme, +p: Nat) -> String:
  port_text.pick(Nat.is_eq(p, default_port(s)), p)

# scheme://host[:port]target, the port omitted when it is the default.
def show(u: M.Url) -> String:
  match u:
    case M.Url{+s, h, p, t}:
      scheme_text(s) ++ ("://" ++ (h ++ (port_text(s, p) ++ t)))

# The Host header's value: host, or host:port for a non-default port.
def host_header(u: M.Url) -> String:
  match u:
    case M.Url{s, h, p, t}:
      h ++ port_text(s, p)

# Cuts
# ----

# A string cut before its first stop char: the part before it, and the rest
# starting with the stop char ("" when there is none).
type Cut is Data:
  Cut{head: String, tail: String}

def cut.con(c: Char, r: Cut) -> Cut:
  match r:
    case Cut{h, t}:
      Cut{SCon{c, h}, t}

# One step of a cut: stop before c, or keep c in front of the cut of t.
def cut.pick(stop: Bool, c: Char, t: String, r: Cut) -> Cut:
  match stop:
    case True{}:
      Cut{SNil{}, SCon{c, t}}
    case False{}:
      cut.con(c, r)

# Cut at the first ':'.
def cut_colon(s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{SNil{}, SNil{}}
    case SCon{+c, +t}:
      cut.pick(UClass.is_colon(uclass(c)), c, t, cut_colon(t))

# Cut at the first '/', '?' or '#'.
def cut_auth(s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{SNil{}, SNil{}}
    case SCon{+c, +t}:
      cut.pick(UClass.is_auth_end(uclass(c)), c, t, cut_auth(t))

# The part of s before its first '#' (all of s when there is none).
def before_hash.pick(hash: Bool, c: Char, rest: String) -> String:
  match hash:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, rest}

def before_hash(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      before_hash.pick(UClass.is_hash(uclass(c)), c, before_hash(t))

def has_at(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      UClass.is_at(uclass(c)) || has_at(t)

def has_bracket(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      UClass.is_bracket(uclass(c)) || has_bracket(t)

# Parsing
# -------

def bad(reason: String) -> Result<&2, &2, M.Error, M.Url>:
  Fail{M.BadUrl{reason}}

def scheme_of.pick(http: Bool, https: Bool) -> Maybe<&2, M.Scheme>:
  match http https:
    case True{} _:
      Some{M.Http{}}
    case False{} True{}:
      Some{M.Https{}}
    case False{} False{}:
      None{}

# The scheme a lowercased scheme name stands for.
def scheme_of(+name: String) -> Maybe<&2, M.Scheme>:
  scheme_of.pick(String.eq(name, "http"), String.eq(name, "https"))

# Why host_ok refused a host: its chars are fine, so it is a number that is
# not a canonical dotted quad; or a bad char.
def host_of.why(chars: Bool) -> Result<&2, &2, M.Error, String>:
  match chars:
    case True{}:
      Fail{M.BadUrl{"ambiguous IPv4 address"}}
    case False{}:
      Fail{M.BadUrl{"bad host"}}

def host_of.check(ok: Bool, h: String) -> Result<&2, &2, M.Error, String>:
  match ok:
    case True{}:
      Done{h}
    case False{}:
      host_of.why(host_chars(h))

# The host, lowercased; nonempty, only host chars, and not an ambiguous
# number (see Numeric hosts).
def host_of(h: String) -> Result<&2, &2, M.Error, String>:
  match h:
    case SNil{}:
      Fail{M.BadUrl{"empty host"}}
    case SCon{c, t}:
      +l = H.lower(SCon{c, t})
      host_of.check(host_ok(l), l)

def port_of.range(ok: Bool, p: Nat) -> Result<&2, &2, M.Error, Nat>:
  match ok:
    case True{}:
      Done{p}
    case False{}:
      Fail{M.BadUrl{"port out of range"}}

# Why a port N.read refused is bad: digits only means it is past LIMIT.
def port_of.why(digits: Bool) -> Result<&2, &2, M.Error, Nat>:
  match digits:
    case True{}:
      Fail{M.BadUrl{"port out of range"}}
    case False{}:
      Fail{M.BadUrl{"bad port"}}

def port_of.num(m: Maybe<&2, Nat>, s: String) -> Result<&2, &2, M.Error, Nat>:
  match m:
    case Some{+p}:
      port_of.range(port_ok(p), p)
    case None{}:
      port_of.why(all_digits(s))

def port_of.digits(s: String) -> Result<&2, &2, M.Error, Nat>:
  match s:
    case SNil{}:
      Fail{M.BadUrl{"empty port"}}
    case SCon{+c, +t}:
      port_of.num(N.read(SCon{c, t}), SCon{c, t})

# The port, from what follows the host: "" (the default) or ":" digits.
def port_of(s: M.Scheme, pp: String) -> Result<&2, &2, M.Error, Nat>:
  match pp:
    case SNil{}:
      Done{default_port(s)}
    case SCon{colon, digits}:
      port_of.digits(digits)

# The target, from what follows the authority (empty, or starting with '/',
# '?' or '#'): "/" when empty or a bare fragment, "/" in front of a bare
# query, and never the fragment.
def target_raw.of(k: UClass, c: Char, t: String) -> String:
  match k:
    case Slash{}:
      SCon{c, before_hash(t)}
    case Query{}:
      SCon{'/', SCon{c, before_hash(t)}}
    case _:
      "/"

def target_raw(rest: String) -> String:
  match rest:
    case SNil{}:
      "/"
    case SCon{+c, t}:
      target_raw.of(uclass(c), c, t)

def target_of.check(ok: Bool, t: String) -> Result<&2, &2, M.Error, String>:
  match ok:
    case True{}:
      Done{t}
    case False{}:
      Fail{M.BadUrl{"bad char in target"}}

def target_of(rest: String) -> Result<&2, &2, M.Error, String>:
  +t = target_raw(rest)
  target_of.check(target_ok(t), t)

# The URL from its checked parts; the first failure otherwise.
def make(
  s: M.Scheme, h: Result<&2, &2, M.Error, String>,
  p: Result<&2, &2, M.Error, Nat>, t: Result<&2, &2, M.Error, String>
) -> Result<&2, &2, M.Error, M.Url>:
  match h p t:
    case Done{hv} Done{pv} Done{tv}:
      Done{M.Url{s, hv, pv, tv}}
    case Fail{e} _ _:
      Fail{e}
    case Done{hv} Fail{e} _:
      Fail{e}
    case Done{hv} Done{pv} Fail{e}:
      Fail{e}

# Step 6: host and port from the authority cut at ':'; the target.
def parse.hostport(+s: M.Scheme, hp: Cut, rest: String) -> Result<&2, &2, M.Error, M.Url>:
  match hp:
    case Cut{h, pp}:
      make(s, host_of(h), port_of(s, pp), target_of(rest))

def parse.auth.pick(
  at: Bool, br: Bool, s: M.Scheme, auth: String, rest: String
) -> Result<&2, &2, M.Error, M.Url>:
  match at br:
    case True{} _:
      bad("userinfo is not supported")
    case False{} True{}:
      bad("IPv6 literals are not supported")
    case False{} False{}:
      parse.hostport(s, cut_colon(auth), rest)

# Steps 4-5: the authority (before the first '/', '?' or '#') and the rest.
def parse.auth(s: M.Scheme, c: Cut) -> Result<&2, &2, M.Error, M.Url>:
  match c:
    case Cut{+a, rest}:
      parse.auth.pick(has_at(a), has_bracket(a), s, a, rest)

def parse.sep.pick(ok: Bool, s: M.Scheme, rest: String) -> Result<&2, &2, M.Error, M.Url>:
  match ok:
    case True{}:
      parse.auth(s, cut_auth(rest))
    case False{}:
      bad("expected :// after the scheme")

# Step 2: "://" right after the scheme name.
def parse.sep(s: M.Scheme, after: String) -> Result<&2, &2, M.Error, M.Url>:
  match after:
    case SCon{a, SCon{b, SCon{c, rest}}}:
      parse.sep.pick(
        UClass.is_colon(uclass(a)) && UClass.is_slash(uclass(b)) && UClass.is_slash(uclass(c)),
        s, rest)
    case _:
      bad("expected :// after the scheme")

def parse.scheme(m: Maybe<&2, M.Scheme>, after: String) -> Result<&2, &2, M.Error, M.Url>:
  match m:
    case Some{s}:
      parse.sep(s, after)
    case None{}:
      bad("unsupported scheme")

# Step 1: the scheme name before the first ':' (case-insensitive).
def parse.cut(c: Cut) -> Result<&2, &2, M.Error, M.Url>:
  match c:
    case Cut{name, after}:
      parse.scheme(scheme_of(H.lower(name)), after)

# scheme "://" host [":" port] [target]. See the top of this file.
def parse(s: String) -> Result<&2, &2, M.Error, M.Url>:
  parse.cut(cut_colon(s))
