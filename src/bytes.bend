import Base

# Bytes, as Base's TCP.send_bytes / TCP.recv_bytes carry them: one List cell
# per byte, each a U32 in 0..255. A cell past 255 is not a byte (all_bytes).
def Bytes() -> Data:
  List<&2, U32>

# The class of a byte, as HTTP/1.1 (RFC 9110 / 9112) reads it.
#
# Every module classifies a byte or a char through `class` and nothing else:
# validators (is this a token? a field value?) and decoders (what does this
# byte do to the parser?) both dispatch on the Class. A proof then reasons
# from an equation `{class(b) == K : Class}` and never looks inside U32
# comparisons. Do not compare a byte with U32.is_lt / U32.is_eq anywhere else.
type Class is Data:
  Digit{value: Nat}         # 0-9, with its value
  HexLetter{value: Nat}     # a-f and A-F, with their value 10..15 (also tchar)
  Letter{}                  # the other ASCII letters (also tchar)
  Tchar{}                   # ! # $ % & ' * + - . ^ _ ` | ~
  Colon{}                   # :
  Semi{}                    # ;
  Slash{}                   # /
  Sp{}                      # space, 0x20
  Htab{}                    # 0x09
  Cr{}                      # 0x0D
  Lf{}                      # 0x0A
  Delim{}                   # the other visible ASCII: " ( ) , < = > ? @ [ \ ] { }
  Ctl{}                     # 0x00-0x1F except HTAB, LF, CR; and 0x7F
  High{}                    # 0x80-0xFF (obs-text in a field value)
  Invalid{}                 # past 0xFF: not a byte

# Classification
# --------------

def in_range(+b: U32, lo: U32, hi: U32) -> Bool:
  U32.is_le(lo, b) && U32.is_le(b, hi)

# ! # $ % & ' * + - . ^ _ ` | ~
def is_tchar_mark(+b: U32) -> Bool:
  U32.is_eq(b, 33) || in_range(b, 35, 39) || U32.is_eq(b, 42) || U32.is_eq(b, 43)
    || U32.is_eq(b, 45) || U32.is_eq(b, 46) || U32.is_eq(b, 94) || U32.is_eq(b, 95)
    || U32.is_eq(b, 96) || U32.is_eq(b, 124) || U32.is_eq(b, 126)

def class.visible(+b: U32) -> Class:
  Bool.pick(Class, in_range(b, 48, 57), Digit{U32.to_nat((b - 48 : U32))},
  Bool.pick(Class, in_range(b, 97, 102), HexLetter{U32.to_nat((b - 87 : U32))},
  Bool.pick(Class, in_range(b, 65, 70), HexLetter{U32.to_nat((b - 55 : U32))},
  Bool.pick(Class, in_range(b, 97, 122) || in_range(b, 65, 90), Letter{},
  Bool.pick(Class, is_tchar_mark(b), Tchar{},
  Delim{})))))

def class.ascii(+b: U32) -> Class:
  Bool.pick(Class, U32.is_eq(b, 13), Cr{},
  Bool.pick(Class, U32.is_eq(b, 10), Lf{},
  Bool.pick(Class, U32.is_eq(b, 9), Htab{},
  Bool.pick(Class, U32.is_eq(b, 32), Sp{},
  Bool.pick(Class, U32.is_eq(b, 58), Colon{},
  Bool.pick(Class, U32.is_eq(b, 59), Semi{},
  Bool.pick(Class, U32.is_eq(b, 47), Slash{},
  Bool.pick(Class, U32.is_lt(b, 32) || U32.is_eq(b, 127), Ctl{},
  class.visible(b)))))))))

def class(+b: U32) -> Class:
  Bool.pick(Class, U32.is_lt(b, 256),
    Bool.pick(Class, U32.is_lt(b, 128), class.ascii(b), High{}),
    Invalid{})

def char_class(c: Char) -> Class:
  class(Char.to_u32(c))

# Class predicates
# ----------------

# A token character (RFC 9110 tchar): a header name or a method is made of these.
def Class.is_tchar(k: Class) -> Bool:
  match k:
    case Digit{v}:
      True{}
    case HexLetter{v}:
      True{}
    case Letter{}:
      True{}
    case Tchar{}:
      True{}
    case _:
      False{}

# A visible ASCII character (VCHAR, 0x21-0x7E).
def Class.is_vchar(k: Class) -> Bool:
  match k:
    case Digit{v}:
      True{}
    case HexLetter{v}:
      True{}
    case Letter{}:
      True{}
    case Tchar{}:
      True{}
    case Colon{}:
      True{}
    case Semi{}:
      True{}
    case Slash{}:
      True{}
    case Delim{}:
      True{}
    case _:
      False{}

# A character a field value may hold inside it: VCHAR, SP or HTAB. The
# encoder accepts only these (and no leading or trailing SP/HTAB); obs-text
# (High) is read from the network but never sent.
def Class.is_field_char(k: Class) -> Bool:
  match k:
    case Sp{}:
      True{}
    case Htab{}:
      True{}
    case _:
      Class.is_vchar(k)

def Class.is_ows(k: Class) -> Bool:
  match k:
    case Sp{}:
      True{}
    case Htab{}:
      True{}
    case _:
      False{}

def Class.is_ascii(k: Class) -> Bool:
  match k:
    case High{}:
      False{}
    case Invalid{}:
      False{}
    case _:
      True{}

def Class.is_byte(k: Class) -> Bool:
  match k:
    case Invalid{}:
      False{}
    case _:
      True{}

# Loops and their specs
# ---------------------
#
# NOTE (JS stack): evaluation is strict and the JS lane's stack holds only
# about 20-40k nested calls of these small defs, so a fold written
# `P(h) && f(t)` or `SCon{g(h), f(t)}` kills the program on a 40 KB body,
# head or header line (the C lane has no such limit). Every def below that
# walks input whose size the caller or the network decides is therefore a
# loop: it recurses only by a direct tail call, with an accumulator.
#
# The plain structural recursion each loop computes stays beside it as
# `<name>.spec`. Nothing calls a spec at runtime; it is the form the law
# proofs induct on. Each pair has one lemma, by induction on the list with
# the accumulator generalized (every step is definitional, plus the case
# split on `ok` for Bool.and associativity):
#   all_bytes.go(xs, ok) == Bool.and(ok, all_bytes.spec(xs))
#   is_ascii.go(s, ok) == Bool.and(ok, is_ascii.spec(s))
#   rev(A, from_ascii.rev(s, acc), ys) == rev(A, acc, List.append(from_ascii.spec(s), ys))
#   latin1_onto(rev(U32, xs, acc), s) == latin1_onto(acc, String.append(to_latin1.spec(xs), s))
# and so, at acc = True{} / Nil{} (with Bool.and(True, b) == b, ys ++ Nil
# == ys and s ++ SNil == s):
#   all_bytes(xs) == all_bytes.spec(xs)        is_ascii(s) == is_ascii.spec(s)
#   from_ascii(s) == from_ascii.spec(s)        to_latin1(xs) == to_latin1.spec(xs)
#   from_ascii_onto(s, ys) == List.append(from_ascii.spec(s), ys)
# A law about the public def rewrites with its corollary once.

# xs reversed, prepended to acc (a loop): rev(xs, acc) == reverse(xs) ++ acc.
def rev(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> List<&2, A>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev(A, t, h <> acc)

# Byte lists
# ----------

def all_bytes.spec(xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Class.is_byte(class(h)) && all_bytes.spec(t)

def all_bytes.go(xs: List<&2, U32>, ok: Bool) -> Bool:
  match xs:
    case Nil{}:
      ok
    case Con{h, t}:
      all_bytes.go(t, ok && Class.is_byte(class(h)))

# Every cell is a byte (0..255).
def all_bytes(xs: List<&2, U32>) -> Bool:
  all_bytes.go(xs, True{})

# ASCII text <-> bytes
# --------------------

def is_ascii.spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Class.is_ascii(char_class(c)) && is_ascii.spec(t)

def is_ascii.go(s: String, ok: Bool) -> Bool:
  match s:
    case SNil{}:
      ok
    case SCon{c, t}:
      is_ascii.go(t, ok && Class.is_ascii(char_class(c)))

# Every char is ASCII (0..127).
def is_ascii(s: String) -> Bool:
  is_ascii.go(s, True{})

def from_ascii.spec(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      Char.to_u32(c) <> from_ascii.spec(t)

# Each char's code, consed onto acc: the bytes of s in reverse, then acc.
def from_ascii.rev(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      from_ascii.rev(t, Char.to_u32(c) <> acc)

# The bytes of s followed by ys: from_ascii(s) ++ ys, as two loops.
def from_ascii_onto(s: String, ys: List<&2, U32>) -> List<&2, U32>:
  rev(U32, from_ascii.rev(s, Nil{}), ys)

# Each char's code as one byte; the caller has checked is_ascii.
def from_ascii(s: String) -> List<&2, U32>:
  from_ascii_onto(s, Nil{})

def to_ascii.con(ok: Bool, h: U32, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match ok rest:
    case True{} Some{s}:
      Some{SCon{Char.from_u32(h), s}}
    case _ _:
      None{}

# The bytes as text, one char per byte, if every byte is ASCII. Law-facing
# (law 1) and called by nothing at runtime, so it stays a plain recursion.
def to_ascii(xs: List<&2, U32>) -> Maybe<&2, String>:
  match xs:
    case Nil{}:
      Some{SNil{}}
    case Con{+h, t}:
      to_ascii.con(Class.is_ascii(class(h)), h, to_ascii(t))

def to_latin1.spec(xs: List<&2, U32>) -> String:
  match xs:
    case Nil{}:
      SNil{}
    case Con{h, t}:
      SCon{Char.from_u32(h), to_latin1.spec(t)}

# The bytes of acc, which holds them in reverse, as text in reading order
# (one char per byte), prepended to s. The decoder keeps a line reversed,
# so latin1_onto(line, SNil{}) is its text with no extra reverse.
def latin1_onto(acc: List<&2, U32>, s: String) -> String:
  match acc:
    case Nil{}:
      s
    case Con{h, t}:
      latin1_onto(t, SCon{Char.from_u32(h), s})

# The bytes as text, one char per byte, whatever they are (Latin-1). The
# decoder reads header lines this way, so obs-text survives as chars 128..255.
# Every cell must be a Unicode scalar (Char.from_u32 aborts the JS lane on a
# surrogate or a value past 0x10FFFF); a caller with cells past 255 rejects
# them first.
def to_latin1(xs: List<&2, U32>) -> String:
  latin1_onto(rev(U32, xs, Nil{}), SNil{})
