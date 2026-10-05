import Base
import ./bytes.bend as B

# UTF-8 (RFC 3629): strings to bytes and strictly back. Tested, not proven:
# this module works with U32 bit arithmetic and comparisons directly, which
# the one-classifier rule allows here because no law is stated about it.

# Encoding
# --------

# How many bytes a code point takes: 1..4, or 0 for a char that is not a
# Unicode scalar value (a surrogate, or past U+10FFFF), which is written as
# U+FFFD instead.
def width(+c: U32) -> Nat:
  Bool.pick(Nat, U32.is_lt(c, 128), 1n,
  Bool.pick(Nat, U32.is_lt(c, 2048), 2n,
  Bool.pick(Nat, U32.is_lt(c, 55296), 3n,
  Bool.pick(Nat, U32.is_lt(c, 57344), 0n,
  Bool.pick(Nat, U32.is_lt(c, 65536), 3n,
  Bool.pick(Nat, U32.is_lt(c, 1114112), 4n,
  0n))))))

# A continuation byte holding bits [k, k+6) of c.
def cont(+c: U32, k: Nat) -> U32:
  (128 .|. ((c >> k) .&. 63) : U32)

def put(w: Nat, +c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  match w:
    case 1n:
      c <> rest
    case 2n:
      (192 .|. (c >> 6n) : U32) <> cont(c, 0n) <> rest
    case 3n:
      (224 .|. (c >> 12n) : U32) <> cont(c, 6n) <> cont(c, 0n) <> rest
    case 4n:
      (240 .|. (c >> 18n) : U32) <> cont(c, 12n) <> cont(c, 6n) <> cont(c, 0n) <> rest
    case _:
      239 <> 191 <> 189 <> rest

# A code point's bytes, prepended to rest.
def put_char(+c: U32, rest: List<&2, U32>) -> List<&2, U32>:
  put(width(c), c, rest)

# The bytes of the chars of r (a reversed string), in reverse order of r,
# prepended to acc. A loop, so long strings do not nest calls.
def encode.go(r: String, acc: List<&2, U32>) -> List<&2, U32>:
  match r:
    case SNil{}:
      acc
    case SCon{c, t}:
      encode.go(t, put_char(Char.to_u32(c), acc))

# The UTF-8 bytes of s. A char that is not a scalar value becomes U+FFFD.
def encode(s: String) -> List<&2, U32>:
  encode.go(String.reverse(s), Nil{})

# Decoding
# --------

# The decoder's state between bytes: the chars so far (reversed).
type State is Data:
  Start{out: String}
  # need more continuation bytes; code so far; the least code point a
  # sequence of this length may encode (to refuse overlongs)
  More{out: String, need: Nat, code: U32, min: U32}
  Bad{}

# The length of the sequence a lead byte starts: 1 for ASCII, 2..4 for a
# multibyte lead, 0 for a byte that starts nothing valid (80..BF are
# continuation bytes; C0, C1 would be overlong; F5..FF, and cells past 255).
def lead_len(+b: U32) -> Nat:
  Bool.pick(Nat, B.Class.is_ascii(B.class(b)), 1n,
  Bool.pick(Nat, U32.is_lt(b, 194), 0n,
  Bool.pick(Nat, U32.is_lt(b, 224), 2n,
  Bool.pick(Nat, U32.is_lt(b, 240), 3n,
  Bool.pick(Nat, U32.is_lt(b, 245), 4n,
  0n)))))

def lead.len(n: Nat, out: String, +b: U32) -> State:
  match n:
    case 1n:
      Start{SCon{Char.from_u32(b), out}}
    case 2n:
      More{out, 1n, (b .&. 31 : U32), 128}
    case 3n:
      More{out, 2n, (b .&. 15 : U32), 2048}
    case 4n:
      More{out, 3n, (b .&. 7 : U32), 65536}
    case _:
      Bad{}

def lead(out: String, +b: U32) -> State:
  lead.len(lead_len(b), out, b)

# A scalar value of a sequence that may encode no less than min.
def scalar_ok(+c: U32, min: U32) -> Bool:
  U32.is_le(min, c) && U32.is_le(c, 1114111)
    && Bool.not(U32.is_le(55296, c) && U32.is_le(c, 57343))

def close(ok: Bool, out: String, c: U32) -> State:
  match ok:
    case True{}:
      Start{SCon{Char.from_u32(c), out}}
    case False{}:
      Bad{}

# The code after the last continuation byte: check it and emit it.
def finish_char(out: String, +c: U32, min: U32) -> State:
  close(scalar_ok(c, min), out, c)

# After one continuation byte, with need-1 still to come.
def advance(out: String, need: Nat, +c: U32, min: U32) -> State:
  match need:
    case 0n:
      finish_char(out, c, min)
    case 1n+p:
      More{out, 1n+p, c, min}

def cont_pick(is_cont: Bool, out: String, need: Nat, code: U32, min: U32, b: U32) -> State:
  match is_cont:
    case True{}:
      advance(out, Nat.sub(need, 1n), ((code << 6n) .|. (b .&. 63) : U32), min)
    case False{}:
      Bad{}

# A byte inside a sequence: it must be a continuation byte (80..BF).
def more(out: String, need: Nat, code: U32, min: U32, +b: U32) -> State:
  cont_pick(B.Class.is_byte(B.class(b)) && U32.is_eq((b .&. 192 : U32), 128), out, need, code, min, b)

def step(s: State, +b: U32) -> State:
  match s:
    case Start{out}:
      lead(out, b)
    case More{out, need, code, min}:
      more(out, need, code, min, b)
    case Bad{}:
      Bad{}

# Steps the state through every byte (the list comes first so the
# recursion is structural on it).
def feed(xs: List<&2, U32>, s: State) -> State:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      feed(t, step(s, h))

def finish(s: State) -> Maybe<&2, String>:
  match s:
    case Start{out}:
      Some{String.reverse(out)}
    case _:
      None{}

# The text the bytes encode, if they are well-formed UTF-8: no overlong
# forms, no surrogates, nothing past U+10FFFF, no stray continuation byte,
# no truncated sequence, and no cell past 255.
def decode(xs: List<&2, U32>) -> Maybe<&2, String>:
  finish(feed(xs, Start{SNil{}}))
