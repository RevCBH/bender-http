import Base
import ./bytes.bend as B

# Decimal and hexadecimal text for Nat: the only way numbers are written to
# or read from HTTP text (ports, statuses, Content-Length, chunk sizes).
#
# show / hex_show count up: a number's digits are a little-endian list,
# digits(0) = [0] and digits(1n+p) = inc(digits(p)), so the roundtrip laws
#   read(show(n)) == Some{n}  and  hex_read(hex_show(n)) == Some{n}  (n <= LIMIT)
# follow by induction on n. The cost is O(n) increments: fine for the
# lengths and ports a client writes.
#
# read / hex_read saturate: the accumulator grows only while it is at most
# LIMIT, so no step computes more than LIMIT * 10 + 9 (LIMIT * 16 + 15 for
# hex) and hostile input like "99999999999999999999999999" cannot push a Nat
# past 2^48 (which aborts the runtime). Above LIMIT the answer is None.

# Every parsed number is at most LIMIT.
def LIMIT() -> Nat:
  4294967295n

# Digit chars
# -----------

# The char of a digit value 0..15: '0'..'9', 'a'..'f'. Each char's class is
# Digit{d} (0..9) or HexLetter{d} (10..15) by computation. Never called with
# d > 15 (a digit list holds values below its base); '?' is not a digit.
def digit_char(d: Nat) -> Char:
  match d:
    case 0n:
      '0'
    case 1n:
      '1'
    case 2n:
      '2'
    case 3n:
      '3'
    case 4n:
      '4'
    case 5n:
      '5'
    case 6n:
      '6'
    case 7n:
      '7'
    case 8n:
      '8'
    case 9n:
      '9'
    case 10n:
      'a'
    case 11n:
      'b'
    case 12n:
      'c'
    case 13n:
      'd'
    case 14n:
      'e'
    case 15n:
      'f'
    case _:
      '?'

# Little-endian digit lists, built by increments
# ----------------------------------------------

# Adds one to a little-endian base-10 digit list.
def dec_inc(ds: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      [1n]
    case Con{d, t}:
      match d:
        case 9n:
          Con{0n, dec_inc(t)}
        case k:
          Con{1n+k, t}

# n increments on the base-10 digit list ds (a loop: tail-recursive).
def dec_count(n: Nat, ds: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      ds
    case 1n+p:
      dec_count(p, dec_inc(ds))

# The base-10 digits of n, least significant first: [0] for 0. As a
# recursion, digits(0) = [0] and digits(1n+p) = dec_inc(digits(p)); it is
# computed as n increments of [0] in a loop (dec_count), because the direct
# recursion nests n calls deep and overflows the JS lane's stack near
# n = 60000. Lemma for the proofs:
#   dec_count(n, dec_inc(ds)) == dec_inc(dec_count(n, ds))  (induction on n).
def dec_digits(n: Nat) -> List<&2, Nat>:
  dec_count(n, [0n])

# Adds one to a little-endian base-16 digit list.
def hex_inc(ds: List<&2, Nat>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      [1n]
    case Con{d, t}:
      match d:
        case 15n:
          Con{0n, hex_inc(t)}
        case k:
          Con{1n+k, t}

# n increments on the base-16 digit list ds (a loop: tail-recursive).
def hex_count(n: Nat, ds: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      ds
    case 1n+p:
      hex_count(p, hex_inc(ds))

# The base-16 digits of n, least significant first: [0] for 0. Like
# dec_digits: hex_digits(1n+p) == hex_inc(hex_digits(p)), computed in a loop.
def hex_digits(n: Nat) -> List<&2, Nat>:
  hex_count(n, [0n])

# A little-endian digit list as text, most significant digit first,
# prepended to acc.
def digits_text(ds: List<&2, Nat>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      digits_text(t, SCon{digit_char(d), acc})

# Showing
# -------

# Decimal, no leading zeros ("0" for 0).
def show(n: Nat) -> String:
  digits_text(dec_digits(n), SNil{})

# Lowercase hexadecimal, no leading zeros ("0" for 0).
def hex_show(n: Nat) -> String:
  digits_text(hex_digits(n), SNil{})

# Reading
# -------

# The value of a decimal digit's class.
def dec_value(k: B.Class) -> Maybe<&2, Nat>:
  match k:
    case B.Digit{v}:
      Some{v}
    case _:
      None{}

# The value of a hexadecimal digit's class (either case).
def hex_value(k: B.Class) -> Maybe<&2, Nat>:
  match k:
    case B.Digit{v}:
      Some{v}
    case B.HexLetter{v}:
      Some{v}
    case _:
      None{}

def push.pick(small: Bool, acc: Nat, base: Nat, d: Nat) -> Nat:
  match small:
    case True{}:
      Nat.add(Nat.mul(acc, base), d)
    case False{}:
      acc

# One more digit d (d < base) on the accumulator, saturating: once acc is
# above LIMIT it stays put, so the result is at most LIMIT * base + base - 1.
def push(+acc: Nat, base: Nat, d: Nat) -> Nat:
  push.pick(Nat.is_le(acc, LIMIT()), acc, base, d)

# The accumulator after one more char: None once any char is not a digit.
def read.step(acc: Maybe<&2, Nat>, base: Nat, d: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match acc d:
    case Some{a} Some{v}:
      Some{push(a, base, v)}
    case _ _:
      None{}

# Folds the chars of a decimal numeral into the accumulator.
def dec_read.go(s: String, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      dec_read.go(t, read.step(acc, 10n, dec_value(B.char_class(c))))

# Folds the chars of a hexadecimal numeral into the accumulator.
def hex_read.go(s: String, acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      acc
    case SCon{c, t}:
      hex_read.go(t, read.step(acc, 16n, hex_value(B.char_class(c))))

def bound.pick(ok: Bool, n: Nat) -> Maybe<&2, Nat>:
  match ok:
    case True{}:
      Some{n}
    case False{}:
      None{}

# Some{n} if n <= LIMIT.
def bound(acc: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match acc:
    case Some{+n}:
      bound.pick(Nat.is_le(n, LIMIT()), n)
    case None{}:
      None{}

# One or more decimal digits (leading zeros allowed); Some only if the value
# is at most LIMIT.
def read(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      bound(dec_read.go(SCon{c, t}, Some{0n}))

# One or more hexadecimal digits, either case (leading zeros allowed); Some
# only if the value is at most LIMIT.
def hex_read(s: String) -> Maybe<&2, Nat>:
  match s:
    case SNil{}:
      None{}
    case SCon{c, t}:
      bound(hex_read.go(SCon{c, t}, Some{0n}))
