import Base
import ../src/bytes.bend as B
import ../src/num.bend as N

# Checker-evaluated tests for num.bend: `bend tests/num_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass.

def T() -> Type:
  Maybe<&2, Nat>

def main() ->
  # digit chars classify as their own value
  {B.char_class(N.digit_char(0n)) == B.Digit{0n} : B.Class} &
  {B.char_class(N.digit_char(9n)) == B.Digit{9n} : B.Class} &
  {B.char_class(N.digit_char(10n)) == B.HexLetter{10n} : B.Class} &
  {B.char_class(N.digit_char(15n)) == B.HexLetter{15n} : B.Class} &
  # digit lists
  {N.dec_digits(0n) == [0n] : List<&2, Nat>} &
  {N.dec_digits(10n) == [0n, 1n] : List<&2, Nat>} &
  {N.dec_digits(109n) == [9n, 0n, 1n] : List<&2, Nat>} &
  {N.hex_digits(256n) == [0n, 0n, 1n] : List<&2, Nat>} &
  # show
  {N.show(0n) == "0" : String} &
  {N.show(7n) == "7" : String} &
  {N.show(10n) == "10" : String} &
  {N.show(99n) == "99" : String} &
  {N.show(100n) == "100" : String} &
  {N.show(1009n) == "1009" : String} &
  {N.show(65535n) == "65535" : String} &
  # hex_show
  {N.hex_show(0n) == "0" : String} &
  {N.hex_show(15n) == "f" : String} &
  {N.hex_show(16n) == "10" : String} &
  {N.hex_show(255n) == "ff" : String} &
  {N.hex_show(4096n) == "1000" : String} &
  {N.hex_show(48879n) == "beef" : String} &
  # read
  {N.read("0") == Some{0n} : T()} &
  {N.read("42") == Some{42n} : T()} &
  {N.read("007") == Some{7n} : T()} &
  {N.read("1234") == Some{1234n} : T()} &
  {N.read("") == None{} : T()} &
  {N.read(" 1") == None{} : T()} &
  {N.read("1 ") == None{} : T()} &
  {N.read("+1") == None{} : T()} &
  {N.read("-1") == None{} : T()} &
  {N.read("1a") == None{} : T()} &
  {N.read("a") == None{} : T()} &
  {N.read("1.0") == None{} : T()} &
  # hex_read
  {N.hex_read("0") == Some{0n} : T()} &
  {N.hex_read("ff") == Some{255n} : T()} &
  {N.hex_read("FF") == Some{255n} : T()} &
  {N.hex_read("BeE") == Some{3054n} : T()} &
  {N.hex_read("0010") == Some{16n} : T()} &
  {N.hex_read("") == None{} : T()} &
  {N.hex_read("g") == None{} : T()} &
  {N.hex_read("0x10") == None{} : T()} &
  {N.hex_read("1 ") == None{} : T()} &
  # roundtrips on samples
  {N.read(N.show(1234n)) == Some{1234n} : T()} &
  {N.hex_read(N.hex_show(4660n)) == Some{4660n} : T()} &
  {N.read(N.show(0n)) == Some{0n} : T()} &
  {N.hex_read(N.hex_show(0n)) == Some{0n} : T()} &
  # hostile text: control chars, non-ASCII, a char past 0xFF
  {N.read("1\r") == None{} : T()} &
  {N.read("\u{663}") == None{} : T()} &
  {N.hex_read("\u{ff}") == None{} : T()} &
  {N.read(SCon{Char.from_u32(4294967295), SNil{}}) == None{} : T()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
