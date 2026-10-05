import Base
import ../src/bytes.bend as B

# Checker-evaluated tests for bytes.bend: `bend tests/bytes_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass. Besides the values,
# every loop is checked against its structural `.spec` on samples (the
# lemmas the law proofs use; see the note in bytes.bend).

def L() -> Type:
  List<&2, U32>

def main() ->
  # classes
  {B.class(13) == B.Cr{} : B.Class} &
  {B.class(48) == B.Digit{0n} : B.Class} &
  {B.class(70) == B.HexLetter{15n} : B.Class} &
  {B.class(200) == B.High{} : B.Class} &
  {B.class(256) == B.Invalid{} : B.Class} &
  # rev
  {B.rev(U32, [1, 2, 3], [9]) == [3, 2, 1, 9] : L()} &
  {B.rev(U32, [], [9]) == [9] : L()} &
  # all_bytes
  {B.all_bytes([]) == True{} : Bool} &
  {B.all_bytes([0, 128, 255]) == True{} : Bool} &
  {B.all_bytes([0, 256, 1]) == False{} : Bool} &
  {B.all_bytes([1, 2, 300]) == False{} : Bool} &
  {B.all_bytes([0, 128, 255]) == B.all_bytes.spec([0, 128, 255]) : Bool} &
  {B.all_bytes([1, 2, 300]) == B.all_bytes.spec([1, 2, 300]) : Bool} &
  {B.all_bytes.go([1, 2], False{}) == False{} : Bool} &
  # is_ascii
  {B.is_ascii("") == True{} : Bool} &
  {B.is_ascii("GET / HTTP/1.1\r\n") == True{} : Bool} &
  {B.is_ascii("caf\u{e9}") == False{} : Bool} &
  {B.is_ascii("\u{100}a") == False{} : Bool} &
  {B.is_ascii("a\u{7f}") == True{} : Bool} &
  {B.is_ascii("caf\u{e9}") == B.is_ascii.spec("caf\u{e9}") : Bool} &
  {B.is_ascii("ab\r\n") == B.is_ascii.spec("ab\r\n") : Bool} &
  # from_ascii
  {B.from_ascii("") == [] : L()} &
  {B.from_ascii("Hi\r\n") == [72, 105, 13, 10] : L()} &
  {B.from_ascii("Hi\r\n") == B.from_ascii.spec("Hi\r\n") : L()} &
  {B.from_ascii.rev("ab", [9]) == [98, 97, 9] : L()} &
  {B.from_ascii_onto("ab", [1, 2]) == [97, 98, 1, 2] : L()} &
  {B.from_ascii_onto("ab", [1, 2]) == List.append(&2, U32, B.from_ascii.spec("ab"), [1, 2]) : L()} &
  {B.from_ascii_onto("", [1]) == [1] : L()} &
  # to_ascii
  {B.to_ascii(B.from_ascii("Hello")) == Some{"Hello"} : Maybe<&2, String>} &
  {B.to_ascii([72, 200]) == None{} : Maybe<&2, String>} &
  # to_latin1 / latin1_onto
  {B.to_latin1([]) == "" : String} &
  {B.to_latin1([72, 105, 233, 255]) == "Hi\u{e9}\u{ff}" : String} &
  {B.to_latin1([72, 105, 233, 255]) == B.to_latin1.spec([72, 105, 233, 255]) : String} &
  {B.latin1_onto([99, 98, 97], "") == "abc" : String} &
  {B.latin1_onto([98, 97], "cd") == "abcd" : String} &
  {B.latin1_onto(B.rev(U32, [97, 98], []), "") == B.to_latin1.spec([97, 98]) : String}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
