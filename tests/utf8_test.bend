import Base
import ../src/utf8.bend as T

# Checker-evaluated tests for utf8.bend: `bend tests/utf8_test.bend` (or
# --check-only) printing ALL PROOFS CHECK is a pass.

def L() -> Type:
  List<&2, U32>

def S() -> Type:
  Maybe<&2, String>

def main() ->
  # encode: one sample per width, and the boundaries
  {T.encode("") == [] : L()} &
  {T.encode("Hi") == [72, 105] : L()} &
  {T.encode("\u{0}") == [0] : L()} &
  {T.encode("\u{7f}") == [127] : L()} &
  {T.encode("\u{80}") == [194, 128] : L()} &
  {T.encode("\u{e9}") == [195, 169] : L()} &
  {T.encode("\u{7ff}") == [223, 191] : L()} &
  {T.encode("\u{800}") == [224, 160, 128] : L()} &
  {T.encode("\u{20ac}") == [226, 130, 172] : L()} &
  {T.encode("\u{d7ff}") == [237, 159, 191] : L()} &
  {T.encode("\u{e000}") == [238, 128, 128] : L()} &
  {T.encode("\u{ffff}") == [239, 191, 191] : L()} &
  {T.encode("\u{10000}") == [240, 144, 128, 128] : L()} &
  {T.encode("\u{1f600}") == [240, 159, 152, 128] : L()} &
  {T.encode("\u{10ffff}") == [244, 143, 191, 191] : L()} &
  # chars that are not scalar values become U+FFFD
  {T.encode(SCon{Char.from_u32(55296), SNil{}}) == [239, 191, 189] : L()} &
  {T.encode(SCon{Char.from_u32(57343), SNil{}}) == [239, 191, 189] : L()} &
  {T.encode(SCon{Char.from_u32(1114112), SNil{}}) == [239, 191, 189] : L()} &
  # decode: valid
  {T.decode([]) == Some{""} : S()} &
  {T.decode([72, 105]) == Some{"Hi"} : S()} &
  {T.decode([0]) == Some{"\u{0}"} : S()} &
  {T.decode([194, 128]) == Some{"\u{80}"} : S()} &
  {T.decode([99, 97, 102, 195, 169]) == Some{"caf\u{e9}"} : S()} &
  {T.decode([223, 191]) == Some{"\u{7ff}"} : S()} &
  {T.decode([224, 160, 128]) == Some{"\u{800}"} : S()} &
  {T.decode([237, 159, 191]) == Some{"\u{d7ff}"} : S()} &
  {T.decode([238, 128, 128]) == Some{"\u{e000}"} : S()} &
  {T.decode([239, 191, 191]) == Some{"\u{ffff}"} : S()} &
  {T.decode([240, 144, 128, 128]) == Some{"\u{10000}"} : S()} &
  {T.decode([244, 143, 191, 191]) == Some{"\u{10ffff}"} : S()} &
  {T.decode([239, 187, 191, 65]) == Some{"\u{feff}A"} : S()} &
  # decode: overlong forms
  {T.decode([192, 128]) == None{} : S()} &
  {T.decode([193, 191]) == None{} : S()} &
  {T.decode([224, 128, 128]) == None{} : S()} &
  {T.decode([224, 159, 191]) == None{} : S()} &
  {T.decode([240, 128, 128, 128]) == None{} : S()} &
  {T.decode([240, 143, 191, 191]) == None{} : S()} &
  # decode: surrogates and past U+10FFFF
  {T.decode([237, 160, 128]) == None{} : S()} &
  {T.decode([237, 191, 191]) == None{} : S()} &
  {T.decode([237, 160, 189, 237, 184, 128]) == None{} : S()} &
  {T.decode([244, 144, 128, 128]) == None{} : S()} &
  {T.decode([245, 128, 128, 128]) == None{} : S()} &
  {T.decode([255]) == None{} : S()} &
  {T.decode([254]) == None{} : S()} &
  # decode: stray continuation bytes, truncation, bad continuation
  {T.decode([128]) == None{} : S()} &
  {T.decode([65, 191]) == None{} : S()} &
  {T.decode([195]) == None{} : S()} &
  {T.decode([65, 226, 130]) == None{} : S()} &
  {T.decode([240, 159, 152]) == None{} : S()} &
  {T.decode([195, 65]) == None{} : S()} &
  {T.decode([226, 130, 65]) == None{} : S()} &
  {T.decode([195, 195, 169]) == None{} : S()} &
  # decode: cells that are not bytes
  {T.decode([256]) == None{} : S()} &
  {T.decode([65, 321]) == None{} : S()} &
  {T.decode([195, 425]) == None{} : S()} &
  {T.decode([195, 4294967295]) == None{} : S()} &
  # roundtrip samples
  {T.decode(T.encode("h\u{e9}llo \u{20ac} \u{1f600}")) == Some{"h\u{e9}llo \u{20ac} \u{1f600}"} : S()}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
