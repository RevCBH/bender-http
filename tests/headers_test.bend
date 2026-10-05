import Base
import ../src/message.bend as M
import ../src/headers.bend as H

# Checker-evaluated tests for headers.bend: `bend tests/headers_test.bend`
# (or --check-only) printing ALL PROOFS CHECK is a pass.

def hs() -> List<&2, M.Header>:
  [M.Header{"Content-Type", "text/plain"}, M.Header{"X-A", "1"},
   M.Header{"x-a", "2"}, M.Header{"Set-Cookie", "a=b"}, M.Header{"X-A", "3"}]

def S() -> Type:
  Maybe<&2, String>

def main() ->
  # tokens
  {H.is_token("Content-Type") == True{} : Bool} &
  {H.is_token("x!#$%&'*+-.^_`|~09azAZ") == True{} : Bool} &
  {H.is_token("") == False{} : Bool} &
  {H.is_token("a b") == False{} : Bool} &
  {H.is_token("a:b") == False{} : Bool} &
  {H.is_token("a\r\nb") == False{} : Bool} &
  {H.is_token("(x)") == False{} : Bool} &
  {H.is_token("caf\u{e9}") == False{} : Bool} &
  {H.is_token("a\u{100}") == False{} : Bool} &
  # values
  {H.is_value("") == True{} : Bool} &
  {H.is_value("text/html; charset=utf-8") == True{} : Bool} &
  {H.is_value("a\tb c") == True{} : Bool} &
  {H.is_value(" a") == False{} : Bool} &
  {H.is_value("a ") == False{} : Bool} &
  {H.is_value("\ta") == False{} : Bool} &
  {H.is_value("a\t") == False{} : Bool} &
  {H.is_value(" ") == False{} : Bool} &
  {H.is_value("a\r\nX-Evil: 1") == False{} : Bool} &
  {H.is_value("a\nb") == False{} : Bool} &
  {H.is_value("a\u{0}b") == False{} : Bool} &
  {H.is_value("a\u{7f}") == False{} : Bool} &
  {H.is_value("caf\u{e9}") == False{} : Bool} &
  # header_ok / headers_ok
  {H.header_ok(M.Header{"Accept", "*/*"}) == True{} : Bool} &
  {H.header_ok(M.Header{"Bad Name", "x"}) == False{} : Bool} &
  {H.header_ok(M.Header{"X", "bad\r\n"}) == False{} : Bool} &
  {H.headers_ok([]) == True{} : Bool} &
  {H.headers_ok(hs()) == True{} : Bool} &
  {H.headers_ok([M.Header{"A", "1"}, M.Header{"", "2"}]) == False{} : Bool} &
  # lower
  {H.lower("Content-TYPE") == "content-type" : String} &
  {H.lower("ABCDEFGHIJKLMNOPQRSTUVWXYZ") == "abcdefghijklmnopqrstuvwxyz" : String} &
  {H.lower("abcxyz09-_@[`{") == "abcxyz09-_@[`{" : String} &
  {H.lower("\u{c0}\u{de}\u{c9}") == "\u{c0}\u{de}\u{c9}" : String} &
  {H.lower("\u{100}\u{41}") == "\u{100}a" : String} &
  {H.lower(H.lower("MiXeD")) == H.lower("MiXeD") : String} &
  # name_eq
  {H.name_eq("HOST", "host") == True{} : Bool} &
  {H.name_eq("Host", "Hosts") == False{} : Bool} &
  {H.name_eq("a", "\u{c1}") == False{} : Bool} &
  # lookup
  {H.get("content-type", hs()) == Some{"text/plain"} : S()} &
  {H.get("X-A", hs()) == Some{"1"} : S()} &
  {H.get("missing", hs()) == None{} : S()} &
  {H.get("x-a", []) == None{} : S()} &
  {H.get_all("x-A", hs()) == ["1", "2", "3"] : List<&2, String>} &
  {H.get_all("nope", hs()) == [] : List<&2, String>} &
  {H.has("SET-COOKIE", hs()) == True{} : Bool} &
  {H.has("cookie", hs()) == False{} : Bool} &
  {H.count("x-a", hs()) == 3n : Nat} &
  {H.count("content-type", hs()) == 1n : Nat} &
  {H.count("host", hs()) == 0n : Nat} &
  {H.get(H.lower("X-A"), hs()) == H.get("X-A", hs()) : S()} &
  {H.get("SET-cookie", hs()) == Some{"a=b"} : S()} &
  {H.get("x-a", [M.Header{"A", "0"}, M.Header{"X-A", "1"}, M.Header{"x-a", "2"}]) == Some{"1"} : S()} &
  {H.has("x-a", [M.Header{"X-A", "1"}]) == True{} : Bool} &
  {H.has("x-a", []) == False{} : Bool} &
  {H.get_all("CONTENT-TYPE", hs()) == ["text/plain"] : List<&2, String>} &
  # loops agree with their specs (the lemmas in headers.bend)
  {H.get_all("X-a", hs()) == H.get_all.spec(H.lower("X-a"), hs()) : List<&2, String>} &
  {H.get_all.go("x-a", hs(), ["0"]) == ["0", "1", "2", "3"] : List<&2, String>} &
  {H.get("X-a", hs()) == List.head(&2, String, H.get_all.spec("x-a", hs())) : S()} &
  {H.has("Set-Cookie", hs()) == Bool.not(List.is_empty(&2, String, H.get_all.spec("set-cookie", hs()))) : Bool} &
  {H.lower("AbC-dE\u{c9}") == H.lower.spec("AbC-dE\u{c9}") : String} &
  {H.lower.go("BC", "a") == "abc" : String} &
  {H.all_tchar("ab-c") == H.all_tchar.spec("ab-c") : Bool} &
  {H.all_tchar("a b") == H.all_tchar.spec("a b") : Bool} &
  {H.all_tchar.go("ab", False{}) == False{} : Bool} &
  {H.all_field_char("a\tb") == H.all_field_char.spec("a\tb") : Bool} &
  {H.all_field_char("a\rb") == H.all_field_char.spec("a\rb") : Bool} &
  {H.headers_ok(hs()) == H.headers_ok.spec(hs()) : Bool} &
  {H.headers_ok([M.Header{"A", "1"}, M.Header{"", "2"}]) == H.headers_ok.spec([M.Header{"A", "1"}, M.Header{"", "2"}]) : Bool} &
  {H.headers_ok([M.Header{"", "2"}, M.Header{"A", "1"}]) == False{} : Bool} &
  # reserved
  {H.reserved("Host") == True{} : Bool} &
  {H.reserved("CONTENT-LENGTH") == True{} : Bool} &
  {H.reserved("transfer-encoding") == True{} : Bool} &
  {H.reserved("Connection") == True{} : Bool} &
  {H.reserved("Content-Type") == False{} : Bool} &
  {H.reserved("Hostname") == False{} : Bool} &
  {H.reserved("") == False{} : Bool}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
