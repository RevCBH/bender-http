import Base
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/decode.bend as D
import ../src/spec.bend as S

# Speed and scale on the C lane:
#   bend tests/decode_big_run.bend -o /tmp/decode_big && time /tmp/decode_big
# 1 MiB bodies (Content-Length, chunked, close-delimited) fed to D.feed in
# pseudo-random pieces of 1..8192 bytes, as a socket reader would; a header
# line of exactly D.LINE_MAX() bytes, and a 1 MB one (TooLarge, at once).
# Prints PASS / FAIL per case with its time in ms, then ALL PASS or SOME
# FAIL. C lane only: S's encoder (List.append, List.take, List.length) and
# S.response_ok (String.length) nest a call per byte, which the JS lane's
# stack cannot hold at this size. (tests/decode_run.bend runs the decoder's
# limit cases on both lanes.)

def R() -> Data:
  Result<&2, &2, M.ParseError, M.Decoded>

def MiB() -> Nat:
  1048576n

# Lists, as loops
# ---------------

def rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev(t, h <> acc)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  rev(rev(xs, Nil{}), ys)

def bytes_eq.go(a: List<&2, U32>, b: List<&2, U32>, ok: Bool) -> Bool:
  match a b:
    case Nil{} Nil{}:
      ok
    case Con{x, xs} Con{y, ys}:
      bytes_eq.go(xs, ys, ok && U32.is_eq(x, y))
    case _ _:
      False{}

def bytes_eq(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  bytes_eq.go(a, b, True{})

def str_eq.go(a: String, b: String, ok: Bool) -> Bool:
  match a b:
    case SNil{} SNil{}:
      ok
    case SCon{x, xs} SCon{y, ys}:
      str_eq.go(xs, ys, ok && Char.is_eq(x, y))
    case _ _:
      False{}

def headers_eq(a: List<&2, M.Header>, b: List<&2, M.Header>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{M.Header{n1, v1}, t1} Con{M.Header{n2, v2}, t2}:
      str_eq.go(n1, n2, True{}) && str_eq.go(v1, v2, True{}) && headers_eq(t1, t2)
    case _ _:
      False{}

def res_is(r: R(), +want: M.Response, rest: List<&2, U32>) -> Bool:
  match r want:
    case Done{M.Decoded{M.Response{v, s1, r1, h1, b1}, x}} M.Response{w, s2, r2, h2, b2}:
      Nat.is_eq(s1, s2) && str_eq.go(r1, r2, True{}) && headers_eq(h1, h2) && bytes_eq(b1, b2)
        && bytes_eq(x, rest)
    case _ _:
      False{}

def is_too_large(r: R()) -> Bool:
  match r:
    case Fail{M.TooLarge{}}:
      True{}
    case _:
      False{}

# Data
# ----

# n bytes, a repeating pattern of every value 0..255 at odd steps.
def body.go(n: Nat, +i: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      acc
    case 1n+p:
      body.go(p, (i + 1 : U32), ((i * 167 + 13) .&. 255 : U32) <> acc)

def body(n: Nat) -> List<&2, U32>:
  body.go(n, 0, Nil{})

def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rlen(+b: List<&2, U32>) -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Content-Type", "application/octet-stream"},
    M.Header{"Content-Length", N.show(MiB())}], b}

def rchunked(+b: List<&2, U32>) -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], b}

def rclose(+b: List<&2, U32>) -> M.Response:
  M.Response{M.Http10{}, 200n, "OK", [M.Header{"Server", "t"}], b}

# A header "Big: " ++ n 'v's: its line is n + 5 bytes.
def rline(n: Nat) -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Big", rep.go(n, 'v', SNil{})},
    M.Header{"Content-Length", "0"}], []}

# A reason of n 'R's: the status line is n + 13 bytes.
def rreason(n: Nat) -> M.Response:
  M.Response{M.Http11{}, 200n, rep.go(n, 'R', SNil{}), [M.Header{"Content-Length", "0"}], []}

# n headers "a: b", then Content-Length: 0 (n + 1 in all).
def many.go(n: Nat, acc: List<&2, M.Header>) -> List<&2, M.Header>:
  match n:
    case 0n:
      acc
    case 1n+p:
      many.go(p, M.Header{"a", "b"} <> acc)

def rheaders(n: Nat) -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", many.go(n, [M.Header{"Content-Length", "0"}]), []}

# Feeding in pieces
# -----------------

def next(+seed: U32) -> U32:
  (seed * 1103515245 + 12345 : U32)

# 1..8192
def size(+seed: U32) -> Nat:
  1n+U32.to_nat(((seed >> 8n) .&. 8191 : U32))

# The first n bytes of xs (reversed onto acc, then put back in order), and the rest.
def cut(n: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32> & List<&2, U32>:
  match n xs:
    case 0n ys:
      (rev(acc, Nil{}), ys)
    case 1n+p Nil{}:
      (rev(acc, Nil{}), Nil{})
    case 1n+p Con{h, t}:
      cut(p, t, h <> acc)

# Feeds the piece in pr, then fuel more pieces of random sizes, then
# whatever is left in one go.
def pieces(fuel: Nat, +seed: U32, pr: List<&2, U32> & List<&2, U32>, s: D.State) -> D.State:
  match fuel:
    case 0n:
      (piece, rest) = pr
      D.feed(D.feed(s, piece), rest)
    case 1n+f:
      (piece, rest) = pr
      +s2 = next(seed)
      pieces(f, s2, cut(size(s2), rest, Nil{}), D.feed(s, piece))

def decode_pieces(max: Nat, xs: List<&2, U32>) -> R():
  D.finish(pieces(4000n, 7, (Nil{}, xs), D.init(M.GET{}, max)))

# Cases
# -----

def verdict(ok: Bool) -> String:
  match ok:
    case True{}:
      "PASS "
    case False{}:
      "FAIL "

# Runs the case after reading the clock (the case is a closure, so its work
# happens between the two readings).
def timed(name: String, run: Unit -> Bool) -> IO(Bool):
  do IO<Bool>:
    t0 : Nat <- IO.now()
    +ok : Bool = run(Unit{})
    IO.print(verdict(ok) ++ name)
    t1 : Nat <- IO.now()
    IO.print("  " ++ Nat.show(Nat.sub(t1, t0)) ++ " ms")
    return ok

def case_length() -> Bool:
  +b = body(MiB())
  res_is(decode_pieces(16777216n, cat(S.encode_response(rlen(b)), [1, 2, 3])), rlen(b), [1, 2, 3])

def case_length_whole() -> Bool:
  +b = body(MiB())
  res_is(D.response(M.GET{}, 16777216n, cat(S.encode_response(rlen(b)), [4])), rlen(b), [4])

def case_chunked(+n: Nat) -> Bool:
  +b = body(MiB())
  res_is(decode_pieces(16777216n, cat(S.encode_head(rchunked(b)), cat(S.encode_chunked(n, b), [9]))),
    rchunked(b), [9])

def case_close() -> Bool:
  +b = body(MiB())
  res_is(decode_pieces(16777216n, S.encode_response(rclose(b))), rclose(b), [])

def case_budget_length() -> Bool:
  is_too_large(decode_pieces(MiB(), S.encode_response(rlen(body(MiB())))))

def case_budget_close() -> Bool:
  is_too_large(decode_pieces(MiB(), S.encode_response(rclose(body(MiB())))))

# At the limit: S.response_ok holds and the response round-trips; one past
# it: S.response_ok fails and the decoder says TooLarge. (S's limits and
# D's agree.)
def at_limit(+r: M.Response) -> Bool:
  S.response_ok(r) && res_is(decode_pieces(16777216n, S.encode_response(r)), r, [])

def past_limit(+r: M.Response) -> Bool:
  Bool.not(S.response_ok(r)) && is_too_large(decode_pieces(16777216n, S.encode_response(r)))

def case_line() -> Bool:
  at_limit(rline(65531n)) && past_limit(rline(65532n))

def case_line_1mb() -> Bool:
  past_limit(rline(1000000n))

def case_reason() -> Bool:
  at_limit(rreason(65523n)) && past_limit(rreason(65524n))

def case_headers() -> Bool:
  at_limit(rheaders(999n)) && past_limit(rheaders(1000n))

def main() -> IO(Unit):
  do IO<Unit>:
    a : Bool <- timed("length 1 MiB, random pieces", u => case_length())
    b : Bool <- timed("length 1 MiB, whole", u => case_length_whole())
    c : Bool <- timed("chunked 1 MiB in 4096-byte chunks, random pieces", u => case_chunked(4096n))
    d : Bool <- timed("chunked 1 MiB in 1000-byte chunks, random pieces", u => case_chunked(1000n))
    e : Bool <- timed("close 1 MiB, random pieces", u => case_close())
    f : Bool <- timed("length 1 MiB past a 1 MiB budget: TooLarge", u => case_budget_length())
    g : Bool <- timed("close 1 MiB past a 1 MiB budget: TooLarge", u => case_budget_close())
    h : Bool <- timed("header line at LINE_MAX; one past it: TooLarge", u => case_line())
    i : Bool <- timed("1 MB header line: TooLarge", u => case_line_1mb())
    j : Bool <- timed("reason at LINE_MAX; one past it: TooLarge", u => case_reason())
    k : Bool <- timed("1000 field lines; 1001: TooLarge", u => case_headers())
    IO.print(Bool.pick(String, a && b && c && d && e && f && g && h && i && j && k, "ALL PASS", "SOME FAIL"))
