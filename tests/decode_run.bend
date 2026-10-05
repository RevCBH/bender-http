import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/decode.bend as D
import ../src/spec.bend as S

# Runtime tests for decode.bend and spec.bend, on both lanes:
#   bend tests/decode_run.bend
#   bend tests/decode_run.bend -o /tmp/decode_run && /tmp/decode_run
# Prints PASS / FAIL per case, then "ALL PASS" or "SOME FAIL: n".
# These cover what the checker cannot evaluate (LIMIT-scale numbers, long
# lines, many headers, many interim responses) and sweeps: every prefix of a
# message is Incomplete, every budget below its length is TooLarge, every
# split of the input decodes the same. tests/decode_test.bend has the
# checker-evaluated cases; tests/decode_big_run.bend the 1 MiB timing run.

def R() -> Data:
  Result<&2, &2, M.ParseError, M.Decoded>

# Lists and text, as loops (long inputs must not nest calls on the JS lane)
# -----------------------------------------------------------------------

def rev(xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      rev(t, h <> acc)

def cat(xs: List<&2, U32>, ys: List<&2, U32>) -> List<&2, U32>:
  rev(rev(xs, Nil{}), ys)

def len.go(xs: List<&2, U32>, n: Nat) -> Nat:
  match xs:
    case Nil{}:
      n
    case Con{h, t}:
      len.go(t, 1n+n)

def len(xs: List<&2, U32>) -> Nat:
  len.go(xs, 0n)

def take.go(n: Nat, xs: List<&2, U32>, acc: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n _:
      rev(acc, Nil{})
    case 1n+p Nil{}:
      rev(acc, Nil{})
    case 1n+p Con{h, t}:
      take.go(p, t, h <> acc)

def take(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  take.go(n, xs, Nil{})

def drop(n: Nat, xs: List<&2, U32>) -> List<&2, U32>:
  match n xs:
    case 0n ys:
      ys
    case 1n+p Nil{}:
      Nil{}
    case 1n+p Con{h, t}:
      drop(p, t)

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

def str_eq(a: String, b: String) -> Bool:
  str_eq.go(a, b, True{})

def rep.go(n: Nat, +c: Char, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      rep.go(p, c, SCon{c, acc})

def rep(n: Nat, c: Char) -> String:
  rep.go(n, c, SNil{})

# s repeated n times (a loop).
def reps.go(n: Nat, +s: String, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+p:
      reps.go(p, s, s ++ acc)

def reps(n: Nat, s: String) -> String:
  reps.go(n, s, SNil{})

# The bytes of ASCII text, as a loop.
def ascii.go(r: String, acc: List<&2, U32>) -> List<&2, U32>:
  match r:
    case SNil{}:
      acc
    case SCon{c, t}:
      ascii.go(t, Char.to_u32(c) <> acc)

def ascii(s: String) -> List<&2, U32>:
  ascii.go(String.reverse(s), Nil{})

# Comparing results
# -----------------

def err_name(e: M.ParseError) -> String:
  match e:
    case M.BadStatusLine{}:
      "BadStatusLine"
    case M.BadVersion{}:
      "BadVersion"
    case M.BadHeader{}:
      "BadHeader"
    case M.BadLength{}:
      "BadLength"
    case M.ConflictingFraming{}:
      "ConflictingFraming"
    case M.UnsupportedEncoding{}:
      "UnsupportedEncoding"
    case M.BadChunk{}:
      "BadChunk"
    case M.UnexpectedUpgrade{}:
      "UnexpectedUpgrade"
    case M.Incomplete{}:
      "Incomplete"
    case M.TooLarge{}:
      "TooLarge"

def version_eq(a: M.Version, b: M.Version) -> Bool:
  match a b:
    case M.Http10{} M.Http10{}:
      True{}
    case M.Http11{} M.Http11{}:
      True{}
    case _ _:
      False{}

def headers_eq(a: List<&2, M.Header>, b: List<&2, M.Header>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{M.Header{n1, v1}, t1} Con{M.Header{n2, v2}, t2}:
      str_eq(n1, n2) && str_eq(v1, v2) && headers_eq(t1, t2)
    case _ _:
      False{}

def resp_eq(a: M.Response, b: M.Response) -> Bool:
  match a b:
    case M.Response{v1, s1, r1, h1, b1} M.Response{v2, s2, r2, h2, b2}:
      version_eq(v1, v2) && Nat.is_eq(s1, s2) && str_eq(r1, r2) && headers_eq(h1, h2)
        && bytes_eq(b1, b2)

def res_eq(a: R(), b: R()) -> Bool:
  match a b:
    case Done{M.Decoded{r1, x1}} Done{M.Decoded{r2, x2}}:
      resp_eq(r1, r2) && bytes_eq(x1, x2)
    case Fail{e1} Fail{e2}:
      String.eq(err_name(e1), err_name(e2))
    case _ _:
      False{}

def is_fail(e: M.ParseError, r: R()) -> Bool:
  res_eq(r, Fail{e})

def body_len(r: R()) -> Nat:
  match r:
    case Done{M.Decoded{M.Response{v, st, rs, hs, b}, rest}}:
      len(b)
    case Fail{e}:
      0n

def dec(m: M.Method, max: Nat, s: String) -> R():
  D.response(m, max, ascii(s))

def get(s: String) -> R():
  dec(M.GET{}, 16777216n, s)

# Long inputs are joined as byte lists (String ++ nests a call per char of
# its left side).
def getb(xs: List<&2, U32>) -> R():
  D.response(M.GET{}, 16777216n, xs)

def ok(v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, body: String,
  rest: String) -> R():
  Done{M.Decoded{M.Response{v, st, rs, hs, ascii(body)}, ascii(rest)}}

def H11() -> String:
  "HTTP/1.1 200 OK\r\n"

def CL5() -> List<&2, M.Header>:
  [M.Header{"Content-Length", "5"}]

def TE() -> List<&2, M.Header>:
  [M.Header{"Transfer-Encoding", "chunked"}]

def chunked(body: String) -> String:
  H11() ++ "Transfer-Encoding: chunked\r\n\r\n" ++ body

# Sweeps
# ------

# Every proper prefix (lengths 0 .. n-1) of xs decodes to Incomplete.
def prefixes_incomplete(n: Nat, +xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+(+p):
      is_fail(M.Incomplete{}, D.response(M.GET{}, 16777216n, take(p, xs)))
        && prefixes_incomplete(p, xs)

# Every budget below n fails with TooLarge.
def budgets_too_small(n: Nat, +xs: List<&2, U32>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+(+p):
      is_fail(M.TooLarge{}, D.response(M.GET{}, p, xs)) && budgets_too_small(p, xs)

# Feeding xs in two pieces, split at every point 0..n, gives the result of
# feeding it whole (law 9 at runtime).
def split_one(+n: Nat, +xs: List<&2, U32>, whole: R()) -> Bool:
  +s0 = D.init(M.GET{}, 16777216n)
  res_eq(D.finish(D.feed(D.feed(s0, take(n, xs)), drop(n, xs))), whole)

def splits_same(n: Nat, +xs: List<&2, U32>, +whole: R()) -> Bool:
  match n:
    case 0n:
      split_one(0n, xs, whole)
    case 1n+(+p):
      split_one(1n+p, xs, whole) && splits_same(p, xs, whole)

# Feeding xs one byte at a time with D.step gives the result of D.response.
def bytewise.go(xs: List<&2, U32>, s: D.State) -> D.State:
  match xs:
    case Nil{}:
      s
    case Con{h, t}:
      bytewise.go(t, D.step(s, h))

def bytewise(+xs: List<&2, U32>) -> Bool:
  res_eq(D.finish(bytewise.go(xs, D.init(M.GET{}, 16777216n))),
    D.response(M.GET{}, 16777216n, xs))

# A message with all three sweeps: n = its length.
def sweep_framed(+xs: List<&2, U32>) -> Bool:
  +n = len(xs)
  +whole = D.response(M.GET{}, 16777216n, xs)
  prefixes_incomplete(n, xs) && budgets_too_small(n, xs) && splits_same(n, xs, whole)
    && bytewise(xs) && Bool.not(is_fail(M.TooLarge{}, D.response(M.GET{}, n, xs)))

# Test data
# ---------

def r1() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}, M.Header{"X-A", "a b"}],
    [104, 101, 108, 108, 111]}

def rc() -> M.Response:
  M.Response{M.Http11{}, 203n, "Non-Authoritative", [M.Header{"Transfer-Encoding", "chunked"}],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 255, 13, 10]}

def rclose() -> M.Response:
  M.Response{M.Http10{}, 500n, "Internal Server Error", [M.Header{"Server", "x"}],
    [13, 10, 13, 10, 72, 84, 84, 80]}

def chunked_roundtrip(+n: Nat) -> Bool:
  res_eq(D.response(M.GET{}, 16777216n,
    cat(S.encode_head(rc()), cat(S.encode_chunked(n, S.response_body(rc())), [1, 2, 3]))),
    Done{M.Decoded{rc(), [1, 2, 3]}})

def chunked_roundtrips(n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+(+p):
      chunked_roundtrip(1n+p) && chunked_roundtrips(p)

# 2 KB (the limit cases below go up to D.LINE_MAX() and past it; every line
# helper is a loop, so a line of any length runs on the JS lane too).
def long_value() -> String:
  rep(2000n, 'v')

# A response whose head holds one header, Big: (n 'v's), then CL 0.
def big_header(n: Nat) -> List<&2, U32>:
  cat(ascii(H11() ++ "Big: "), ascii(rep(n, 'v') ++ "\r\nContent-Length: 0\r\n\r\n"))

def big_header_ok(n: Nat) -> R():
  ok(M.Http11{}, 200n, "OK", [M.Header{"Big", rep(n, 'v')}, M.Header{"Content-Length", "0"}], "", "")

# Status line "HTTP/1.1 200 " (13 bytes) and a reason of n 'R's.
def big_reason(n: Nat) -> List<&2, U32>:
  cat(ascii("HTTP/1.1 200 "), ascii(rep(n, 'R') ++ "\r\nContent-Length: 0\r\n\r\n"))

# A chunk-size line "1;" (2 bytes) and an extension of n 'e's.
def big_ext(n: Nat) -> List<&2, U32>:
  cat(ascii(chunked("1;")), ascii(rep(n, 'e') ++ "\r\nx\r\n0\r\n\r\n"))

# A trailer line "T: " (3 bytes) and n 't's.
def big_trailer(n: Nat) -> List<&2, U32>:
  cat(ascii(chunked("1\r\nx\r\n0\r\nT: ")), ascii(rep(n, 't') ++ "\r\n\r\n"))

# A line with no colon: "X" and n 'v's.
def big_bad(n: Nat) -> List<&2, U32>:
  cat(ascii(H11() ++ "X"), ascii(rep(n, 'v') ++ "\r\n\r\n"))

# n field lines "a: b" and then Content-Length: 3 (so n + 1 in all).
def n_headers(n: Nat) -> List<&2, U32>:
  cat(ascii(H11()), cat(ascii(reps(n, "a: b\r\n")), ascii("Content-Length: 3\r\n\r\nabc")))

# An interim 103 with n field lines.
def interim_n(n: Nat) -> List<&2, U32>:
  cat(ascii("HTTP/1.1 103 Early\r\n"), cat(ascii(reps(n, "L: x\r\n")), ascii("\r\n")))

# n trailer lines.
def n_trailers(n: Nat) -> List<&2, U32>:
  cat(ascii(chunked("1\r\nx\r\n0\r\n")), cat(ascii(reps(n, "T: 1\r\n")), ascii("\r\n")))

def cell_status(c: U32) -> R():
  D.response(M.GET{}, 100n, cat(ascii("HTTP/1.1 200 O"), [c, 13, 10, 13, 10]))

def cell_header(c: U32) -> R():
  D.response(M.GET{}, 100n, cat(ascii(H11() ++ "X: a"), [c, 13, 10, 13, 10]))

def many_headers() -> String:
  reps(500n, "X-Many: some value\r\n")

def interims() -> String:
  reps(400n, "HTTP/1.1 100 Continue\r\n\r\n")

def cases() -> List<(String & Bool)>:
  [
    # framings
    ("length", res_eq(get(H11() ++ "Content-Length: 5\r\n\r\nhelloEXTRA"),
      ok(M.Http11{}, 200n, "OK", CL5(), "hello", "EXTRA"))),
    ("length 0", res_eq(get(H11() ++ "Content-Length: 0\r\n\r\nX"),
      ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "0"}], "", "X"))),
    ("length list", res_eq(get(H11() ++ "Content-Length: 5 , 5\r\ncontent-length: 05\r\n\r\nhello"),
      ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5 , 5"},
        M.Header{"content-length", "05"}], "hello", ""))),
    ("length conflict", is_fail(M.BadLength{}, get(H11() ++ "Content-Length: 5\r\nContent-Length: 4\r\n\r\nhello"))),
    ("length list conflict", is_fail(M.BadLength{}, get(H11() ++ "Content-Length: 5, 4\r\n\r\nhello"))),
    ("length 20 nines", is_fail(M.BadLength{}, get(H11() ++ "Content-Length: 99999999999999999999\r\n\r\n"))),
    ("length 5000 nines", is_fail(M.BadLength{}, get(H11() ++ "Content-Length: " ++ rep(5000n, '9') ++ "\r\n\r\n"))),
    ("length LIMIT+1", is_fail(M.BadLength{}, get(H11() ++ "Content-Length: 4294967296\r\n\r\n"))),
    ("length LIMIT past budget", is_fail(M.TooLarge{}, get(H11() ++ "Content-Length: 4294967295\r\n\r\n"))),
    ("length 5000 zeros", res_eq(get(H11() ++ "Content-Length: " ++ rep(5000n, '0') ++ "5\r\n\r\nhello"),
      ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", rep(5000n, '0') ++ "5"}], "hello", ""))),
    ("chunked", res_eq(get(chunked("5;x=y\r\nhello\r\n1\r\n!\r\n0\r\nT: 1\r\n\r\nNEXT")),
      ok(M.Http11{}, 200n, "OK", TE(), "hello!", "NEXT"))),
    ("chunked size LIMIT+1", is_fail(M.TooLarge{}, get(chunked("100000000\r\n")))),
    ("chunked size 27 fs", is_fail(M.TooLarge{}, get(chunked("fffffffffffffffffffffffffff\r\n")))),
    ("chunked size 5000 Fs", is_fail(M.TooLarge{}, get(chunked(rep(5000n, 'F') ++ "\r\n")))),
    ("chunked size LIMIT past budget", is_fail(M.TooLarge{}, get(chunked("ffffffff\r\n")))),
    ("chunked size 5000 zeros", res_eq(get(chunked(rep(5000n, '0') ++ "1\r\nx\r\n0\r\n\r\n")),
      ok(M.Http11{}, 200n, "OK", TE(), "x", ""))),
    ("chunked bad size", is_fail(M.BadChunk{}, get(chunked("5x\r\nhello\r\n0\r\n\r\n")))),
    ("chunked bad ext", is_fail(M.BadChunk{}, get(chunked("5;\u{7f}\r\nhello\r\n0\r\n\r\n")))),
    ("chunked no CRLF", is_fail(M.BadChunk{}, get(chunked("5\r\nhello0\r\n\r\n")))),
    ("chunked bad trailer", is_fail(M.BadHeader{}, get(chunked("0\r\nX\r\n\r\n")))),
    ("te+cl", is_fail(M.ConflictingFraming{}, get(H11() ++ "Transfer-Encoding: chunked\r\nContent-Length: 0\r\n\r\n"))),
    ("te gzip", is_fail(M.UnsupportedEncoding{}, get(H11() ++ "Transfer-Encoding: gzip\r\n\r\n"))),
    ("close", res_eq(get(H11() ++ "\r\nabc\r\n\r\ndef"), ok(M.Http11{}, 200n, "OK", [], "abc\r\n\r\ndef", ""))),
    ("head", res_eq(dec(M.HEAD{}, 1000n, H11() ++ "Content-Length: 5\r\n\r\nX"),
      ok(M.Http11{}, 200n, "OK", CL5(), "", "X"))),
    ("204", res_eq(get("HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\n"),
      ok(M.Http11{}, 204n, "No Content", CL5(), "", ""))),
    ("304", res_eq(get("HTTP/1.1 304 Not Modified\r\n\r\nX"),
      ok(M.Http11{}, 304n, "Not Modified", [], "", "X"))),
    ("101", is_fail(M.UnexpectedUpgrade{}, get("HTTP/1.1 101 Switching Protocols\r\n\r\n"))),
    ("interim", res_eq(get("HTTP/1.1 100 Continue\r\nA: 1\r\n\r\n" ++ H11() ++ "Content-Length: 5\r\n\r\nhello"),
      ok(M.Http11{}, 200n, "OK", CL5(), "hello", ""))),
    ("400 interims", res_eq(getb(cat(ascii(interims()), ascii(H11() ++ "Content-Length: 5\r\n\r\nhello"))),
      ok(M.Http11{}, 200n, "OK", CL5(), "hello", ""))),
    ("400 interims charged", is_fail(M.TooLarge{},
      D.response(M.GET{}, 10042n, cat(ascii(interims()), ascii(H11() ++ "Content-Length: 5\r\n\r\nhello"))))),
    ("400 interims fit", res_eq(D.response(M.GET{}, 10043n,
      cat(ascii(interims()), ascii(H11() ++ "Content-Length: 5\r\n\r\nhello"))),
      ok(M.Http11{}, 200n, "OK", CL5(), "hello", ""))),
    # status lines
    ("http/1.0", res_eq(get("HTTP/1.0 200 OK\r\n\r\n"), ok(M.Http10{}, 200n, "OK", [], "", ""))),
    ("no reason", res_eq(get("HTTP/1.1 200\r\n\r\n"), ok(M.Http11{}, 200n, "", [], "", ""))),
    ("obs-text reason", res_eq(D.response(M.GET{}, 100n, cat(ascii("HTTP/1.1 200 "),
      [233, 255, 128, 9, 32, 13, 10, 13, 10])),
      ok(M.Http11{}, 200n, "\u{e9}\u{ff}\u{80}\t ", [], "", ""))),
    ("bad version", is_fail(M.BadVersion{}, get("HTTP/2.0 200 OK\r\n\r\n"))),
    ("bad status", is_fail(M.BadStatusLine{}, get("HTTP/1.1 2000 OK\r\n\r\n"))),
    ("status 99999999999999999999", is_fail(M.BadStatusLine{}, get("HTTP/1.1 99999999999999999999 OK\r\n\r\n"))),
    ("status 4000000000", is_fail(M.BadStatusLine{}, get("HTTP/1.1 4000000000 OK\r\n\r\n"))),
    ("non-byte cell", is_fail(M.BadStatusLine{}, D.response(M.GET{}, 100n,
      cat(ascii("HTTP/1.1 200 O"), [331, 13, 10, 13, 10])))),
    ("non-byte cell in header", is_fail(M.BadHeader{}, D.response(M.GET{}, 100n,
      cat(ascii(H11() ++ "A: "), [256, 13, 10, 13, 10])))),
    ("bare LF status", is_fail(M.BadStatusLine{}, get("HTTP/1.1 200 OK\n\r\n"))),
    # field lines
    ("ows trim", res_eq(get(H11() ++ "A: \t x y \t\r\nB:\r\n\r\n"),
      ok(M.Http11{}, 200n, "OK", [M.Header{"A", "x y"}, M.Header{"B", ""}], "", ""))),
    ("obs-fold", is_fail(M.BadHeader{}, get(H11() ++ "A: 1\r\n 2\r\n\r\n"))),
    ("bare LF header", is_fail(M.BadHeader{}, get(H11() ++ "A: 1\n\r\n"))),
    ("bare LF end", is_fail(M.BadHeader{}, get(H11() ++ "A: 1\r\n\n"))),
    ("space before colon", is_fail(M.BadHeader{}, get(H11() ++ "A : 1\r\n\r\n"))),
    ("2 KB header value", res_eq(getb(cat(ascii(H11() ++ "Big: "), ascii(long_value() ++ "\r\n\r\n"))),
      ok(M.Http11{}, 200n, "OK", [M.Header{"Big", long_value()}], "", ""))),
    ("long header line past budget", is_fail(M.TooLarge{},
      D.response(M.GET{}, 1024n, cat(ascii(H11() ++ "Big: "), ascii(long_value() ++ "\r\n\r\n"))))),
    ("500 headers", Nat.is_eq(body_len(getb(cat(ascii(H11()),
      cat(ascii(many_headers()), ascii("Content-Length: 3\r\n\r\nabc"))))), 3n)),
    # limits: a line holds at most LINE_MAX (65536) bytes, a head or a
    # trailer section at most FIELDS_MAX (1000) field lines; past them
    # TooLarge, never a crash (JS lane included)
    ("header line at LINE_MAX", res_eq(getb(big_header(65531n)), big_header_ok(65531n))),
    ("header line LINE_MAX+1", is_fail(M.TooLarge{}, getb(big_header(65532n)))),
    ("header line 100 KB", is_fail(M.TooLarge{}, getb(big_header(100000n)))),
    ("header line 1 MB", is_fail(M.TooLarge{}, getb(big_header(1000000n)))),
    ("reason at LINE_MAX", res_eq(getb(big_reason(65523n)),
      ok(M.Http11{}, 200n, rep(65523n, 'R'), [M.Header{"Content-Length", "0"}], "", ""))),
    ("reason LINE_MAX+1", is_fail(M.TooLarge{}, getb(big_reason(65524n)))),
    ("reason 64 KB+", is_fail(M.TooLarge{}, getb(big_reason(70000n)))),
    ("chunk ext at LINE_MAX", res_eq(getb(big_ext(65534n)), ok(M.Http11{}, 200n, "OK", TE(), "x", ""))),
    ("chunk ext LINE_MAX+1", is_fail(M.TooLarge{}, getb(big_ext(65535n)))),
    ("chunk ext 1 MB", is_fail(M.TooLarge{}, getb(big_ext(1000000n)))),
    ("trailer at LINE_MAX", res_eq(getb(big_trailer(65533n)), ok(M.Http11{}, 200n, "OK", TE(), "x", ""))),
    ("trailer LINE_MAX+1", is_fail(M.TooLarge{}, getb(big_trailer(65534n)))),
    ("bad line 65000", is_fail(M.BadHeader{}, getb(big_bad(65000n)))),
    ("content-length 65000 zeros", res_eq(get(H11() ++ "Content-Length: " ++ rep(65000n, '0') ++ "5\r\n\r\nhello"),
      ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", rep(65000n, '0') ++ "5"}], "hello", ""))),
    ("1000 headers", Nat.is_eq(body_len(getb(n_headers(999n))), 3n)),
    ("1001 headers", is_fail(M.TooLarge{}, getb(n_headers(1000n)))),
    ("30000 headers", is_fail(M.TooLarge{}, getb(n_headers(30000n)))),
    ("1000 headers per interim head", Nat.is_eq(body_len(getb(cat(interim_n(1000n),
      cat(interim_n(1000n), n_headers(999n))))), 3n)),
    ("1001 headers in an interim", is_fail(M.TooLarge{}, getb(cat(interim_n(1001n), n_headers(0n))))),
    ("1000 trailers", res_eq(getb(n_trailers(1000n)), ok(M.Http11{}, 200n, "OK", TE(), "x", ""))),
    ("1001 trailers", is_fail(M.TooLarge{}, getb(n_trailers(1001n)))),
    # cells that are not bytes fail the line (no abort on the JS lane)
    ("cell 55296 in status", is_fail(M.BadStatusLine{}, cell_status(55296))),
    ("cell 1114112 in status", is_fail(M.BadStatusLine{}, cell_status(1114112))),
    ("cell 55296 in header", is_fail(M.BadHeader{}, cell_header(55296))),
    ("cell 1114112 in header", is_fail(M.BadHeader{}, cell_header(1114112))),
    ("cell 4294967295 in header", is_fail(M.BadHeader{}, cell_header(4294967295))),
    # status code 3DIGIT; HTTP/1.0 with Transfer-Encoding
    ("status leading zero", is_fail(M.BadStatusLine{}, get("HTTP/1.1 0200 OK\r\n\r\n"))),
    ("http/1.0 chunked", is_fail(M.UnsupportedEncoding{},
      get("HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi\r\n0\r\n\r\n"))),
    # roundtrips
    ("length roundtrip", res_eq(D.response(M.GET{}, 1000n, cat(S.encode_response(r1()), [9, 9])),
      Done{M.Decoded{r1(), [9, 9]}})),
    ("chunked roundtrips n=1..30", chunked_roundtrips(30n)),
    ("close roundtrip", res_eq(D.response(M.GET{}, 1000n, S.encode_response(rclose())),
      Done{M.Decoded{rclose(), []}})),
    # sweeps
    ("sweep length", sweep_framed(S.encode_response(r1()))),
    ("sweep chunked", sweep_framed(cat(S.encode_head(rc()), S.encode_chunked(4n, S.response_body(rc()))))),
    ("sweep chunked ext trailers", sweep_framed(ascii(chunked("3;a=b\r\nabc\r\n0\r\nT: 1\r\n\r\n")))),
    ("sweep interim", sweep_framed(ascii("HTTP/1.1 103 Early\r\nL: x\r\n\r\n" ++ H11() ++ "Content-Length: 2\r\n\r\nhi"))),
    ("splits close", splits_same(70n, S.encode_response(rclose()),
      D.response(M.GET{}, 16777216n, S.encode_response(rclose())))),
    ("bytewise close", bytewise(S.encode_response(rclose()))),
    ("done stops", D.done(D.feed(D.init(M.GET{}, 100n), S.encode_response(r1())))
      && Bool.not(D.done(D.feed(D.init(M.GET{}, 100n), S.encode_response(rclose())))))
  ]

def report(xs: List<(String & Bool)>, fails: Nat) -> IO(Unit):
  match xs:
    case Nil{}:
      match fails:
        case 0n:
          IO.print("ALL PASS")
        case 1n+p:
          IO.print("SOME FAIL: " ++ Nat.show(1n+p))
    case Con{c, t}:
      match c:
        case (name, ok):
          match ok:
            case True{}:
              do IO<Unit>:
                IO.print("PASS " ++ name)
                report(t, fails)
            case False{}:
              do IO<Unit>:
                IO.print("FAIL " ++ name)
                report(t, 1n+fails)

def main() -> IO(Unit):
  report(cases(), 0n)
