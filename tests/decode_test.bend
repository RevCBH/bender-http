import Base
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/decode.bend as D
import ../src/spec.bend as S

# Checker-evaluated tests for decode.bend and spec.bend:
#   bend tests/decode_test.bend --check-only   (ALL PROOFS CHECK is a pass)
# Every framing, status line and field line variants, chunk extensions and
# trailers, budget exhaustion and truncation in every phase, and laws 9-16
# of docs/DESIGN.md on concrete inputs. Generated cases; keep the tuple at
# the end as long as the list of equalities.

def R() -> Type:
  Result<&2, &2, M.ParseError, M.Decoded>

def Bytes() -> Data:
  List<&2, U32>

def ok(v: M.Version, st: Nat, rs: String, hs: List<&2, M.Header>, body: String,
  rest: String) -> R():
  Done{M.Decoded{M.Response{v, st, rs, hs, B.from_ascii(body)}, B.from_ascii(rest)}}

# The state after feeding a message in two pieces, split after n bytes.
def split_at(+n: Nat, +xs: List<&2, U32>) -> D.State:
  D.feed(D.feed(D.init(M.GET{}, 400n), List.take(&2, U32, xs, n)), List.drop(&2, U32, xs, n))

def without_body(r: M.Response) -> M.Response:
  match r:
    case M.Response{v, st, rs, hs, b}:
      M.Response{v, st, rs, hs, []}

def body_len(r: R()) -> Nat:
  match r:
    case Done{M.Decoded{M.Response{v, st, rs, hs, b}, rest}}:
      List.length(&2, U32, b)
    case Fail{e}:
      0n

def r1() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}, M.Header{"X-A", "a b"}],
    [104, 101, 108, 108, 111]}

def r0() -> M.Response:
  M.Response{M.Http11{}, 201n, "Created", [M.Header{"content-length", "0"}], []}

def rbin() -> M.Response:
  M.Response{M.Http11{}, 299n, "x\ty", [M.Header{"Content-Length", "6"}, M.Header{"E", ""}],
    [0, 13, 10, 255, 128, 10]}

def rc() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}, M.Header{"T", "1"}],
    [104, 101, 108, 108, 111]}

def rc0() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"transfer-encoding", "Chunked"}], []}

def rc16() -> M.Response:
  M.Response{M.Http11{}, 500n, "Oops", [M.Header{"Transfer-Encoding", "chunked"}],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]}

def rclose() -> M.Response:
  M.Response{M.Http11{}, 404n, "Not Found", [M.Header{"Server", "t"}], [13, 10, 13, 10, 0, 255]}

def rclose0() -> M.Response:
  M.Response{M.Http11{}, 200n, "", [], []}

def r10() -> M.Response:
  M.Response{M.Http10{}, 200n, "OK", [M.Header{"Content-Length", "2"}], [111, 107]}

def r204() -> M.Response:
  M.Response{M.Http11{}, 204n, "No Content", [M.Header{"Content-Length", "5"}], []}

def r304() -> M.Response:
  M.Response{M.Http11{}, 304n, "Not Modified", [M.Header{"Transfer-Encoding", "chunked"}], []}

def r100() -> M.Response:
  M.Response{M.Http11{}, 100n, "Continue", [], []}

def r103() -> M.Response:
  M.Response{M.Http11{}, 103n, "Early Hints", [M.Header{"Link", "</s.css>"}], []}

def rboth() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"},
    M.Header{"Transfer-Encoding", "chunked"}], [104, 101, 108, 108, 111]}

# A reason with leading OWS: response_ok, and it round-trips.
def rows() -> M.Response:
  M.Response{M.Http11{}, 200n, " \tOK", [M.Header{"Content-Length", "2"}], [104, 105]}

# Law 13 edge: HEAD, status 999, HTTP/1.0, both framing headers.
def r999() -> M.Response:
  M.Response{M.Http10{}, 999n, "X", [M.Header{"Content-Length", "5"},
    M.Header{"Transfer-Encoding", "chunked"}], []}

def SM() -> Type:
  String & Maybe<&2, String>

# A state reading a line of this kind with this much room.
def at_line(kind: D.LineKind, room: Nat) -> D.State:
  D.State{M.GET{}, 400n, D.ReadLine{kind, [], room}}

def head_room(n: Nat) -> D.LineKind:
  D.KField{D.Head{M.Http11{}, 200n, "OK", [], n}}

def rA1() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"A", "1"}], []}

def rA1B2() -> M.Response:
  M.Response{M.Http11{}, 200n, "OK", [M.Header{"A", "1"}, M.Header{"B", "2"}], []}

def main() ->
  # Content-Length framing
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhelloEXTRA")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "hello", "EXTRA") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 0\r\n\r\nNEXT")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "0"}], "", "NEXT") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\ncontent-length: 5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}, M.Header{"content-length", "5"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5, 5 ,5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5, 5 ,5"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 005\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "005"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nContent-Length: 6\r\n\r\nhello!")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5,6\r\n\r\nhello!")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5,,5\r\n\r\nhello")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5,\r\n\r\nhello")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: \r\n\r\n")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: -1\r\n\r\n")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: +5\r\n\r\nhello")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 0x5\r\n\r\nhello")) == Fail{M.BadLength{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5 5\r\n\r\nhello")) == Fail{M.BadLength{}} : R()} &
  {D.content_length([M.Header{"Content-Length", "12"}, M.Header{"X", "1"}, M.Header{"CONTENT-LENGTH", "12, 012"}]) == Some{12n} : Maybe<&2, Nat>} &
  {D.content_length([M.Header{"X", "1"}]) == None{} : Maybe<&2, Nat>} &
  {D.content_length([]) == None{} : Maybe<&2, Nat>} &
  {D.content_length([M.Header{"Content-Length", "1"}, M.Header{"Content-Length", "2"}]) == None{} : Maybe<&2, Nat>} &
  {D.content_length([M.Header{"Content-Length", "x"}]) == None{} : Maybe<&2, Nat>} &
  # a Content-Length past the budget fails before the body arrives
  {D.response(M.GET{}, 100n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 500\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 43n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "hello", "") : R()} &
  {D.response(M.GET{}, 42n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 39n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 38n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  # chunked framing
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "NEXT") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhe\r\n3\r\nllo\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nA\r\n0123456789\r\na\r\nabcdefghij\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "0123456789abcdefghij", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n005\r\nhello\r\n000\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: CHUNKED\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "CHUNKED"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\ntransfer-encoding:  Chunked \r\n\r\n5\r\nhello\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"transfer-encoding", "Chunked"}], "hello", "") : R()} &
  # chunk extensions
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;name=value\r\nhello\r\n0;last\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5 ; a=\"b c\"; d\r\nhello\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;\r\nhello\r\n0\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5;a\u{1}\r\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  # trailers are parsed and discarded
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX-Sum: 1\r\nX-Other:  two \r\n\r\nNEXT")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "NEXT") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nbad trailer\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n folded\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX: 1\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  # bad chunks
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\nzz\r\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n\r\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n 5\r\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n-5\r\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0x5\r\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\nhello\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhelloX\r\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\rX0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\n0\r\n\r\n")) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n1000\r\nhello")) == Fail{M.TooLarge{}} : R()} &
  # Transfer-Encoding other than chunked alone; with Content-Length
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 5\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) == Fail{M.ConflictingFraming{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nTransfer-Encoding: chunked\r\n\r\nhello")) == Fail{M.ConflictingFraming{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: x\r\nTransfer-Encoding: gzip\r\n\r\nhello")) == Fail{M.ConflictingFraming{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip\r\n\r\nhello")) == Fail{M.UnsupportedEncoding{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: gzip, chunked\r\n\r\nhello")) == Fail{M.UnsupportedEncoding{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n")) == Fail{M.UnsupportedEncoding{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked, chunked\r\n\r\n0\r\n\r\n")) == Fail{M.UnsupportedEncoding{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: \r\n\r\n")) == Fail{M.UnsupportedEncoding{}} : R()} &
  # close-delimited
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nServer: x\r\n\r\nall of this\r\n is body")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Server", "x"}], "all of this\r\n is body", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 200 OK\r\n\r\nold")) ==
    ok(M.Http10{}, 200n, "OK", [], "old", "") : R()} &
  # no body: HEAD, 204, 304 (the bytes after the head are leftover)
  {D.response(M.HEAD{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nNEXT")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "", "NEXT") : R()} &
  {D.response(M.HEAD{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 204 No Content\r\nContent-Length: 5\r\n\r\nNEXT")) ==
    ok(M.Http11{}, 204n, "No Content", [M.Header{"Content-Length", "5"}], "", "NEXT") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 304 Not Modified\r\nTransfer-Encoding: chunked\r\n\r\n")) ==
    ok(M.Http11{}, 304n, "Not Modified", [M.Header{"Transfer-Encoding", "chunked"}], "", "") : R()} &
  {D.response(M.POST{}, 400n, B.from_ascii("HTTP/1.1 204 No Content\r\n\r\n")) ==
    ok(M.Http11{}, 204n, "No Content", [], "", "") : R()} &
  # interim responses
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 103 Early Hints\r\nLink: </a>\r\n\r\nHTTP/1.1 102 Processing\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "hello", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 204 No Content\r\n\r\n")) ==
    ok(M.Http11{}, 204n, "No Content", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\n\r\n")) == Fail{M.UnexpectedUpgrade{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 100 Continue\r\n\r\n")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 66n, B.from_ascii("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 68n, B.from_ascii("HTTP/1.1 100 Continue\r\n\r\nHTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhello")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Content-Length", "5"}], "hello", "") : R()} &
  # status lines
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 \r\n\r\n")) ==
    ok(M.Http11{}, 200n, "", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 404 Not  Found \r\n\r\n")) ==
    ok(M.Http11{}, 404n, "Not  Found ", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 \u{e9}t\u{e9}\tok\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "\u{e9}t\u{e9}\tok", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 999 X\r\n\r\n")) ==
    ok(M.Http11{}, 999n, "X", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 599 \r\n\r\n")) ==
    ok(M.Http11{}, 599n, "", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 404 Nope\r\n\r\n")) ==
    ok(M.Http10{}, 404n, "Nope", [], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 O\u{1}K\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 O\u{7f}K\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\rX\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1  200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 20 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 099 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 1000 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 2x0 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1\t200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.10 200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("http/1.1 200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTPS/1.1 200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("\r\nHTTP/1.1 200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/2 200 OK\r\n\r\n")) == Fail{M.BadVersion{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/2.0 200 OK\r\n\r\n")) == Fail{M.BadVersion{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.2 200 OK\r\n\r\n")) == Fail{M.BadVersion{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/0.9 200 OK\r\n\r\n")) == Fail{M.BadVersion{}} : R()} &
  {D.response(M.GET{}, 400n, [72, 84, 84, 80, 47, 49, 46, 49, 32, 50, 48, 48, 32, 300, 13, 10, 13, 10]) == Fail{M.BadStatusLine{}} : R()} &
  # field lines: OWS trimming, obs-text, empty values
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A:   v  \r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "v"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A:\tv\t\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "v"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A:v\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "v"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A:\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", ""}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A:   \r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", ""}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: a \t b\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "a \t b"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: a:b: c\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "a:b: c"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: caf\u{e9}\u{ff}\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "caf\u{e9}\u{ff}"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\n!#$%&'*+-.^_`|~09az: 1\r\nB: 2\r\nb: 3\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"!#$%&'*+-.^_`|~09az", "1"}, M.Header{"B", "2"}, M.Header{"b", "3"}], "", "") : R()} &
  # obs-fold, bad names, bad values, bare LF
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n folded\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\tfolded\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\n X-A: 1\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A : 1\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\n: 1\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nNoColon\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX(A): 1\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX\u{e9}: 1\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\u{0}2\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\u{7f}\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\rX\r\n\r\n")) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\rX")) == Fail{M.BadHeader{}} : R()} &
  # truncation: Incomplete in every phase
  {D.response(M.GET{}, 400n, B.from_ascii("")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 20")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\n")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\r")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\n\r\nhell")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhel")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r")) == Fail{M.Incomplete{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\nX: 1\r\n")) == Fail{M.Incomplete{}} : R()} &
  # budget exhaustion in every phase
  {D.response(M.GET{}, 0n, B.from_ascii("HTTP/1.1 200 OK\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 5n, B.from_ascii("HTTP/1.1 200 OK\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 16n, B.from_ascii("HTTP/1.1 200 OK\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 20n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 26n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 27n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "1"}], "", "") : R()} &
  {D.response(M.GET{}, 28n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\r\nbody")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 31n, B.from_ascii("HTTP/1.1 200 OK\r\nX-A: 1\r\n\r\nbody")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"X-A", "1"}], "body", "") : R()} &
  {D.response(M.GET{}, 47n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 52n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 56n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 59n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.GET{}, 62n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) ==
    ok(M.Http11{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "hello", "NEXT") : R()} &
  {D.response(M.GET{}, 61n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n")) == Fail{M.TooLarge{}} : R()} &
  # a failed state stays failed; done
  {D.done(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\n"))) == False{} : Bool} &
  {D.done(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 1\r\n\r\nx"))) == True{} : Bool} &
  {D.done(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\n\r\nxyz"))) == False{} : Bool} &
  {D.done(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/9"))) == False{} : Bool} &
  {D.done(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/9.9 200 OK\r\n"))) == True{} : Bool} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/9.9 200 OK\r\n\r\nHTTP/1.1 200 OK\r\n\r\n")) == Fail{M.BadVersion{}} : R()} &
  # law 9 feed_split, concrete: every split of a message gives the same state
  {split_at(0n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(1n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(9n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(17n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(18n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(30n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(46n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(47n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(50n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(55n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(62n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(64n, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\nNEXT")) : D.State} &
  {split_at(3n, B.from_ascii("HTTP/1.1 200 OK\r\n\r\n")) == D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\n\r\n")) : D.State} &
  # laws 10-12: roundtrips through S.encode_*
  {S.encode_response(r1()) == B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 5\r\nX-A: a b\r\n\r\nhello") : Bytes} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_response(r1()), [1, 2, 255])) == Done{M.Decoded{r1(), [1, 2, 255]}} : R()} &
  {D.response(M.GET{}, 53n, S.encode_response(r1())) == Done{M.Decoded{r1(), []}} : R()} &
  {D.response(M.GET{}, 52n, S.encode_response(r1())) == Fail{M.TooLarge{}} : R()} &
  {D.response(M.POST{}, 400n, S.encode_response(r0())) == Done{M.Decoded{r0(), []}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_response(r0()), [9])) == Done{M.Decoded{r0(), [9]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_response(rbin()), [0])) == Done{M.Decoded{rbin(), [0]}} : R()} &
  {S.encode_chunked(2n, [104, 101, 108, 108, 111]) == B.from_ascii("2\r\nhe\r\n2\r\nll\r\n1\r\no\r\n0\r\n\r\n") : Bytes} &
  {S.encode_chunked(7n, []) == B.from_ascii("0\r\n\r\n") : Bytes} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc()), List.append(&2, U32, S.encode_chunked(1n, S.response_body(rc())), [7, 8]))) == Done{M.Decoded{rc(), [7, 8]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc()), List.append(&2, U32, S.encode_chunked(2n, S.response_body(rc())), [7, 8]))) == Done{M.Decoded{rc(), [7, 8]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc()), List.append(&2, U32, S.encode_chunked(5n, S.response_body(rc())), [7, 8]))) == Done{M.Decoded{rc(), [7, 8]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc()), List.append(&2, U32, S.encode_chunked(100n, S.response_body(rc())), [7, 8]))) == Done{M.Decoded{rc(), [7, 8]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc0()), List.append(&2, U32, S.encode_chunked(3n, []), [7]))) == Done{M.Decoded{rc0(), [7]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc16()), S.encode_chunked(16n, S.response_body(rc16())))) == Done{M.Decoded{rc16(), []}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(rc16()), S.encode_chunked(3n, S.response_body(rc16())))) == Done{M.Decoded{rc16(), []}} : R()} &
  {D.response(M.GET{}, 400n, S.encode_response(rclose())) == Done{M.Decoded{rclose(), []}} : R()} &
  {D.response(M.GET{}, 400n, S.encode_response(rclose0())) == Done{M.Decoded{rclose0(), []}} : R()} &
  {D.response(M.GET{}, 400n, S.encode_response(r10())) == Done{M.Decoded{r10(), []}} : R()} &
  {S.response_ok(r1()) == True{} : Bool} &
  {S.response_ok(r0()) == True{} : Bool} &
  {S.response_ok(rc()) == True{} : Bool} &
  {S.response_ok(rclose()) == True{} : Bool} &
  {S.response_ok(r10()) == True{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 204n, "No Content", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 304n, "", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 199n, "", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 1000n, "", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 200n, " OK", [], []}) == True{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 200n, "O\rK", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 200n, "caf\u{e9}", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 200n, "OK", [M.Header{"A B", "1"}], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 200n, "OK", [M.Header{"A", " 1"}], []}) == False{} : Bool} &
  # law 13: no body
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(r204()), [1, 2])) == Done{M.Decoded{r204(), [1, 2]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(r304()), [])) == Done{M.Decoded{r304(), []}} : R()} &
  {D.response(M.HEAD{}, 400n, List.append(&2, U32, S.encode_head(r1()), [3])) == Done{M.Decoded{without_body(r1()), [3]}} : R()} &
  {D.response(M.HEAD{}, 400n, List.append(&2, U32, S.encode_head(rc()), [])) == Done{M.Decoded{without_body(rc()), []}} : R()} &
  # law 14: interim skipped
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(r100()), List.append(&2, U32, S.encode_response(r1()), [5]))) == Done{M.Decoded{r1(), [5]}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, S.encode_head(r103()), List.append(&2, U32, S.encode_head(r100()), S.encode_response(r1())))) == Done{M.Decoded{r1(), []}} : R()} &
  # law 15: Content-Length with Transfer-Encoding fails
  {D.response(M.GET{}, 400n, S.encode_response(rboth())) == Fail{M.ConflictingFraming{}} : R()} &
  # law 16: size bound, concrete
  {body_len(D.response(M.GET{}, 53n, S.encode_response(r1()))) == 5n : Nat} &
  {Nat.is_le(body_len(D.response(M.GET{}, 400n, S.encode_response(rclose()))), 400n) == True{} : Bool} &
  {body_len(D.response(M.GET{}, 40n, S.encode_response(rclose()))) == 0n : Nat} &
  # response_ok / head_ok (laws 10-15 hypotheses)
  {S.response_ok(rows()) == True{} : Bool} &
  {D.response(M.GET{}, 400n, S.encode_response(rows())) == Done{M.Decoded{rows(), []}} : R()} &
  {S.response_ok(M.Response{M.Http11{}, 999n, "X", [], []}) == True{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 101n, "X", [], []}) == False{} : Bool} &
  {S.response_ok(M.Response{M.Http11{}, 100n, "X", [], []}) == False{} : Bool} &
  {S.head_ok(r204()) == True{} : Bool} &
  {S.head_ok(r100()) == True{} : Bool} &
  {S.head_ok(r999()) == True{} : Bool} &
  {S.head_ok(M.Response{M.Http11{}, 100n, "\r", [], []}) == False{} : Bool} &
  {S.head_ok(M.Response{M.Http11{}, 204n, "No Content", [M.Header{"A", " a"}], []}) == False{} : Bool} &
  {D.response(M.HEAD{}, 400n, List.append(&2, U32, S.encode_head(r999()), [1])) == Done{M.Decoded{r999(), [1]}} : R()} &
  # status code: 3DIGIT, no leading zeros
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 0200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 000000000000000000000000000204 OK\r\nContent-Length: 2\r\n\r\nhi")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 0100 Continue\r\n\r\nHTTP/1.1 200 OK\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 00101 X\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 000 X\r\n\r\n")) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.1 100 X\r\n\r\nHTTP/1.1 100 Y\r\n\r\nHTTP/1.1 200 Z\r\n\r\n")) ==
    ok(M.Http11{}, 200n, "Z", [], "", "") : R()} &
  # HTTP/1.0 with Transfer-Encoding is faulty (RFC 9112 6.1)
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nhi\r\n0\r\n\r\nZ")) == Fail{M.UnsupportedEncoding{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 200 OK\r\nTransfer-Encoding: gzip\r\n\r\nhi")) == Fail{M.UnsupportedEncoding{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\nContent-Length: 2\r\n\r\nhi")) == Fail{M.ConflictingFraming{}} : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 204 X\r\nTransfer-Encoding: chunked\r\n\r\nZ")) ==
    ok(M.Http10{}, 204n, "X", [M.Header{"Transfer-Encoding", "chunked"}], "", "Z") : R()} &
  {D.response(M.HEAD{}, 400n, B.from_ascii("HTTP/1.0 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n")) ==
    ok(M.Http10{}, 200n, "OK", [M.Header{"Transfer-Encoding", "chunked"}], "", "") : R()} &
  {D.response(M.GET{}, 400n, B.from_ascii("HTTP/1.0 200 OK\r\nContent-Length: 2\r\n\r\nhiZ")) ==
    ok(M.Http10{}, 200n, "OK", [M.Header{"Content-Length", "2"}], "hi", "Z") : R()} &
  # cells that are not bytes (not Unicode scalars either) fail the line
  {D.response(M.GET{}, 400n, List.append(&2, U32, B.from_ascii("HTTP/1.1 200 O"), [55296, 13, 10, 13, 10])) == Fail{M.BadStatusLine{}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, B.from_ascii("HTTP/1.1 200 OK\r\nX: a"), [1114112, 13, 10, 13, 10])) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5"), [55296, 13, 10])) == Fail{M.BadChunk{}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\nX: "), [4294967295, 13, 10, 13, 10])) == Fail{M.BadHeader{}} : R()} &
  {D.response(M.GET{}, 400n, List.append(&2, U32, B.from_ascii("HTTP/1.1 200 OK\r\n\r\n"), [55296, 1114112])) ==
    Done{M.Decoded{M.Response{M.Http11{}, 200n, "OK", [], [55296, 1114112]}, []}} : R()} &
  # close_delimited: only a body that runs to the close
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\n\r\nab"))) == True{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.0 200 OK\r\nServer: x\r\n\r\n"))) == True{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\na"))) == False{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nab"))) == False{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n0\r\n\r\n"))) == False{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.HEAD{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\n\r\n"))) == False{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\n"))) == False{} : Bool} &
  {D.close_delimited(D.feed(D.init(M.GET{}, 400n), B.from_ascii("HTTP/1.1 200 OK\r\nX\r\n\r\n"))) == False{} : Bool} &
  # line and field-count limits (the real ones, LINE_MAX and FIELDS_MAX, in decode_run)
  {D.LINE_MAX() == 65536n : Nat} &
  {D.FIELDS_MAX() == 1000n : Nat} &
  {D.init(M.GET{}, 7n) == D.State{M.GET{}, 7n, D.ReadLine{D.KStatus{}, [], 65536n}} : D.State} &
  {D.line_push(D.KStatus{}, [], 0n, 65) == D.Failed{M.TooLarge{}} : D.Phase} &
  {D.field_add(D.Head{M.Http11{}, 200n, "OK", [], 0n}, Some{M.Header{"A", "1"}}) == D.Failed{M.TooLarge{}} : D.Phase} &
  {D.trailer_add(Some{M.Header{"A", "1"}}, r1(), [], 0n) == D.Failed{M.TooLarge{}} : D.Phase} &
  {D.finish(D.feed(at_line(head_room(9n), 4n), B.from_ascii("A: 1\r\n\r\n"))) == Done{M.Decoded{rA1(), []}} : R()} &
  {D.finish(D.feed(at_line(head_room(9n), 3n), B.from_ascii("A: 1\r\n\r\n"))) == Fail{M.TooLarge{}} : R()} &
  {D.finish(D.feed(at_line(head_room(9n), 3n), B.from_ascii("A:\n"))) == Fail{M.BadHeader{}} : R()} &
  {D.finish(D.feed(at_line(D.KStatus{}, 15n), B.from_ascii("HTTP/1.1 200 OK\r\n\r\n"))) ==
    ok(M.Http11{}, 200n, "OK", [], "", "") : R()} &
  {D.finish(D.feed(at_line(D.KStatus{}, 14n), B.from_ascii("HTTP/1.1 200 OK\r\n\r\n"))) == Fail{M.TooLarge{}} : R()} &
  {D.finish(D.feed(at_line(head_room(2n), 65536n), B.from_ascii("A: 1\r\nB: 2\r\n\r\n"))) == Done{M.Decoded{rA1B2(), []}} : R()} &
  {D.finish(D.feed(at_line(head_room(1n), 65536n), B.from_ascii("A: 1\r\nB: 2\r\n\r\n"))) == Fail{M.TooLarge{}} : R()} &
  {D.finish(D.feed(at_line(head_room(0n), 65536n), B.from_ascii("\r\n"))) == ok(M.Http11{}, 200n, "OK", [], "", "") : R()} &
  {D.finish(D.feed(at_line(D.KTrailer{rA1(), [], 1n}, 65536n), B.from_ascii("A: 1\r\n\r\nZ"))) == Done{M.Decoded{rA1(), [90]}} : R()} &
  {D.finish(D.feed(at_line(D.KTrailer{rA1(), [], 1n}, 65536n), B.from_ascii("A: 1\r\nB: 2\r\n\r\n"))) == Fail{M.TooLarge{}} : R()} &
  {D.finish(D.feed(at_line(D.KSize{rA1(), []}, 3n), B.from_ascii("0;x\r\n\r\n"))) == Done{M.Decoded{rA1(), []}} : R()} &
  {D.finish(D.feed(at_line(D.KSize{rA1(), []}, 2n), B.from_ascii("0;x\r\n\r\n"))) == Fail{M.TooLarge{}} : R()} &
  # the line helpers' loops agree with their specs (the lemmas, on samples)
  {D.split(D.AtColon{}, "") == D.split.spec(D.AtColon{}, "") : SM()} &
  {D.split(D.AtColon{}, "abc") == D.split.spec(D.AtColon{}, "abc") : SM()} &
  {D.split(D.AtColon{}, ":") == D.split.spec(D.AtColon{}, ":") : SM()} &
  {D.split(D.AtColon{}, "a:") == D.split.spec(D.AtColon{}, "a:") : SM()} &
  {D.split(D.AtColon{}, ":b") == D.split.spec(D.AtColon{}, ":b") : SM()} &
  {D.split(D.AtColon{}, "ab:c:d") == ("ab", Some{"c:d"}) : SM()} &
  {D.split(D.AtSp{}, "200 OK now") == D.split.spec(D.AtSp{}, "200 OK now") : SM()} &
  {D.split(D.AtSemi{}, "5 ;x") == ("5 ", Some{"x"}) : SM()} &
  {D.trim_left("") == D.trim_left.spec("") : String} &
  {D.trim_left(" \t ") == D.trim_left.spec(" \t ") : String} &
  {D.trim_left(" \ta b\t ") == D.trim_left.spec(" \ta b\t ") : String} &
  {D.trim_left("x") == D.trim_left.spec("x") : String} &
  {D.trim_right("") == D.trim_right.spec("") : String} &
  {D.trim_right(" \t ") == D.trim_right.spec(" \t ") : String} &
  {D.trim_right(" \ta b\t ") == D.trim_right.spec(" \ta b\t ") : String} &
  {D.trim_right("x") == D.trim_right.spec("x") : String} &
  {D.trim(" \ta b\t ") == "a b" : String} &
  {D.items("") == D.items.spec("") : List<&2, String>} &
  {D.items(",") == D.items.spec(",") : List<&2, String>} &
  {D.items("1, 2,,3 ") == D.items.spec("1, 2,,3 ") : List<&2, String>} &
  {D.items("ab") == D.items.spec("ab") : List<&2, String>} &
  {D.items("1, 2,,3 ") == ["1", " 2", "", "3 "] : List<&2, String>} &
  {D.all_text("a \t\u{e9}") == D.all_text.spec("a \t\u{e9}") : Bool} &
  {D.all_text("a\rb") == D.all_text.spec("a\rb") : Bool} &
  {D.all_text("a\rb") == False{} : Bool} &
  {D.all_hex("09afAF") == True{} : Bool} &
  {D.all_hex("0x") == D.all_hex.spec("0x") : Bool} &
  {D.all_hex("") == D.all_hex.spec("") : Bool} &
  {D.line_text([67, 66, 65]) == "ABC" : String} &
  {D.line_text([233, 10]) == B.to_latin1([10, 233]) : String}:
  ({==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==})
