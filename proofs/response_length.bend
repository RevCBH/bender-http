# Laws 10 (response_length_roundtrip) and 14 (interim_skipped): a
# Content-Length response decodes to itself, after any number of skipped
# interim heads; the bytes after it are left over.
#
# Law 10, for r = Response{v, st, rs, hs, body}, H = encode_head(r),
# K = len(body) + slack:
#   - encode_response(r) ++ rest is H ++ (body ++ rest) (cat_assoc) and the
#     budget len(H ++ body) + slack is len(H) + K (budget_split);
#   - the head lemma (DL.head_at) leaves State{meth, K, head_phase(meth, K, r)}
#     before body ++ rest;
#   - with a final body status, no Transfer-Encoding (te_none) and the
#     Content-Length values agreeing on len(body) (cl_phase), that phase is
#     length_next(r0, [], len(body)) (length_phase; r0 is r with body []);
#   - the body bytes run the LengthBody phase down to Complete, one budget
#     unit each, and rest becomes the reversed leftover (body_feed);
#   - finish reverses the body and the leftover back (DL.rev_rev).
# Law 14: the head lemma for the interim head i lands in line(KStatus) with
# budget len(encode_response(r)) + slack (DL.head_phase_interim), which is
# init(meth, that budget): law 10 for r.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/decode.bend as D
import ../src/spec.bend as S
import ../proofs/decode_lemmas.bend as DL

# Nat and budget facts
# --------------------

# n <= n + s.
def le_add(n: Nat, s: Nat) -> {Nat.is_le(n, Nat.add(n, s)) == True{} : Bool}:
  match n:
    case 0n:
      DL.le_zero_l(s)
    case 1n+p:
      le_add(p, s)

# a < b: a <= b.
def lt_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      DL.le_zero_l(b)
    case 1n+ap 0n:
      DL.absurd_ft({Nat.is_le(1n+ap, 0n) == True{} : Bool}, e)
    case 1n+ap 1n+bp:
      lt_le(ap, bp, e)

# The budget for xs ++ ys plus s is len(xs) plus the budget for ys plus s.
def budget_split(xs: List<&2, U32>, -ys: List<&2, U32>, -s: Nat)
  -> {Nat.add(Laws.len(Laws.cat(xs, ys)), s) == Nat.add(Laws.len(xs), Nat.add(Laws.len(ys), s)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      %budget_split(t, ys, s) : {1n+Nat.add(Laws.len(Laws.cat(t, ys)), s) == 1n+_ : Nat}
      {==}

# Header lookup
# -------------

# has.go with found = True is True, whatever the headers.
def has_go_true(-l: String, hs: List<&2, M.Header>) -> {H.has.go(l, hs, True{}) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def hn_pick(-l: String, t: List<&2, M.Header>, hit: Bool, -v: String, e: {H.has.go(l, t, hit) == False{} : Bool},
  ih: {H.has.go(l, t, False{}) == False{} : Bool} -> {H.get_all.go(l, t, Nil{}) == Nil{} : List<&2, String>})
  -> {H.get_all.go(l, t, H.get_all.pick(hit, v, Nil{})) == Nil{} : List<&2, String>}:
  match hit:
    case True{}:
      DL.absurd_tf({H.get_all.go(l, t, H.get_all.pick(True{}, v, Nil{})) == Nil{} : List<&2, String>},
        Equal.trans(Bool, True{}, H.has.go(l, t, True{}), False{},
          Equal.sym(Bool, H.has.go(l, t, True{}), True{}, has_go_true(l, t)), e))
    case False{}:
      ih(e)

# No header found: get_all finds nothing.
def has_none(+l: String, hs: List<&2, M.Header>, e: {H.has.go(l, hs, False{}) == False{} : Bool})
  -> {H.get_all.go(l, hs, Nil{}) == Nil{} : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Con{M.Header{+n, +v}, +t}:
      hn_pick(l, t, String.eq(l, H.lower(n)), v, e, x => has_none(l, t, x))

# not H.has(name, hs): get_all(name, hs) is [].
def has_get_all_nil(+name: String, hs: List<&2, M.Header>, e: {H.has(name, hs) == False{} : Bool})
  -> {H.get_all(name, hs) == Nil{} : List<&2, String>}:
  has_none(H.lower(name), hs, e)

# Framing
# -------

# The Content-Length values agree on n and the budget left is n + s: the
# body phase with n bytes to go.
def cl_phase(cl: List<&2, String>, n: Nat, s: Nat, -r0: M.Response, e: {D.cl_of(cl) == Some{n} : Maybe<&2, Nat>})
  -> {D.framing.cl(cl, Nat.add(n, s), r0) == D.length_next(r0, Nil{}, n) : D.Phase}:
  match cl:
    case Nil{}:
      Empty.absurd({D.framing.cl(Nil{}, Nat.add(n, s), r0) == D.length_next(r0, Nil{}, n) : D.Phase}, DL.none_ne_some(n, e))
    case Con{x, t}:
      %Equal.sym(Maybe<&2, Nat>, D.cl_of(Con{x, t}), Some{n}, e) :
        {D.cl_framing(Nat.add(n, s), _, r0) == D.length_next(r0, Nil{}, n) : D.Phase}
      %Equal.sym(Bool, Nat.is_le(n, Nat.add(n, s)), True{}, le_add(n, s)) :
        {D.cl.fits(_, n, r0) == D.length_next(r0, Nil{}, n) : D.Phase}
      {==}

# After the head of a final response with a body, no Transfer-Encoding and a
# Content-Length of len(body), with budget len(body) + s left: the body phase.
def length_phase(m: M.Method, s: Nat, -v: M.Version, +st: Nat, -rs: String, +hs: List<&2, M.Header>, body: List<&2, U32>,
  +ok: {S.body_status_ok(st) == True{} : Bool}, e0: {D.is_head(m) == False{} : Bool},
  e2: {D.content_length(hs) == Some{Laws.len(body)} : Maybe<&2, Nat>}, e3: {H.has("transfer-encoding", hs) == False{} : Bool})
  -> {DL.head_phase(m, Nat.add(Laws.len(body), s), M.Response{v, st, rs, hs, body})
      == D.length_next(M.Response{v, st, rs, hs, Nil{}}, Nil{}, Laws.len(body)) : D.Phase}:
  Equal.trans(D.Phase, DL.head_phase(m, Nat.add(Laws.len(body), s), M.Response{v, st, rs, hs, body}),
    D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), Nat.add(Laws.len(body), s),
      M.Response{v, st, rs, hs, Nil{}}),
    D.length_next(M.Response{v, st, rs, hs, Nil{}}, Nil{}, Laws.len(body)),
    DL.head_phase_body(m, Nat.add(Laws.len(body), s), v, st, rs, hs, body, DL.bs_101(st, ok), DL.bs_200(st, ok),
      DL.no_body_false(m, st, e0, DL.bs_204(st, ok), DL.bs_304(st, ok))),
    Equal.trans(D.Phase,
      D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), Nat.add(Laws.len(body), s),
        M.Response{v, st, rs, hs, Nil{}}),
      D.framing.te(v, Nil{}, H.get_all("content-length", hs), Nat.add(Laws.len(body), s), M.Response{v, st, rs, hs, Nil{}}),
      D.length_next(M.Response{v, st, rs, hs, Nil{}}, Nil{}, Laws.len(body)),
      Equal.cong(List<&2, String>, D.Phase,
        x => D.framing.te(v, x, H.get_all("content-length", hs), Nat.add(Laws.len(body), s), M.Response{v, st, rs, hs, Nil{}}),
        H.get_all("transfer-encoding", hs), Nil{}, has_get_all_nil("transfer-encoding", hs, e3)),
      cl_phase(H.get_all("content-length", hs), Laws.len(body), s, M.Response{v, st, rs, hs, Nil{}}, e2)))

# The body
# --------

# The body bytes xs (then rest) in the LengthBody phase with acc read so far
# and budget len(xs) + s: each byte costs one unit, the message completes
# with the body acc then xs, and rest is kept as the (reversed) leftover.
def body_feed(-m: M.Method, -r0: M.Response, xs: List<&2, U32>, acc: List<&2, U32>, -s: Nat, rest: List<&2, U32>)
  -> {D.feed(D.State{m, Nat.add(Laws.len(xs), s), D.length_next(r0, acc, Laws.len(xs))}, Laws.cat(xs, rest))
      == D.State{m, s, D.Complete{D.with_body(r0, D.rev(U32, xs, acc)), D.rev(U32, rest, Nil{})}} : D.State}:
  match xs:
    case Nil{}:
      DL.feed_complete(m, s, D.with_body(r0, acc), rest, Nil{})
    case Con{h, t}:
      body_feed(m, r0, t, h <> acc, s, rest)

# Law 10
# ------

def length_law(meth: M.Method, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, +e1: {S.response_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool},
  e2: {D.content_length(hs) == Some{Laws.len(body)} : Maybe<&2, Nat>}, e3: {H.has("transfer-encoding", hs) == False{} : Bool})
  -> {D.response(meth, Nat.add(Laws.len(S.encode_response(M.Response{v, st, rs, hs, body})), slack),
        Laws.cat(S.encode_response(M.Response{v, st, rs, hs, body}), rest))
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}:
  %Equal.sym(List<&2, U32>,
    Laws.cat(Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), body), rest),
    Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), Laws.cat(body, rest)),
    DL.cat_assoc(S.encode_head(M.Response{v, st, rs, hs, body}), body, rest)) :
    {D.response(meth, Nat.add(Laws.len(S.encode_response(M.Response{v, st, rs, hs, body})), slack), _)
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(Nat,
    Nat.add(Laws.len(Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), body)), slack),
    Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), Nat.add(Laws.len(body), slack)),
    budget_split(S.encode_head(M.Response{v, st, rs, hs, body}), body, slack)) :
    {D.response(meth, _, Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), Laws.cat(body, rest)))
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.init(meth, Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), Nat.add(Laws.len(body), slack))),
      Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), Laws.cat(body, rest))),
    D.feed(D.State{meth, Nat.add(Laws.len(body), slack), DL.head_phase(meth, Nat.add(Laws.len(body), slack), M.Response{v, st, rs, hs, body})},
      Laws.cat(body, rest)),
    DL.head_at(meth, M.Response{v, st, rs, hs, body}, Nat.add(Laws.len(body), slack), Laws.cat(body, rest),
      DL.status_value_show(st, DL.bs_100(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_999(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      DL.response_ok_head(M.Response{v, st, rs, hs, body}, e1))) :
    {D.finish(_) == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.Phase, DL.head_phase(meth, Nat.add(Laws.len(body), slack), M.Response{v, st, rs, hs, body}),
    D.length_next(M.Response{v, st, rs, hs, Nil{}}, Nil{}, Laws.len(body)),
    length_phase(meth, slack, v, st, rs, hs, body, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1), e0, e2, e3)) :
    {D.finish(D.feed(D.State{meth, Nat.add(Laws.len(body), slack), _}, Laws.cat(body, rest)))
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.State{meth, Nat.add(Laws.len(body), slack), D.length_next(M.Response{v, st, rs, hs, Nil{}}, Nil{}, Laws.len(body))},
      Laws.cat(body, rest)),
    D.State{meth, slack, D.Complete{D.with_body(M.Response{v, st, rs, hs, Nil{}}, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}},
    body_feed(meth, M.Response{v, st, rs, hs, Nil{}}, body, Nil{}, slack, rest)) :
    {D.finish(_) == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(List<&2, U32>, D.rev(U32, D.rev(U32, body, Nil{}), Nil{}), body, DL.rev_rev(U32, body)) :
    {Done{M.Decoded{M.Response{v, st, rs, hs, _}, D.rev(U32, D.rev(U32, rest, Nil{}), Nil{})}}
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(List<&2, U32>, D.rev(U32, D.rev(U32, rest, Nil{}), Nil{}), rest, DL.rev_rev(U32, rest)) :
    {Done{M.Decoded{M.Response{v, st, rs, hs, body}, _}} == Done{M.Decoded{M.Response{v, st, rs, hs, body}, rest}} : Laws.Res()}
  {==}

def Laws.response_length_roundtrip(meth, r, rest, slack, e0, e1, e2, e3):
  match r:
    case M.Response{v, st, rs, hs, body}:
      length_law(meth, v, st, rs, hs, body, rest, slack, e0, e1, e2, e3)

# Law 14
# ------

def interim_law(meth: M.Method, +vi: M.Version, +sti: Nat, +rsi: String, +hsi: List<&2, M.Header>, +bi: List<&2, U32>,
  +r: M.Response, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, e1: {Nat.is_le(100n, sti) == True{} : Bool},
  +e2: {Nat.is_lt(sti, 200n) == True{} : Bool}, e3: {Nat.is_eq(sti, 101n) == False{} : Bool},
  e4: {S.head_ok(M.Response{vi, sti, rsi, hsi, bi}) == True{} : Bool}, e5: {S.response_ok(r) == True{} : Bool},
  e6: {D.content_length(S.response_headers(r)) == Some{Laws.len(S.response_body(r))} : Maybe<&2, Nat>},
  e7: {H.has("transfer-encoding", S.response_headers(r)) == False{} : Bool})
  -> {D.response(meth, Nat.add(Laws.len(Laws.cat(S.encode_head(M.Response{vi, sti, rsi, hsi, bi}), S.encode_response(r))), slack),
        Laws.cat(S.encode_head(M.Response{vi, sti, rsi, hsi, bi}), Laws.cat(S.encode_response(r), rest)))
      == Done{M.Decoded{r, rest}} : Laws.Res()}:
  %Equal.sym(Nat,
    Nat.add(Laws.len(Laws.cat(S.encode_head(M.Response{vi, sti, rsi, hsi, bi}), S.encode_response(r))), slack),
    Nat.add(Laws.len(S.encode_head(M.Response{vi, sti, rsi, hsi, bi})), Nat.add(Laws.len(S.encode_response(r)), slack)),
    budget_split(S.encode_head(M.Response{vi, sti, rsi, hsi, bi}), S.encode_response(r), slack)) :
    {D.response(meth, _, Laws.cat(S.encode_head(M.Response{vi, sti, rsi, hsi, bi}), Laws.cat(S.encode_response(r), rest)))
      == Done{M.Decoded{r, rest}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.init(meth, Nat.add(Laws.len(S.encode_head(M.Response{vi, sti, rsi, hsi, bi})), Nat.add(Laws.len(S.encode_response(r)), slack))),
      Laws.cat(S.encode_head(M.Response{vi, sti, rsi, hsi, bi}), Laws.cat(S.encode_response(r), rest))),
    D.feed(D.State{meth, Nat.add(Laws.len(S.encode_response(r)), slack),
        DL.head_phase(meth, Nat.add(Laws.len(S.encode_response(r)), slack), M.Response{vi, sti, rsi, hsi, bi})},
      Laws.cat(S.encode_response(r), rest)),
    DL.head_at(meth, M.Response{vi, sti, rsi, hsi, bi}, Nat.add(Laws.len(S.encode_response(r)), slack),
      Laws.cat(S.encode_response(r), rest),
      DL.status_value_show(sti, e1, DL.le_trans(sti, 200n, 999n, lt_le(sti, 200n, e2), {==})), e4)) :
    {D.finish(_) == Done{M.Decoded{r, rest}} : Laws.Res()}
  %Equal.sym(D.Phase, DL.head_phase(meth, Nat.add(Laws.len(S.encode_response(r)), slack), M.Response{vi, sti, rsi, hsi, bi}),
    D.line(D.KStatus{}),
    DL.head_phase_interim(meth, Nat.add(Laws.len(S.encode_response(r)), slack), vi, sti, rsi, hsi, bi, e3, e2)) :
    {D.finish(D.feed(D.State{meth, Nat.add(Laws.len(S.encode_response(r)), slack), _}, Laws.cat(S.encode_response(r), rest)))
      == Done{M.Decoded{r, rest}} : Laws.Res()}
  Laws.response_length_roundtrip(meth, r, rest, slack, e0, e5, e6, e7)

def Laws.interim_skipped(meth, i, r, rest, slack, e0, e1, e2, e3, e4, e5, e6, e7):
  match i:
    case M.Response{vi, sti, rsi, hsi, bi}:
      interim_law(meth, vi, sti, rsi, hsi, bi, r, rest, slack, e0, e1, e2, e3, e4, e5, e6, e7)
