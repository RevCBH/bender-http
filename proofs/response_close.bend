# Law 12 (response_close_roundtrip): a response with no Content-Length and no
# Transfer-Encoding reads back whole when its body runs to the close.
#
# The proof is the head lemma (proofs/decode_lemmas.bend) and the close body:
#   - the budget len(head ++ body) + slack is len(head) + (len(body) + slack)
#     (len_cat, close_add_assoc);
#   - feeding init(meth, len(head) + K) with head ++ body is feeding body to
#     State{meth, K, head_phase(meth, K, r)} (head_at);
#   - with a final body-carrying status (response_ok, not HEAD) and neither
#     framing header (has == False, so get_all == []: has_false_get_all),
#     that phase is CloseBody{r without its body, []} (head_phase_close);
#   - each body byte spends one unit and is consed onto the reversed body
#     (close_feed), leaving State{meth, slack, CloseBody{.., rev(body)}};
#   - finish reverses it back (with_body, rev_rev): Done{Decoded{r, []}}.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/decode.bend as D
import ../src/spec.bend as S
import ../proofs/decode_lemmas.bend as DL

# Nat
# ---

def close_add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %close_add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# The budget of law 12, regrouped: len(head ++ body) + slack is
# len(head) + (len(body) + slack).
def close_budget(+hd: List<&2, U32>, +body: List<&2, U32>, +slack: Nat)
  -> {Nat.add(Laws.len(Laws.cat(hd, body)), slack) == Nat.add(Laws.len(hd), Nat.add(Laws.len(body), slack)) : Nat}:
  Equal.trans(Nat, Nat.add(Laws.len(Laws.cat(hd, body)), slack), Nat.add(Nat.add(Laws.len(hd), Laws.len(body)), slack),
    Nat.add(Laws.len(hd), Nat.add(Laws.len(body), slack)),
    Equal.cong(Nat, Nat, x => Nat.add(x, slack), Laws.len(Laws.cat(hd, body)), Nat.add(Laws.len(hd), Laws.len(body)),
      DL.len_cat(hd, body)),
    close_add_assoc(Laws.len(hd), Laws.len(body), slack))

# Header lookup
# -------------

# has.go with found = True is True, whatever is left.
def has_go_true(-l: String, t: List<&2, M.Header>) -> {H.has.go(l, t, True{}) == True{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{h, tt}:
      {==}

def has_false_pick(-l: String, +t: List<&2, M.Header>, hit: Bool, -v: String,
  e: {H.has.go(l, t, hit) == False{} : Bool},
  ih: {H.has.go(l, t, False{}) == False{} : Bool} -> {H.get_all.go(l, t, Nil{}) == Nil{} : List<&2, String>})
  -> {H.get_all.go(l, t, H.get_all.pick(hit, v, Nil{})) == Nil{} : List<&2, String>}:
  match hit:
    case True{}:
      DL.absurd_tf({H.get_all.go(l, t, Con{v, Nil{}}) == Nil{} : List<&2, String>},
        Equal.trans(Bool, True{}, H.has.go(l, t, True{}), False{}, Equal.sym(Bool, H.has.go(l, t, True{}), True{}, has_go_true(l, t)), e))
    case False{}:
      ih(e)

def has_false_go(+l: String, hs: List<&2, M.Header>, e: {H.has.go(l, hs, False{}) == False{} : Bool})
  -> {H.get_all.go(l, hs, Nil{}) == Nil{} : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Con{M.Header{+n, +v}, +t}:
      has_false_pick(l, t, String.eq(l, H.lower(n)), v, e, x => has_false_go(l, t, x))

# H.has(name, hs) == False: get_all(name, hs) is empty.
def has_false_get_all(+name: String, hs: List<&2, M.Header>, e: {H.has(name, hs) == False{} : Bool})
  -> {H.get_all(name, hs) == Nil{} : List<&2, String>}:
  has_false_go(H.lower(name), hs, e)

# The phase after the head
# ------------------------

# A final status with a body and neither framing header: the body runs to the close.
def head_phase_close(-m: M.Method, -k: Nat, +v: M.Version, +st: Nat, -rs: String, +hs: List<&2, M.Header>, -body: List<&2, U32>,
  e101: {Nat.is_eq(st, 101n) == False{} : Bool}, elt: {Nat.is_lt(st, 200n) == False{} : Bool},
  e_nb: {D.no_body(m, st) == False{} : Bool},
  e_te: {H.has("transfer-encoding", hs) == False{} : Bool}, e_cl: {H.has("content-length", hs) == False{} : Bool})
  -> {DL.head_phase(m, k, M.Response{v, st, rs, hs, body}) == D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}:
  %Equal.sym(D.Phase, DL.head_phase(m, k, M.Response{v, st, rs, hs, body}),
    D.framing.te(v, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}}),
    DL.head_phase_body(m, k, v, st, rs, hs, body, e101, elt, e_nb)) :
    {_ == D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}
  %Equal.sym(List<&2, String>, H.get_all("transfer-encoding", hs), Nil{}, has_false_get_all("transfer-encoding", hs, e_te)) :
    {D.framing.te(v, _, H.get_all("content-length", hs), k, M.Response{v, st, rs, hs, Nil{}})
      == D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}
  %Equal.sym(List<&2, String>, H.get_all("content-length", hs), Nil{}, has_false_get_all("content-length", hs, e_cl)) :
    {D.framing.te(v, Nil{}, _, k, M.Response{v, st, rs, hs, Nil{}})
      == D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, Nil{}} : D.Phase}
  {==}

# The close-delimited body
# ------------------------

# Each byte of a close-delimited body spends one unit and joins the reversed body.
def close_feed(-m: M.Method, xs: List<&2, U32>, -s: Nat, -r: M.Response, acc: List<&2, U32>)
  -> {D.feed(D.State{m, Nat.add(Laws.len(xs), s), D.CloseBody{r, acc}}, xs)
      == D.State{m, s, D.CloseBody{r, D.rev(U32, xs, acc)}} : D.State}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      close_feed(m, t, s, r, h <> acc)

# Law 12
# ------

def close_law(meth: M.Method, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, +e1: {S.response_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool},
  e2: {H.has("transfer-encoding", hs) == False{} : Bool}, e3: {H.has("content-length", hs) == False{} : Bool})
  -> {D.response(meth, Nat.add(Laws.len(S.encode_response(M.Response{v, st, rs, hs, body})), slack),
        S.encode_response(M.Response{v, st, rs, hs, body}))
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, Nil{}}} : Laws.Res()}:
  %Equal.sym(Nat, Nat.add(Laws.len(Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), body)), slack),
    Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), Nat.add(Laws.len(body), slack)),
    close_budget(S.encode_head(M.Response{v, st, rs, hs, body}), body, slack)) :
    {D.finish(D.feed(D.init(meth, _), Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), body)))
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, Nil{}}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.init(meth, Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), Nat.add(Laws.len(body), slack))),
      Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), body)),
    D.feed(D.State{meth, Nat.add(Laws.len(body), slack), DL.head_phase(meth, Nat.add(Laws.len(body), slack), M.Response{v, st, rs, hs, body})}, body),
    DL.head_at(meth, M.Response{v, st, rs, hs, body}, Nat.add(Laws.len(body), slack), body,
      DL.status_value_show(st, DL.bs_100(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_999(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      DL.response_ok_head(M.Response{v, st, rs, hs, body}, e1))) :
    {D.finish(_) == Done{M.Decoded{M.Response{v, st, rs, hs, body}, Nil{}}} : Laws.Res()}
  %Equal.sym(D.Phase, DL.head_phase(meth, Nat.add(Laws.len(body), slack), M.Response{v, st, rs, hs, body}),
    D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, Nil{}},
    head_phase_close(meth, Nat.add(Laws.len(body), slack), v, st, rs, hs, body,
      DL.bs_101(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
      DL.bs_200(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
      DL.no_body_false(meth, st, e0, DL.bs_204(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_304(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      e2, e3)) :
    {D.finish(D.feed(D.State{meth, Nat.add(Laws.len(body), slack), _}, body))
      == Done{M.Decoded{M.Response{v, st, rs, hs, body}, Nil{}}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.State{meth, Nat.add(Laws.len(body), slack), D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, Nil{}}}, body),
    D.State{meth, slack, D.CloseBody{M.Response{v, st, rs, hs, Nil{}}, D.rev(U32, body, Nil{})}},
    close_feed(meth, body, slack, M.Response{v, st, rs, hs, Nil{}}, Nil{})) :
    {D.finish(_) == Done{M.Decoded{M.Response{v, st, rs, hs, body}, Nil{}}} : Laws.Res()}
  %Equal.sym(List<&2, U32>, D.rev(U32, D.rev(U32, body, Nil{}), Nil{}), body, DL.rev_rev(U32, body)) :
    {Done{M.Decoded{M.Response{v, st, rs, hs, _}, Nil{}}} == Done{M.Decoded{M.Response{v, st, rs, hs, body}, Nil{}}} : Laws.Res()}
  {==}

def Laws.response_close_roundtrip(meth, r, slack, e0, e1, e2, e3):
  match r:
    case M.Response{v, st, rs, hs, body}:
      close_law(meth, v, st, rs, hs, body, slack, e0, e1, e2, e3)
