# Laws 13 (no_body), 15 (reject_cl_te) and 15b (reject_cl_te_fails): the
# response ends at its head, or fails there.
#
# Each is the head lemma (proofs/decode_lemmas.bend) and one framing step:
#   - feeding init(meth, len(head) + slack) with head ++ rest is feeding rest
#     to State{meth, slack, head_phase(meth, slack, r)} (head_at);
#   - for law 13 (HEAD, 204 or 304, status 200..999) that phase is Complete
#     with the bodiless response (head_phase_complete), so rest is leftover
#     (feed_complete) and finish gives it back (rev_rev);
#   - for law 15 (a final status with a body, Content-Length and
#     Transfer-Encoding both present) it is Failed{ConflictingFraming}
#     (head_phase_conflict), which no later byte changes (feed_failed);
#   - for law 15b, with any budget, the run of the head (head_charge) ends in
#     that failure or, when the budget is short, in TooLarge
#     (charge_fail_feed): a failure either way.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/decode.bend as D
import ../src/spec.bend as S
import ../proofs/decode_lemmas.bend as DL

# Law 13
# ------

def no_body_law(meth: M.Method, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +rest: List<&2, U32>, +slack: Nat,
  e0: {D.no_body(meth, st) == True{} : Bool}, +e1: {Nat.is_le(200n, st) == True{} : Bool},
  e2: {Nat.is_le(st, 999n) == True{} : Bool}, e3: {S.head_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool})
  -> {D.response(meth, Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), slack),
        Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), rest))
      == Done{M.Decoded{M.Response{v, st, rs, hs, Nil{}}, rest}} : Laws.Res()}:
  %Equal.sym(D.State,
    D.feed(D.init(meth, Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), slack)),
      Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), rest)),
    D.feed(D.State{meth, slack, DL.head_phase(meth, slack, M.Response{v, st, rs, hs, body})}, rest),
    DL.head_at(meth, M.Response{v, st, rs, hs, body}, slack, rest,
      DL.status_value_show(st, DL.le_trans(100n, 200n, st, {==}, e1), e2), e3)) :
    {D.finish(_) == Done{M.Decoded{M.Response{v, st, rs, hs, Nil{}}, rest}} : Laws.Res()}
  %Equal.sym(D.Phase, DL.head_phase(meth, slack, M.Response{v, st, rs, hs, body}), D.Complete{M.Response{v, st, rs, hs, Nil{}}, Nil{}},
    DL.head_phase_complete(meth, slack, v, st, rs, hs, body, DL.final_not_101(st, e1), DL.final_not_lt(st, e1), e0)) :
    {D.finish(D.feed(D.State{meth, slack, _}, rest)) == Done{M.Decoded{M.Response{v, st, rs, hs, Nil{}}, rest}} : Laws.Res()}
  %Equal.sym(D.State, D.feed(D.State{meth, slack, D.Complete{M.Response{v, st, rs, hs, Nil{}}, Nil{}}}, rest),
    D.State{meth, slack, D.Complete{M.Response{v, st, rs, hs, Nil{}}, D.rev(U32, rest, Nil{})}},
    DL.feed_complete(meth, slack, M.Response{v, st, rs, hs, Nil{}}, rest, Nil{})) :
    {D.finish(_) == Done{M.Decoded{M.Response{v, st, rs, hs, Nil{}}, rest}} : Laws.Res()}
  %Equal.sym(List<&2, U32>, D.rev(U32, D.rev(U32, rest, Nil{}), Nil{}), rest, DL.rev_rev(U32, rest)) :
    {Done{M.Decoded{M.Response{v, st, rs, hs, Nil{}}, _}} == Done{M.Decoded{M.Response{v, st, rs, hs, Nil{}}, rest}} : Laws.Res()}
  {==}

def Laws.no_body(meth, r, rest, slack, e0, e1, e2, e3):
  match r:
    case M.Response{v, st, rs, hs, body}:
      no_body_law(meth, v, st, rs, hs, body, rest, slack, e0, e1, e2, e3)

# Law 15
# ------

def reject_law(meth: M.Method, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, +e1: {S.response_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool},
  e2: {H.has("content-length", hs) == True{} : Bool}, e3: {H.has("transfer-encoding", hs) == True{} : Bool})
  -> {D.response(meth, Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), slack),
        Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), rest))
      == Fail{M.ConflictingFraming{}} : Laws.Res()}:
  %Equal.sym(D.State,
    D.feed(D.init(meth, Nat.add(Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), slack)),
      Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), rest)),
    D.feed(D.State{meth, slack, DL.head_phase(meth, slack, M.Response{v, st, rs, hs, body})}, rest),
    DL.head_at(meth, M.Response{v, st, rs, hs, body}, slack, rest,
      DL.status_value_show(st, DL.bs_100(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_999(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      DL.response_ok_head(M.Response{v, st, rs, hs, body}, e1))) :
    {D.finish(_) == Fail{M.ConflictingFraming{}} : Laws.Res()}
  %Equal.sym(D.Phase, DL.head_phase(meth, slack, M.Response{v, st, rs, hs, body}), D.Failed{M.ConflictingFraming{}},
    DL.head_phase_conflict(meth, slack, v, st, rs, hs, body,
      DL.bs_101(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
      DL.bs_200(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
      DL.no_body_false(meth, st, e0, DL.bs_204(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_304(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      e2, e3)) :
    {D.finish(D.feed(D.State{meth, slack, _}, rest)) == Fail{M.ConflictingFraming{}} : Laws.Res()}
  %Equal.sym(D.State, D.feed(D.State{meth, slack, D.Failed{M.ConflictingFraming{}}}, rest),
    D.State{meth, slack, D.Failed{M.ConflictingFraming{}}}, DL.feed_failed(meth, slack, M.ConflictingFraming{}, rest)) :
    {D.finish(_) == Fail{M.ConflictingFraming{}} : Laws.Res()}
  {==}

def Laws.reject_cl_te(meth, r, rest, slack, e0, e1, e2, e3):
  match r:
    case M.Response{v, st, rs, hs, body}:
      reject_law(meth, v, st, rs, hs, body, rest, slack, e0, e1, e2, e3)

# Law 15b
# -------

def reject_fails_law(+meth: M.Method, +v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +m: Nat, +rest: List<&2, U32>,
  +e0: {D.is_head(meth) == False{} : Bool}, +e1: {S.response_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool},
  +e2: {H.has("content-length", hs) == True{} : Bool}, +e3: {H.has("transfer-encoding", hs) == True{} : Bool})
  -> {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.response(meth, m, Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), rest)))
      == True{} : Bool}:
  %Equal.sym(D.State, D.feed(D.init(meth, m), Laws.cat(S.encode_head(M.Response{v, st, rs, hs, body}), rest)),
    D.feed(DL.charge(meth, Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), m,
      k => DL.head_phase(meth, k, M.Response{v, st, rs, hs, body})), rest),
    DL.head_charge(meth, M.Response{v, st, rs, hs, body}, m, rest,
      DL.status_value_show(st, DL.bs_100(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_999(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      DL.response_ok_head(M.Response{v, st, rs, hs, body}, e1))) :
    {Result.is_fail(&2, &2, M.ParseError, M.Decoded, D.finish(_)) == True{} : Bool}
  DL.charge_fail_feed(meth, Laws.len(S.encode_head(M.Response{v, st, rs, hs, body})), m,
    k => DL.head_phase(meth, k, M.Response{v, st, rs, hs, body}), M.ConflictingFraming{}, rest,
    k => DL.head_phase_conflict(meth, k, v, st, rs, hs, body,
      DL.bs_101(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
      DL.bs_200(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
      DL.no_body_false(meth, st, e0, DL.bs_204(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1)),
        DL.bs_304(st, DL.response_ok_status(M.Response{v, st, rs, hs, body}, e1))),
      e2, e3))

def Laws.reject_cl_te_fails(meth, r, m, rest, e0, e1, e2, e3):
  match r:
    case M.Response{v, st, rs, hs, body}:
      reject_fails_law(meth, v, st, rs, hs, body, m, rest, e0, e1, e2, e3)
