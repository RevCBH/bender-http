# Law 11: a chunked response decodes to itself, whatever the chunk size.
#
# The decoder reads the head (DL.head_at: the head lemma of
# proofs/decode_lemmas.bend) and, the status being final with a body and
# Transfer-Encoding "chunked" alone (no Content-Length, HTTP/1.1), starts a
# chunk-size line. Then, with exact budgets (a run of `len(seg)` bytes from
# budget len(seg) + k leaves k):
#   size_line    hex_show(c) CRLF in a chunk-size line: ChunkData{.., c}
#                (needs c <= the budget left, and hex_read(hex_show(c)) == c:
#                law 3, proofs/num.bend)
#   data_crlf    the c data bytes, then CR LF: the next chunk-size line, the
#                data pushed (reversed) onto the body so far
#   chunk_feed   one chunk: S.chunk(d)
#   chunks_feed  every chunk of S.chunks(fuel, n, xs), by induction on fuel
#                (take ++ drop == xs, so the chunks' data are xs)
#   last_chunk   "0" CRLF CRLF: the trailers end at once; complete
# and the leftover bytes are kept reversed and reversed back by finish.
#
# LAWS.bend states law 11 for chunk sizes n <= 65535 (hypothesis es), which
# chunked_small proves; Laws.response_chunked_roundtrip is defined at the end.
# chunked_given_room proves the unbounded form from one more hypothesis, RoomFor(n): the
# chunk-size line of n fits the line limit, String.length(N.hex_show(n)) <=
# D.LINE_MAX() (65536). Every chunk has at most n bytes, and room_mono passes
# the room down to it. The decoder fails with TooLarge on a longer line, so the
# law needs this fact. Proven corollaries:
#   chunked_small     law 11 for every n <= 0xFFFF (hex_room_small gives the room)
#   chunked_room_all  law 11 given RoomAll (room for every c <= N.LIMIT())
# RoomFor(n) for every n <= N.LIMIT() is true (hex_show(4294967295) is
# "ffffffff"), but no proof of it can be checked in practice. The hypothesis
# {Nat.is_le(n, 4294967295n) == True} says something about n only through
# computing with the literal. Both checkers handle a Nat literal one Succ at
# a time: lit_step, and literal-vs-literal conversion is value equality only
# (bend.ts term_compare, case Lit). So any upper bound on the literal costs
# all ~4.3e9 peels: about 1.9 h on the box at 1.55 us a peel (.scratch/rc2/t),
# and the BendTT kernel caps each wnf/conv at FUEL = 4e8 steps.
# Making N.LIMIT() structural (U32.to_nat(4294967295), or 15 + 16 * ...) does
# not help either. wnf re-wraps every unfolded field in a fresh share cell, so
# two occurrences of N.LIMIT() unfold separately, never meet a shared node, and
# compare to depth ~4e9. Only a literal body, returned as the same object,
# compares at once. Even `def lem(c, e: {Nat.is_le(c, N.LIMIT()) == True}) ->
# {Nat.is_le(c, N.LIMIT()) == True}: e` overflows the stack
# (.scratch/rc2/p1/a.bend), which would break num.bend, url.bend and
# decode_lemmas.bend.
# Closing the law therefore needs a decision outside this file:
#   (a) LAWS.bend: bound n by 65535; then the law is chunked_small; or
#   (b) spec: chunks(.., Nat.min(n, 65535n), ..) in S.encode_chunked. This is
#       not behavior-preserving, and .scratch/rc/cap holds the checked variant:
#       `bend` and `--verdict` both print ALL PROOFS CHECK.
import Base
import ../LAWS.bend as Laws
import ../src/bytes.bend as B
import ../src/message.bend as M
import ../src/num.bend as N
import ../src/headers.bend as H
import ../src/decode.bend as D
import ../src/spec.bend as S
import ../proofs/num.bend as NP
import ../proofs/decode_lemmas.bend as DL

# Nat facts
# ---------

def le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      le_refl(p)

# The bytes of d, then anything: at least len(d), with any budget on top.
def le_len_cat(d: List<&2, U32>, zs: List<&2, U32>, k: Nat)
  -> {Nat.is_le(Laws.len(d), Nat.add(Laws.len(Laws.cat(d, zs)), k)) == True{} : Bool}:
  match d:
    case Nil{}:
      DL.le_zero_l(Nat.add(Laws.len(zs), k))
    case Con{h, t}:
      le_len_cat(t, zs, k)

# Lists
# -----

def rev_cat(xs: List<&2, U32>, -ys: List<&2, U32>, acc: List<&2, U32>)
  -> {D.rev(U32, Laws.cat(xs, ys), acc) == D.rev(U32, ys, D.rev(U32, xs, acc)) : List<&2, U32>}:
  match xs:
    case Nil{}:
      {==}
    case Con{h, t}:
      rev_cat(t, ys, h <> acc)

def take_drop(xs: List<&2, U32>, n: Nat)
  -> {Laws.cat(List.take(&2, U32, xs, n), List.drop(&2, U32, xs, n)) == xs : List<&2, U32>}:
  match xs n:
    case Nil{} m0:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %take_drop(t, p) : {Con{h, Laws.cat(List.take(&2, U32, t, p), List.drop(&2, U32, t, p))} == Con{h, _} : List<&2, U32>}
      {==}

def len_take(xs: List<&2, U32>, n: Nat) -> {Nat.is_le(Laws.len(List.take(&2, U32, xs, n)), n) == True{} : Bool}:
  match xs n:
    case Nil{} m0:
      DL.le_zero_l(m0)
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      len_take(t, p)

def len_drop(xs: List<&2, U32>, n: Nat) -> {Nat.is_le(Laws.len(List.drop(&2, U32, xs, n)), Laws.len(xs)) == True{} : Bool}:
  match xs n:
    case Nil{} m0:
      {==}
    case Con{h, t} 0n:
      le_refl(Laws.len(t))
    case Con{h, +t} 1n+(+p):
      NP.le_succ(Laws.len(List.drop(&2, U32, t, p)), Laws.len(t), len_drop(t, p))

# Hex text
# --------

# A digit char's class does not stop a split at ';'.
def dclass_nosemi(k: B.Class, e: {DL.dclass(k) == True{} : Bool}) -> {Bool.not(D.stop_class(D.AtSemi{}, k)) == True{} : Bool}:
  match k:
    case B.Digit{d}:
      {==}
    case B.HexLetter{d}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      DL.absurd_ft({Bool.not(D.stop_class(D.AtSemi{}, B.Semi{})) == True{} : Bool}, e)
    case B.Slash{}:
      {==}
    case B.Sp{}:
      {==}
    case B.Htab{}:
      {==}
    case B.Cr{}:
      {==}
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

# A digit char's class is not SP/HTAB.
def dclass_nows(k: B.Class, e: {DL.dclass(k) == True{} : Bool}) -> {Bool.not(B.Class.is_ows(k)) == True{} : Bool}:
  match k:
    case B.Digit{d}:
      {==}
    case B.HexLetter{d}:
      {==}
    case B.Letter{}:
      {==}
    case B.Tchar{}:
      {==}
    case B.Colon{}:
      {==}
    case B.Semi{}:
      {==}
    case B.Slash{}:
      {==}
    case B.Sp{}:
      DL.absurd_ft({Bool.not(B.Class.is_ows(B.Sp{})) == True{} : Bool}, e)
    case B.Htab{}:
      DL.absurd_ft({Bool.not(B.Class.is_ows(B.Htab{})) == True{} : Bool}, e)
    case B.Cr{}:
      {==}
    case B.Lf{}:
      {==}
    case B.Delim{}:
      {==}
    case B.Ctl{}:
      {==}
    case B.High{}:
      {==}
    case B.Invalid{}:
      {==}

# The digit chars of ds prepended to acc have no ';', as acc has none.
def dt_nosemi(ds: List<&2, Nat>, -acc: String, e: {DL.nostop(D.AtSemi{}, acc) == True{} : Bool})
  -> {DL.nostop(D.AtSemi{}, N.digits_text(ds, acc)) == True{} : Bool}:
  match ds:
    case Nil{}:
      e
    case Con{+d, t}:
      dt_nosemi(t, SCon{N.digit_char(d), acc},
        DL.and_intro(Bool.not(D.stops(D.AtSemi{}, N.digit_char(d))), DL.nostop(D.AtSemi{}, acc),
          dclass_nosemi(B.char_class(N.digit_char(d)), DL.dc(d)), e))

# Prepending chars keeps the last char.
def dt_last(ds: List<&2, Nat>, -x: Char, -acc: String, e: {H.last_not_ows(SCon{x, acc}) == True{} : Bool})
  -> {H.last_not_ows(N.digits_text(ds, SCon{x, acc})) == True{} : Bool}:
  match ds:
    case Nil{}:
      e
    case Con{d, t}:
      dt_last(t, N.digit_char(d), SCon{x, acc}, e)

def dt_last_con(ds: List<&2, Nat>, e: {NP.is_con(ds) == True{} : Bool})
  -> {H.last_not_ows(N.digits_text(ds, SNil{})) == True{} : Bool}:
  match ds:
    case Nil{}:
      DL.absurd_ft({H.last_not_ows(N.digits_text(Nil{}, SNil{})) == True{} : Bool}, e)
    case Con{+d, t}:
      dt_last(t, N.digit_char(d), SNil{}, dclass_nows(B.char_class(N.digit_char(d)), DL.dc(d)))

# hex_show(c) is plain, has no ';' and does not end in OWS.
def hex_plain(+c: Nat) -> {DL.plain_str(N.hex_show(c)) == True{} : Bool}:
  DL.dt_plain(N.hex_digits(c), SNil{}, {==})

def hex_nosemi(+c: Nat) -> {DL.nostop(D.AtSemi{}, N.hex_show(c)) == True{} : Bool}:
  dt_nosemi(N.hex_digits(c), SNil{}, {==})

def hex_last(+c: Nat) -> {H.last_not_ows(N.hex_show(c)) == True{} : Bool}:
  dt_last_con(N.hex_digits(c), NP.hex_count_con(c, [0n], {==}))

# The room of a chunk-size line
# -----------------------------

# The chunk-size line of a chunk of c bytes fits the line limit.
def RoomFor(c: Nat) -> Data:
  {Nat.is_le(String.length(N.hex_show(c)), D.LINE_MAX()) == True{} : Bool}

def le_add_l(p: Nat, -a: Nat, -b: Nat, e: {Nat.is_le(a, b) == True{} : Bool})
  -> {Nat.is_le(Nat.add(p, a), Nat.add(p, b)) == True{} : Bool}:
  match p:
    case 0n:
      e
    case 1n+pp:
      le_add_l(pp, a, b, e)

def inc_len_d(d: Nat, +t: List<&2, Nat>,
  ih: {Nat.is_le(List.length(&2, Nat, N.hex_inc(t)), 1n+List.length(&2, Nat, t)) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, Nat, N.hex_inc(Con{d, t})), 2n+List.length(&2, Nat, t)) == True{} : Bool}:
  match d:
    case 0n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 1n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 2n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 3n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 4n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 5n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 6n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 7n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 8n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 9n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 10n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 11n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 12n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 13n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 14n:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))
    case 15n:
      ih
    case 16n+k:
      NP.le_succ(List.length(&2, Nat, t), List.length(&2, Nat, t), le_refl(List.length(&2, Nat, t)))

# One increment adds at most one digit.
def inc_len(ds: List<&2, Nat>) -> {Nat.is_le(List.length(&2, Nat, N.hex_inc(ds)), 1n+List.length(&2, Nat, ds)) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      inc_len_d(d, t, inc_len(t))

# n increments add at most n digits.
def count_len(n: Nat, +ds: List<&2, Nat>)
  -> {Nat.is_le(List.length(&2, Nat, N.hex_count(n, ds)), Nat.add(n, List.length(&2, Nat, ds))) == True{} : Bool}:
  match n:
    case 0n:
      le_refl(List.length(&2, Nat, ds))
    case 1n+(+p):
      %NP.add_succ(p, List.length(&2, Nat, ds)) :
        {Nat.is_le(List.length(&2, Nat, N.hex_count(p, N.hex_inc(ds))), _) == True{} : Bool}
      NP.le_trans(List.length(&2, Nat, N.hex_count(p, N.hex_inc(ds))), Nat.add(p, List.length(&2, Nat, N.hex_inc(ds))),
        Nat.add(p, 1n+List.length(&2, Nat, ds)),
        count_len(p, N.hex_inc(ds)),
        le_add_l(p, List.length(&2, Nat, N.hex_inc(ds)), 1n+List.length(&2, Nat, ds), inc_len(ds)))

# The text of a digit list has one char per digit.
def slen_dt(ds: List<&2, Nat>, +acc: String)
  -> {String.length(N.digits_text(ds, acc)) == Nat.add(List.length(&2, Nat, ds), String.length(acc)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +t}:
      Equal.trans(Nat, String.length(N.digits_text(t, SCon{N.digit_char(d), acc})),
        Nat.add(List.length(&2, Nat, t), 1n+String.length(acc)), 1n+Nat.add(List.length(&2, Nat, t), String.length(acc)),
        slen_dt(t, SCon{N.digit_char(d), acc}), NP.add_succ(List.length(&2, Nat, t), String.length(acc)))

# hex_show(c) has at most c + 1 chars.
def hex_len(+c: Nat) -> {Nat.is_le(String.length(N.hex_show(c)), 1n+c) == True{} : Bool}:
  %Equal.sym(Nat, String.length(N.hex_show(c)), Nat.add(List.length(&2, Nat, N.hex_digits(c)), 0n), slen_dt(N.hex_digits(c), SNil{})) :
    {Nat.is_le(_, 1n+c) == True{} : Bool}
  %Equal.sym(Nat, Nat.add(List.length(&2, Nat, N.hex_digits(c)), 0n), List.length(&2, Nat, N.hex_digits(c)),
    NP.add_zero(List.length(&2, Nat, N.hex_digits(c)))) :
    {Nat.is_le(_, 1n+c) == True{} : Bool}
  %NP.add_comm(c, 1n) : {Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), _) == True{} : Bool}
  count_len(c, [0n])

# Room is monotone: a smaller chunk size has no more hex digits.
def count_add(a: Nat, -b: Nat, +ds: List<&2, Nat>)
  -> {N.hex_count(Nat.add(a, b), ds) == N.hex_count(b, N.hex_count(a, ds)) : List<&2, Nat>}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      count_add(p, b, N.hex_inc(ds))

def inc_len_ge_d(d: Nat, +t: List<&2, Nat>,
  ih: {Nat.is_le(List.length(&2, Nat, t), List.length(&2, Nat, N.hex_inc(t))) == True{} : Bool})
  -> {Nat.is_le(1n+List.length(&2, Nat, t), List.length(&2, Nat, N.hex_inc(Con{d, t}))) == True{} : Bool}:
  match d:
    case 0n:
      le_refl(List.length(&2, Nat, t))
    case 1n:
      le_refl(List.length(&2, Nat, t))
    case 2n:
      le_refl(List.length(&2, Nat, t))
    case 3n:
      le_refl(List.length(&2, Nat, t))
    case 4n:
      le_refl(List.length(&2, Nat, t))
    case 5n:
      le_refl(List.length(&2, Nat, t))
    case 6n:
      le_refl(List.length(&2, Nat, t))
    case 7n:
      le_refl(List.length(&2, Nat, t))
    case 8n:
      le_refl(List.length(&2, Nat, t))
    case 9n:
      le_refl(List.length(&2, Nat, t))
    case 10n:
      le_refl(List.length(&2, Nat, t))
    case 11n:
      le_refl(List.length(&2, Nat, t))
    case 12n:
      le_refl(List.length(&2, Nat, t))
    case 13n:
      le_refl(List.length(&2, Nat, t))
    case 14n:
      le_refl(List.length(&2, Nat, t))
    case 15n:
      ih
    case 16n+k:
      le_refl(List.length(&2, Nat, t))

# An increment never drops a digit.
def inc_len_ge(ds: List<&2, Nat>) -> {Nat.is_le(List.length(&2, Nat, ds), List.length(&2, Nat, N.hex_inc(ds))) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, +t}:
      inc_len_ge_d(d, t, inc_len_ge(t))

def count_len_ge(n: Nat, +ds: List<&2, Nat>)
  -> {Nat.is_le(List.length(&2, Nat, ds), List.length(&2, Nat, N.hex_count(n, ds))) == True{} : Bool}:
  match n:
    case 0n:
      le_refl(List.length(&2, Nat, ds))
    case 1n+(+p):
      NP.le_trans(List.length(&2, Nat, ds), List.length(&2, Nat, N.hex_inc(ds)), List.length(&2, Nat, N.hex_count(p, N.hex_inc(ds))),
        inc_len_ge(ds), count_len_ge(p, N.hex_inc(ds)))

def sub_add(c: Nat, y: Nat, e: {Nat.is_le(c, y) == True{} : Bool}) -> {Nat.add(c, Nat.sub(y, c)) == y : Nat}:
  match c y:
    case 0n 0n:
      {==}
    case 0n 1n+yp:
      {==}
    case 1n+cp 0n:
      DL.absurd_ft({Nat.add(1n+cp, Nat.sub(0n, 1n+cp)) == 0n : Nat}, e)
    case 1n+cp 1n+yp:
      %sub_add(cp, yp, e) : {1n+Nat.add(cp, Nat.sub(yp, cp)) == 1n+_ : Nat}
      {==}

def digits_len_mono(+c: Nat, +y: Nat, e: {Nat.is_le(c, y) == True{} : Bool})
  -> {Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), List.length(&2, Nat, N.hex_digits(y))) == True{} : Bool}:
  %sub_add(c, y, e) :
    {Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), List.length(&2, Nat, N.hex_count(_, [0n]))) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, N.hex_count(Nat.add(c, Nat.sub(y, c)), [0n]), N.hex_count(Nat.sub(y, c), N.hex_count(c, [0n])),
    count_add(c, Nat.sub(y, c), [0n])) :
    {Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), List.length(&2, Nat, _)) == True{} : Bool}
  count_len_ge(Nat.sub(y, c), N.hex_count(c, [0n]))

# hex_show(c) has one char per hex digit.
def hex_slen(+c: Nat) -> {String.length(N.hex_show(c)) == List.length(&2, Nat, N.hex_digits(c)) : Nat}:
  Equal.trans(Nat, String.length(N.hex_show(c)), Nat.add(List.length(&2, Nat, N.hex_digits(c)), 0n), List.length(&2, Nat, N.hex_digits(c)),
    slen_dt(N.hex_digits(c), SNil{}), NP.add_zero(List.length(&2, Nat, N.hex_digits(c))))

def room_mono(+c: Nat, +y: Nat, e: {Nat.is_le(c, y) == True{} : Bool}, r: RoomFor(y)) -> RoomFor(c):
  %Equal.sym(Nat, String.length(N.hex_show(c)), List.length(&2, Nat, N.hex_digits(c)), hex_slen(c)) :
    {Nat.is_le(_, D.LINE_MAX()) == True{} : Bool}
  NP.le_trans(List.length(&2, Nat, N.hex_digits(c)), String.length(N.hex_show(y)), D.LINE_MAX(),
    Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), String.length(N.hex_show(y))),
      Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), List.length(&2, Nat, N.hex_digits(y))), True{},
      Equal.cong(Nat, Bool, x => Nat.is_le(List.length(&2, Nat, N.hex_digits(c)), x), String.length(N.hex_show(y)),
        List.length(&2, Nat, N.hex_digits(y)), hex_slen(y)),
      digits_len_mono(c, y, e)),
    r)

# Every chunk size N.hex_read accepts has a chunk-size line that fits. (True:
# hex_show(N.LIMIT()) is "ffffffff"; see the header for why it is a
# hypothesis.)
def RoomAll() -> Type:
  @c: Nat -> {Nat.is_le(c, N.LIMIT()) == True{} : Bool} -> RoomFor(c)

# A chunk of at most 0xFFFF bytes: its size line fits the line limit.
def hex_room_small(+c: Nat, e: {Nat.is_le(c, 65535n) == True{} : Bool}) -> RoomFor(c):
  NP.le_trans(String.length(N.hex_show(c)), 1n+c, D.LINE_MAX(), hex_len(c), e)

# Splits with no stop char
# ------------------------

def split_go_none(t: String, hit: Bool, x: Char, -acc: String, +stop: D.Stop,
  eh: {hit == False{} : Bool}, +e: {DL.nostop(stop, t) == True{} : Bool})
  -> {D.split.go(t, hit, x, acc, stop) == (String.reverse(String.reverse.go(t, SCon{x, acc})), None{}) : String & Maybe<&2, String>}:
  match t hit:
    case SNil{} True{}:
      DL.absurd_tf({D.split.go(SNil{}, True{}, x, acc, stop) == (String.reverse(SCon{x, acc}), None{}) : String & Maybe<&2, String>}, eh)
    case SCon{y, z} True{}:
      DL.absurd_tf({D.split.go(SCon{y, z}, True{}, x, acc, stop)
        == (String.reverse(String.reverse.go(SCon{y, z}, SCon{x, acc})), None{}) : String & Maybe<&2, String>}, eh)
    case SNil{} False{}:
      {==}
    case SCon{+y, z} False{}:
      split_go_none(z, D.stops(stop, y), y, SCon{x, acc}, stop,
        DL.not_true(D.stops(stop, y), DL.and_l(Bool.not(D.stops(stop, y)), DL.nostop(stop, z), e)),
        DL.and_r(Bool.not(D.stops(stop, y)), DL.nostop(stop, z), e))

# No char of s stops the split: all of s, and None.
def split_none(+stop: D.Stop, s: String, +e: {DL.nostop(stop, s) == True{} : Bool})
  -> {D.split(stop, s) == (s, None{}) : String & Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      Equal.trans(String & Maybe<&2, String>, D.split(stop, SCon{c, t}),
        (String.reverse(String.reverse.go(t, SCon{c, SNil{}})), None{}), (SCon{c, t}, None{}),
        split_go_none(t, D.stops(stop, c), c, SNil{}, stop,
          DL.not_true(D.stops(stop, c), DL.and_l(Bool.not(D.stops(stop, c)), DL.nostop(stop, t), e)),
          DL.and_r(Bool.not(D.stops(stop, c)), DL.nostop(stop, t), e)),
        Equal.cong(String, String & Maybe<&2, String>, y => (y, None{}),
          String.reverse(String.reverse.go(t, SCon{c, SNil{}})), SCon{c, t}, DL.rev_single(t, c)))

# A chunk
# -------

# The text of a chunk-size line hex_show(c) (c >= 1, c <= LIMIT, c at most
# the budget k left after the line): read the c data bytes.
def size_check_hex(-kk: Nat, -r0: M.Response, -acc: List<&2, U32>, +c: Nat,
  e_pos: {Nat.is_le(1n, c) == True{} : Bool}, e_lim: {Nat.is_le(c, N.LIMIT()) == True{} : Bool},
  e_fit: {Nat.is_le(c, kk) == True{} : Bool})
  -> {D.size.check(True{}, N.hex_show(c), N.hex_read(N.hex_show(c)), kk, r0, acc) == D.ChunkData{r0, acc, c} : D.Phase}:
  match c:
    case 0n:
      DL.absurd_ft({D.size.check(True{}, N.hex_show(0n), N.hex_read(N.hex_show(0n)), kk, r0, acc) == D.ChunkData{r0, acc, 0n} : D.Phase}, e_pos)
    case 1n+(+p):
      %Equal.sym(Maybe<&2, Nat>, N.hex_read(N.hex_show(1n+p)), Some{1n+p}, Laws.hex_roundtrip(1n+p, e_lim)) :
        {D.size.check(True{}, N.hex_show(1n+p), _, kk, r0, acc) == D.ChunkData{r0, acc, 1n+p} : D.Phase}
      %Equal.sym(Bool, Nat.is_le(1n+p, kk), True{}, e_fit) :
        {D.chunk.fits(_, 1n+p, r0, acc) == D.ChunkData{r0, acc, 1n+p} : D.Phase}
      {==}

def size_end_hex(-kk: Nat, -r0: M.Response, -acc: List<&2, U32>, +c: Nat,
  e_pos: {Nat.is_le(1n, c) == True{} : Bool}, e_lim: {Nat.is_le(c, N.LIMIT()) == True{} : Bool},
  e_fit: {Nat.is_le(c, kk) == True{} : Bool})
  -> {D.size_end(kk, r0, acc, N.hex_show(c)) == D.ChunkData{r0, acc, c} : D.Phase}:
  %Equal.sym(String & Maybe<&2, String>, D.split(D.AtSemi{}, N.hex_show(c)), (N.hex_show(c), None{}),
    split_none(D.AtSemi{}, N.hex_show(c), hex_nosemi(c))) :
    {D.size.parts(kk, r0, acc, _) == D.ChunkData{r0, acc, c} : D.Phase}
  %Equal.sym(String, D.trim_right(N.hex_show(c)), N.hex_show(c), DL.trim_right_id(N.hex_show(c), hex_last(c))) :
    {D.size.check(True{}, _, N.hex_read(_), kk, r0, acc) == D.ChunkData{r0, acc, c} : D.Phase}
  size_check_hex(kk, r0, acc, c, e_pos, e_lim, e_fit)

# The chunk-size line hex_show(c) CRLF, with kk budget left after it.
def size_line(-m: M.Method, -r0: M.Response, -acc: List<&2, U32>, +c: Nat, +kk: Nat, +ys: List<&2, U32>,
  e_pos: {Nat.is_le(1n, c) == True{} : Bool}, +e_lim: {Nat.is_le(c, N.LIMIT()) == True{} : Bool},
  e_fit: {Nat.is_le(c, kk) == True{} : Bool}, e_room: RoomFor(c))
  -> {D.feed(D.State{m, Nat.add(Laws.len(DL.line_bytes(N.hex_show(c))), kk), D.line(D.KSize{r0, acc})},
        Laws.cat(DL.line_bytes(N.hex_show(c)), ys))
      == D.feed(D.State{m, kk, D.ChunkData{r0, acc, c}}, ys) : D.State}:
  %DL.feed_cat(D.State{m, Nat.add(Laws.len(DL.line_bytes(N.hex_show(c))), kk), D.line(D.KSize{r0, acc})},
    DL.line_bytes(N.hex_show(c)), ys) :
    {_ == D.feed(D.State{m, kk, D.ChunkData{r0, acc, c}}, ys) : D.State}
  %Equal.sym(D.State,
    D.feed(D.State{m, Nat.add(Laws.len(DL.line_bytes(N.hex_show(c))), kk), D.ReadLine{D.KSize{r0, acc}, Nil{}, D.LINE_MAX()}},
      DL.line_bytes(N.hex_show(c))),
    DL.charge(m, Laws.len(DL.line_bytes(N.hex_show(c))), Nat.add(Laws.len(DL.line_bytes(N.hex_show(c))), kk),
      DL.end_k(m, D.KSize{r0, acc}, N.hex_show(c))),
    DL.line_feed_text(m, D.KSize{r0, acc}, N.hex_show(c), D.LINE_MAX(), Nat.add(Laws.len(DL.line_bytes(N.hex_show(c))), kk),
      hex_plain(c), e_room)) :
    {D.feed(_, ys) == D.feed(D.State{m, kk, D.ChunkData{r0, acc, c}}, ys) : D.State}
  %Equal.sym(D.State,
    DL.charge(m, Laws.len(DL.line_bytes(N.hex_show(c))), Nat.add(Laws.len(DL.line_bytes(N.hex_show(c))), kk),
      DL.end_k(m, D.KSize{r0, acc}, N.hex_show(c))),
    D.State{m, kk, DL.end_k(m, D.KSize{r0, acc}, N.hex_show(c))(kk)},
    DL.charge_exact(m, Laws.len(DL.line_bytes(N.hex_show(c))), kk, DL.end_k(m, D.KSize{r0, acc}, N.hex_show(c)))) :
    {D.feed(_, ys) == D.feed(D.State{m, kk, D.ChunkData{r0, acc, c}}, ys) : D.State}
  %Equal.sym(D.Phase, D.size_end(kk, r0, acc, N.hex_show(c)), D.ChunkData{r0, acc, c},
    size_end_hex(kk, r0, acc, c, e_pos, e_lim, e_fit)) :
    {D.feed(D.State{m, kk, _}, ys) == D.feed(D.State{m, kk, D.ChunkData{r0, acc, c}}, ys) : D.State}
  {==}

# The data bytes d of a chunk, then CR LF: the next chunk-size line, d pushed
# onto the body so far (reversed).
def data_crlf(-m: M.Method, -r0: M.Response, d: List<&2, U32>, acc: List<&2, U32>, -k: Nat, -ys: List<&2, U32>)
  -> {D.feed(D.State{m, Nat.add(Laws.len(Laws.cat(d, [13, 10])), k), D.ChunkData{r0, acc, Laws.len(d)}},
        Laws.cat(Laws.cat(d, [13, 10]), ys))
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys) : D.State}:
  match d:
    case Nil{}:
      {==}
    case Con{h, t}:
      data_crlf(m, r0, t, h <> acc, k, ys)

# The chunk's bytes: its size line, then its data and CR LF.
def chunk_bytes(+d: List<&2, U32>)
  -> {S.chunk(d) == Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10])) : List<&2, U32>}:
  Equal.cong(List<&2, U32>, List<&2, U32>, x => Laws.cat(x, Laws.cat(d, [13, 10])),
    B.from_ascii(String.append(N.hex_show(Laws.len(d)), "\r\n")), DL.line_bytes(N.hex_show(Laws.len(d))),
    DL.line_bytes_eq(N.hex_show(Laws.len(d))))

# One chunk S.chunk(d) (d not empty, at most LIMIT bytes) from a chunk-size
# line, k budget left after it: the next chunk-size line, d pushed onto the body.
def chunk_feed(-m: M.Method, -r0: M.Response, +d: List<&2, U32>, +acc: List<&2, U32>, +k: Nat, +ys: List<&2, U32>,
  e_pos: {Nat.is_le(1n, Laws.len(d)) == True{} : Bool}, e_lim: {Nat.is_le(Laws.len(d), N.LIMIT()) == True{} : Bool},
  e_room: RoomFor(Laws.len(d)))
  -> {D.feed(D.State{m, Nat.add(Laws.len(S.chunk(d)), k), D.line(D.KSize{r0, acc})}, Laws.cat(S.chunk(d), ys))
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys) : D.State}:
  %Equal.sym(List<&2, U32>, S.chunk(d), Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10])), chunk_bytes(d)) :
    {D.feed(D.State{m, Nat.add(Laws.len(_), k), D.line(D.KSize{r0, acc})}, Laws.cat(_, ys))
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys) : D.State}
  %Equal.sym(List<&2, U32>,
    Laws.cat(Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10])), ys),
    Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(Laws.cat(d, [13, 10]), ys)),
    DL.cat_assoc(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10]), ys)) :
    {D.feed(D.State{m, Nat.add(Laws.len(Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10]))), k), D.line(D.KSize{r0, acc})}, _)
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys) : D.State}
  %Equal.sym(Nat, Laws.len(Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10]))),
    Nat.add(Laws.len(DL.line_bytes(N.hex_show(Laws.len(d)))), Laws.len(Laws.cat(d, [13, 10]))),
    DL.len_cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(d, [13, 10]))) :
    {D.feed(D.State{m, Nat.add(_, k), D.line(D.KSize{r0, acc})},
        Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(Laws.cat(d, [13, 10]), ys)))
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys) : D.State}
  %NP.add_assoc(Laws.len(DL.line_bytes(N.hex_show(Laws.len(d)))), Laws.len(Laws.cat(d, [13, 10])), k) :
    {D.feed(D.State{m, _, D.line(D.KSize{r0, acc})},
        Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(Laws.cat(d, [13, 10]), ys)))
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys) : D.State}
  Equal.trans(D.State,
    D.feed(D.State{m, Nat.add(Laws.len(DL.line_bytes(N.hex_show(Laws.len(d)))), Nat.add(Laws.len(Laws.cat(d, [13, 10])), k)), D.line(D.KSize{r0, acc})},
      Laws.cat(DL.line_bytes(N.hex_show(Laws.len(d))), Laws.cat(Laws.cat(d, [13, 10]), ys))),
    D.feed(D.State{m, Nat.add(Laws.len(Laws.cat(d, [13, 10])), k), D.ChunkData{r0, acc, Laws.len(d)}}, Laws.cat(Laws.cat(d, [13, 10]), ys)),
    D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, d, acc)})}, ys),
    size_line(m, r0, acc, Laws.len(d), Nat.add(Laws.len(Laws.cat(d, [13, 10])), k), Laws.cat(Laws.cat(d, [13, 10]), ys),
      e_pos, e_lim, le_len_cat(d, [13, 10], k), e_room),
    data_crlf(m, r0, d, acc, k, ys))

# The chunks
# ----------

# The chunk after this one starts from the body so far with the chunk's data
# pushed; take ++ drop is the rest of the input.
def rev_take_drop(+t: List<&2, U32>, +q: Nat, +acc: List<&2, U32>)
  -> {D.rev(U32, List.drop(&2, U32, t, q), D.rev(U32, List.take(&2, U32, t, q), acc)) == D.rev(U32, t, acc) : List<&2, U32>}:
  Equal.trans(List<&2, U32>, D.rev(U32, List.drop(&2, U32, t, q), D.rev(U32, List.take(&2, U32, t, q), acc)),
    D.rev(U32, Laws.cat(List.take(&2, U32, t, q), List.drop(&2, U32, t, q)), acc), D.rev(U32, t, acc),
    Equal.sym(List<&2, U32>, D.rev(U32, Laws.cat(List.take(&2, U32, t, q), List.drop(&2, U32, t, q)), acc),
      D.rev(U32, List.drop(&2, U32, t, q), D.rev(U32, List.take(&2, U32, t, q), acc)),
      rev_cat(List.take(&2, U32, t, q), List.drop(&2, U32, t, q), acc)),
    Equal.cong(List<&2, U32>, List<&2, U32>, x => D.rev(U32, x, acc),
      Laws.cat(List.take(&2, U32, t, q), List.drop(&2, U32, t, q)), t, take_drop(t, q)))

# Every chunk of S.chunks(fuel, 1 + q, xs) (fuel >= len(xs), 1 + q <= LIMIT)
# from a chunk-size line, k budget left after them: the next chunk-size line,
# xs pushed onto the body.
def chunks_feed(-m: M.Method, -r0: M.Response, +q: Nat, fuel: Nat, xs: List<&2, U32>, +acc: List<&2, U32>, +k: Nat, +ys: List<&2, U32>,
  e_fuel: {Nat.is_le(Laws.len(xs), fuel) == True{} : Bool},
  +e_q: {Nat.is_le(1n+q, N.LIMIT()) == True{} : Bool}, +e_rq: RoomFor(1n+q))
  -> {D.feed(D.State{m, Nat.add(Laws.len(S.chunks(fuel, 1n+q, xs)), k), D.line(D.KSize{r0, acc})}, Laws.cat(S.chunks(fuel, 1n+q, xs), ys))
      == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, xs, acc)})}, ys) : D.State}:
  match fuel xs:
    case 0n Nil{}:
      {==}
    case 0n Con{h, t}:
      DL.absurd_ft({D.feed(D.State{m, Nat.add(Laws.len(S.chunks(0n, 1n+q, Con{h, t})), k), D.line(D.KSize{r0, acc})},
          Laws.cat(S.chunks(0n, 1n+q, Con{h, t}), ys))
        == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, Con{h, t}, acc)})}, ys) : D.State}, e_fuel)
    case 1n+f Nil{}:
      {==}
    case 1n+(+f) Con{+h, +t}:
      %Equal.sym(List<&2, U32>, Laws.cat(Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), S.chunks(f, 1n+q, List.drop(&2, U32, t, q))), ys), Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys)),
        DL.cat_assoc(S.chunk(Con{h, List.take(&2, U32, t, q)}), S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys)) :
        {D.feed(D.State{m, Nat.add(Laws.len(Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), S.chunks(f, 1n+q, List.drop(&2, U32, t, q)))), k), D.line(D.KSize{r0, acc})}, _) == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, Con{h, t}, acc)})}, ys) : D.State}
      %Equal.sym(Nat, Laws.len(Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), S.chunks(f, 1n+q, List.drop(&2, U32, t, q)))), Nat.add(Laws.len(S.chunk(Con{h, List.take(&2, U32, t, q)})), Laws.len(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)))), DL.len_cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), S.chunks(f, 1n+q, List.drop(&2, U32, t, q)))) :
        {D.feed(D.State{m, Nat.add(_, k), D.line(D.KSize{r0, acc})}, Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys))) == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, Con{h, t}, acc)})}, ys) : D.State}
      %NP.add_assoc(Laws.len(S.chunk(Con{h, List.take(&2, U32, t, q)})), Laws.len(S.chunks(f, 1n+q, List.drop(&2, U32, t, q))), k) :
        {D.feed(D.State{m, _, D.line(D.KSize{r0, acc})}, Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys))) == D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, Con{h, t}, acc)})}, ys) : D.State}
      Equal.trans(D.State,
        D.feed(D.State{m, Nat.add(Laws.len(S.chunk(Con{h, List.take(&2, U32, t, q)})), Nat.add(Laws.len(S.chunks(f, 1n+q, List.drop(&2, U32, t, q))), k)), D.line(D.KSize{r0, acc})}, Laws.cat(S.chunk(Con{h, List.take(&2, U32, t, q)}), Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys))),
        D.feed(D.State{m, Nat.add(Laws.len(S.chunks(f, 1n+q, List.drop(&2, U32, t, q))), k), D.line(D.KSize{r0, D.rev(U32, Con{h, List.take(&2, U32, t, q)}, acc)})}, Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys)),
        D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, Con{h, t}, acc)})}, ys),
        chunk_feed(m, r0, Con{h, List.take(&2, U32, t, q)}, acc, Nat.add(Laws.len(S.chunks(f, 1n+q, List.drop(&2, U32, t, q))), k), Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys),
          DL.le_zero_l(Laws.len(List.take(&2, U32, t, q))),
          DL.le_trans(1n+Laws.len(List.take(&2, U32, t, q)), 1n+q, N.LIMIT(), len_take(t, q), e_q),
          room_mono(1n+Laws.len(List.take(&2, U32, t, q)), 1n+q, len_take(t, q), e_rq)),
        Equal.trans(D.State,
          D.feed(D.State{m, Nat.add(Laws.len(S.chunks(f, 1n+q, List.drop(&2, U32, t, q))), k), D.line(D.KSize{r0, D.rev(U32, Con{h, List.take(&2, U32, t, q)}, acc)})}, Laws.cat(S.chunks(f, 1n+q, List.drop(&2, U32, t, q)), ys)),
          D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, List.drop(&2, U32, t, q), D.rev(U32, Con{h, List.take(&2, U32, t, q)}, acc))})}, ys),
          D.feed(D.State{m, k, D.line(D.KSize{r0, D.rev(U32, Con{h, t}, acc)})}, ys),
          chunks_feed(m, r0, q, f, List.drop(&2, U32, t, q), D.rev(U32, Con{h, List.take(&2, U32, t, q)}, acc), k, ys,
            DL.le_trans(Laws.len(List.drop(&2, U32, t, q)), Laws.len(t), f, len_drop(t, q), e_fuel), e_q, e_rq),
          Equal.cong(List<&2, U32>, D.State, x => D.feed(D.State{m, k, D.line(D.KSize{r0, x})}, ys),
            D.rev(U32, List.drop(&2, U32, t, q), D.rev(U32, Con{h, List.take(&2, U32, t, q)}, acc)), D.rev(U32, Con{h, t}, acc),
            rev_take_drop(t, q, h <> acc))))

# The last chunk "0" CRLF and the empty trailer section CRLF: complete.
def last_chunk(-m: M.Method, -r0: M.Response, -a: List<&2, U32>, -k: Nat, -ys: List<&2, U32>)
  -> {D.feed(D.State{m, Nat.add(Laws.len(B.from_ascii("0\r\n\r\n")), k), D.line(D.KSize{r0, a})}, Laws.cat(B.from_ascii("0\r\n\r\n"), ys))
      == D.feed(D.State{m, k, D.Complete{D.with_body(r0, a), Nil{}}}, ys) : D.State}:
  {==}

# The framing
# -----------

def has_true(-l: String, hs: List<&2, M.Header>) -> {H.has.go(l, hs, True{}) == True{} : Bool}:
  match hs:
    case Nil{}:
      {==}
    case Con{h, t}:
      {==}

def ga_nohit(+l: String, +t: List<&2, M.Header>, hit: Bool, -v: String, +acc: List<&2, String>,
  e: {H.has.go(l, t, hit) == False{} : Bool},
  ih: {H.has.go(l, t, False{}) == False{} : Bool} -> {H.get_all.go(l, t, acc) == B.rev(String, acc, Nil{}) : List<&2, String>})
  -> {H.get_all.go(l, t, H.get_all.pick(hit, v, acc)) == B.rev(String, acc, Nil{}) : List<&2, String>}:
  match hit:
    case True{}:
      DL.absurd_tf({H.get_all.go(l, t, v <> acc) == B.rev(String, acc, Nil{}) : List<&2, String>},
        Equal.trans(Bool, True{}, H.has.go(l, t, True{}), False{}, Equal.sym(Bool, H.has.go(l, t, True{}), True{}, has_true(l, t)), e))
    case False{}:
      ih(e)

# No header lowers to l: get_all finds nothing.
def ga_none(+l: String, hs: List<&2, M.Header>, +acc: List<&2, String>, e: {H.has.go(l, hs, False{}) == False{} : Bool})
  -> {H.get_all.go(l, hs, acc) == B.rev(String, acc, Nil{}) : List<&2, String>}:
  match hs:
    case Nil{}:
      {==}
    case Con{M.Header{+n, +v}, +t}:
      ga_nohit(l, t, String.eq(l, H.lower(n)), v, acc, e, x => ga_none(l, t, acc, x))

# H.has(name, hs) is False: get_all(name, hs) is empty.
def has_none(+name: String, +hs: List<&2, M.Header>, e: {H.has(name, hs) == False{} : Bool})
  -> {D.nonempty(H.get_all(name, hs)) == False{} : Bool}:
  Equal.cong(List<&2, String>, Bool, x => D.nonempty(x), H.get_all(name, hs), Nil{}, ga_none(H.lower(name), hs, Nil{}, e))

# Transfer-Encoding chunked alone, no Content-Length, HTTP/1.1: a chunk-size line.
def te_chunked(te: List<&2, String>, -cl: List<&2, String>, -k: Nat, -r: M.Response,
  e_te: {D.chunked_only(te) == True{} : Bool}, e_cl: {D.nonempty(cl) == False{} : Bool})
  -> {D.framing.te(M.Http11{}, te, cl, k, r) == D.line(D.KSize{r, Nil{}}) : D.Phase}:
  match te:
    case Nil{}:
      DL.absurd_ft({D.framing.te(M.Http11{}, Nil{}, cl, k, r) == D.line(D.KSize{r, Nil{}}) : D.Phase}, e_te)
    case Con{x, t}:
      %Equal.sym(Bool, D.nonempty(cl), False{}, e_cl) :
        {D.te_framing(_, False{}, D.chunked_only(Con{x, t}), r) == D.line(D.KSize{r, Nil{}}) : D.Phase}
      %Equal.sym(Bool, D.chunked_only(Con{x, t}), True{}, e_te) :
        {D.te_framing(False{}, False{}, _, r) == D.line(D.KSize{r, Nil{}}) : D.Phase}
      {==}

# After the head
# --------------

# The chunked body S.encode_chunked(1 + q, body), then rest, from the first
# chunk-size line: complete with the body, rest left over (reversed).
def after_head(-m: M.Method, -r0: M.Response, +q: Nat, +body: List<&2, U32>, +slack: Nat, +rest: List<&2, U32>,
  +e_q: {Nat.is_le(1n+q, N.LIMIT()) == True{} : Bool}, +e_rq: RoomFor(1n+q))
  -> {D.feed(D.State{m, Nat.add(Laws.len(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n"))), slack), D.line(D.KSize{r0, Nil{}})},
        Laws.cat(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n")), rest))
      == D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}} : D.State}:
  %Equal.sym(List<&2, U32>, Laws.cat(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n")), rest),
    Laws.cat(S.chunks(Laws.len(body), 1n+q, body), Laws.cat(B.from_ascii("0\r\n\r\n"), rest)),
    DL.cat_assoc(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n"), rest)) :
    {D.feed(D.State{m, Nat.add(Laws.len(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n"))), slack), D.line(D.KSize{r0, Nil{}})}, _)
      == D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}} : D.State}
  %Equal.sym(Nat, Laws.len(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n"))),
    Nat.add(Laws.len(S.chunks(Laws.len(body), 1n+q, body)), Laws.len(B.from_ascii("0\r\n\r\n"))),
    DL.len_cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n"))) :
    {D.feed(D.State{m, Nat.add(_, slack), D.line(D.KSize{r0, Nil{}})},
        Laws.cat(S.chunks(Laws.len(body), 1n+q, body), Laws.cat(B.from_ascii("0\r\n\r\n"), rest)))
      == D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}} : D.State}
  %NP.add_assoc(Laws.len(S.chunks(Laws.len(body), 1n+q, body)), Laws.len(B.from_ascii("0\r\n\r\n")), slack) :
    {D.feed(D.State{m, _, D.line(D.KSize{r0, Nil{}})},
        Laws.cat(S.chunks(Laws.len(body), 1n+q, body), Laws.cat(B.from_ascii("0\r\n\r\n"), rest)))
      == D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}} : D.State}
  Equal.trans(D.State,
    D.feed(D.State{m, Nat.add(Laws.len(S.chunks(Laws.len(body), 1n+q, body)), Nat.add(Laws.len(B.from_ascii("0\r\n\r\n")), slack)), D.line(D.KSize{r0, Nil{}})},
      Laws.cat(S.chunks(Laws.len(body), 1n+q, body), Laws.cat(B.from_ascii("0\r\n\r\n"), rest))),
    D.feed(D.State{m, Nat.add(Laws.len(B.from_ascii("0\r\n\r\n")), slack), D.line(D.KSize{r0, D.rev(U32, body, Nil{})})},
      Laws.cat(B.from_ascii("0\r\n\r\n"), rest)),
    D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}},
    chunks_feed(m, r0, q, Laws.len(body), body, Nil{}, Nat.add(Laws.len(B.from_ascii("0\r\n\r\n")), slack),
      Laws.cat(B.from_ascii("0\r\n\r\n"), rest), le_refl(Laws.len(body)), e_q, e_rq),
    Equal.trans(D.State,
      D.feed(D.State{m, Nat.add(Laws.len(B.from_ascii("0\r\n\r\n")), slack), D.line(D.KSize{r0, D.rev(U32, body, Nil{})})},
        Laws.cat(B.from_ascii("0\r\n\r\n"), rest)),
      D.feed(D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), Nil{}}}, rest),
      D.State{m, slack, D.Complete{D.with_body(r0, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}},
      last_chunk(m, r0, D.rev(U32, body, Nil{}), slack, rest),
      DL.feed_complete(m, slack, D.with_body(r0, D.rev(U32, body, Nil{})), rest, Nil{})))

# The law
# -------

def chunked_law(meth: M.Method, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  +q: Nat, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, +e1: {S.response_ok(M.Response{M.Http11{}, st, rs, hs, body}) == True{} : Bool},
  e2: {D.chunked_only(H.get_all("transfer-encoding", hs)) == True{} : Bool},
  e3: {H.has("content-length", hs) == False{} : Bool},
  +e5: {Nat.is_le(1n+q, N.LIMIT()) == True{} : Bool}, hr: RoomFor(1n+q))
  -> {D.response(meth, Nat.add(Laws.len(Laws.cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), S.encode_chunked(1n+q, body))), slack), Laws.cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), Laws.cat(S.encode_chunked(1n+q, body), rest)))
      == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}:
  %Equal.sym(Nat, Laws.len(Laws.cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), S.encode_chunked(1n+q, body))), Nat.add(Laws.len(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body})), Laws.len(S.encode_chunked(1n+q, body))), DL.len_cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), S.encode_chunked(1n+q, body))) :
    {D.finish(D.feed(D.init(meth, Nat.add(_, slack)), Laws.cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), Laws.cat(S.encode_chunked(1n+q, body), rest)))) == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %NP.add_assoc(Laws.len(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body})), Laws.len(S.encode_chunked(1n+q, body)), slack) :
    {D.finish(D.feed(D.init(meth, _), Laws.cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), Laws.cat(S.encode_chunked(1n+q, body), rest)))) == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.init(meth, Nat.add(Laws.len(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body})), Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack))), Laws.cat(S.encode_head(M.Response{M.Http11{}, st, rs, hs, body}), Laws.cat(S.encode_chunked(1n+q, body), rest))),
    D.feed(D.State{meth, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), DL.head_phase(meth, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), M.Response{M.Http11{}, st, rs, hs, body})}, Laws.cat(S.encode_chunked(1n+q, body), rest)),
    DL.head_at(meth, M.Response{M.Http11{}, st, rs, hs, body}, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), Laws.cat(S.encode_chunked(1n+q, body), rest),
      DL.status_value_show(st, DL.bs_100(st, DL.response_ok_status(M.Response{M.Http11{}, st, rs, hs, body}, e1)), DL.bs_999(st, DL.response_ok_status(M.Response{M.Http11{}, st, rs, hs, body}, e1))),
      DL.response_ok_head(M.Response{M.Http11{}, st, rs, hs, body}, e1))) :
    {D.finish(_) == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.Phase, DL.head_phase(meth, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), M.Response{M.Http11{}, st, rs, hs, body}),
    D.framing.te(M.Http11{}, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), M.Response{M.Http11{}, st, rs, hs, Nil{}}),
    DL.head_phase_body(meth, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), M.Http11{}, st, rs, hs, body, DL.bs_101(st, DL.response_ok_status(M.Response{M.Http11{}, st, rs, hs, body}, e1)), DL.bs_200(st, DL.response_ok_status(M.Response{M.Http11{}, st, rs, hs, body}, e1)),
      DL.no_body_false(meth, st, e0, DL.bs_204(st, DL.response_ok_status(M.Response{M.Http11{}, st, rs, hs, body}, e1)), DL.bs_304(st, DL.response_ok_status(M.Response{M.Http11{}, st, rs, hs, body}, e1))))) :
    {D.finish(D.feed(D.State{meth, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), _}, Laws.cat(S.encode_chunked(1n+q, body), rest))) == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.Phase,
    D.framing.te(M.Http11{}, H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), M.Response{M.Http11{}, st, rs, hs, Nil{}}),
    D.line(D.KSize{M.Response{M.Http11{}, st, rs, hs, Nil{}}, Nil{}}),
    te_chunked(H.get_all("transfer-encoding", hs), H.get_all("content-length", hs), Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), M.Response{M.Http11{}, st, rs, hs, Nil{}}, e2,
      has_none("content-length", hs, e3))) :
    {D.finish(D.feed(D.State{meth, Nat.add(Laws.len(S.encode_chunked(1n+q, body)), slack), _}, Laws.cat(S.encode_chunked(1n+q, body), rest))) == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(D.State,
    D.feed(D.State{meth, Nat.add(Laws.len(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n"))), slack), D.line(D.KSize{M.Response{M.Http11{}, st, rs, hs, Nil{}}, Nil{}})},
      Laws.cat(Laws.cat(S.chunks(Laws.len(body), 1n+q, body), B.from_ascii("0\r\n\r\n")), rest)),
    D.State{meth, slack, D.Complete{D.with_body(M.Response{M.Http11{}, st, rs, hs, Nil{}}, D.rev(U32, body, Nil{})), D.rev(U32, rest, Nil{})}},
    after_head(meth, M.Response{M.Http11{}, st, rs, hs, Nil{}}, q, body, slack, rest,
      e5, hr)) :
    {D.finish(_) == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(List<&2, U32>, D.rev(U32, D.rev(U32, body, Nil{}), Nil{}), body, DL.rev_rev(U32, body)) :
    {Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, _}, D.rev(U32, D.rev(U32, rest, Nil{}), Nil{})}} == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  %Equal.sym(List<&2, U32>, D.rev(U32, D.rev(U32, rest, Nil{}), Nil{}), rest, DL.rev_rev(U32, rest)) :
    {Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, _}} == Done{M.Decoded{M.Response{M.Http11{}, st, rs, hs, body}, rest}} : Laws.Res()}
  {==}

# The law's statement for r, n, rest, slack.
def chunked_goal(meth: M.Method, +r: M.Response, n: Nat, +rest: List<&2, U32>, slack: Nat) -> Type:
  {D.response(meth,
      Nat.add(Laws.len(Laws.cat(S.encode_head(r), S.encode_chunked(n, S.response_body(r)))), slack),
      Laws.cat(S.encode_head(r), Laws.cat(S.encode_chunked(n, S.response_body(r)), rest)))
    == Done{M.Decoded{r, rest}} : Laws.Res()}

def chunked_n(meth: M.Method, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  n: Nat, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, e1: {S.response_ok(M.Response{M.Http11{}, st, rs, hs, body}) == True{} : Bool},
  e2: {D.chunked_only(H.get_all("transfer-encoding", hs)) == True{} : Bool},
  e3: {H.has("content-length", hs) == False{} : Bool},
  e4: {Nat.is_le(1n, n) == True{} : Bool}, e5: {Nat.is_le(n, N.LIMIT()) == True{} : Bool}, hr: RoomFor(n))
  -> chunked_goal(meth, M.Response{M.Http11{}, st, rs, hs, body}, n, rest, slack):
  match n:
    case 0n:
      DL.absurd_ft(chunked_goal(meth, M.Response{M.Http11{}, st, rs, hs, body}, 0n, rest, slack), e4)
    case 1n+q:
      chunked_law(meth, st, rs, hs, body, q, rest, slack, e0, e1, e2, e3, e5, hr)

def chunked_v(meth: M.Method, v: M.Version, +st: Nat, +rs: String, +hs: List<&2, M.Header>, +body: List<&2, U32>,
  n: Nat, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, e1: {S.response_ok(M.Response{v, st, rs, hs, body}) == True{} : Bool},
  e2: {D.chunked_only(H.get_all("transfer-encoding", hs)) == True{} : Bool},
  e3: {H.has("content-length", hs) == False{} : Bool},
  e4: {Nat.is_le(1n, n) == True{} : Bool}, e5: {Nat.is_le(n, N.LIMIT()) == True{} : Bool},
  e6: {Laws.is_http11(M.Response{v, st, rs, hs, body}) == True{} : Bool}, hr: RoomFor(n))
  -> chunked_goal(meth, M.Response{v, st, rs, hs, body}, n, rest, slack):
  match v:
    case M.Http10{}:
      DL.absurd_ft(chunked_goal(meth, M.Response{M.Http10{}, st, rs, hs, body}, n, rest, slack), e6)
    case M.Http11{}:
      chunked_n(meth, st, rs, hs, body, n, rest, slack, e0, e1, e2, e3, e4, e5, hr)

# Law 11, given the room of the chunk-size line of n: hex_show(n) fits the
# line limit (every chunk is at most n bytes; see the header).
def chunked_given_room(meth: M.Method, r: M.Response, n: Nat, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, e1: {S.response_ok(r) == True{} : Bool},
  e2: {D.chunked_only(H.get_all("transfer-encoding", S.response_headers(r))) == True{} : Bool},
  e3: {H.has("content-length", S.response_headers(r)) == False{} : Bool},
  e4: {Nat.is_le(1n, n) == True{} : Bool}, e5: {Nat.is_le(n, N.LIMIT()) == True{} : Bool},
  e6: {Laws.is_http11(r) == True{} : Bool}, hr: RoomFor(n))
  -> chunked_goal(meth, r, n, rest, slack):
  match r:
    case M.Response{v, st, rs, hs, body}:
      chunked_v(meth, v, st, rs, hs, body, n, rest, slack, e0, e1, e2, e3, e4, e5, e6, hr)

# Law 11 for any chunk size up to N.LIMIT(), given RoomAll (see the header).
def chunked_room_all(meth: M.Method, r: M.Response, +n: Nat, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, e1: {S.response_ok(r) == True{} : Bool},
  e2: {D.chunked_only(H.get_all("transfer-encoding", S.response_headers(r))) == True{} : Bool},
  e3: {H.has("content-length", S.response_headers(r)) == False{} : Bool},
  e4: {Nat.is_le(1n, n) == True{} : Bool}, +e5: {Nat.is_le(n, N.LIMIT()) == True{} : Bool},
  e6: {Laws.is_http11(r) == True{} : Bool}, hr: RoomAll())
  -> chunked_goal(meth, r, n, rest, slack):
  chunked_given_room(meth, r, n, rest, slack, e0, e1, e2, e3, e4, e5, e6, hr(n, e5))

# Law 11 as stated, for every chunk size n <= 0xFFFF: no extra hypothesis.
def chunked_small(meth: M.Method, r: M.Response, +n: Nat, +rest: List<&2, U32>, +slack: Nat,
  e0: {D.is_head(meth) == False{} : Bool}, e1: {S.response_ok(r) == True{} : Bool},
  e2: {D.chunked_only(H.get_all("transfer-encoding", S.response_headers(r))) == True{} : Bool},
  e3: {H.has("content-length", S.response_headers(r)) == False{} : Bool},
  e4: {Nat.is_le(1n, n) == True{} : Bool}, e5: {Nat.is_le(n, N.LIMIT()) == True{} : Bool},
  e6: {Laws.is_http11(r) == True{} : Bool}, es: {Nat.is_le(n, 65535n) == True{} : Bool})
  -> chunked_goal(meth, r, n, rest, slack):
  chunked_given_room(meth, r, n, rest, slack, e0, e1, e2, e3, e4, e5, e6, hex_room_small(n, es))

# Law 11 (LAWS.bend bounds the chunk size by 65535; see the note above).
def Laws.response_chunked_roundtrip(meth, r, n, rest, slack, e0, e1, e2, e3, e4, e5, e6, es):
  chunked_small(meth, r, n, rest, slack, e0, e1, e2, e3, e4, e5, e6, es)
